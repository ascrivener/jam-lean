import Services.Bootstrap.Fmt.Hex
import Services.Bootstrap.Fmt.Dec4
import Services.Bootstrap.Fmt.Du5

/-!
# Byte templates and argument functions, as `core::fmt::write` meets them

- `TItem`, `Tmpl μ a ts`: memory μ holds at a the byte template of the items ts, then 0. A
  literal of n octets (1 ≤ n < 128) is the byte n and the octets; an argument with default
  options is the byte 0xC0.
- `ArgOk`: what `core::fmt::write` assumes of an argument's formatting function e with value v,
  relative to the caller's starting point (μA, sA, spA). From any memory the run reaches without
  touching the caller's frame (`Keeps pb spA …` from μA), and a `Formatter` into a `String`, it
  either returns `Ok` with the `String` at most M octets longer, within 7n + 2(cap' − cap) + C
  steps, or reaches a failed allocator call. `hex32_ok`, `dec32_ok` and `dec64_ok` give it for
  `{:x}` of a u32, `{}` of a u32 and `{}` of a u64.
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

/-- One item of a byte template: a literal of n octets, or an argument with default options. -/
inductive TItem where
  | lit (n : Nat)
  | arg

/-- The template of the items ts at a: each literal's byte n (1 ≤ n < 128) and its n octets, each
    argument's byte 0xC0, then the byte 0; all readable. -/
def Tmpl (μ : Memory) : Nat → List TItem → Prop
  | a, [] => rdN μ a 1 = 0 ∧ μ.readable a = true
  | a, .lit n :: ts => 1 ≤ n ∧ n < 128 ∧ rdN μ a 1 = n ∧
      (∀ b, a ≤ b → b < a + 1 + n → μ.readable b = true) ∧ Tmpl μ (a + 1 + n) ts
  | a, .arg :: ts => rdN μ a 1 = 192 ∧ μ.readable a = true ∧ Tmpl μ (a + 1) ts

/-- The template's size in octets, with its final 0. -/
def tsize : List TItem → Nat
  | [] => 1
  | .lit n :: ts => n + 1 + tsize ts
  | .arg :: ts => 1 + tsize ts

/-- The number of arguments. -/
def nargs : List TItem → Nat
  | [] => 0
  | .lit _ :: ts => nargs ts
  | .arg :: ts => nargs ts + 1

/-- The most octets the template writes, each argument writing at most M. -/
def tlen (M : Nat) : List TItem → Nat
  | [] => 0
  | .lit n :: ts => n + tlen M ts
  | .arg :: ts => M + tlen M ts

/-- The steps `core::fmt::write` takes over the template, past the `String`'s growth: 7n + 2100
    for a literal of n octets, 7M + C + 100 for an argument. -/
def tcost (M C : Nat) : List TItem → Nat
  | [] => 40
  | .lit n :: ts => 7 * n + 2100 + tcost M C ts
  | .arg :: ts => 7 * M + C + 100 + tcost M C ts

/-- The literals' total length. -/
def tlits : List TItem → Nat
  | [] => 0
  | .lit n :: ts => n + tlits ts
  | .arg :: ts => tlits ts

theorem tsize_pos (ts : List TItem) : 1 ≤ tsize ts := by
  cases ts with
  | nil => simp [tsize]
  | cons it ts => cases it <;> simp [tsize] <;> omega

theorem tlits_le (M : Nat) (ts : List TItem) : tlits ts ≤ tlen M ts := by
  induction ts with
  | nil => simp [tlits, tlen]
  | cons it ts ih => cases it <;> simp [tlits, tlen] <;> omega

theorem tlits_lt (ts : List TItem) : tlits ts < tsize ts := by
  induction ts with
  | nil => simp [tlits, tsize]
  | cons it ts ih => cases it <;> simp [tlits, tsize] <;> omega

/-- A template is kept by a change that keeps the octets and their readability below 196608. -/
theorem Tmpl.congr {μ μ' : Memory} :
    ∀ (ts : List TItem) (a : Nat), Tmpl μ a ts → a + tsize ts ≤ 196608 →
      (∀ b, b < 196608 → μ'.read b = μ.read b ∧ μ'.readable b = μ.readable b) → Tmpl μ' a ts := by
  intro ts
  induction ts with
  | nil =>
    intro a h ha k
    simp only [Tmpl, tsize] at h ha ⊢
    refine ⟨by rw [rdN_frame (fun j hj => (k _ (by omega)).1)]; exact h.1, by rw [(k a (by omega)).2]; exact h.2⟩
  | cons it ts ih =>
    intro a h ha k
    cases it with
    | lit n =>
      simp only [Tmpl, tsize] at h ha ⊢
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      exact ⟨h1, h2, by rw [rdN_frame (fun j hj => (k _ (by omega)).1)]; exact h3,
        fun b hb1 hb2 => by rw [(k b (by omega)).2]; exact h4 b hb1 hb2, ih _ h5 (by omega) k⟩
    | arg =>
      simp only [Tmpl, tsize] at h ha ⊢
      obtain ⟨h1, h2, h3⟩ := h
      exact ⟨by rw [rdN_frame (fun j hj => (k _ (by omega)).1)]; exact h1, by rw [(k a (by omega)).2]; exact h2,
        ih _ h3 (by omega) k⟩

/-- **An argument's formatting function, as `core::fmt::write` calls it**: the function at e,
    called with the value v (ω₇) and a `Formatter` F into the `String` W (ω₈), from any memory μ
    the run reaches from the caller's (μA, sA) keeping the caller's frame (at or above spA), either
    returns `Ok` (ω₇ = 0) to the return address with the `String` n ≤ M octets longer (the text
    unspecified) within 7n + 2(cap' − cap) + C steps, the context kept, ω₀, ω₁, ω₅, ω₆ restored and
    from sp up only W … W + 24 changed; or reaches a failed allocator call within 2³⁰ + C steps. -/
def ArgOk (p : ByteArray) (P : Program) {X : Type} (R : HostRel X) (env : RefineHost.Env)
    (pb S0 S1 Z : Nat) (μA : Memory) (sA : State) (spA e v M C : Nat) : Prop :=
  ∀ (ω : Regs) (μ : Memory) (x : X) (s : State) (sp F W cap len ret t v5 v6 : Nat),
    HeapCtx env pb S0 S1 μ s → s.base % 8 = 0 → Keeps pb spA (fun _ => False) sA μA μ s →
    Fmtr sA s μ F W cap len →
    ω[0] = UInt64.ofNat ret → ω[1] = UInt64.ofNat sp → ω[5] = UInt64.ofNat v5 →
    ω[6] = UInt64.ofNat v6 → ω[7] = UInt64.ofNat v → ω[8] = UInt64.ofNat F →
    v5 < 18446744073709551616 → v6 < 18446744073709551616 →
    (0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) → P.jumpTable.getD (ret / 2 - 1) 0 = t →
    P.isBlockStart t = true →
    (S0 + Z ≤ sp ∧ sp % 8 = 0 ∧ 2147483648 + Z ≤ sp) → sp ≤ spA → (sp ≤ W ∧ W + 24 ≤ S1) →
    (sp ≤ F ∧ F + 24 ≤ S1 ∧ (F + 24 ≤ W ∨ W + 24 ≤ F)) → len + M < 134217728 →
    (∃ ω' μ' x' s' cap' n, n ≤ M ∧
      FreeStepsH p R e ω μ x t ω' μ' x' (7 * n + 2 * (cap' - cap) + C) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Fmtr sA s' μ' F W cap' (len + n) ∧ cap ≤ cap' ∧
      cap' ≤ max cap (max 8 (2 * (len + n))) ∧
      Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) sA μ μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0) ∨
    Exhausts p R pb e ω μ x (1073741824 + C)

/-- An `ArgOk` holds for a larger M and C. -/
theorem ArgOk.mono {p : ByteArray} {P : Program} {X : Type} {R : HostRel X} {env : RefineHost.Env}
    {pb S0 S1 Z : Nat} {μA : Memory} {sA : State} {spA e v M C M' C' : Nat}
    (h : ArgOk p P R env pb S0 S1 Z μA sA spA e v M C) (hM : M ≤ M') (hC : C ≤ C') :
    ArgOk p P R env pb S0 S1 Z μA sA spA e v M' C' := by
  intro ω μ x s sp F W cap len ret t v5 v6 H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hF hn
  rcases h ω μ x s sp F W cap len ret t v5 v6 H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hF
      (by omega) with ⟨ω', μ', x', s', cap', n, hn', run, rest⟩ | hx
  · exact Or.inl ⟨ω', μ', x', s', cap', n, by omega, run.mono (by omega), rest⟩
  · exact Or.inr (hx.mono (by omega))

/-- A frame with the stack pointer raised past the changed octets `E` below it. -/
theorem Keeps.lift {pb sp sp' : Nat} {E E' : Nat → Prop} {s₀ s : State} {μ₀ μ : Memory}
    (h : Keeps pb sp E s₀ μ₀ μ s) (hsp : sp ≤ sp') (hE : ∀ a, E a → sp' ≤ a → E' a) :
    Keeps pb sp' E' s₀ μ₀ μ s :=
  { h with hi := fun a ha hb hn => h.hi a (by omega) hb (fun e => hn (hE a e ha)) }

/-- A value of `size` octets at or above spA, readable from the caller's memory μA, stays readable
    in every memory the run reaches keeping the caller's frame: the stack's pages are outside the
    heap. -/
theorem Keeps.readable {env : RefineHost.Env} {pb S0 S1 spA : Nat} {sA s : State} {μA μ : Memory}
    (H : HeapCtx env pb S0 S1 μ s) (hS : S0 ≤ spA) (K : Keeps pb spA (fun _ => False) sA μA μ s)
    {a : Nat} (ha : spA ≤ a) (hr : μA.readable a = true) : μ.readable a = true := by
  have := H.hSb
  rw [(K.access a (Or.inr (by unfold pageSize; omega))).1]; exact hr

variable {X : Type} {R : HostRel X}

/-- **`{:x}` of a u32** (60525, `hex32`) as an argument: a value at v (4 octets, at or above spA,
    readable in μA). -/
theorem hex32_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 Z : Nat) (hZ : 600 ≤ Z) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA v : Nat) (hS : S0 ≤ spA) (hv : spA ≤ v ∧ v + 4 < 4294967296)
    (hrv : ∀ a, v ≤ a → a < v + 4 → μA.readable a = true) :
    ArgOk p P R env pb S0 S1 Z μA sA spA 60525 v 8 2500 := by
  intro ω μ x s sp F W cap len ret t v5 v6 H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hF hn
  rcases hex32 (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω μ sA s sp F W v cap len ret t v5 v6 H hba hf
      h0 h1 h5 h6 h7 h8 ⟨hv5, hv6⟩ hret hjt hbt ⟨by omega, hsp.2.1, by omega⟩ hW hF ⟨by omega, hv.2⟩
      (fun a h1 h2 => K.readable H hS (by omega) (hrv a h1 h2)) hn with
    ⟨ω', μ', x', s', cap', n, hn', run, rest⟩ | hx
  · exact Or.inl ⟨ω', μ', x', s', cap', n, hn', run.mono (by omega), rest⟩
  · exact Or.inr (hx.mono (by omega))

/-- **`{}` of a u32** (68146, `dec32`) as an argument: a value at v (4 octets). -/
theorem dec32_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 Z : Nat) (hZ : 600 ≤ Z) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA v : Nat) (hS : S0 ≤ spA) (hv : spA ≤ v ∧ v + 4 < 4294967296)
    (hrv : ∀ a, v ≤ a → a < v + 4 → μA.readable a = true) :
    ArgOk p P R env pb S0 S1 Z μA sA spA 68146 v 10 2700 := by
  intro ω μ x s sp F W cap len ret t v5 v6 H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hF hn
  rcases dec32 (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω μ sA s sp F W v cap len ret t v5 v6 H hba hf
      h0 h1 h5 h6 h7 h8 ⟨hv5, hv6⟩ hret hjt hbt ⟨by omega, hsp.2.1, by omega⟩ hW hF ⟨by omega, hv.2⟩
      (fun a h1 h2 => K.readable H hS (by omega) (hrv a h1 h2)) hn with
    ⟨ω', μ', x', s', cap', n, hn', run, rest⟩ | hx
  · exact Or.inl ⟨ω', μ', x', s', cap', n, hn', run.mono (by omega), rest⟩
  · exact Or.inr (hx.mono (by omega))

/-- **`{}` of a u64** (68449, `dec64`) as an argument: a value at v (8 octets). -/
theorem dec64_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 Z : Nat) (hZ : 600 ≤ Z) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA v : Nat) (hS : S0 ≤ spA) (hv : spA ≤ v ∧ v + 8 < 4294967296)
    (hrv : ∀ a, v ≤ a → a < v + 8 → μA.readable a = true) :
    ArgOk p P R env pb S0 S1 Z μA sA spA 68449 v 20 2900 := by
  intro ω μ x s sp F W cap len ret t v5 v6 H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hF hn
  rcases dec64 (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω μ sA s sp F W v cap len ret t v5 v6 H hba hf
      h0 h1 h5 h6 h7 h8 ⟨hv5, hv6⟩ hret hjt hbt ⟨by omega, hsp.2.1, by omega⟩ hW hF ⟨by omega, hv.2⟩
      (fun a h1 h2 => K.readable H hS (by omega) (hrv a h1 h2)) hn with
    ⟨ω', μ', x', s', cap', n, hn', run, rest⟩ | hx
  · exact Or.inl ⟨ω', μ', x', s', cap', n, hn', run.mono (by omega), rest⟩
  · exact Or.inr (hx.mono (by omega))

end Services.Bootstrap.Fmt
