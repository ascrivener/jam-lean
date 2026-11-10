import Services.Bootstrap.Fmt.Write
import Services.Bootstrap.Fmt.FormatSteps

/-!
# `alloc::fmt::format_inner` (59375), frame-only: `FmtCall`

`format_inner` is what `format!` calls. It estimates the capacity from the template, allocates the
`String`'s buffer (`alloc`, through `AllocOk`), runs `core::fmt::write` into it (`fmt_write`) and
moves the `String` to O.

- `StrOut s s' μ O`: O holds a `String` (`Str`, some capacity and length) whose buffer, if any, is
  an allocated chunk of s' that no allocated chunk of s had. Its text is not stated.
- `FmtCall`: a call of `format_inner` returns to t with `StrOut`, the context kept, from sp up
  only O … O + 24 changed, and ω₀, ω₁, ω₅, ω₆ restored; or it reaches a failed allocator call.
- `format_inner`: `FmtCall` for every template of literals and default-option arguments whose
  functions are `ArgOk`, within `fmtCost M C ts` steps.
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **The `String` a formatting call returns, at O**: some capacity and length (`Str`), its buffer
    a chunk allocated in s' and fresh against s. The text is left unstated. -/
def StrOut (s s' : State) (μ : Memory) (O : Nat) : Prop := ∃ cap len, Str s s' μ O cap len

/-- **A call of `format_inner` (59375)** from (ω, μ, x) with allocator state s, output `String` at O
    (ω₇) and return address t: within N steps it either returns to t with the `String` at O
    (`StrOut`), the allocator's context kept with the same base, from sp up only O … O + 24 changed
    (`Keeps`), and ω₀, ω₁, ω₅, ω₆ restored; or it reaches a failed allocator call. -/
def FmtCall (p : ByteArray) {X : Type} (R : HostRel X) (env : RefineHost.Env) (pb S0 S1 : Nat)
    (ω : Regs) (μ : Memory) (x : X) (s : State) (sp O t N : Nat) : Prop :=
  (∃ ω' μ' x' s', FreeStepsH p R 59375 ω μ x t ω' μ' x' N ∧ HeapCtx env pb S0 S1 μ' s' ∧
    s'.base = s.base ∧ Keeps pb sp (fun a => O ≤ a ∧ a < O + 24) s μ μ' s' ∧ StrOut s s' μ' O ∧
    ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6]) ∨
  Exhausts p R pb 59375 ω μ x N

/-- The steps `format_inner` takes over the template ts, each argument writing at most M octets in
    7M + C steps. -/
def fmtCost (M C : Nat) (ts : List TItem) : Nat := 2147483648 + tcost M C ts + 30 * tsize ts + 1000

/-- A `String` moved: its three words copied to O. -/
theorem Str.move {s₀ s : State} {μ μ' : Memory} {W O cap len : Nat} (h : Str s₀ s μ W cap len)
    (e0 : rdN μ' O 8 = rdN μ W 8) (e8 : rdN μ' (O + 8) 8 = rdN μ (W + 8) 8)
    (e16 : rdN μ' (O + 16) 8 = rdN μ (W + 16) 8) : Str s₀ s μ' O cap len :=
  ⟨e0.trans h.rc, e16.trans h.rl, h.le, h.lt, h.base, by
    rcases h.buf with h0 | ⟨c, hc, hu, ha, hs, hf⟩
    · exact Or.inl h0
    · exact Or.inr ⟨c, hc, hu, ha.trans e8.symm, hs, hf⟩⟩

variable {X : Type} {R : HostRel X}

/-- **The capacity estimate's loop** (59436 … 59536) over the items ts from the cursor c, with the
    sum L (ω₆) and the flag f ≤ 1 (ω₇): the estimate in ω₆ is 0 or 2(L + `tlits ts`), memory and
    ω₀ … ω₄ kept. -/
theorem fi_loop {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (μ : Memory) :
    ∀ (ts : List TItem) (c L f : Nat) (ω : Regs), Tmpl μ c ts → c + tsize ts < 4294967296 →
      L + tlits ts < 1073741824 → f ≤ 1 →
      ω[6] = UInt64.ofNat L → ω[7] = UInt64.ofNat f → ω[8] = UInt64.ofNat 128 →
      ω[9] = UInt64.ofNat 4611686018427387904 → ω[11] = UInt64.ofNat c →
      ∃ ω' e, (e = 0 ∨ e = 2 * (L + tlits ts)) ∧
        FreeStepsH p R 59436 ω μ x 59536 ω' μ x (30 * tsize ts) ∧
        ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[2] = ω[2] ∧ ω'[3] = ω[3] ∧ ω'[4] = ω[4] ∧
        ω'[6] = UInt64.ofNat e := by
  intro ts
  induction ts with
  | nil =>
    intro c L f ω hT hc hL hf h6 h7 _ _ h11
    simp only [Tmpl, tsize, tlits] at hT hc hL ⊢
    obtain ⟨ω', e, he, run, rest⟩ := fi_est (p := p) (P := P) (R := R) x ω μ c L f (by omega) (by omega) hf
      h6 h7 h11 hT.1 hT.2
    exact ⟨ω', e, by omega, run.mono (by omega), rest⟩
  | cons it ts ih =>
    intro c L f ω hT hc hL hf h6 h7 h8 h9 h11
    cases it with
    | lit n =>
      simp only [Tmpl, tsize, tlits] at hT hc hL ⊢
      obtain ⟨hn1, hn2, hb, hrb, hT'⟩ := hT
      obtain ⟨ω1, run1, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := fi_head (p := p) (P := P) (R := R)
        x ω μ c n (by omega) h11 hb (by omega) (hrb c (by omega) (by omega))
      obtain ⟨ω2, run2, b0, b1, b2, b3, b4, b6, b7, b8, b9, b11⟩ := fi_lit (p := p) (P := P) (R := R) x ω1 μ c n L
        (by omega) (by omega) ⟨hn1, hn2⟩ (a6.trans h6) a10 (a11.trans h11)
      obtain ⟨ω', e, he, run3, c0, c1, c2, c3, c4, c6⟩ := ih (c + 1 + n) (L + n) f ω2 hT' (by omega) (by omega) hf b6
        (b7.trans (a7.trans h7)) (b8.trans (a8.trans h8)) (b9.trans (a9.trans h9)) b11
      exact ⟨ω', e, by omega, ((run1.trans run2).trans run3).mono (by omega), c0.trans (b0.trans a0),
        c1.trans (b1.trans a1), c2.trans (b2.trans a2), c3.trans (b3.trans a3), c4.trans (b4.trans a4), c6⟩
    | arg =>
      simp only [Tmpl, tsize, tlits] at hT hc hL ⊢
      obtain ⟨hb, hrb, hT'⟩ := hT
      obtain ⟨ω1, run1, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := fi_head (p := p) (P := P) (R := R)
        x ω μ c 192 (by omega) h11 hb (by omega) hrb
      obtain ⟨ω2, f', hf', run2, b0, b1, b2, b3, b4, b6, b7, b8, b9, b11⟩ := fi_arg (p := p) (P := P) (R := R) x ω1 μ
        c L f (by omega) (by omega) hf (a6.trans h6) (a7.trans h7) (a8.trans h8) (a9.trans h9) a10 (a11.trans h11)
      obtain ⟨ω', e, he, run3, c0, c1, c2, c3, c4, c6⟩ := ih (c + 1) L f' ω2 hT' (by omega) (by omega) hf' b6 b7
        (b8.trans (a8.trans h8)) (b9.trans (a9.trans h9)) b11
      exact ⟨ω', e, he, ((run1.trans run2).trans run3).mono (by omega), c0.trans (b0.trans a0),
        c1.trans (b1.trans a1), c2.trans (b2.trans a2), c3.trans (b3.trans a3), c4.trans (b4.trans a4), c6⟩

/-- **`format_inner` from its call of `core::fmt::write`** (64495, return 59665) to its return: with
    the `String` (capacity cap, length 0, fresh against s) at U + 24 and the frame at U = S − 72,
    `core::fmt::write` runs (`fmt_write`) and `fi_ret` moves the `String` to O. -/
theorem fi_tail {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (S O tp args ret t v5 v6 M C cap : Nat) (ts : List TItem)
    (x : X) (ω : Regs) (μ μ1 : Memory) (s s1 : State)
    (H1 : HeapCtx env pb S0 S1 μ1 s1) (hba : s1.base % 8 = 0) (hs : Str s s1 μ1 (S - 72 + 24) cap 0)
    (KA : Keeps pb S (fun _ => False) s μ μ1 s1)
    (h0 : ω[0] = UInt64.ofNat 2588) (h1 : ω[1] = UInt64.ofNat (S - 72))
    (h7 : ω[7] = UInt64.ofNat (S - 72 + 24)) (h8 : ω[8] = UInt64.ofNat 77016)
    (h9 : ω[9] = UInt64.ofNat tp) (h10 : ω[10] = UInt64.ofNat args)
    (rO : rdN μ1 (S - 72 + 16) 8 = O) (r6 : rdN μ1 (S - 72 + 48) 8 = v6) (r5 : rdN μ1 (S - 72 + 56) 8 = v5)
    (r0 : rdN μ1 (S - 72 + 64) 8 = ret)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hS : S0 + 800 ≤ S ∧ S % 8 = 0 ∧ 2147484500 ≤ S ∧ S ≤ S1) (hO : S ≤ O ∧ O + 24 ≤ S1)
    (hro : RoW μ1) (hTm : Tmpl μ1 tp ts) (htp : 65536 ≤ tp ∧ tp + tsize ts + 24 ≤ 196608)
    (hargs : args < 18446744073709551616 ∧ args % 2 = 0)
    (hA : ArgsAt p P R env pb S0 S1 μ s S args 0 ts M C) (hi : nargs ts < 268435456)
    (hn : tlen M ts < 134217728) :
    (∃ ω' μ' x' s', FreeStepsH p R 64495 ω μ1 x t ω' μ' x' (tcost M C ts + 1073741940) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s1.base ∧ Keeps pb S (fun a => O ≤ a ∧ a < O + 24) s μ1 μ' s' ∧
      StrOut s s' μ' O ∧ ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6) ∨
    Exhausts p R pb 64495 ω μ1 x (2147483648 + tcost M C ts + 100) := by
  have hst : ∀ a, S0 ≤ a → a < S1 → μ1.writable a = true := H1.st
  have hS1 := H1.hS1
  have hSb := H1.hSb
  rcases fmt_write (p := p) (P := P) (R := R) env pb S0 S1 HA HR μ s S (S - 72) (S - 72 + 24) tp args 2588 59665
      ω[5].toNat ω[6].toNat M C ts x ω μ1 s1 cap 0 H1 hba hs KA h0 h1 UInt64.ofNat_toNat.symm
      UInt64.ofNat_toNat.symm h7 h8 h9 h10 ⟨UInt64.toNat_lt _, UInt64.toNat_lt _⟩ (by decide) jte_1293 bs_59665
      ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega⟩ hro hTm htp hargs hA hi (by omega) with
    ⟨ω2, μ2, x2, s2, cap2, n, hn2, run2, H2, hb2, hs2, hc1, hc2, K2, e0, e1, e5, e6, e7⟩ | hx
  · have kU : ∀ a, S - 72 ≤ a → a < S - 72 + 24 → μ2.read a = μ1.read a := fun a h1 h2 =>
      K2.hi a h1 (by omega) (by omega)
    have kU' : ∀ a, S - 72 + 48 ≤ a → a < S → μ2.read a = μ1.read a := fun a h1 h2 =>
      K2.hi a (by omega) (by omega) (by omega)
    obtain ⟨ω3, μ3, run3, f0, f1, f5, f6, m0, m8, m16, fr3, rd3, wr3⟩ := fi_ret (p := p) (P := P) (R := R) x2 ω2 μ2
      (S - 72) O ret t v5 v6 (rdN μ2 (S - 72 + 24) 8) (rdN μ2 (S - 72 + 32) 8) (rdN μ2 (S - 72 + 40) 8)
      ⟨by omega, by omega⟩ ⟨by omega, Or.inr (by omega)⟩ e1 e7 rfl rfl rfl
      (by rw [rdN_frame (fun j hj => kU _ (by omega) (by omega))]; exact rO)
      (by rw [rdN_frame (fun j hj => kU' _ (by omega) (by omega))]; exact r0)
      (by rw [rdN_frame (fun j hj => kU' _ (by omega) (by omega))]; exact r5)
      (by rw [rdN_frame (fun j hj => kU' _ (by omega) (by omega))]; exact r6)
      hret hjt hbt (fun a h1 h2 => Memory.readable_of_writable (H2.st a (by omega) (by omega)))
      (fun a h1 h2 => H2.st a (by omega) (by omega))
    have K3 : Keeps pb S (fun a => O ≤ a ∧ a < O + 24) s μ2 μ3 s2 :=
      Keeps.of_frame (Z := fun a => O ≤ a ∧ a < O + 24) hs2.base (fun a ha hz => fr3 a ha (by omega)) rd3 wr3
        (fun a hz => H2.st a (by omega) (by omega)) (fun a hz _ => hz)
        (fun a hz hg => by unfold Glob at hg; omega)
        (fun d hd hu a ha => by
          have := chunk_bounds H2.wf (hs2.base d hd hu)
          have := H2.hbT
          unfold InData at ha; omega)
    have K23 : Keeps pb S (fun a => O ≤ a ∧ a < O + 24) s μ1 μ3 s2 := by
      have := (K2.lift (sp' := S) (E' := fun a => O ≤ a ∧ a < O + 24) (by omega) (fun a h h' => by omega)).trans' K3
      rwa [Nat.max_self] at this
    have := hs2.lt
    refine Or.inl ⟨ω3, μ3, x2, s2, (run2.trans run3).mono (by omega),
      ctx_hi H2 (fun a ha => fr3 a (by omega) (Or.inl (by omega))) wr3, hb2, K23,
      ⟨cap2, 0 + n, hs2.move m0 m8 m16⟩, f0, by rw [f1, show S - 72 + 72 = S by omega], f5, f6⟩
  · exact Or.inr hx

/-- **`alloc::fmt::format_inner`, frame-only: `FmtCall`** (59375). Called with the output `String`'s
    address O (ω₇), a template ts at tp (ω₈, `Tmpl`, in the read-only data) and arguments at an even
    address args (ω₉) whose functions are `ArgOk` from this call's start (μ, s, S), and a return
    address ω₀ that `djump` resolves to t, it either returns to t with a `String` at O (`StrOut`,
    the text unspecified), the context kept, from S up only O … O + 24 changed, and ω₀, ω₁, ω₅, ω₆
    restored; or it reaches a failed allocator call. The bound is `fmtCost M C ts`. -/
theorem format_inner {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (S O tp args ret t M C : Nat) (ts : List TItem) (x : X) (ω : Regs) (μ : Memory) (s : State)
    (H : HeapCtx env pb S0 S1 μ s) (hba : s.base % 8 = 0)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat O)
    (h8 : ω[8] = UInt64.ofNat tp) (h9 : ω[9] = UInt64.ofNat args)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hS : S0 + 800 ≤ S ∧ S % 8 = 0 ∧ 2147484500 ≤ S ∧ S ≤ S1) (hO : S ≤ O ∧ O + 24 ≤ S1)
    (hro : RoW μ) (hTm : Tmpl μ tp ts) (htp : 65536 ≤ tp ∧ tp + tsize ts + 24 ≤ 196608)
    (hargs : args < 18446744073709551616 ∧ args % 2 = 0)
    (hA : ArgsAt p P R env pb S0 S1 μ s S args 0 ts M C) (hi : nargs ts < 268435456)
    (hn : tlen M ts < 134217728) :
    FmtCall p R env pb S0 S1 ω μ x s S O t (fmtCost M C ts) := by
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  have hS1 := H.hS1
  have hSb := H.hSb
  have hro0 := H.ro
  have htl := tlits_le M ts
  have hts := tlits_lt ts
  have htc := tcost_ge M C ts
  have hv5 := UInt64.toNat_lt ω[5]
  have hv6 := UInt64.toNat_lt ω[6]
  have hzd : ∀ (Z : Nat → Prop), (∀ a, Z a → S - 72 ≤ a) → ∀ d ∈ chunks s, d.used = true → ∀ a, InData d a →
      a < 4294967296 ∧ ¬ Z a := fun Z hZ d hd hu a ha => by
    have := chunk_bounds H.wf hd
    have := H.hbT
    unfold InData at ha
    exact ⟨by omega, fun hz => by have := hZ a hz; omega⟩
  -- the frame's writes keep the context, the caller's frame and the template
  have frame : ∀ μ1 : Memory, (∀ a, a < 4294967296 → (a < S - 72 ∨ S ≤ a) → μ1.read a = μ.read a) →
      (∀ a, μ1.readable a = μ.readable a) → (∀ a, μ1.writable a = μ.writable a) →
      HeapCtx env pb S0 S1 μ1 s ∧ Keeps pb S (fun _ => False) s μ μ1 s ∧ RoW μ1 ∧ Tmpl μ1 tp ts := by
    intro μ1 fr rd wr
    have K : Keeps pb S (fun _ => False) s μ μ1 s :=
      Keeps.of_frame (Z := fun a => S - 72 ≤ a ∧ a < S) (fun _ h _ => h) (fun a ha hz => fr a ha (by omega)) rd wr
        (fun a hz => hst a (by omega) (by omega)) (fun a hz h => by omega)
        (fun a hz hg => by unfold Glob at hg; omega) (hzd _ (fun a hz => hz.1))
    exact ⟨ctx_hi H (fun a ha => fr a (by omega) (Or.inl (by omega))) wr, K,
      hro.congr (fun a h1 h2 => K.ro_low H a h2), Tmpl.congr ts tp hTm (by omega) (K.ro_low H)⟩
  -- the end, from the call of `core::fmt::write`
  have fin : ∀ (ω1 : Regs) (μ1 : Memory) (x1 : X) (s1 : State) (cap n0 : Nat),
      FreeStepsH p R 59375 ω μ x 64495 ω1 μ1 x1 n0 → n0 ≤ 30 * tsize ts + 600 →
      HeapCtx env pb S0 S1 μ1 s1 → s1.base = s.base → Str s s1 μ1 (S - 72 + 24) cap 0 →
      Keeps pb S (fun _ => False) s μ μ1 s1 →
      ω1[0] = UInt64.ofNat 2588 → ω1[1] = UInt64.ofNat (S - 72) → ω1[7] = UInt64.ofNat (S - 72 + 24) →
      ω1[8] = UInt64.ofNat 77016 → ω1[9] = UInt64.ofNat tp → ω1[10] = UInt64.ofNat args →
      rdN μ1 (S - 72 + 16) 8 = O → rdN μ1 (S - 72 + 48) 8 = ω[6].toNat →
      rdN μ1 (S - 72 + 56) 8 = ω[5].toNat → rdN μ1 (S - 72 + 64) 8 = ret → RoW μ1 → Tmpl μ1 tp ts →
      FmtCall p R env pb S0 S1 ω μ x s S O t (fmtCost M C ts) := by
    intro ω1 μ1 x1 s1 cap n0 run1 hn0 H1 hb1 hs1 K1 a0 a1 a7 a8 a9 a10 rO r6 r5 r0 hro1 hTm1
    rcases fi_tail (p := p) (P := P) (R := R) env pb S0 S1 HA HR S O tp args ret t ω[5].toNat ω[6].toNat M C cap
        ts x1 ω1 μ μ1 s s1 H1 (by rw [hb1]; exact hba) hs1 K1 a0 a1 a7 a8 a9 a10 rO r6 r5 r0 hret hjt hbt hS hO
        hro1 hTm1 htp hargs hA hi hn with
      ⟨ω', μ', x', s', run', H', hb', K', hso, g0, g1, g5, g6⟩ | hx
    · refine Or.inl ⟨ω', μ', x', s', (run1.trans run').mono (by unfold fmtCost; omega), H', hb'.trans hb1, ?_,
        hso, g0.trans h0.symm, g1.trans h1.symm, g5.trans UInt64.ofNat_toNat, g6.trans UInt64.ofNat_toNat⟩
      have := (K1.mono (Nat.le_refl _) (fun a h => False.elim h)).trans' K'
      rwa [Nat.max_self] at this
    · exact Or.inr ((Exhausts.pre run1 hx).mono (by unfold fmtCost; omega))
  cases ts with
  | nil =>
    simp only [Tmpl, tsize] at hTm htp
    obtain ⟨ω1, μ1, run1, a0, a1, a7, a8, a9, a10, mO, m24, m32, m40, m48, m56, m64, fr1, rd1, wr1⟩ :=
      fi_entry0 (p := p) (P := P) (R := R) x ω μ S O tp args ret ω[5].toNat ω[6].toNat ⟨by omega, by omega⟩ h0 h1
        UInt64.ofNat_toNat.symm UInt64.ofNat_toNat.symm h7 h8 h9
        ⟨by omega, hv5, hv6, by omega, by omega, hargs.1, hargs.2⟩ hTm.1 hTm.2 (by omega)
        (fun a h1 h2 => hst a (by omega) (by omega))
    obtain ⟨H1, K1, hro1, hTm1⟩ := frame μ1 fr1 rd1 wr1
    exact fin ω1 μ1 x s 0 24 run1 (by omega) H1 rfl
      ⟨m24, by rw [show S - 72 + 24 + 16 = S - 72 + 40 by omega]; exact m40, Nat.le_refl _, by omega, fun _ h _ => h, Or.inl rfl⟩ K1 a0 a1 a7 a8 a9 a10 mO m48 m56 m64 hro1
      hTm1
  | cons it ts =>
    have hts' := tsize_pos ts
    -- the estimate
    have est : ∃ ω2 μ1 e, (e = 0 ∨ e = 2 * tlits (it :: ts)) ∧
        FreeStepsH p R 59375 ω μ x 59536 ω2 μ1 x (30 * tsize (it :: ts) + 20) ∧
        ω2[1] = UInt64.ofNat (S - 72) ∧ ω2[2] = UInt64.ofNat tp ∧ ω2[3] = UInt64.ofNat args ∧
        ω2[4] = UInt64.ofNat 0 ∧ ω2[6] = UInt64.ofNat e ∧
        rdN μ1 (S - 72 + 16) 8 = O ∧ rdN μ1 (S - 72 + 48) 8 = ω[6].toNat ∧
        rdN μ1 (S - 72 + 56) 8 = ω[5].toNat ∧ rdN μ1 (S - 72 + 64) 8 = ret ∧
        (∀ a, a < 4294967296 → (a < S - 72 ∨ S ≤ a) → μ1.read a = μ.read a) ∧
        (∀ a, μ1.readable a = μ.readable a) ∧ (∀ a, μ1.writable a = μ.writable a) := by
      have hb : rdN μ tp 1 = it.byte ∧ μ.readable tp = true ∧ 1 ≤ it.byte := by
        cases it with
        | lit n => exact ⟨hTm.2.2.1, hTm.2.2.2.1 tp (by omega) (by omega), hTm.1⟩
        | arg => exact ⟨hTm.1, hTm.2.1, by simp [TItem.byte]⟩
      obtain ⟨ω1, μ1, run1, a1, a2, a3, a4, a6, a7, a8, a9, a10, a11, mO, m48, m56, m64, fr1, rd1, wr1⟩ :=
        fi_entry (p := p) (P := P) (R := R) x ω μ S O tp args it.byte ret ω[5].toNat ω[6].toNat
          ⟨by omega, by omega⟩ h0 h1 UInt64.ofNat_toNat.symm UInt64.ofNat_toNat.symm h7 h8 h9
          ⟨by omega, hv5, hv6, by omega, by omega, hargs.1, hargs.2⟩ hb.1 (by omega) hb.2.1 (by omega)
          (fun a h1 h2 => hst a (by omega) (by omega))
      have hTm1 : Tmpl μ1 tp (it :: ts) := Tmpl.congr _ tp hTm (by omega)
        (fun a ha => ⟨fr1 a (by omega) (Or.inl (by omega)), rd1 a⟩)
      cases it with
      | lit n =>
        simp only [Tmpl, tsize, tlits, TItem.byte] at hTm1 htp hts a10 ⊢
        obtain ⟨hn1, hn2, -, -, hT'⟩ := hTm1
        obtain ⟨ω2, run2, b0, b1, b2, b3, b4, b6, b7, b8, b9, b11⟩ := fi_lit (p := p) (P := P) (R := R) x ω1 μ1 tp
          n 0 (by omega) (by omega) ⟨hn1, hn2⟩ a6 a10 a11
        obtain ⟨ω3, e, he, run3, c0, c1, c2, c3, c4, c6⟩ := fi_loop (p := p) (P := P) (R := R) x μ1 ts (tp + 1 + n)
          (0 + n) 0 ω2 hT' (by omega) (by omega) (Nat.zero_le _) b6 (b7.trans a7) (b8.trans a8) (b9.trans a9) b11
        exact ⟨ω3, μ1, e, by omega, ((run1.trans run2).trans run3).mono (by omega), c1.trans (b1.trans a1),
          c2.trans (b2.trans a2), c3.trans (b3.trans a3), c4.trans (b4.trans a4), c6, mO, m48, m56, m64, fr1, rd1,
          wr1⟩
      | arg =>
        simp only [Tmpl, tsize, tlits, TItem.byte] at hTm1 htp hts a10 ⊢
        obtain ⟨-, -, hT'⟩ := hTm1
        obtain ⟨ω2, f', hf', run2, b0, b1, b2, b3, b4, b6, b7, b8, b9, b11⟩ := fi_arg (p := p) (P := P) (R := R) x ω1
          μ1 tp 0 0 (by omega) (by omega) (Nat.zero_le _) a6 a7 a8 a9 a10 a11
        obtain ⟨ω3, e, he, run3, c0, c1, c2, c3, c4, c6⟩ := fi_loop (p := p) (P := P) (R := R) x μ1 ts (tp + 1)
          0 f' ω2 hT' (by omega) (by omega) hf' b6 b7 (b8.trans a8) (b9.trans a9) b11
        exact ⟨ω3, μ1, e, by omega, ((run1.trans run2).trans run3).mono (by omega), c1.trans (b1.trans a1),
          c2.trans (b2.trans a2), c3.trans (b3.trans a3), c4.trans (b4.trans a4), c6, mO, m48, m56, m64, fr1, rd1,
          wr1⟩
    obtain ⟨ω2, μ1, e, he, run2, a1, a2, a3, a4, a6, mO, m48, m56, m64, fr1, rd1, wr1⟩ := est
    have hel : e < 268435456 := by
      have := tlits_le M (it :: ts)
      omega
    obtain ⟨H1, K1, hro1, hTm1⟩ := frame μ1 fr1 rd1 wr1
    have hst1 : ∀ a, S0 ≤ a → a < S1 → μ1.writable a = true := H1.st
    by_cases he0 : e = 0
    · subst he0
      obtain ⟨ω3, μ3, run3, b0, b1, b7, b8, b9, b10, m24, m32, m40, fr3, rd3, wr3⟩ := fi_zero (p := p) (P := P)
        (R := R) x ω2 μ1 (S - 72) tp args ⟨by omega, by omega⟩ (by omega) hargs.1 a1 a2 a3 a4 a6
        (fun a h1 h2 => hst1 a (by omega) (by omega))
      have k3 : ∀ a, a < 4294967296 → (a < S - 72 ∨ S ≤ a) → μ3.read a = μ.read a := fun a ha h =>
        (fr3 a ha (by omega)).trans (fr1 a ha h)
      obtain ⟨H3, K3, hro3, hTm3⟩ := frame μ3 k3 (fun a => (rd3 a).trans (rd1 a)) (fun a => (wr3 a).trans (wr1 a))
      have k3' : ∀ a, (S - 72 + 16 ≤ a ∧ a < S - 72 + 24) ∨ (S - 72 + 48 ≤ a ∧ a < S) → μ3.read a = μ1.read a :=
        fun a ha => fr3 a (by omega) (by omega)
      exact fin ω3 μ3 x s 0 _ (run2.trans run3) (by omega) H3 rfl
        ⟨m24, by rw [show S - 72 + 24 + 16 = S - 72 + 40 by omega]; exact m40, Nat.le_refl _, by omega, fun _ h _ => h, Or.inl rfl⟩ K3 b0 (b1.trans a1) b7 b8 (b9.trans a2)
        (b10.trans a3)
        (by rw [rdN_frame (fun j hj => k3' _ (by omega))]; exact mO)
        (by rw [rdN_frame (fun j hj => k3' _ (by omega))]; exact m48)
        (by rw [rdN_frame (fun j hj => k3' _ (by omega))]; exact m56)
        (by rw [rdN_frame (fun j hj => k3' _ (by omega))]; exact m64) hro3 hTm3
    · obtain ⟨ω3, μ3, run3, b0, b1, b5, b6, b7, b8, mA, mT, fr3, rd3, wr3⟩ := fi_alloc (p := p) (P := P) (R := R)
        x ω2 μ1 (S - 72) tp args e ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) hargs.1 a1 a2 a3 a4 a6
        (fun a h1 h2 => hst1 a (by omega) (by omega))
      have k3 : ∀ a, a < 4294967296 → (a < S - 72 ∨ S ≤ a) → μ3.read a = μ.read a := fun a ha h =>
        (fr3 a ha (by omega)).trans (fr1 a ha h)
      obtain ⟨H3, K3, hro3, hTm3⟩ := frame μ3 k3 (fun a => (rd3 a).trans (rd1 a)) (fun a => (wr3 a).trans (wr1 a))
      rcases HA ω3 μ3 x s (S - 72) e 1 H3 (b1.trans a1) b7 b8 (Nat.le_refl _) (by decide) (by omega) (by omega)
          (by omega) (by omega) with
        ⟨ptr, s4, ω4, μ4, x4, run4, H4, hb4, K4, hc4, hf4, hp4, c7, c0, c1, c5, c6⟩ | ⟨ω4, μ4, x4, run4, c7, hfail⟩
      · have hcb := chunk_bounds H4.wf hc4
        simp only at hcb
        have hbT := H4.hbT
        have run5 := fi_ret_alloc (p := p) (P := P) (R := R) x4 ω4 μ4 (c0.trans b0)
        have k4 : ∀ a, S - 72 ≤ a → a < 4294967296 → μ4.read a = μ3.read a := fun a h1 h2 => K4.hi a h1 h2 id
        obtain ⟨ω6, μ6, run6, d0, d1, d7, d8, d9, d10, m24, m32, m40, fr6, rd6, wr6⟩ := fi_alloced (p := p)
          (P := P) (R := R) x4 ω4 μ4 (S - 72) tp args e ptr ⟨by omega, by omega⟩ (by omega) ⟨by omega, by omega⟩
          (c1.trans (b1.trans a1)) (c5.trans b5) (c6.trans b6) c7
          (by rw [rdN_frame (fun j hj => k4 _ (by omega) (by omega))]; exact mA)
          (by rw [rdN_frame (fun j hj => k4 _ (by omega) (by omega))]; exact mT)
          (fun a h1 h2 => Memory.readable_of_writable (H4.st a (by omega) (by omega)))
          (fun a h1 h2 => H4.st a (by omega) (by omega))
        have K6 : Keeps pb S (fun _ => False) s μ4 μ6 s4 :=
          Keeps.of_frame (Z := fun a => S - 72 + 24 ≤ a ∧ a < S - 72 + 48) K4.used
            (fun a ha hz => fr6 a ha (by omega)) rd6 wr6 (fun a hz => H4.st a (by omega) (by omega))
            (fun a hz h => by omega) (fun a hz hg => by unfold Glob at hg; omega)
            (hzd _ (fun a hz => by omega))
        have KA6 : Keeps pb S (fun _ => False) s μ μ6 s4 := by
          have := (K3.trans' (K4.lift (sp' := S) (E' := fun _ => False) (by omega) (fun a h _ => h))).trans' K6
          rwa [Nat.max_self, Nat.max_self] at this
        have hro6 := KA6.ro_low H
        have k6 : ∀ a, (S - 72 + 16 ≤ a ∧ a < S - 72 + 24) ∨ (S - 72 + 48 ≤ a ∧ a < S) → μ6.read a = μ1.read a :=
          fun a ha => by rw [fr6 a (by omega) (by omega), k4 a (by omega) (by omega), fr3 a (by omega) (by omega)]
        exact fin ω6 μ6 x4 s4 e _ (((run2.trans run3).trans run4).trans (run5.trans run6)) (by omega)
          (ctx_hi H4 (fun a ha => fr6 a (by omega) (Or.inl (by omega))) wr6) hb4
          ⟨m24, by rw [show S - 72 + 24 + 16 = S - 72 + 40 by omega]; exact m40, Nat.zero_le _, by omega, K4.used,
            Or.inr ⟨⟨ptr - 32, (e + 31) / 32 + 1, true⟩, hc4, rfl,
              by rw [show S - 72 + 24 + 8 = S - 72 + 32 by omega, m32]; show ptr - 32 + 32 = ptr; omega, rfl, hf4⟩⟩
          KA6 d0 (d1.trans (c1.trans (b1.trans a1))) d7 d8 d9 d10
          (by rw [rdN_frame (fun j hj => k6 _ (by omega))]; exact mO)
          (by rw [rdN_frame (fun j hj => k6 _ (by omega))]; exact m48)
          (by rw [rdN_frame (fun j hj => k6 _ (by omega))]; exact m56)
          (by rw [rdN_frame (fun j hj => k6 _ (by omega))]; exact m64)
          (hro.congr (fun a h1 h2 => hro6 a h2)) (Tmpl.congr _ tp hTm (by omega) hro6)
      · obtain ⟨hb, hfail⟩ := hfail
        exact Or.inr ⟨ω4, μ4, x4, 40611, ((run2.trans run3).trans run4).mono (by unfold fmtCost; omega), c7,
          Or.inl ⟨rfl, s, hb, _, hfail⟩⟩

end Services.Bootstrap.Fmt
