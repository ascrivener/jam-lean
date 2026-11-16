import Services.Bootstrap.Fmt.Write

/-!
# `core::fmt::write` (64495) over one argument with explicit options

`Fmt/Write.lean` covers templates of literals and default-option arguments (`Tmpl`). The hex path
of the code-hash and memo fields (57922, per octet) calls `core::fmt::write` with template 70833,
whose only item is an argument with explicit options (`{:02x}`):

- 0xC3: an argument (bits 7, 6) with an options word (bit 0) and a width (bit 1), no precision
  (bit 2), no explicit index (bit 3) and neither width nor precision taken from an argument
  (bits 4, 5);
- the options word, 4 octets (0x69000020 in 70833: fill ' ', the zero flag, width given, alignment
  unknown);
- the width, 2 octets (2 in 70833);
- the byte 0, the template's end.

`core::fmt::write` hands the argument's function a `Formatter` at T + 48 with that options word at
T + 64 and the width at T + 68 (precision 0 at T + 70), instead of the default word (64652 …
64838; 64495 … 64611, 64843 … 64600 and the end as for `Tmpl`).

- `FmtrO`: a `Formatter` as `Fmtr`, with options word o and width w.
- `ArgOkO`: `ArgOk` for a `Formatter` with options o and width w.
- `TmplO μ c o w`: the one-item template at c.
- `fmt_write_o`: `core::fmt::write` over such a template, as `fmt_write`.
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **A `Formatter` at F writing into the `String` at W, with options word o and width w**: as
    `Fmtr`, the options word o at F + 16 and the width w at F + 20. -/
structure FmtrO (s₀ s : State) (μ : Memory) (F W cap len o w : Nat) : Prop where
  buf : rdN μ F 8 = W
  vt : rdN μ (F + 8) 8 = 77016
  opts : rdN μ (F + 16) 4 = o
  width : rdN μ (F + 20) 2 = w
  vws : rdN μ 77040 8 = 2596
  vwc : rdN μ 77048 8 = 2592
  /-- The read-only data (65536 … 77144) is readable. -/
  vrd : ∀ a, 65536 ≤ a → a < 77144 → μ.readable a = true
  str : Str s₀ s μ W cap len

/-- **An argument's formatting function, called with explicit options**: `ArgOk`, for a
    `Formatter` with options word o and width w (`FmtrO`). -/
def ArgOkO (p : ByteArray) (P : Program) {X : Type} (R : HostRel X) (env : RefineHost.Env)
    (pb S0 S1 Z : Nat) (μA : Memory) (sA : State) (spA e v o w M C : Nat) : Prop :=
  ∀ (ω : Regs) (μ : Memory) (x : X) (s : State) (sp F W cap len ret t v5 v6 : Nat),
    HeapCtx env pb S0 S1 μ s → s.base % 8 = 0 → Keeps pb spA (fun _ => False) sA μA μ s →
    FmtrO sA s μ F W cap len o w →
    ω[0] = UInt64.ofNat ret → ω[1] = UInt64.ofNat sp → ω[5] = UInt64.ofNat v5 →
    ω[6] = UInt64.ofNat v6 → ω[7] = UInt64.ofNat v → ω[8] = UInt64.ofNat F →
    v5 < 18446744073709551616 → v6 < 18446744073709551616 →
    (0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) → P.jumpTable.getD (ret / 2 - 1) 0 = t →
    P.isBlockStart t = true →
    (S0 + Z ≤ sp ∧ sp % 8 = 0 ∧ 2147483648 + Z ≤ sp) → sp ≤ spA → (sp ≤ W ∧ W + 24 ≤ S1) → W + 24 ≤ spA →
    (sp ≤ F ∧ F + 24 ≤ S1 ∧ (F + 24 ≤ W ∨ W + 24 ≤ F)) → len + M < 134217728 →
    (∃ ω' μ' x' s' cap' n, n ≤ M ∧
      FreeStepsH p R e ω μ x t ω' μ' x' (7 * n + 2 * (cap' - cap) + C) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ FmtrO sA s' μ' F W cap' (len + n) o w ∧ cap ≤ cap' ∧
      cap' ≤ max cap (max 8 (2 * (len + n))) ∧
      Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) sA μ μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0) ∨
    Exhausts p R pb e ω μ x (1073741824 + C)

/-- The one-item template at c: 0xC3, the options word o (4 octets), the width w (2 octets), then
    0; all 8 octets readable. -/
def TmplO (μ : Memory) (c o w : Nat) : Prop :=
  rdN μ c 1 = 195 ∧ rdN μ (c + 1) 4 = o ∧ rdN μ (c + 5) 2 = w ∧ rdN μ (c + 7) 1 = 0 ∧
    ∀ a, c ≤ a → a < c + 8 → μ.readable a = true

/-- A word of n octets read back where it was just written. -/
theorem rdN_writeN_sameN (μ : Memory) (a n v : Nat) (ha : a + n ≤ 4294967296) :
    rdN (μ.writeN a (Num.encodeLE n v)) a n = v % 256 ^ n := by
  unfold rdN
  rw [Memory.readN_writeN_same _ _ _ _ (by simp) (by simp [two32]; omega), Num.decodeLE_encodeLE,
    Nat.pow_mul]

theorem sx4_small {o : Nat} (h : o < 2147483648) : Exec.u64 (Num.signed 4 o) = o := by
  unfold Exec.u64 Num.unsigned Num.signed
  rw [if_pos (show o < 2 ^ 31 by omega)]
  show ((2 ^ 64 + (o : Int)) % (2 ^ 64 : Int)).toNat = _
  omega

/-- 64611 … 64838, an argument with options word o and width w (0xC3 at the cursor c): the
    argument i (the index at T + 24), the pair (v, fn) at args + 16 i, is called through fn with v
    (ω₇) and the `Formatter` at T + 48 (ω₈): W at T + 48, the vtable at T + 56, o at T + 64 and w
    at T + 68. The return address is 2732 (64843); i and c + 7 stay in ω₅, ω₆. -/
theorem wro_arg {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs)
    (μ : Memory) (T W c i args v fn e o w : Nat) (hT : 65536 ≤ T ∧ T + 96 < 4294967296)
    (hc : c + 8 < 4294967296) (hW : W < 18446744073709551616) (hi : args + 16 * i + 16 < 4294967296)
    (ho : o < 2147483648)
    (h1 : ω[1] = UInt64.ofNat T) (h5 : ω[5] = UInt64.ofNat 195) (h9 : ω[9] = UInt64.ofNat c)
    (h12 : ω[12] = UInt64.ofNat W)
    (ro : rdN μ (c + 1) 4 = o) (rw' : rdN μ (c + 5) 2 = w)
    (rvt : rdN μ (T + 8) 8 = 77016) (ra : rdN μ (T + 16) 8 = args)
    (ri : rdN μ (T + 24) 8 = i) (rv : rdN μ (args + 16 * i) 8 = v) (rf : rdN μ (args + 16 * i + 8) 8 = fn)
    (hfn : 0 < fn ∧ fn ≤ 2806 ∧ fn % 2 = 0) (hjt : P.jumpTable.getD (fn / 2 - 1) 0 = e)
    (hbt : P.isBlockStart e = true)
    (hrc : ∀ a, c ≤ a → a < c + 8 → μ.readable a = true)
    (hra : ∀ a, args + 16 * i ≤ a → a < args + 16 * i + 16 → μ.readable a = true)
    (hr : ∀ a, T ≤ a → a < T + 32 → μ.readable a = true)
    (hw : ∀ a, T + 48 ≤ a → a < T + 72 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 64611 ω μ x e ω' μ' x 41 ∧
      ω'[0] = UInt64.ofNat 2732 ∧ ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat i ∧
      ω'[6] = UInt64.ofNat (c + 7) ∧ ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (T + 48) ∧
      rdN μ' (T + 48) 8 = W ∧ rdN μ' (T + 56) 8 = 77016 ∧ rdN μ' (T + 64) 4 = o ∧
      rdN μ' (T + 68) 2 = w ∧
      (∀ a, a < 4294967296 → (a < T + 48 ∨ T + 72 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hsx : sx8 195 = 18446744073709551555 := by decide
  have hi64 : i < 268435456 := by omega
  have e16 : args + i * 16 = args + 16 * i := by omega
  have rv' : rdN μ (args + i * 16) 8 = v := by rw [e16]; exact rv
  have rf' : rdN μ (args + i * 16 + 8) 8 = fn := by rw [e16]; exact rf
  have hra' : ∀ a, args + i * 16 ≤ a → a < args + i * 16 + 16 → μ.readable a = true := by rw [e16]; exact hra
  have hfn' : fn % 18446744073709551616 % 4294967296 = fn := by omega
  have hv64 : v < 18446744073709551616 := by rw [← rv]; exact rdN_lt64 μ _
  have hwl : w < 65536 := by rw [← rw']; exact rdN_lt μ _ 2
  have hsxo : Exec.u64 (Num.signed 4 o) = o := sx4_small ho
  have ho4 : o % 256 ^ 4 = o := Nat.mod_eq_of_lt (by omega)
  have hw2 : w % 256 ^ 2 = w := Nat.mod_eq_of_lt (by omega)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h9, h12, hT, hc, hW, hi, hi64, ho, ro, rw', hwl, hsxo, rvt, ra, ri, rv', rf', hfn, hfn', hjt,
      hbt, hrc, hra', hr, hw, hsx, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Nat.mod_eq_of_lt hW, Nat.mod_eq_of_lt hv64, rdN_lit8,
      Num.decodeLE_encodeLE, h1, h9, h12]
    · rw [rdN_writeN_sameN _ _ _ _ (by omega), ho4]
    · rw [rdN_writeN_sameN _ _ _ _ (by omega), hw2]

/-- 64843 … 64599, after the argument's `Ok`: the index (T + 24) goes to i + 1 and the loop goes on
    at 64600. -/
theorem wro_ret {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs)
    (μ : Memory) (T i : Nat) (hT : 65536 ≤ T ∧ T + 96 < 4294967296) (hi : i < 268435456)
    (h1 : ω[1] = UInt64.ofNat T) (h5 : ω[5] = UInt64.ofNat i) (h7 : ω[7] = UInt64.ofNat 0)
    (hw : ∀ a, T + 24 ≤ a → a < T + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 64843 ω μ x 64600 ω' μ' x 4 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[6] = ω[6] ∧ rdN μ' (T + 24) 8 = i + 1 ∧
      (∀ a, a < 4294967296 → (a < T + 24 ∨ T + 32 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h7, hT, hi, hw]
  · refine ⟨?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8]

/-- **`core::fmt::write` into a `String`, one argument with explicit options** (64495): called with
    the `String` W (ω₇), its vtable 77016 (ω₈), the template `TmplO μ tp o w` at tp (ω₉: 0xC3, the
    options word o, the width w, 0) and the arguments at an even address args (ω₁₀), whose first
    pair (v, fn) in the caller's memory μA names an `ArgOkO … o w` function, and a return address
    ω₀ that `djump` resolves to t, it either:
    - returns `Ok` (ω₇ = 0) to t, ω₀, ω₁, ω₅, ω₆ as they were, the `String` at most M octets longer
      (the text unspecified), within 7M + C + 100 + 2(cap' − cap) steps, the context kept and, from
      sp up, only W … W + 24 changed; or
    - reaches a failed allocator call. -/
theorem fmt_write_o {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 Z : Nat) (hZ : 600 ≤ Z)
    (μA : Memory) (sA : State) (spA S W tp args ret t v5 v6 o w v fn e M C : Nat)
    (x : X) (ω : Regs) (μ : Memory) (s : State) (cap len : Nat)
    (H : HeapCtx env pb S0 S1 μ s) (hba : s.base % 8 = 0) (hs : Str sA s μ W cap len)
    (KA : Keeps pb spA (fun _ => False) sA μA μ s)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat W) (h8 : ω[8] = UInt64.ofNat 77016)
    (h9 : ω[9] = UInt64.ofNat tp) (h10 : ω[10] = UInt64.ofNat args)
    (hv : v5 < 18446744073709551616 ∧ v6 < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hS : S0 + Z + 96 ≤ S ∧ S % 8 = 0 ∧ 2147483648 + Z + 96 ≤ S) (hW : S ≤ W ∧ W + 24 ≤ spA ∧ W + 24 ≤ S1)
    (hro : RoW μ) (hTm : TmplO μ tp o w) (htp : 65536 ≤ tp ∧ tp + 8 + 24 ≤ 196608) (ho : o < 2147483648)
    (hargs : args % 2 = 0)
    (hA0 : spA ≤ args) (hA1 : args + 16 < 4294967296)
    (hAr : ∀ a, args ≤ a → a < args + 16 → μA.readable a = true)
    (hAv : rdN μA args 8 = v) (hAf : rdN μA (args + 8) 8 = fn)
    (hfn : 0 < fn ∧ fn ≤ 2806 ∧ fn % 2 = 0) (hje : P.jumpTable.getD (fn / 2 - 1) 0 = e)
    (hbe : P.isBlockStart e = true) (hok : ArgOkO p P R env pb S0 S1 Z μA sA spA e v o w M C)
    (hn : len + M < 134217728) :
    (∃ ω' μ' x' s' cap' n, n ≤ M ∧
      FreeStepsH p R 64495 ω μ x t ω' μ' x' (7 * M + C + 100 + 2 * (cap' - cap)) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Str sA s' μ' W cap' (len + n) ∧ cap ≤ cap' ∧
      cap' ≤ max cap (max 8 (2 * (len + n))) ∧ Keeps pb S (fun a => W ≤ a ∧ a < W + 24) sA μ μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0) ∨
    Exhausts p R pb 64495 ω μ x (1073741824 + C + 100) := by
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  have hS1 := H.hS1
  have hSb := H.hSb
  have hcap := hs.lt
  obtain ⟨tb, to, tw, te, trd⟩ := hTm
  have hzd : ∀ (Z : Nat → Prop), (∀ a, Z a → S - 96 ≤ a) → ∀ d ∈ chunks sA, d.used = true → ∀ a, InData d a →
      a < 4294967296 ∧ ¬ Z a := fun Z hZ d hd hu a ha => by
    have := chunk_bounds H.wf (hs.base d hd hu)
    have := H.hbT
    unfold InData at ha
    exact ⟨by omega, fun hz => by have := hZ a hz; omega⟩
  obtain ⟨ω1, μ1, run1, a1, a5, a9, a12, m0, m8, m16, m24, m32, m40, m72, m80, m88, fr1, rd1, wr1⟩ :=
    wr_entry (p := p) (P := P) (R := R) x ω μ S W tp args 195 ret v5 v6 ⟨by omega, by omega⟩ h0 h1 h5 h6 h7 h8
      h9 h10 ⟨by omega, hv.1, hv.2, by omega, by omega, by omega, hargs⟩ tb (by decide) (trd tp (by omega) (by omega))
      (by omega) hro.vws (fun a h1 h2 => hro.vrd a (by omega) (by omega)) (fun a h1 h2 => hst a (by omega) (by omega))
  have K1 : Keeps pb S (fun a => W ≤ a ∧ a < W + 24) sA μ μ1 s :=
    Keeps.of_frame (Z := fun a => S - 96 ≤ a ∧ a < S) hs.base (fun a ha hz => fr1 a ha (by omega)) rd1 wr1
      (fun a hz => hst a (by omega) (by omega)) (fun a hz h => by omega)
      (fun a hz hg => by unfold Glob at hg; omega) (hzd _ (fun a hz => hz.1))
  have H1 : HeapCtx env pb S0 S1 μ1 s := ctx_hi H (fun a ha => fr1 a (by omega) (Or.inl (by omega))) wr1
  have KA1 : Keeps pb spA (fun _ => False) sA μA μ1 s := by
    have := KA.trans' (K1.lift (sp' := spA) (E' := fun _ => False) (by omega) (fun a h h' => by omega))
    rwa [Nat.max_self] at this
  have hs1 : Str sA s μ1 W cap len := hs.update (fun j hj => fr1 _ (by omega) (Or.inr (by omega)))
    ((rdN_frame (μ := μ) (μ' := μ1) (fun j hj => by
      rw [show W + 16 + j = W + (16 + j) by omega, fr1 _ (by omega) (Or.inr (by omega))])).trans hs.rl) hs.le
  have hst1 : ∀ a, S0 ≤ a → a < S1 → μ1.writable a = true := H1.st
  -- the argument
  have kA : ∀ a, spA ≤ a → a < 4294967296 → μ1.read a = μA.read a := fun a h1 h2 => KA1.hi a h1 h2 id
  have k1 : ∀ a, a < S - 96 → μ1.read a = μ.read a := fun a ha => fr1 a (by omega) (Or.inl ha)
  generalize hTdef : S - 96 = T at *
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, m48, m56, m64, m68, fr2, rd2, wr2⟩ :=
    wro_arg (p := p) (P := P) (R := R) x ω1 μ1 T W tp 0 args v fn e o w ⟨by omega, by omega⟩ (by omega) (by omega)
      (by omega) ho a1 a5 a9 a12
      (by rw [rdN_frame (fun j hj => k1 _ (by omega))]; exact to)
      (by rw [rdN_frame (fun j hj => k1 _ (by omega))]; exact tw)
      m8 m16 m24
      (by rw [Nat.mul_zero, Nat.add_zero, rdN_frame (fun j hj => kA _ (by omega) (by omega))]; exact hAv)
      (by rw [Nat.mul_zero, Nat.add_zero, rdN_frame (fun j hj => kA _ (by omega) (by omega))]; exact hAf)
      hfn hje hbe (fun a h1 h2 => by rw [rd1]; exact trd a h1 h2)
      (fun a h1 h2 => KA1.readable H1 (by omega) (by omega) (hAr a (by omega) (by omega)))
      (fun a h1 h2 => Memory.readable_of_writable (hst1 a (by omega) (by omega)))
      (fun a h1 h2 => hst1 a (by omega) (by omega))
  have wr12 : ∀ a, μ2.writable a = μ1.writable a := wr2
  have H2 : HeapCtx env pb S0 S1 μ2 s := ctx_hi H1 (fun a ha => fr2 a (by omega) (Or.inl (by omega))) wr12
  have K2 : Keeps pb T (wrE T W) sA μ1 μ2 s :=
    Keeps.of_frame (Z := fun a => T + 48 ≤ a ∧ a < T + 72) hs.base
      (fun a ha hz => fr2 a ha (by omega)) rd2 wr12 (fun a hz => hst1 a (by omega) (by omega))
      (fun a hz h => Or.inr (Or.inr ⟨by omega, hz.2⟩)) (fun a hz hg => by unfold Glob at hg; omega)
      (hzd _ (fun a hz => by omega))
  have KA2 : Keeps pb spA (fun _ => False) sA μA μ2 s := by
    have := KA1.trans' (K2.lift (sp' := spA) (E' := fun _ => False) (by omega) (fun a h h' => by
      unfold wrE at h; omega))
    rwa [Nat.max_self] at this
  have hro1 : RoW μ1 := hro.congr (fun a h1 h2 => K1.ro_low H a h2)
  have hro2 := K2.ro_low H1
  have hf2 : FmtrO sA s μ2 (T + 48) W cap len o w :=
    ⟨m48, by rw [show T + 48 + 8 = T + 56 by omega]; exact m56,
     by rw [show T + 48 + 16 = T + 64 by omega]; exact m64,
     by rw [show T + 48 + 20 = T + 68 by omega]; exact m68,
     (hro1.congr (fun a h1 h2 => hro2 a h2)).vws, (hro1.congr (fun a h1 h2 => hro2 a h2)).vwc,
     (hro1.congr (fun a h1 h2 => hro2 a h2)).vrd,
     hs1.update (fun j hj => fr2 _ (by omega) (Or.inr (by omega)))
      ((rdN_frame (μ := μ1) (μ' := μ2) (fun j hj => by
        rw [show W + 16 + j = W + (16 + j) by omega, fr2 _ (by omega) (Or.inr (by omega))])).trans hs1.rl)
      hs1.le⟩
  rcases hok ω2 μ2 x s T (T + 48) W cap len 2732 64843 0 (tp + 7) H2 hba KA2 hf2 b0 (b1.trans a1)
      b5 b6 b7 b8 (by omega) (by omega) (by decide) jte_1365 bs_64843 ⟨by omega, by omega, by omega⟩ (by omega)
      ⟨by omega, hW.2.2⟩ hW.2.1 ⟨by omega, by omega, Or.inl (by omega)⟩ hn with
    ⟨ω3, μ3, x3, s3, cap3, n, hnM, run3, H3, hb3, hf3, hc31, hc32, K3, e0, e1, e5, e6, e7⟩ | hx
  · obtain ⟨ω4, μ4, run4, f0, f1, f6, fi, fr4, rd4, wr4⟩ := wro_ret (p := p) (P := P) (R := R) x3 ω3 μ3 T 0
      ⟨by omega, by omega⟩ (by omega) e1 e5 e7 (fun a h1 h2 => H3.st a (by omega) (by omega))
    have K4 : Keeps pb T (wrE T W) sA μ3 μ4 s3 :=
      Keeps.of_frame (Z := fun a => T + 24 ≤ a ∧ a < T + 32) hf3.str.base
        (fun a ha hz => fr4 a ha (by omega)) rd4 wr4 (fun a hz => H3.st a (by omega) (by omega))
        (fun a hz h => Or.inr (Or.inl ⟨by omega, by omega⟩)) (fun a hz hg => by unfold Glob at hg; omega)
        (fun d hd hu a ha => by
          have := chunk_bounds H3.wf (hf3.str.base d hd hu)
          have := H3.hbT
          unfold InData at ha; omega)
    have H4 : HeapCtx env pb S0 S1 μ4 s3 := ctx_hi H3 (fun a ha => fr4 a (by omega) (Or.inl (by omega))) wr4
    have K24 : Keeps pb T (wrE T W) sA μ2 μ4 s3 := by
      have := (K3.mono (Nat.le_refl _) (fun a h => Or.inl h)).trans' (E := wrE T W) K4
      rwa [Nat.max_self] at this
    have K14 : Keeps pb T (wrE T W) sA μ1 μ4 s3 := by
      have := K2.trans' K24
      rwa [Nat.max_self] at this
    have hro4 := K14.ro_low H1
    have kT : ∀ a, T + 72 ≤ a ∧ a < T + 96 → μ4.read a = μ1.read a := fun a ha =>
      K14.hi a (by omega) (by omega) (by unfold wrE; omega)
    have hs4 : Str sA s3 μ4 W cap3 (len + n) := hf3.str.update
      (fun j hj => fr4 _ (by omega) (Or.inr (by omega)))
      ((rdN_frame (μ := μ3) (μ' := μ4) (fun j hj => by
        rw [show W + 16 + j = W + (16 + j) by omega, fr4 _ (by omega) (Or.inr (by omega))])).trans hf3.str.rl)
      hf3.str.le
    obtain ⟨ω5, run5, g0, g1, g5, g6, g7⟩ := wr_end (p := p) (P := P) (R := R) x3 ω4 μ4 T (tp + 7) ret t v5 v6
      ⟨by omega, by omega⟩ (by omega) (f1.trans e1)
      (by rw [f6, e6])
      (by rw [rdN_frame (fun j hj => (hro4 _ (by omega)).1), rdN_frame (fun j hj => k1 _ (by omega))]; exact te)
      (by rw [rdN_frame (fun j hj => kT _ (by omega))]; exact m88)
      (by rw [rdN_frame (fun j hj => kT _ (by omega))]; exact m80)
      (by rw [rdN_frame (fun j hj => kT _ (by omega))]; exact m72)
      hret hjt hbt (by rw [(hro4 _ (by omega)).2, rd1]; exact trd _ (by omega) (by omega))
      (fun a h1 h2 => Memory.readable_of_writable (H4.st a (by omega) (by omega)))
    refine Or.inl ⟨ω5, μ4, x3, s3, cap3, n, hnM,
      ((((run1.trans run2).trans run3).trans run4).trans run5).mono (by omega), H4, hb3, hs4, hc31, hc32, ?_,
      g0, by rw [g1, show T + 96 = S by omega], g5, g6, g7⟩
    have := K1.trans' (K14.lift (sp' := S) (E' := fun a => W ≤ a ∧ a < W + 24) (by omega) (fun a h h' => by
      unfold wrE at h; omega))
    rwa [Nat.max_self] at this
  · exact Or.inr ((Exhausts.pre (run1.trans run2) hx).mono (by omega))

end Services.Bootstrap.Fmt
