import Services.Bootstrap.Fmt.Write

/-!
# `core::fmt::write` (64495) with an explicit-options argument first

`fmt::write`'s templates can carry an argument with explicit options: the byte 0xC0 | flags, then
the fields the flags announce. This file covers the form 0xC3 (`{:…w…}`): an options word o (4
octets, below 2³¹) and a width w (2 octets), the argument taken in order (as `{:02x}` gives, the
template 70833: 0xC3, o = 0x69000020, w = 2, then the end byte). Its function is called with a
`Formatter` carrying o and w (`FmtrO`), and is given as an `ArgOkO`.

- `wr_spec`: 64611 … the argument's function, the `Formatter` built at T + 48;
- `wr_spec_ret`: 64843 … 64600, after its `Ok`;
- `wr_item_spec`: one such item, then plain items ts (`WrLoop`);
- `fmt_write_spec`: `core::fmt::write` over such an item followed by plain items ts.
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **A `Formatter` with options o and width w** (and precision 0) at F, into the `String` W: as
    `Fmtr`, with the options word o and width w in place of the default ones. -/
structure FmtrO (s₀ s : State) (μ : Memory) (F W cap len o w : Nat) : Prop where
  buf : rdN μ F 8 = W
  vt : rdN μ (F + 8) 8 = 77016
  opts : rdN μ (F + 16) 4 = o
  width : rdN μ (F + 20) 2 = w
  prec : rdN μ (F + 22) 2 = 0
  vws : rdN μ 77040 8 = 2596
  vwc : rdN μ 77048 8 = 2592
  vrd : ∀ a, 65536 ≤ a → a < 77144 → μ.readable a = true
  str : Str s₀ s μ W cap len

/-- **An argument's function called with an options-carrying `Formatter`**: `ArgOk` with `FmtrO`
    (options o, width w) for `Fmtr`, before and after. -/
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

/-- The explicit-options item at c: 0xC3, the options word o (below 2³¹), the width w; readable. -/
def SpecAt (μ : Memory) (c o w : Nat) : Prop :=
  rdN μ c 1 = 195 ∧ rdN μ (c + 1) 4 = o ∧ o < 2147483648 ∧ rdN μ (c + 5) 2 = w ∧
    ∀ a, c ≤ a → a < c + 7 → μ.readable a = true

theorem SpecAt.congr {μ μ' : Memory} {c o w : Nat} (h : SpecAt μ c o w) (hc : c + 7 ≤ 196608)
    (k : ∀ b, b < 196608 → μ'.read b = μ.read b ∧ μ'.readable b = μ.readable b) : SpecAt μ' c o w :=
  ⟨by rw [rdN_frame (fun j hj => (k _ (by omega)).1)]; exact h.1,
   by rw [rdN_frame (fun j hj => (k _ (by omega)).1)]; exact h.2.1, h.2.2.1,
   by rw [rdN_frame (fun j hj => (k _ (by omega)).1)]; exact h.2.2.2.1,
   fun a h1 h2 => by rw [(k a (by omega)).2]; exact h.2.2.2.2 a h1 h2⟩

theorem u64_signed4 (o : Nat) (ho : o < 2147483648) : Exec.u64 (Num.signed 4 o) = o := by
  have h : o < 2 ^ (8 * 4 - 1) := by simpa using ho
  simp only [Exec.u64, Num.signed, Num.unsigned, h, if_true]
  omega

theorem rdN_writeN_enc (μ : Memory) (a n v : Nat) (ha : a + n ≤ 4294967296) :
    rdN (μ.writeN a (Num.encodeLE n v)) a n = v % 256 ^ n := by
  unfold rdN
  rw [Memory.readN_writeN_same _ _ _ _ (by simp) (by simp [two32]; omega), Num.decodeLE_encodeLE, Nat.pow_mul]

theorem rdN_writeN_zero2 (μ : Memory) (a : Nat) (ha : a + 2 ≤ 4294967296) :
    rdN (μ.writeN a [UInt8.ofNat 0, UInt8.ofNat 0]) a 2 = 0 := by
  unfold rdN
  rw [Memory.readN_writeN_same _ _ _ _ (by simp) (by simp [two32]; try omega)]
  decide

/-- 64611 … 64838 and the jump, an argument with explicit options (0xC3 at the cursor c, then o and
    w): the argument i (the index at T + 24), the pair (v, fn) at args + 16 i, is called through fn
    with v (ω₇) and the `Formatter` at T + 48 (ω₈): W at T + 48, the vtable at T + 56, o at T + 64, w
    at T + 68, precision 0 at T + 70. The return address is 2732 (64843); i and c + 7 stay in ω₅, ω₆. -/
theorem wr_spec {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs)
    (μ : Memory) (T W c i args v fn e o w : Nat) (hT : 65536 ≤ T ∧ T + 96 < 4294967296)
    (hc : c + 7 < 4294967296) (hW : W < 18446744073709551616) (hi : args + 16 * i + 16 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat T) (h5 : ω[5] = UInt64.ofNat 195) (h9 : ω[9] = UInt64.ofNat c)
    (h12 : ω[12] = UInt64.ofNat W)
    (rvt : rdN μ (T + 8) 8 = 77016) (ra : rdN μ (T + 16) 8 = args)
    (ri : rdN μ (T + 24) 8 = i) (rv : rdN μ (args + 16 * i) 8 = v) (rf : rdN μ (args + 16 * i + 8) 8 = fn)
    (ro : rdN μ (c + 1) 4 = o) (ho : o < 2147483648) (rw2 : rdN μ (c + 5) 2 = w)
    (hrc : ∀ a, c ≤ a → a < c + 7 → μ.readable a = true)
    (hfn : 0 < fn ∧ fn ≤ 2806 ∧ fn % 2 = 0) (hjt : P.jumpTable.getD (fn / 2 - 1) 0 = e)
    (hbt : P.isBlockStart e = true)
    (hra : ∀ a, args + 16 * i ≤ a → a < args + 16 * i + 16 → μ.readable a = true)
    (hr : ∀ a, T ≤ a → a < T + 32 → μ.readable a = true)
    (hw : ∀ a, T + 48 ≤ a → a < T + 72 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 64611 ω μ x e ω' μ' x 39 ∧
      ω'[0] = UInt64.ofNat 2732 ∧ ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat i ∧
      ω'[6] = UInt64.ofNat (c + 7) ∧ ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (T + 48) ∧
      rdN μ' (T + 48) 8 = W ∧ rdN μ' (T + 56) 8 = 77016 ∧ rdN μ' (T + 64) 4 = o ∧
      rdN μ' (T + 68) 2 = w ∧ rdN μ' (T + 70) 2 = 0 ∧
      (∀ a, a < 4294967296 → (a < T + 48 ∨ T + 72 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hsx : sx8 195 = 18446744073709551555 := by decide
  have a1 : Exec.bitwise (· && ·) 195 1 = 1 := by decide
  have a2 : Exec.bitwise (· && ·) 195 2 = 2 := by decide
  have a4 : Exec.bitwise (· && ·) 195 4 = 0 := by decide
  have a8 : Exec.bitwise (· && ·) 195 8 = 0 := by decide
  have a16 : Exec.bitwise (· && ·) 195 16 = 0 := by decide
  have a32 : Exec.bitwise (· && ·) 195 32 = 0 := by decide
  have hs4 := u64_signed4 o ho
  have hw2 : w < 65536 := by rw [← rw2]; exact rdN_lt μ _ 2
  have hi64 : i < 268435456 := by omega
  have e16 : args + i * 16 = args + 16 * i := by omega
  have rv' : rdN μ (args + i * 16) 8 = v := by rw [e16]; exact rv
  have rf' : rdN μ (args + i * 16 + 8) 8 = fn := by rw [e16]; exact rf
  have hra' : ∀ a, args + i * 16 ≤ a → a < args + i * 16 + 16 → μ.readable a = true := by rw [e16]; exact hra
  have hfn' : fn % 18446744073709551616 % 4294967296 = fn := by omega
  have hv64 : v < 18446744073709551616 := by rw [← rv]; exact rdN_lt64 μ _
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h9, h12, hT, hc, hW, hi, hi64, rvt, ra, ri, rv', rf', ro, rw2, hrc, hs4, ho, hw2, hfn, hfn', hjt, hbt,
      hra', hr, hw, hsx, a1, a2, a4, a8, a16, a32, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := first | (simp only [Num.length_encodeLE, List.length_cons, List.length_nil, PVM.two32]; done) | ((try simp only [Num.length_encodeLE, List.length_cons, List.length_nil, PVM.two32]); omega)) only
      [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some', List.lookup_nil,
        Option.getD_none, rdN_writeN_disjoint, PVM.Memory.read_writeN_disjoint, PVM.Memory.readable_writeN,
        PVM.Memory.writable_writeN, rdN_writeN_enc, rdN_writeN_zero2, rdN_lit8, h1]
    all_goals first | rfl | (simp only [Nat.reducePow]; omega) | omega |
      (rw [Num.decodeLE_encodeLE]; simp only [Nat.reduceMul, Nat.reducePow]; omega) | decide

/-- 64843 … 64599, after an explicit-options argument's `Ok`: the index (T + 24) goes to i + 1 and
    the loop goes on at 64600. -/
theorem wr_spec_ret {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs)
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

/-- The explicit-options argument i: the pair (v, fn) at args + 16 i in the caller's memory μA, at or
    above spA, fn a jump-table address of an `ArgOkO` function (options o, width w). -/
def ArgAtO (p : ByteArray) (P : Program) {X : Type} (R : HostRel X) (env : RefineHost.Env)
    (pb S0 S1 Z : Nat) (μA : Memory) (sA : State) (spA args i o w M C : Nat) : Prop :=
  ∃ v fn e, spA ≤ args + 16 * i ∧ args + 16 * i + 16 < 4294967296 ∧
    (∀ a, args + 16 * i ≤ a → a < args + 16 * i + 16 → μA.readable a = true) ∧
    rdN μA (args + 16 * i) 8 = v ∧ rdN μA (args + 16 * i + 8) 8 = fn ∧
    (0 < fn ∧ fn ≤ 2806 ∧ fn % 2 = 0) ∧ P.jumpTable.getD (fn / 2 - 1) 0 = e ∧
    P.isBlockStart e = true ∧ ArgOkO p P R env pb S0 S1 Z μA sA spA e v o w M C

/-- **An explicit-options item, then the rest of the loop** (from 64611, the byte 0xC3 in ω₅, the
    cursor c in ω₉, W in ω₁₂), the plain items ts after it: as `WrLoop`, with the item's argument
    (an `ArgOkO` with M', C') counting 7M' + C' + 100 steps and M' octets. -/
theorem wr_item_spec {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 Z : Nat) (hZ : 600 ≤ Z) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA T W args ret t v5 v6 M C : Nat)
    (hT : S0 + Z ≤ T ∧ T % 8 = 0 ∧ 2147483648 + Z ≤ T) (hW : T + 96 ≤ W ∧ W + 24 ≤ spA ∧ W + 24 ≤ S1)
    (hv : v5 < 18446744073709551616 ∧ v6 < 18446744073709551616)
    (ts : List TItem) (ih : WrLoop p P R env pb S0 S1 Z μA sA spA T W args ret t v5 v6 M C ts)
    (o w M' C' : Nat)
    (c i cap len : Nat) (ω : Regs) (μ : Memory) (x : X) (s : State)
    (H : HeapCtx env pb S0 S1 μ s) (hba : s.base % 8 = 0) (hs : Str sA s μ W cap len)
    (KA : Keeps pb spA (fun _ => False) sA μA μ s) (hF : WFrame μ T W args i ret v5 v6) (hro : RoW μ)
    (hSp : SpecAt μ c o w) (hTm : Tmpl μ (c + 7) ts) (hc0 : 65536 ≤ c) (hc1 : c + 7 + tsize ts + 24 ≤ 196608)
    (h1 : ω[1] = UInt64.ofNat T) (a5 : ω[5] = UInt64.ofNat 195) (a9 : ω[9] = UInt64.ofNat c)
    (a12 : ω[12] = UInt64.ofNat W)
    (hA0 : ArgAtO p P R env pb S0 S1 Z μA sA spA args i o w M' C')
    (hA : ArgsAt p P R env pb S0 S1 Z μA sA spA args (i + 1) ts M C) (hi : i + 1 + nargs ts < 268435456)
    (hn : len + (M' + tlen M ts) < 134217728) :
    (∃ ω' μ' x' s' cap' n, n ≤ M' + tlen M ts ∧
      FreeStepsH p R 64611 ω μ x t ω' μ' x' (7 * M' + C' + 100 + tcost M C ts - 4 + 2 * (cap' - cap)) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Str sA s' μ' W cap' (len + n) ∧ cap ≤ cap' ∧
      cap' ≤ max cap (max 8 (2 * (len + n))) ∧ Keeps pb T (wrE T W) sA μ μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (T + 96) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0) ∨
    Exhausts p R pb 64611 ω μ x (2147483648 + (7 * M' + C' + 100 + tcost M C ts) - 4 - 2 * cap) := by
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  have hS1 := H.hS1
  have hSb := H.hSb
  have hcap := hs.lt
  have hzd : ∀ (Z : Nat → Prop), (∀ a, Z a → T ≤ a) → ∀ d ∈ chunks sA, d.used = true → ∀ a, InData d a →
      a < 4294967296 ∧ ¬ Z a := fun Z hZ d hd hu a ha => by
    have := chunk_bounds H.wf (hs.base d hd hu)
    have := H.hbT
    unfold InData at ha
    exact ⟨by omega, fun hz => by have := hZ a hz; omega⟩
  have hts := tsize_pos ts
  have htc := tcost_ge M C ts
  obtain ⟨hb, ho1, ho, hw1, hrb⟩ := hSp
  have hTm' := hTm
  obtain ⟨v, fn, e, hA0, hA1, hAr, hAv, hAf, hfn, hje, hbe, hok⟩ := hA0
  obtain ⟨ω1, run1, a1, rfl⟩ : ∃ ω1, FreeStepsH p R 64611 ω μ x 64611 ω1 μ x 0 ∧ ω1[1] = ω[1] ∧ ω1 = ω :=
    ⟨ω, FreeStepsH.refl, rfl, rfl⟩
  have kA : ∀ a, spA ≤ a → a < 4294967296 → μ.read a = μA.read a := fun a h1 h2 => KA.hi a h1 h2 id
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, m48, m56, m64, m68, m70, fr2, rd2, wr2⟩ :=
    wr_spec (p := p) (P := P) (R := R) x ω1 μ T W c i args v fn e o w ⟨by omega, by omega⟩ (by omega) (by omega)
      (by omega) (a1.trans h1) a5 a9 a12 hF.vt hF.args hF.idx
      (by rw [rdN_frame (fun j hj => kA _ (by omega) (by omega))]; exact hAv)
      (by rw [rdN_frame (fun j hj => kA _ (by omega) (by omega))]; exact hAf) ho1 ho hw1 hrb hfn hje hbe
      (fun a h1 h2 => KA.readable H (by omega) (by omega) (hAr a h1 h2))
      (fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)))
      (fun a h1 h2 => hst a (by omega) (by omega))
  have wr12 : ∀ a, μ2.writable a = μ.writable a := wr2
  have H2 : HeapCtx env pb S0 S1 μ2 s := ctx_hi H (fun a ha => fr2 a (by omega) (Or.inl (by omega))) wr12
  have K2 : Keeps pb T (wrE T W) sA μ μ2 s :=
    Keeps.of_frame (Z := fun a => T + 48 ≤ a ∧ a < T + 72) hs.base
      (fun a ha hz => fr2 a ha (by omega)) rd2 wr12 (fun a hz => hst a (by omega) (by omega))
      (fun a hz h => Or.inr (Or.inr ⟨by omega, hz.2⟩)) (fun a hz hg => by unfold Glob at hg; omega)
      (hzd _ (fun a hz => by omega))
  have KA2 : Keeps pb spA (fun _ => False) sA μA μ2 s := by
    have := KA.trans' (K2.lift (sp' := spA) (E' := fun _ => False) (by omega) (fun a h h' => by
      unfold wrE at h; omega))
    rwa [Nat.max_self] at this
  have hro2 := K2.ro_low H
  have hf2 : FmtrO sA s μ2 (T + 48) W cap len o w :=
    ⟨m48, by rw [show T + 48 + 8 = T + 56 by omega]; exact m56,
     by rw [show T + 48 + 16 = T + 64 by omega]; exact m64,
     by rw [show T + 48 + 20 = T + 68 by omega]; exact m68,
     by rw [show T + 48 + 22 = T + 70 by omega]; exact m70,
     (hro.congr (fun a h1 h2 => hro2 a h2)).vws, (hro.congr (fun a h1 h2 => hro2 a h2)).vwc,
     (hro.congr (fun a h1 h2 => hro2 a h2)).vrd,
     hs.update (fun j hj => fr2 _ (by omega) (Or.inr (by omega)))
      ((rdN_frame (μ := μ) (μ' := μ2) (fun j hj => by
        rw [show W + 16 + j = W + (16 + j) by omega, fr2 _ (by omega) (Or.inr (by omega))])).trans hs.rl)
      hs.le⟩
  rcases hok ω2 μ2 x s T (T + 48) W cap len 2732 64843 i (c + 7) H2 hba KA2 hf2 b0 (b1.trans (a1.trans h1))
      b5 b6 b7 b8 (by omega) (by omega) (by decide) jte_1365 bs_64843 hT (by omega) ⟨by omega, hW.2.2⟩ hW.2.1
      ⟨by omega, by omega, Or.inl (by omega)⟩ (by omega) with
    ⟨ω3, μ3, x3, s3, cap3, n, hnM, run3, H3, hb3, hf3, hc31, hc32, K3, e0, e1, e5, e6, e7⟩ | hx
  · obtain ⟨ω4, μ4, run4, f0, f1, f6, fi, fr4, rd4, wr4⟩ := wr_spec_ret (p := p) (P := P) (R := R) x3 ω3 μ3 T i
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
    have K14 : Keeps pb T (wrE T W) sA μ μ4 s3 := by
      have := K2.trans' K24
      rwa [Nat.max_self] at this
    have KA4 : Keeps pb spA (fun _ => False) sA μA μ4 s3 := by
      have := KA.trans' (K14.lift (sp' := spA) (E' := fun _ => False) (by omega) (fun a h h' => by
        unfold wrE at h; omega))
      rwa [Nat.max_self] at this
    have hro4 := K14.ro_low H
    have := hf3.str.lt
    have kT : ∀ a, (T ≤ a ∧ a < T + 24) ∨ (T + 32 ≤ a ∧ a < T + 48) ∨ (T + 72 ≤ a ∧ a < T + 96) →
        μ4.read a = μ.read a := fun a ha => K14.hi a (by omega) (by omega) (by unfold wrE; omega)
    have hF4 : WFrame μ4 T W args (i + 1) ret v5 v6 := hF.congr kT fi
    have hs4 : Str sA s3 μ4 W cap3 (len + n) := hf3.str.update
      (fun j hj => fr4 _ (by omega) (Or.inr (by omega)))
      ((rdN_frame (μ := μ3) (μ' := μ4) (fun j hj => by
        rw [show W + 16 + j = W + (16 + j) by omega, fr4 _ (by omega) (Or.inr (by omega))])).trans hf3.str.rl)
      hf3.str.le
    rcases ih (c + 7) (i + 1) cap3 (len + n) ω4 μ4 x3 s3 H4 (by rw [hb3]; exact hba) hs4 KA4 hF4
        (hro.congr (fun a h1 h2 => hro4 a h2)) (Tmpl.congr ts _ hTm' (by omega) hro4) (by omega) (by omega)
        (f1.trans e1) (by rw [f6, e6])
        hA
        (by omega) (by omega) with
      ⟨ω', μ', x', s', cap', n', hn', run', H', hb', hs', hc1', hc2', K', g0, g1, g5, g6, g7⟩ | hx
    · refine Or.inl ⟨ω', μ', x', s', cap', n + n', by omega,
        ((((run1.trans run2).trans run3).trans run4).trans run').mono (by omega), H', hb'.trans hb3,
        by rw [← Nat.add_assoc]; exact hs', by omega, by omega, ?_, g0, g1, g5, g6, g7⟩
      have := K14.trans' K'
      rwa [Nat.max_self] at this
    · exact Or.inr ((Exhausts.pre (((run1.trans run2).trans run3).trans run4) hx).mono (by omega))
  · exact Or.inr ((Exhausts.pre (run1.trans run2) hx).mono (by omega))

/-- **`core::fmt::write`** (64495) into a `String`, over a template whose first item has explicit
    options (0xC3, the options word o, the width w: `SpecAt`), its argument an `ArgOkO` (M', C'), followed by
    plain items ts: as `fmt_write`, the item counting 7M' + C' + 100 steps and M' octets. -/
theorem fmt_write_spec {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 Z : Nat) (hZ : 600 ≤ Z) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA S W tp args ret t v5 v6 M C : Nat) (ts : List TItem) (o w M' C' : Nat)
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
    (hro : RoW μ) (hSp : SpecAt μ tp o w) (hTm : Tmpl μ (tp + 7) ts)
    (htp : 65536 ≤ tp ∧ tp + 7 + tsize ts + 24 ≤ 196608)
    (hargs : args < 18446744073709551616 ∧ args % 2 = 0)
    (hA0 : ArgAtO p P R env pb S0 S1 Z μA sA spA args 0 o w M' C')
    (hA : ArgsAt p P R env pb S0 S1 Z μA sA spA args 1 ts M C) (hi : 1 + nargs ts < 268435456)
    (hn : len + (M' + tlen M ts) < 134217728) :
    (∃ ω' μ' x' s' cap' n, n ≤ M' + tlen M ts ∧
      FreeStepsH p R 64495 ω μ x t ω' μ' x' (7 * M' + C' + 100 + tcost M C ts + 100 + 2 * (cap' - cap)) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Str sA s' μ' W cap' (len + n) ∧ cap ≤ cap' ∧
      cap' ≤ max cap (max 8 (2 * (len + n))) ∧ Keeps pb S (fun a => W ≤ a ∧ a < W + 24) sA μ μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0) ∨
    Exhausts p R pb 64495 ω μ x (2147483648 + (7 * M' + C' + 100 + tcost M C ts) + 100) := by
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  have hS1 := H.hS1
  have hSb := H.hSb
  have hcap := hs.lt
  have htc := tcost_ge M C ts
  have hzd : ∀ (Z : Nat → Prop), (∀ a, Z a → S - 96 ≤ a) → ∀ d ∈ chunks sA, d.used = true → ∀ a, InData d a →
      a < 4294967296 ∧ ¬ Z a := fun Z hZ d hd hu a ha => by
    have := chunk_bounds H.wf (hs.base d hd hu)
    have := H.hbT
    unfold InData at ha
    exact ⟨by omega, fun hz => by have := hZ a hz; omega⟩
  have hts := tsize_pos ts
  have hb : rdN μ tp 1 = 195 ∧ μ.readable tp = true := ⟨hSp.1, hSp.2.2.2.2 tp (by omega) (by omega)⟩
  obtain ⟨ω1, μ1, run1, a1, a5, a9, a12, m0, m8, m16, m24, m32, m40, m72, m80, m88, fr1, rd1, wr1⟩ :=
    wr_entry (p := p) (P := P) (R := R) x ω μ S W tp args 195 ret v5 v6 ⟨by omega, by omega⟩ h0 h1 h5 h6 h7 h8
      h9 h10 ⟨by omega, hv.1, hv.2, by omega, by omega, hargs.1, hargs.2⟩ hb.1 (by omega) hb.2 (by omega) hro.vws
      (fun a h1 h2 => hro.vrd a (by omega) (by omega)) (fun a h1 h2 => hst a (by omega) (by omega))
  have K1 : Keeps pb S (fun a => W ≤ a ∧ a < W + 24) sA μ μ1 s :=
    Keeps.of_frame (Z := fun a => S - 96 ≤ a ∧ a < S) hs.base (fun a ha hz => fr1 a ha (by omega)) rd1 wr1
      (fun a hz => hst a (by omega) (by omega)) (fun a hz h => by omega)
      (fun a hz hg => by unfold Glob at hg; omega) (hzd _ (fun a hz => hz.1))
  have H1 : HeapCtx env pb S0 S1 μ1 s := ctx_hi H (fun a ha => fr1 a (by omega) (Or.inl (by omega))) wr1
  have KA1 : Keeps pb spA (fun _ => False) sA μA μ1 s := by
    have := KA.trans' (K1.lift (sp' := spA) (E' := fun _ => False) (by omega) (fun a h h' => by omega))
    rwa [Nat.max_self] at this
  have hro1 := K1.ro_low H
  have hs1 : Str sA s μ1 W cap len := hs.update (fun j hj => fr1 _ (by omega) (Or.inr (by omega)))
    ((rdN_frame (μ := μ) (μ' := μ1) (fun j hj => by
      rw [show W + 16 + j = W + (16 + j) by omega, fr1 _ (by omega) (Or.inr (by omega))])).trans hs.rl) hs.le
  have hF1 : WFrame μ1 (S - 96) W args 0 ret v5 v6 := ⟨m0, m8, m16, m24, m32, m40, m72, m80, m88⟩
  rcases wr_item_spec (p := p) (P := P) (R := R) env pb S0 S1 Z hZ HA HR μA sA spA (S - 96) W args ret t v5 v6 M C
      ⟨by omega, by omega, by omega⟩ ⟨by omega, hW.2.1, hW.2.2⟩ hv ts
      (wr_loop (p := p) (P := P) (R := R) env pb S0 S1 Z hZ HA HR μA sA spA (S - 96) W args ret t v5 v6 M C
        ⟨by omega, by omega, by omega⟩ ⟨by omega, hW.2.1, hW.2.2⟩ hv hret hjt hbt ts)
      o w M' C' tp 0 cap len ω1 μ1 x s H1 hba hs1 KA1 hF1 (hro.congr (fun a h1 h2 => hro1 a h2))
      (hSp.congr (by omega) hro1) (Tmpl.congr _ _ hTm (by omega) hro1) htp.1 (by omega) a1 a5 a9 a12
      hA0 (by rw [show (0 : Nat) + 1 = 1 from rfl]; exact hA) (by omega) hn with
    ⟨ω', μ', x', s', cap', n, hn', run', H', hb', hs', hc1', hc2', K', g0, g1, g5, g6, g7⟩ | hx
  · refine Or.inl ⟨ω', μ', x', s', cap', n, hn', (run1.trans run').mono (by omega), H', hb', hs', hc1', hc2',
      ?_, g0, by rw [g1, show S - 96 + 96 = S by omega], g5, g6, g7⟩
    have := K1.trans' (K'.lift (sp' := S) (E' := fun a => W ≤ a ∧ a < W + 24) (by omega) (fun a h h' => by
      unfold wrE at h; omega))
    rwa [Nat.max_self] at this
  · exact Or.inr ((Exhausts.pre run1 hx).mono (by omega))

end Services.Bootstrap.Fmt
