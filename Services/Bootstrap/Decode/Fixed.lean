import Services.Bootstrap.Decode.Tag
import Services.Bootstrap.Reader

/-!
# `Instruction::decode`: variants with fixed-width fields

A field is read by the reader (58434) into a buffer below the frame, and handed back through a small
return stub that loads it into a register (for a `u32`, the stub at 3780). This file proves
`Zombify { ejector: u32 }` (tag 3), the first such variant.
-/

namespace Services.Bootstrap.Decode.Fixed

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Decode.Tag

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

macro "post_simp" : tactic => `(tactic| (
  all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
    ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, PVM.Memory.readN_writeN_same,
    PVM.Memory.readN_writeN_disjoint, PVM.Memory.read_writeN_disjoint, PVM.Memory.readable_writeN,
    PVM.Memory.writable_writeN, PVM.Num.length_encodeLE, List.length_cons, List.length_nil, PVM.two32]
  all_goals try (congr 1; omega)
  all_goals try rfl))

/-- 21219 … 21243: `Zombify`'s decoder sets up the read of its `u32`: a 16-octet frame at A − 16
    with the return address 970 at A − 8 and a zeroed buffer at A − 12, and calls the reader with
    ω₇ = ω₆ (the reader), ω₈ = A − 12, ω₉ = 4 and the return address 98. -/
theorem z1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (A : Nat)
    (hA : 65536 + 16 ≤ A ∧ A < 4294967296) (h1 : ω[1] = UInt64.ofNat A)
    (hw : ∀ a, A - 16 ≤ a → a < A → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 21219 ω μ x 58434 ω' μ' x 9 ∧
      ω'[0] = UInt64.ofNat 98 ∧ ω'[1] = UInt64.ofNat (A - 16) ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = ω[6] ∧ ω'[8] = UInt64.ofNat (A - 12) ∧ ω'[9] = UInt64.ofNat 4 ∧
      μ'.readN (A - 8) 8 = Num.encodeLE 8 970 ∧
      (∀ a, a < 4294967296 → (a < A - 12 ∨ A ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hA, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    rw [show A - 16 + 8 = A - 8 by omega, Memory.readN_writeN_same _ _ _ _ (by rfl) (by simp [two32])]
    rfl

/-- 3780 … 3789 then 21247 … 21282: the `u32` stub loads the 4 octets read at A − 12 into ω₈, pops
    its frame and returns to 21247; the read succeeded (ω₇ = 0), so the `u32` goes to O + 8 and
    `Zombify`'s discriminant word 2^63 + 2 to O, and the decoder returns through its frame at A. -/
theorem z2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (A O ret t v5 v6 v : Nat) (hA : 65536 + 16 ≤ A ∧ A + 56 < 4294967296) (hO : O + 12 ≤ 4294967296)
    (hOA : O + 12 ≤ A - 12 ∨ A + 56 ≤ O)
    (h1 : ω[1] = UInt64.ofNat (A - 16)) (h5 : ω[5] = UInt64.ofNat O) (h7 : ω[7] = UInt64.ofNat 0)
    (hv : v < 4294967296) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (sv : μ.readN (A - 12) 4 = Num.encodeLE 4 v) (sr : μ.readN (A - 8) 8 = Num.encodeLE 8 970)
    (s0 : μ.readN (A + 48) 8 = Num.encodeLE 8 ret) (s5 : μ.readN (A + 40) 8 = Num.encodeLE 8 v5)
    (s6 : μ.readN (A + 32) 8 = Num.encodeLE 8 v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hw : ∀ a, O ≤ a → a < O + 12 → μ.writable a = true)
    (hr : ∀ a, A - 16 ≤ a → a < A + 56 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 3780 ω μ x t ω' μ' x 17 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775810 ∧ μ'.readN (O + 8) 4 = Num.encodeLE 4 v ∧
      (∀ a, a < 4294967296 → (a < O ∨ O + 12 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rd : ∀ a n w, w < 2 ^ (8 * n) → μ.readN a n = Num.encodeLE n w → rdN μ a n = w := by
    intro a n w hw h
    show Num.decodeLE _ = _
    rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hw]
  have rv := rd _ 4 v hv sv
  have r970 := rd _ 8 970 (by decide) sr
  have r0 := rd _ 8 ret (by omega) s0
  have r5 := rd _ 8 v5 hv5 s5
  have r6 := rd _ 8 v6 hv6 s6
  have e4 : Num.encodeLE 4 (sxw 4 v) = Num.encodeLE 4 v := encodeLE_sxw 4 v (Or.inr rfl) hv
  have rv' : rdN μ (A - 16 + 4) 4 = v := by rw [show A - 16 + 4 = A - 12 by omega]; exact rv
  have r970' : rdN μ (A - 16 + 8) 8 = 970 := by rw [show A - 16 + 8 = A - 8 by omega]; exact r970
  have e4' : Num.encodeLE 4 (sxw 4 v % 18446744073709551616 % 4294967296) = Num.encodeLE 4 v := by
    rw [Nat.mod_mod_of_dvd _ (by decide), show (4294967296 : Nat) = 256 ^ 4 from rfl, encodeLE_mod, e4]
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h7, hA, hO, hOA, hw, hr, rv', r970', r0, r5, r6, hret, hjt, hbt, e4,
      rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try exact e4'

macro "fr_conv" : tactic => `(tactic| (simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
  decide_eq_false_iff_not, not_and, Nat.not_lt] at *; omega))

/-- **`Zombify`**: from 20626, with tag 3 read without error, the reader `{ptr, len}` at rd (ω₆)
    holding at least 4 more octets, `Instruction::decode` returns `Zombify { ejector }` in its slot O:
    the discriminant word 2^63 + 2 at O and the 4 octets of `ejector` (ℰ₄, read from ptr) at O + 8.
    The reader is advanced by 4. Memory changes only in the stack below A, the reader and O … O + 12. -/
theorem zombify {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (A O ret t v5 v6 rd ptr len : Nat) (F : Frame P A O ret t v5 v6 ω μ)
    (hA : 65536 + 104 ≤ A) (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (tag : μ.read A = 3) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296) (hptr : 65536 ≤ ptr ∧ ptr + 16 < 4294967296)
    (hlen : 4 ≤ len ∧ len < 4294967296)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hrdA : rd + 16 ≤ A - 104 ∨ A + 56 ≤ rd) (hpA : ptr + 16 ≤ A - 104 ∨ A ≤ ptr)
    (hOA' : O + 12 ≤ A - 104 ∨ A + 56 ≤ O) (hOr : O + 12 ≤ rd ∨ rd + 16 ≤ O)
    (hO12 : O + 12 ≤ 4294967296)
    (hws : ∀ a, A - 104 ≤ a → a < A → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hwO : ∀ a, O ≤ a → a < O + 12 → μ.writable a = true)
    (hrp : ∀ a, ptr ≤ a → a < ptr + 4 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 20626 ω μ x t ω' μ' x 120 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775810 ∧ μ'.readN (O + 8) 4 = μ.readN ptr 4 ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 4) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 4) ∧
      (∀ a, a < 4294967296 → (a < A - 104 ∨ A ≤ a) → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 12 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hA2 := F.hA
  -- the dispatch to 21219
  obtain ⟨ω1, run1, e0, e1, e5, e6⟩ := dispatch (p := p) (P := P) (R := R) x ω μ A 3 (by decide) (by omega)
    F.h1 h7 tag tab (F.hr A (by omega) (by omega)) hrt
  -- the read's setup
  obtain ⟨ω2, μ2, run2, f0, f1, f5, f6, f7, f8, f9, f970, ffr, frd, fwr⟩ := z1 (p := p) (P := P) (R := R) x ω1 μ A
    (by omega) (e1.trans F.h1) (fun a h1 h2 => hws a (by omega) h2)
  -- the read of 4 octets
  obtain ⟨ω3, μ3, run3, g0, g1, g2, g3, g4, g5, g6, g12, g7, gR0, gR8, gbuf, gfr, grd, gwr⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω2 μ2 98 3780 (A - 16) rd (A - 12) ptr len 4 f0 f1
      (f7.trans (e6.trans h6)) f8 f9 (by decide) jte_48 bs_3780 (by omega) (by omega) (by omega) hptr
      (by decide) hlen.1 hlen.2 (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [fwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [frd]; exact hrp a h1 h2)
      (by rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact hR8)
  -- memory after the read, back to μ
  have back3 : ∀ a, a < 4294967296 → (a < A - 104 ∨ A ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ3.read a = μ.read a :=
    fun a h0 h1 h2 => (gfr a h0 (by omega) h2 (by omega)).trans (ffr a h0 (by omega))
  have hv : Num.decodeLE (μ.readN ptr 4) < 4294967296 := by
    have := decodeLE_lt (μ.readN ptr 4); simpa [Memory.length_readN] using this
  have ev : Num.encodeLE 4 (Num.decodeLE (μ.readN ptr 4)) = μ.readN ptr 4 := by
    have := encodeLE_decodeLE (μ.readN ptr 4); simpa [Memory.length_readN] using this
  have sv : μ3.readN (A - 12) 4 = Num.encodeLE 4 (Num.decodeLE (μ.readN ptr 4)) := by
    rw [ev, gbuf]; exact Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))
  have hfar : ∀ a, A ≤ a → a < A + 56 → μ3.read a = μ.read a := fun a h1 h2 => back3 a (by omega) (by omega) (by omega)
  obtain ⟨ω4, μ4, run4, k0, k1, k5, k6, kO, kO8, kfr, krd, kwr⟩ := z2 (p := p) (P := P) (R := R) x ω3 μ3
    A O ret t v5 v6 (Num.decodeLE (μ.readN ptr 4)) ⟨by omega, hA2⟩ hO12 (by omega) (g1.trans f1)
    (g5.trans (f5.trans (e5.trans F.h5))) g7 hv F.hv5 F.hv6 sv
    (by rw [Memory.readN_congr (fun j hj => gfr _ (by omega) (by omega) (by omega) (by omega))]; exact f970)
    (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega))]; exact F.s0)
    (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega))]; exact F.s5)
    (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega))]; exact F.s6)
    F.hret F.hjt F.hbt
    (fun a h1 h2 => by rw [gwr, fwr]; exact hwO a h1 h2)
    (fun a h1 h2 => by
      rw [grd, frd]
      rcases Nat.lt_or_ge a A with h | h
      · exact Memory.readable_of_writable (hws a (by omega) h)
      · exact F.hr a h h2)
  refine ⟨ω4, μ4, (run1.trans (run2.trans (run3.trans run4))).mono (by omega), k0, k1, k5, k6, kO,
    kO8.trans ev, ?_, ?_, ?_, fun a => by rw [krd, grd, frd], fun a => by rw [kwr, gwr, fwr]⟩
  · rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (by omega))]; exact gR0
  · rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (by omega))]; exact gR8
  · intro a h0 h1 h2 h3
    rw [kfr a h0 h3]; exact back3 a h0 h1 h2


/-- 3791 … 3804: the `u64` reader's setup: a 16-octet frame at S − 16 holding the return address,
    a zeroed buffer at S − 16, and the call of the reader with ω₈ = S − 16, ω₉ = 8, return 100. -/
theorem u64_pre {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S ret : Nat)
    (hS : 65536 + 16 ≤ S ∧ S < 4294967296) (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat S)
    (hret : ret < 18446744073709551616)
    (hw : ∀ a, S - 16 ≤ a → a < S → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 3791 ω μ x 58434 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 100 ∧ ω'[1] = UInt64.ofNat (S - 16) ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = ω[7] ∧ ω'[8] = UInt64.ofNat (S - 16) ∧ ω'[9] = UInt64.ofNat 8 ∧
      μ'.readN (S - 8) 8 = Num.encodeLE 8 ret ∧
      (∀ a, a < 4294967296 → (a < S - 16 ∨ S ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, hS, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    rw [show S - 16 + 8 = S - 8 by omega, Memory.readN_writeN_same _ _ _ _ (by simp) (by simp [two32])]

/-- 3810 … 3818: the `u64` reader's end: the 8 octets read at S − 16 go to ω₈, and it returns to
    the address saved at S − 8. -/
theorem u64_post {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S ret t v : Nat) (hS : 65536 + 16 ≤ S ∧ S < 4294967296) (h1 : ω[1] = UInt64.ofNat (S - 16))
    (hv : v < 18446744073709551616)
    (sv : μ.readN (S - 16) 8 = Num.encodeLE 8 v) (sr : μ.readN (S - 8) 8 = Num.encodeLE 8 ret)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hr : ∀ a, S - 16 ≤ a → a < S → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 3810 ω μ x t ω' μ x 4 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat S ∧ ω'[8] = UInt64.ofNat v ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = ω[7] := by
  have rd : ∀ a w, w < 2 ^ 64 → μ.readN a 8 = Num.encodeLE 8 w → rdN μ a 8 = w := by
    intro a w hw h
    show Num.decodeLE _ = _
    rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hw]
  have rv : rdN μ (S - 16) 8 = v := rd _ v hv sv
  have rr : rdN μ (S - 16 + 8) 8 = ret := by
    rw [show S - 16 + 8 = S - 8 by omega]; exact rd _ ret (by omega) sr
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hS, hr, rv, rr, hret, hjt, hbt, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    post_simp

/-- **The `u64` reader** (3791): called with return address `ret` (ω₀), sp = S and the reader
    `{ptr, len}` at rd (ω₇) holding at least 8 octets, it returns to `ret`'s target with ω₇ = 0,
    ω₈ = the `u64` read (ℰ₈⁻¹ of the 8 octets at ptr) and the reader advanced by 8. Memory changes
    only in the stack below S and the reader. -/
theorem read_u64 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S ret t rd ptr len : Nat) (hS : 65536 + 104 ≤ S ∧ S < 4294967296)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat rd)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296) (hptr : 65536 ≤ ptr ∧ ptr + 16 < 4294967296)
    (hlen : 8 ≤ len ∧ len < 4294967296)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hrdS : rd + 16 ≤ S - 104 ∨ S ≤ rd) (hpS : ptr + 16 ≤ S - 104 ∨ S ≤ ptr)
    (hws : ∀ a, S - 104 ≤ a → a < S → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hrp : ∀ a, ptr ≤ a → a < ptr + 8 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 3791 ω μ x t ω' μ' x 120 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat 0 ∧ ω'[8] = UInt64.ofNat (Num.decodeLE (μ.readN ptr 8)) ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 8) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 8) ∧
      (∀ a, a < 4294967296 → (a < S - 104 ∨ S ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨ω1, μ1, run1, f0, f1, f5, f6, f7, f8, f9, fret, ffr, frd, fwr⟩ := u64_pre (p := p) (P := P) (R := R)
    x ω μ S ret ⟨by omega, hS.2⟩ h0 h1 (by omega) (fun a h1 h2 => hws a (by omega) h2)
  obtain ⟨ω2, μ2, run2, g0, g1, g2, g3, g4, g5, g6, g12, g7, gR0, gR8, gbuf, gfr, grd, gwr⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω1 μ1 100 3810 (S - 16) rd (S - 16) ptr len 8 f0 f1
      (f7.trans h7) f8 f9 (by decide) jte_49 bs_3810 (by omega) hrd (by omega) hptr
      (by decide) hlen.1 hlen.2 (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [fwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [frd]; exact hrp a h1 h2)
      (by rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact hR8)
  have hv : Num.decodeLE (μ.readN ptr 8) < 18446744073709551616 := by
    have := decodeLE_lt (μ.readN ptr 8); simpa [Memory.length_readN] using this
  have ev : Num.encodeLE 8 (Num.decodeLE (μ.readN ptr 8)) = μ.readN ptr 8 := by
    have := encodeLE_decodeLE (μ.readN ptr 8); simpa [Memory.length_readN] using this
  obtain ⟨ω3, run3, k0, k1, k8, k5, k6, k7⟩ := u64_post (p := p) (P := P) (R := R) x ω2 μ2 S ret t
    (Num.decodeLE (μ.readN ptr 8)) ⟨by omega, hS.2⟩ (g1.trans f1) hv
    (by rw [ev, gbuf]; exact Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega)))
    (by rw [Memory.readN_congr (fun j hj => gfr _ (by omega) (by omega) (by omega) (by omega))]; exact fret)
    hret hjt hbt
    (fun a h1 h2 => by rw [grd, frd]; exact Memory.readable_of_writable (hws a (by omega) h2))
  refine ⟨ω3, μ2, (run1.trans (run2.trans run3)).mono (by omega), k0, k1, ?_, ?_, ?_, k8, gR0, gR8,
    fun a h0 h1 h2 => ?_, fun a => by rw [grd, frd], fun a => by rw [gwr, fwr]⟩
  · rw [k5, g5, f5]
  · rw [k6, g6, f6]
  · rw [k7, g7]
  · rw [gfr a h0 (by omega) h2 (by omega)]; exact ffr a h0 (by omega)

end Services.Bootstrap.Decode.Fixed
