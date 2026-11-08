import Services.Bootstrap.Decode.Tag
import Services.Bootstrap.ReaderBig

/-!
# `Instruction::decode`: variants with a 32-octet hash field

A hash is read with the reader straight into the decoder's frame at A (`read_big_sp`), then copied
word by word into the result slot. This file proves `Yield { hash }` (tag 14), the first of them.
-/

namespace Services.Bootstrap.Decode.Hash

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

/-- n + m octets are the first n, then the m after them. -/
theorem readN_add (μ : Memory) (a n m : Nat) : μ.readN a (n + m) = μ.readN a n ++ μ.readN (a + n) m := by
  simp only [Memory.readN, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  simp [Function.comp, Nat.add_assoc]

/-- 20778 … 20796: `Yield`'s decoder zeroes the 32 octets at A and calls the reader for 32 octets
    into A (ω₇ = ω₆, ω₈ = A, ω₉ = 32, return address 940). -/
theorem y1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (A : Nat)
    (hA : A + 32 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat A)
    (hw : ∀ a, A ≤ a → a < A + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 20778 ω μ x 58434 ω' μ' x 8 ∧
      ω'[0] = UInt64.ofNat 940 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = ω[6] ∧ ω'[8] = UInt64.ofNat A ∧ ω'[9] = UInt64.ofNat 32 ∧
      (∀ a, a < 4294967296 → (a < A ∨ A + 32 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hA, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try exact UInt64.ofNat_toNat

/-- 32 octets as four words. -/
theorem readN_32 (μ : Memory) (a : Nat) : μ.readN a 32 =
    μ.readN a 8 ++ μ.readN (a + 8) 8 ++ μ.readN (a + 16) 8 ++ μ.readN (a + 24) 8 := by
  rw [show (32 : Nat) = 8 + 8 + 8 + 8 from rfl, readN_add, readN_add, readN_add]

/-- Four words copied from A … A + 32 to O + 8 … O + 40, as the decoders' stores leave them: the copy
    holds the 32 octets. -/
theorem copy4 (μ ν : Memory) (A O : Nat) (hO : O + 40 ≤ 4294967296) :
    ((((ν.writeN (O + 8) (Num.encodeLE 8 (rdN μ A 8 % 18446744073709551616))).writeN (O + 16)
      (Num.encodeLE 8 (rdN μ (A + 8) 8 % 18446744073709551616))).writeN (O + 24)
      (Num.encodeLE 8 (rdN μ (A + 16) 8 % 18446744073709551616))).writeN (O + 32)
      (Num.encodeLE 8 (rdN μ (A + 24) 8 % 18446744073709551616))).readN (O + 8) 32 = μ.readN A 32 := by
  have hm : ∀ a, rdN μ a 8 % 18446744073709551616 = rdN μ a 8 := fun a => Nat.mod_eq_of_lt (rdN_lt64 μ a)
  rw [hm A, hm (A + 8), hm (A + 16), hm (A + 24), encodeLE_rdN, encodeLE_rdN, encodeLE_rdN, encodeLE_rdN]
  rw [readN_32, readN_32]
  try simp only [Nat.add_assoc, Nat.reduceAdd]
  simp (disch := (simp [two32] <;> omega)) only [Memory.readN_writeN_same, Memory.readN_writeN_disjoint]

/-- 20803 … 20855: the read succeeded (ω₇ = 0), so the 32 octets at A are copied to O + 8, `Yield`'s
    discriminant word 2^63 + 13 goes to O, and the decoder returns through its frame at A. -/
theorem y2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (A O ret t v5 v6 : Nat) (hA : A + 56 < 4294967296) (hO : O + 40 ≤ 4294967296)
    (hOA : O + 40 ≤ A ∨ A + 56 ≤ O)
    (h1 : ω[1] = UInt64.ofNat A) (h5 : ω[5] = UInt64.ofNat O) (h7 : ω[7] = UInt64.ofNat 0)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (s0 : μ.readN (A + 48) 8 = Num.encodeLE 8 ret) (s5 : μ.readN (A + 40) 8 = Num.encodeLE 8 v5)
    (s6 : μ.readN (A + 32) 8 = Num.encodeLE 8 v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hw : ∀ a, O ≤ a → a < O + 40 → μ.writable a = true)
    (hr : ∀ a, A ≤ a → a < A + 56 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 20803 ω μ x t ω' μ' x 17 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775821 ∧ μ'.readN (O + 8) 32 = μ.readN A 32 ∧
      (∀ a, a < 4294967296 → (a < O ∨ O + 40 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rd : ∀ a w, w < 2 ^ 64 → μ.readN a 8 = Num.encodeLE 8 w → rdN μ a 8 = w := by
    intro a w hw h
    show Num.decodeLE _ = _
    rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hw]
  have r0 := rd _ ret (by omega) s0
  have r5 := rd _ v5 hv5 s5
  have r6 := rd _ v6 hv6 s6
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h7, hA, hO, hOA, hw, hr, r0, r5, r6, hret, hjt, hbt, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try exact copy4 μ μ A O hO

/-- **`Yield`**: from 20626, with tag 14 read without error and the reader `{ptr, len}` at rd (ω₆)
    holding at least 32 more octets, `Instruction::decode` returns `Yield { hash }` in its slot O:
    the discriminant word 2^63 + 13 at O and the 32 octets of `hash`, copied from ptr, at O + 8.
    The reader is advanced by 32. Memory changes only in A − 88 … A + 32 (the reader's frames and
    the hash buffer), the reader and O … O + 40. -/
theorem yield {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (A O ret t v5 v6 rd ptr len : Nat) (F : Frame P A O ret t v5 v6 ω μ)
    (hA : 65536 + 88 ≤ A ∧ A % 8 = 0) (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (tag : μ.read A = 14) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296) (hptr : 65536 ≤ ptr ∧ ptr + 48 < 4294967296)
    (hlen : 32 ≤ len ∧ len < 4294967296)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hrdA : rd + 16 ≤ A - 88 ∨ A + 56 ≤ rd) (hpA : ptr + 56 ≤ A - 88 ∨ A + 56 ≤ ptr)
    (hOA' : O + 40 ≤ A - 88 ∨ A + 56 ≤ O) (hOr : O + 40 ≤ rd ∨ rd + 16 ≤ O)
    (hO40 : O + 40 ≤ 4294967296)
    (hws : ∀ a, A - 88 ≤ a → a < A + 32 → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hwO : ∀ a, O ≤ a → a < O + 40 → μ.writable a = true)
    (hrp : ∀ a, ptr ≤ a → a < ptr + 32 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 20626 ω μ x t ω' μ' x 510 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775821 ∧ μ'.readN (O + 8) 32 = μ.readN ptr 32 ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 32) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 32) ∧
      (∀ a, a < 4294967296 → (a < A - 88 ∨ A + 32 ≤ a) → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 40 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hA2 := F.hA
  obtain ⟨ω1, run1, e0, e1, e5, e6⟩ := dispatch (p := p) (P := P) (R := R) x ω μ A 14 (by decide) (by omega)
    F.h1 h7 tag tab (F.hr A (by omega) (by omega)) hrt
  obtain ⟨ω2, μ2, run2, f0, f1, f5, f6, f7, f8, f9, ffr, frd, fwr⟩ := y1 (p := p) (P := P) (R := R) x ω1 μ A
    (by omega) (e1.trans F.h1) (fun a h1 h2 => hws a (by omega) h2)
  obtain ⟨ω3, μ3, run3, g0, g1, g5, g6, g7, gR0, gR8, gbuf, gfr, grd, gwr⟩ :=
    read_big_sp (p := p) (P := P) (R := R) x ω2 μ2 940 20803 A rd A ptr len 32 f0 (f1.trans (e1.trans F.h1))
      (f7.trans (e6.trans h6)) f8 f9 (by decide) jte_469 bs_20803 ⟨by omega, by omega, hA.2⟩ hrd
      (by omega) (by omega) (by decide) hlen.1 hlen.2 (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [fwr]; exact hws a h1 (by omega))
      (fun a h1 h2 => by rw [fwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [fwr]; exact hws a (by omega) h2)
      (fun a h1 h2 => by rw [frd]; exact hrp a h1 h2)
      (by rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact hR8)
  have hfar : ∀ a, A + 32 ≤ a → a < A + 56 → μ3.read a = μ.read a :=
    fun a h1 h2 => (gfr a (by omega) (by omega) (by omega) (by omega)).trans (ffr a (by omega) (by omega))
  obtain ⟨ω4, μ4, run4, k0, k1, k5, k6, kO, kO8, kfr, krd, kwr⟩ := y2 (p := p) (P := P) (R := R) x ω3 μ3
    A O ret t v5 v6 hA2 hO40 (by omega) (g1.trans (f1.trans (e1.trans F.h1))) (g5.trans (f5.trans (e5.trans F.h5))) g7 F.hv5 F.hv6
    (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega))]; exact F.s0)
    (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega))]; exact F.s5)
    (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega))]; exact F.s6)
    F.hret F.hjt F.hbt (fun a h1 h2 => by rw [gwr, fwr]; exact hwO a h1 h2)
    (fun a h1 h2 => by rw [grd, frd]; exact F.hr a h1 h2)
  refine ⟨ω4, μ4, (run1.trans (run2.trans (run3.trans run4))).mono (by omega), k0, k1, k5, k6, kO,
    ?_, ?_, ?_, ?_, fun a => by rw [krd, grd, frd], fun a => by rw [kwr, gwr, fwr]⟩
  · rw [kO8, gbuf]; exact Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))
  · rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (by omega))]; exact gR0
  · rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (by omega))]; exact gR8
  · intro a h0 h1 h2 h3
    rw [kfr a h0 h3, gfr a h0 (by omega) h2 (by omega)]; exact ffr a h0 (by omega)

end Services.Bootstrap.Decode.Hash
