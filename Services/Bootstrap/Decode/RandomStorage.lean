import Services.Bootstrap.Decode.Tag
import Services.Bootstrap.Reader

/-!
# `Instruction::decode` of `RandomStorageAccumulate(Err(()))`

`RandomStorageAccumulate` (tag 22) holds a `Result<Vec<[u8; 32]>, ()>`. Its decoder opens a 56-octet
frame at F = A − 56, keeps its result slot (A) at F, and reads the result's tag octet into F + 8
(`read_ok`). For tag 1 (`Err`) it stores the niche word 2^64 − 1 at A; for tag 0 (`Ok`) it decodes the
`Vec`, which allocates when it is not empty. Back in `Instruction::decode` the three words at A are
copied to O + 8 after the discriminant word 2^63 + 21 at O.

This file proves the `Err` case: `random_storage_err`.
-/

namespace Services.Bootstrap.Decode.RandomStorage

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

theorem rd8 {μ : Memory} {a w : Nat} (hw : w < 2 ^ 64) (h : μ.readN a 8 = Num.encodeLE 8 w) : rdN μ a 8 = w := by
  show Num.decodeLE _ = _
  rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hw]

/-- 21975 … 22014: the decoder opens its frame at F = A − 56 (the return address 1018, O and the reader
    at F + 48, F + 40, F + 32, its result slot A at F), zeroes the octet at F + 8 and calls the reader
    for 1 octet into F + 8 (return address 1676). -/
theorem q1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (A O rd : Nat)
    (hA : 65536 + 56 ≤ A ∧ A < 4294967296) (h1 : ω[1] = UInt64.ofNat A) (h5 : ω[5] = UInt64.ofNat O)
    (h6 : ω[6] = UInt64.ofNat rd) (hO : O < 18446744073709551616) (hrd : rd < 18446744073709551616)
    (hw : ∀ a, A - 56 ≤ a → a < A → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 21975 ω μ x 58434 ω' μ' x 15 ∧
      ω'[0] = UInt64.ofNat 1676 ∧ ω'[1] = UInt64.ofNat (A - 56) ∧ ω'[5] = UInt64.ofNat O ∧
      ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (A - 48) ∧
      ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (A - 8) 8 = Num.encodeLE 8 1018 ∧ μ'.readN (A - 16) 8 = Num.encodeLE 8 O ∧
      μ'.readN (A - 24) 8 = Num.encodeLE 8 rd ∧ μ'.readN (A - 56) 8 = Num.encodeLE 8 A ∧
      (∀ a, a < 4294967296 → (a < A - 56 ∨ A ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hA, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals (try simp only [show A - 56 + 48 = A - 8 by omega, show A - 56 + 40 = A - 16 by omega,
      show A - 56 + 32 = A - 24 by omega, show A - 56 + 8 = A - 48 by omega])
    post_simp
    all_goals try (rw [Nat.mod_eq_of_lt (by omega)])
    all_goals try (congr 1; exact Nat.mod_eq_of_lt (by omega))
    all_goals try assumption

/-- 35823 … 35935: the tag read succeeded (ω₇ = 0) and is 1 (`Err`): the niche word 2^64 − 1 goes to
    the result slot A (from F), and the decoder restores ω₀, ω₅, ω₆ from F + 48, F + 40, F + 32 and returns
    (to 22018 for the return address 1018). -/
theorem q_err {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (F A r0 t v5 v6 : Nat) (hF : 65536 ≤ F ∧ F + 56 < 4294967296)
    (hAF : A + 8 ≤ 4294967296) (hAF' : A + 8 ≤ F ∨ F + 56 ≤ A)
    (h1 : ω[1] = UInt64.ofNat F) (h7 : ω[7] = UInt64.ofNat 0)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (tag : μ.read (F + 8) = 1) (sA : μ.readN F 8 = Num.encodeLE 8 A)
    (s0 : μ.readN (F + 48) 8 = Num.encodeLE 8 r0) (s5 : μ.readN (F + 40) 8 = Num.encodeLE 8 v5)
    (s6 : μ.readN (F + 32) 8 = Num.encodeLE 8 v6)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0)
    (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hr : ∀ a, F ≤ a → a < F + 56 → μ.readable a = true)
    (hw : ∀ a, A ≤ a → a < A + 8 → μ.writable a = true) :
    ∃ ω', FreeStepsH p R 35823 ω μ x t ω' (μ.writeN A (Num.encodeLE 8 18446744073709551615)) x 20 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (F + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 := by
  have rb : rdN μ (F + 8) 1 = 1 := by
    simp only [rdN, Memory.readN, List.range_one, List.map_cons, List.map_nil, Nat.add_zero, tag,
      Num.decodeLE]
    simp
  have rA := rd8 (by omega) sA
  have r0' := rd8 (by omega) s0
  have r5 := rd8 hv5 s5
  have r6 := rd8 hv6 s6
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h7, hF, hAF, hAF', hw, hr, rb, rA, r0', r5, r6, hret, hjt, hbt, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_⟩
    post_simp

/-- 22018 … 22070: the result at A is not the error word (w₀ ≠ 2^64 − 2): its three words w₀, w₁, w₂
    are copied to O + 8, the discriminant word 2^63 + 21 goes to O, and the function returns through
    its frame at A. -/
theorem q2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (A O w0 w1 w2 ret t v5 v6 : Nat) (hA : 65536 ≤ A ∧ A + 56 < 4294967296)
    (hO : O + 32 ≤ 4294967296) (hOA : O + 32 ≤ A ∨ A + 56 ≤ O)
    (h1 : ω[1] = UInt64.ofNat A) (h5 : ω[5] = UInt64.ofNat O)
    (hw0 : w0 < 18446744073709551616) (hw0' : w0 ≠ 18446744073709551614)
    (hw1 : w1 < 18446744073709551616) (hw2 : w2 < 18446744073709551616)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (s0' : μ.readN A 8 = Num.encodeLE 8 w0) (s1' : μ.readN (A + 8) 8 = Num.encodeLE 8 w1)
    (s2' : μ.readN (A + 16) 8 = Num.encodeLE 8 w2)
    (s0 : μ.readN (A + 48) 8 = Num.encodeLE 8 ret) (s5 : μ.readN (A + 40) 8 = Num.encodeLE 8 v5)
    (s6 : μ.readN (A + 32) 8 = Num.encodeLE 8 v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hr : ∀ a, A ≤ a → a < A + 56 → μ.readable a = true)
    (hw : ∀ a, O ≤ a → a < O + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 22018 ω μ x t ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775829 ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 w0 ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 w1 ∧ μ'.readN (O + 24) 8 = Num.encodeLE 8 w2 ∧
      (∀ a, a < 4294967296 → (a < O ∨ O + 32 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r0' := rd8 hw0 s0'
  have r1' := rd8 hw1 s1'
  have r2' := rd8 hw2 s2'
  have r0 := rd8 (by omega) s0
  have r5 := rd8 hv5 s5
  have r6 := rd8 hv6 s6
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hA, hO, hOA, hw, hr, r0', r1', r2', r0, r5, r6, hw0', hret, hjt, hbt, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp

/-- A read of one octet as `read`. -/
theorem read_of_readN1 {μ ν : Memory} {a b : Nat} (h : μ.readN a 1 = ν.readN b 1) : μ.read a = ν.read b := by
  simpa [Memory.readN] using h

/-- **`RandomStorageAccumulate(Err(()))`**: from 20626, with tag 22 read without error and the reader
    `{ptr, len}` at rd (ω₆) holding the octet 1 (`Err`) next, `Instruction::decode` returns
    `RandomStorageAccumulate(Err(()))` in its slot O: the discriminant word 2^63 + 21 at O and the niche
    word 2^64 − 1 at O + 8. The reader is advanced by 1. Memory changes only in A − 144 … A + 8 (the
    frames), the reader and O … O + 32. -/
theorem random_storage_err {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (A O ret t v5 v6 rd ptr len : Nat) (F : Frame P A O ret t v5 v6 ω μ)
    (hA : 65536 + 144 ≤ A) (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (tag : μ.read A = 22) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296) (hptr : 65536 ≤ ptr ∧ ptr + 16 < 4294967296)
    (hlen : 1 ≤ len ∧ len < 4294967296)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (herr : μ.read ptr = 1)
    (hrdA : rd + 16 ≤ A - 144 ∨ A + 56 ≤ rd) (hpA : ptr + 16 ≤ A - 144 ∨ A + 56 ≤ ptr)
    (hOA : O + 32 ≤ A - 144 ∨ A + 56 ≤ O) (hOr : O + 32 ≤ rd ∨ rd + 16 ≤ O) (hO32 : O + 32 ≤ 4294967296)
    (hws : ∀ a, A - 144 ≤ a → a < A + 8 → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hwO : ∀ a, O ≤ a → a < O + 32 → μ.writable a = true)
    (hrp : μ.readable ptr = true) :
    ∃ ω' μ', FreeStepsH p R 20626 ω μ x t ω' μ' x 130 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775829 ∧
      μ'.readN (O + 8) 8 = Num.encodeLE 8 18446744073709551615 ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 1) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 1) ∧
      (∀ a, a < 4294967296 → (a < A - 144 ∨ A + 8 ≤ a) → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 32 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hA2 := F.hA
  have hO64 : O < 18446744073709551616 := by have := F.hO; omega
  obtain ⟨ω1, run1, e0, e1, e5, e6⟩ := dispatch (p := p) (P := P) (R := R) x ω μ A 22 (by decide) (by omega)
    F.h1 h7 tag tab (F.hr A (by omega) (by omega)) hrt
  obtain ⟨ω3, μ3, run3, g0, g1, g5, g6, g7, g8, g9, gs0, gs5, gs6, gsA, gfr, grd, gwr⟩ :=
    q1 (p := p) (P := P) (R := R) x ω1 μ A O rd ⟨by omega, by omega⟩ (e1.trans F.h1) (e5.trans F.h5)
      (e6.trans h6) hO64 (by omega) (fun a h1 h2 => hws a (by omega) (by omega))
  obtain ⟨ω4, μ4, run4, ⟨k0, k1', -, -, -, k5, k6, -, k7, kR0, kR8, kbuf, kfr, krd, kwr⟩⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω3 μ3 1676 35823 (A - 56) rd (A - 48) ptr len 1 g0 g1 g7 g8 g9
      (by decide) jte_837 bs_35823 ⟨by omega, by omega⟩ hrd ⟨by omega, by omega⟩ hptr (by decide) hlen.1
      hlen.2 (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [gwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [gwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [gwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [grd, show a = ptr by omega]; exact hrp)
      (by rw [Memory.readN_congr (fun j hj => gfr _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => gfr _ (by omega) (by omega))]; exact hR8)
  have htag : μ4.read (A - 56 + 8) = 1 := by
    rw [show A - 56 + 8 = A - 48 by omega, read_of_readN1 kbuf, ← herr]
    exact gfr ptr (by omega) (by omega)
  have hfr4 : ∀ a, A - 56 ≤ a → a < A + 56 → a ≠ A - 48 → μ4.read a = μ3.read a :=
    fun a h1 h2 h3 => kfr a (by omega) (by omega) (by omega) (by omega)
  obtain ⟨ω5, run5, m0, m1, m5, m6⟩ := q_err (p := p) (P := P) (R := R) x ω4 μ4 (A - 56) A 1018 22018 O rd
    ⟨by omega, by omega⟩ (by omega) (by omega) (by rw [k1', g1]) k7 hO64 (by omega) htag
    (by rw [Memory.readN_congr (fun j hj => hfr4 _ (by omega) (by omega) (by omega))]; exact gsA)
    (by rw [Memory.readN_congr (fun j hj => hfr4 _ (by omega) (by omega) (by omega)), show A - 56 + 48 = A - 8 by omega]; exact gs0)
    (by rw [Memory.readN_congr (fun j hj => hfr4 _ (by omega) (by omega) (by omega)), show A - 56 + 40 = A - 16 by omega]; exact gs5)
    (by rw [Memory.readN_congr (fun j hj => hfr4 _ (by omega) (by omega) (by omega)), show A - 56 + 32 = A - 24 by omega]; exact gs6)
    (by decide) jte_508 bs_22018
    (fun a h1 h2 => by rw [krd, grd]; exact Memory.readable_of_writable (hws a (by omega) (by omega)))
    (fun a h1 h2 => by rw [kwr, gwr]; exact hws a (by omega) (by omega))
  have two : (4294967296 : Nat) = two32 := rfl
  generalize hμ5 : μ4.writeN A (Num.encodeLE 8 18446744073709551615) = μ5 at run5
  have w5 : ∀ a, a < 4294967296 → (a < A ∨ A + 8 ≤ a) → μ5.read a = μ4.read a := fun a h1 h2 => by
    rw [← hμ5]; exact Memory.read_writeN_disjoint _ _ _ _ (by simp; omega) (by simp [two32]; omega) (by simp [two32]; omega)
  have hfar : ∀ a, a < 4294967296 → (a < A - 144 ∨ A + 8 ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ5.read a = μ.read a :=
    fun a h0 h1 h2 => (w5 a h0 (by omega)).trans ((kfr a h0 (by omega) h2 (by omega)).trans (gfr a h0 (by omega)))
  have rd5 : ∀ a, μ5.readable a = μ.readable a := fun a => by rw [← hμ5, Memory.readable_writeN, krd, grd]
  have wr5 : ∀ a, μ5.writable a = μ.writable a := fun a => by rw [← hμ5, Memory.writable_writeN, kwr, gwr]
  obtain ⟨ω6, μ6, run6, n0, n1, n5, n6, nO, nO8, -, -, nfr, nrd, nwr⟩ :=
    q2 (p := p) (P := P) (R := R) x ω5 μ5 A O 18446744073709551615 (rdN μ5 (A + 8) 8) (rdN μ5 (A + 16) 8)
      ret t v5 v6 ⟨by omega, by omega⟩ hO32 (by omega) (by rw [m1]; congr 1; omega) (by rw [m5]) (by decide)
      (by decide) (rdN_lt64 _ _) (rdN_lt64 _ _) F.hv5 F.hv6
      (by rw [← hμ5]; exact Memory.readN_writeN_same _ _ _ _ (by simp) (by simp [two32]))
      (encodeLE_rdN _ _ _).symm (encodeLE_rdN _ _ _).symm
      (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega) (by omega))]; exact F.s0)
      (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega) (by omega))]; exact F.s5)
      (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega) (by omega))]; exact F.s6)
      F.hret F.hjt F.hbt (fun a h1 h2 => by rw [rd5]; exact F.hr a h1 h2)
      (fun a h1 h2 => by rw [wr5]; exact hwO a h1 h2)
  refine ⟨ω6, μ6, (run1.trans (run3.trans (run4.trans (run5.trans run6)))).mono (by omega),
    n0, n1, n5, n6, nO, nO8, ?_, ?_, ?_, fun a => by rw [nrd, rd5], fun a => by rw [nwr, wr5]⟩
  · rw [Memory.readN_congr (a := rd) (n := 8) (fun j hj => (nfr _ (by omega) (by omega)).trans (w5 _ (by omega) (by omega)))]; exact kR0
  · rw [Memory.readN_congr (a := rd + 8) (n := 8) (fun j hj => (nfr _ (by omega) (by omega)).trans (w5 _ (by omega) (by omega)))]; exact kR8
  · intro a h0 h1 h2 h3
    rw [nfr a h0 h3]; exact hfar a h0 h1 h2

end Services.Bootstrap.Decode.RandomStorage
