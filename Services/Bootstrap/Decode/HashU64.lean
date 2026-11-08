import Services.Bootstrap.Decode.Hash
import Services.Bootstrap.Decode.Fixed

/-!
# `Instruction::decode`: variants with a hash and a `u64`

`Solicit { hash, len: u64 }` (tag 6) is decoded by a helper at 21749 with its own 88-octet frame at
S = A − 88: it reads the hash into S + 32 (`read_big_sp`), moves it to S, reads the `u64` into S + 32
(`read_ok`), and stores the variant into the slot O. Then `Instruction::decode` returns as usual.
-/

namespace Services.Bootstrap.Decode.HashU64

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Decode.Tag
  Services.Bootstrap.Decode.Hash

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 21741 … 21789: `Solicit`'s decoder enters the helper: an 88-octet frame at S = A − 88 saving the
    return address 1002, O and the reader at S + 80, S + 72, S + 64, a zeroed buffer at S + 32, and
    the call of the reader for 32 octets into S + 32 (return address 1092). -/
theorem s1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (A O rd : Nat)
    (hA : 65536 + 88 ≤ A ∧ A < 4294967296) (h1 : ω[1] = UInt64.ofNat A) (h5 : ω[5] = UInt64.ofNat O)
    (h6 : ω[6] = UInt64.ofNat rd) (hO : O < 18446744073709551616) (hrd : rd < 18446744073709551616)
    (hw : ∀ a, A - 88 ≤ a → a < A → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 21741 ω μ x 58434 ω' μ' x 18 ∧
      ω'[0] = UInt64.ofNat 1092 ∧ ω'[1] = UInt64.ofNat (A - 88) ∧ ω'[5] = UInt64.ofNat O ∧
      ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (A - 56) ∧
      ω'[9] = UInt64.ofNat 32 ∧
      μ'.readN (A - 8) 8 = Num.encodeLE 8 1002 ∧ μ'.readN (A - 16) 8 = Num.encodeLE 8 O ∧
      μ'.readN (A - 24) 8 = Num.encodeLE 8 rd ∧
      (∀ a, a < 4294967296 → (a < A - 88 ∨ A ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hA, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals (simp only [show A - 88 + 80 = A - 8 by omega, show A - 88 + 72 = A - 16 by omega,
      show A - 88 + 64 = A - 24 by omega]; post_simp)

/-- Four words copied from A … A + 32 to D … D + 32, as the stores leave them. -/
theorem copy4g (μ ν : Memory) (A D : Nat) (hD : D + 32 ≤ 4294967296) :
    ((((ν.writeN D (Num.encodeLE 8 (rdN μ A 8 % 18446744073709551616))).writeN (D + 8)
      (Num.encodeLE 8 (rdN μ (A + 8) 8 % 18446744073709551616))).writeN (D + 16)
      (Num.encodeLE 8 (rdN μ (A + 16) 8 % 18446744073709551616))).writeN (D + 24)
      (Num.encodeLE 8 (rdN μ (A + 24) 8 % 18446744073709551616))).readN D 32 = μ.readN A 32 := by
  have hm : ∀ a, rdN μ a 8 % 18446744073709551616 = rdN μ a 8 := fun a => Nat.mod_eq_of_lt (rdN_lt64 μ a)
  rw [hm A, hm (A + 8), hm (A + 16), hm (A + 24), encodeLE_rdN, encodeLE_rdN, encodeLE_rdN, encodeLE_rdN]
  rw [readN_32, readN_32]
  simp (disch := (simp [two32] <;> omega)) only [Memory.readN_writeN_same, Memory.readN_writeN_disjoint]

/-- 23395 … 23433: the hash read succeeded (ω₇ = 0): the helper moves it from S + 32 to S, zeroes
    S + 32 … S + 40 and calls the reader for 8 octets into S + 32 (return address 1094). -/
theorem s2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S : Nat)
    (hS : S + 64 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat 0)
    (hw : ∀ a, S ≤ a → a < S + 40 → μ.writable a = true)
    (hr : ∀ a, S + 32 ≤ a → a < S + 64 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 23395 ω μ x 58434 ω' μ' x 15 ∧
      ω'[0] = UInt64.ofNat 1094 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = ω[6] ∧ ω'[8] = UInt64.ofNat (S + 32) ∧ ω'[9] = UInt64.ofNat 8 ∧
      μ'.readN S 32 = μ.readN (S + 32) 32 ∧
      (∀ a, a < 4294967296 → (a < S ∨ S + 40 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hS, hw, hr, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try exact UInt64.ofNat_toNat
    all_goals try (have := copy4g μ μ (S + 32) S (by omega); simp only [Nat.add_assoc, Nat.reduceAdd] at this; exact this)

/-- 23440 … 23517 then 21793 … 21805: the `u64` read succeeded (ω₇ = 0): the helper stores
    `Solicit`'s discriminant word 2^63 + 5 at O, the hash (S … S + 32) at O + 8 and the `u64`
    (S + 32) at O + 40, pops its frame and returns to 21793, and the decoder returns through its frame
    at A = S + 88. -/
theorem s3 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S O ret t v5 v6 v o6 : Nat) (hA : S + 88 + 56 < 4294967296) (hO : O + 48 ≤ 4294967296)
    (hOS : O + 48 ≤ S ∨ S + 144 ≤ O)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat O) (h7 : ω[7] = UInt64.ofNat 0)
    (hv : v < 18446744073709551616) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (ho6 : o6 < 18446744073709551616) (hOv : O < 18446744073709551616)
    (sv : μ.readN (S + 32) 8 = Num.encodeLE 8 v)
    (sr : μ.readN (S + 80) 8 = Num.encodeLE 8 1002) (sO : μ.readN (S + 72) 8 = Num.encodeLE 8 O)
    (so6 : μ.readN (S + 64) 8 = Num.encodeLE 8 o6)
    (s0 : μ.readN (S + 136) 8 = Num.encodeLE 8 ret) (s5 : μ.readN (S + 128) 8 = Num.encodeLE 8 v5)
    (s6 : μ.readN (S + 120) 8 = Num.encodeLE 8 v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hw : ∀ a, O ≤ a → a < O + 48 → μ.writable a = true)
    (hr : ∀ a, S ≤ a → a < S + 144 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 23440 ω μ x t ω' μ' x 24 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (S + 144) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775813 ∧ μ'.readN (O + 8) 32 = μ.readN S 32 ∧
      μ'.readN (O + 40) 8 = Num.encodeLE 8 v ∧
      (∀ a, a < 4294967296 → (a < O ∨ O + 48 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rd : ∀ a w, w < 2 ^ 64 → μ.readN a 8 = Num.encodeLE 8 w → rdN μ a 8 = w := by
    intro a w hw h
    show Num.decodeLE _ = _
    rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hw]
  have rv := rd _ v hv sv
  have rr := rd _ 1002 (by decide) sr
  have rO := rd _ O hOv sO
  have ro6 := rd _ o6 ho6 so6
  have r0 : rdN μ (S + 88 + 48) 8 = ret := by rw [show S + 88 + 48 = S + 136 by omega]; exact rd _ ret (by omega) s0
  have r5 : rdN μ (S + 88 + 40) 8 = v5 := by rw [show S + 88 + 40 = S + 128 by omega]; exact rd _ v5 hv5 s5
  have r6 : rdN μ (S + 88 + 32) 8 = v6 := by rw [show S + 88 + 32 = S + 120 by omega]; exact rd _ v6 hv6 s6
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h7, hA, hO, hOS, hw, hr, rv, rr, rO, ro6, r0, r5, r6, hret, hjt, hbt,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try (rw [show O + 16 = O + 8 + 8 by omega, show O + 24 = O + 8 + 16 by omega,
      show O + 32 = O + 8 + 24 by omega]; exact copy4g μ _ S (O + 8) (by omega))

end Services.Bootstrap.Decode.HashU64
