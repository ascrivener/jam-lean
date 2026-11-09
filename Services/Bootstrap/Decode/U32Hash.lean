import Services.Bootstrap.Decode.HashU64

/-!
# `Instruction::decode`: `Eject { target: u32, code_hash }`

`Eject` (tag 4) is decoded by a helper with a 64-octet frame at S = A − 64: it reads the `u32` into
S + 8 (`read_ok`), parks it (sign-extended) at S, reads the hash into S + 8 (`read_big_sp`), and stores
the variant into the slot O: the discriminant word 2^63 + 3 at O, the hash at O + 8 and the `u32` at
O + 40.
-/

namespace Services.Bootstrap.Decode.U32Hash

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Decode.Tag
  Services.Bootstrap.Decode.Hash Services.Bootstrap.Decode.HashU64

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 20914 … 20953: `Eject`'s decoder enters the helper: a 64-octet frame at S = A − 64 saving the
    return address 948, O and the reader at S + 56, S + 48, S + 40, a zeroed `u32` at S + 8, and the
    call of the reader for 4 octets into S + 8 (return address 1084). -/
theorem e1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (A O rd : Nat)
    (hA : 65536 + 64 ≤ A ∧ A < 4294967296) (h1 : ω[1] = UInt64.ofNat A) (h5 : ω[5] = UInt64.ofNat O)
    (h6 : ω[6] = UInt64.ofNat rd) (hO : O < 18446744073709551616) (hrd : rd < 18446744073709551616)
    (hw : ∀ a, A - 64 ≤ a → a < A → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 20914 ω μ x 58434 ω' μ' x 15 ∧
      ω'[0] = UInt64.ofNat 1084 ∧ ω'[1] = UInt64.ofNat (A - 64) ∧ ω'[5] = UInt64.ofNat O ∧
      ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (A - 56) ∧
      ω'[9] = UInt64.ofNat 4 ∧
      μ'.readN (A - 8) 8 = Num.encodeLE 8 948 ∧ μ'.readN (A - 16) 8 = Num.encodeLE 8 O ∧
      μ'.readN (A - 24) 8 = Num.encodeLE 8 rd ∧
      (∀ a, a < 4294967296 → (a < A - 64 ∨ A ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hA, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals (simp only [show A - 64 + 56 = A - 8 by omega, show A - 64 + 48 = A - 16 by omega,
      show A - 64 + 40 = A - 24 by omega, show A - 64 + 8 = A - 56 by omega]; post_simp)

/-- The low four octets of a word. -/
theorem take_encodeLE (x : Nat) : (Num.encodeLE 8 x).take 4 = Num.encodeLE 4 x := by
  simp [Num.encodeLE]

/-- A sign-extended `u32`, reduced to 64 bits, has the `u32`'s four octets. -/
theorem encodeLE4_sxw (v : Nat) (hv : v < 4294967296) :
    Num.encodeLE 4 (sxw 4 v % 18446744073709551616) = Num.encodeLE 4 v := by
  rw [← encodeLE_mod 4 (sxw 4 v % 18446744073709551616), Nat.mod_mod_of_dvd _ (by decide), encodeLE_mod,
    encodeLE_sxw 4 v (Or.inr rfl) hv]

/-- 23188 … 23217: the `u32` read succeeded (ω₇ = 0): the helper parks it, sign-extended, as a word at
    S, zeroes S + 8 … S + 40 and calls the reader for 32 octets into S + 8 (return address 1086). -/
theorem e2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S v : Nat)
    (hS : S + 40 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat 0)
    (hv : v < 4294967296) (sv : μ.readN (S + 8) 4 = Num.encodeLE 4 v)
    (hw : ∀ a, S ≤ a → a < S + 40 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 23188 ω μ x 58434 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 1086 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = ω[6] ∧ ω'[8] = UInt64.ofNat (S + 8) ∧ ω'[9] = UInt64.ofNat 32 ∧
      (μ'.readN S 8).take 4 = Num.encodeLE 4 v ∧
      (∀ a, a < 4294967296 → (a < S ∨ S + 40 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rv : rdN μ (S + 8) 4 = v := by
    show Num.decodeLE _ = _
    rw [sv, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (by simpa using hv)]
  have hr : ∀ a, S ≤ a → a < S + 40 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hS, hw, hr, rv, ↓rdN_fold, ↓loadI_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try exact UInt64.ofNat_toNat
    all_goals try (rw [take_encodeLE, encodeLE4_sxw v hv])

/-- 23224 … 23301 then 20957 … 20969: the hash read succeeded (ω₇ = 0): the helper stores `Eject`'s
    discriminant word 2^63 + 3 at O, the hash (S + 8 … S + 40) at O + 8 and the `u32` (the low four
    octets of the word at S) at O + 40, pops its frame and returns to 20957, and the decoder returns
    through its frame at A = S + 64. -/
theorem e3 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S O ret t v5 v6 w o6 : Nat) (hA : S + 64 + 56 < 4294967296) (hO : O + 44 ≤ 4294967296)
    (hOS : O + 44 ≤ S ∨ S + 120 ≤ O)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat O) (h7 : ω[7] = UInt64.ofNat 0)
    (hw64 : w < 18446744073709551616) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (ho6 : o6 < 18446744073709551616) (hOv : O < 18446744073709551616)
    (sw : μ.readN S 8 = Num.encodeLE 8 w)
    (sr : μ.readN (S + 56) 8 = Num.encodeLE 8 948) (sO : μ.readN (S + 48) 8 = Num.encodeLE 8 O)
    (so6 : μ.readN (S + 40) 8 = Num.encodeLE 8 o6)
    (s0 : μ.readN (S + 112) 8 = Num.encodeLE 8 ret) (s5 : μ.readN (S + 104) 8 = Num.encodeLE 8 v5)
    (s6 : μ.readN (S + 96) 8 = Num.encodeLE 8 v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hw : ∀ a, O ≤ a → a < O + 44 → μ.writable a = true)
    (hr : ∀ a, S ≤ a → a < S + 120 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 23224 ω μ x t ω' μ' x 24 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (S + 120) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775811 ∧ μ'.readN (O + 8) 32 = μ.readN (S + 8) 32 ∧
      μ'.readN (O + 40) 4 = Num.encodeLE 4 w ∧
      (∀ a, a < 4294967296 → (a < O ∨ O + 44 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rd : ∀ a w, w < 2 ^ 64 → μ.readN a 8 = Num.encodeLE 8 w → rdN μ a 8 = w := by
    intro a w hw h
    show Num.decodeLE _ = _
    rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hw]
  have rw0 := rd _ w hw64 sw
  have rr := rd _ 948 (by decide) sr
  have rO := rd _ O hOv sO
  have ro6 := rd _ o6 ho6 so6
  have r0 : rdN μ (S + 64 + 48) 8 = ret := by rw [show S + 64 + 48 = S + 112 by omega]; exact rd _ ret (by omega) s0
  have r5 : rdN μ (S + 64 + 40) 8 = v5 := by rw [show S + 64 + 40 = S + 104 by omega]; exact rd _ v5 hv5 s5
  have r6 : rdN μ (S + 64 + 32) 8 = v6 := by rw [show S + 64 + 32 = S + 96 by omega]; exact rd _ v6 hv6 s6
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h7, hA, hO, hOS, hw, hr, rw0, rr, rO, ro6, r0, r5, r6, hret, hjt, hbt,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try (rw [show O + 16 = O + 8 + 8 by omega, show O + 24 = O + 8 + 16 by omega,
      show O + 32 = O + 8 + 24 by omega, show S + 16 = S + 8 + 8 by omega, show S + 24 = S + 8 + 16 by omega,
      show S + 32 = S + 8 + 24 by omega]; exact copy4g μ _ (S + 8) (O + 8) (by omega))
    all_goals try exact encodeLE_mod 4 w

end Services.Bootstrap.Decode.U32Hash
