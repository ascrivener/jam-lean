import Services.Bootstrap.Decode.U32Hash

/-!
# `Instruction::decode`: `Lookup { service: u32, hash, eager: bool }`

`Lookup` (tag 8) is decoded by a helper with a 96-octet frame at S = A − 96: it reads the `u32` into
S + 40 (`read_ok`) and parks it at S, reads the hash into S + 40 (`read_big_sp`) and moves it to S + 8,
reads one octet into S + 40 (`read_ok`), checks that it is 0 or 1 (`bool`), and stores the variant into
the slot O: the discriminant word 2^63 + 7 at O, the `u32` at O + 8, the hash at O + 12 and the bool
at O + 44.
-/

namespace Services.Bootstrap.Decode.Lookup

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Decode.Tag
  Services.Bootstrap.Decode.Hash Services.Bootstrap.Decode.HashU64 Services.Bootstrap.Decode.U32Hash

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 21918 … 21957: `Lookup`'s decoder enters the helper: a 96-octet frame at S = A − 96 saving the
    return address 1014, O and the reader at S + 88, S + 80, S + 72, a zeroed `u32` at S + 40, and the
    call of the reader for 4 octets into S + 40 (return address 1100). -/
theorem l1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (A O rd : Nat)
    (hA : 65536 + 96 ≤ A ∧ A < 4294967296) (h1 : ω[1] = UInt64.ofNat A) (h5 : ω[5] = UInt64.ofNat O)
    (h6 : ω[6] = UInt64.ofNat rd) (hO : O < 18446744073709551616) (hrd : rd < 18446744073709551616)
    (hw : ∀ a, A - 96 ≤ a → a < A → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 21918 ω μ x 58434 ω' μ' x 15 ∧
      ω'[0] = UInt64.ofNat 1100 ∧ ω'[1] = UInt64.ofNat (A - 96) ∧ ω'[5] = UInt64.ofNat O ∧
      ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (A - 56) ∧
      ω'[9] = UInt64.ofNat 4 ∧
      μ'.readN (A - 8) 8 = Num.encodeLE 8 1014 ∧ μ'.readN (A - 16) 8 = Num.encodeLE 8 O ∧
      μ'.readN (A - 24) 8 = Num.encodeLE 8 rd ∧
      (∀ a, a < 4294967296 → (a < A - 96 ∨ A ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hA, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals (simp only [show A - 96 + 88 = A - 8 by omega, show A - 96 + 80 = A - 16 by omega,
      show A - 96 + 72 = A - 24 by omega, show A - 96 + 40 = A - 56 by omega]; post_simp)

/-- 23643 … 23672: the `u32` read succeeded (ω₇ = 0): the helper parks it, sign-extended, as a word at
    S, zeroes S + 40 … S + 72 and calls the reader for 32 octets into S + 40 (return address 1102). -/
theorem l2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S v : Nat)
    (hS : S + 72 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat 0)
    (hv : v < 4294967296) (sv : μ.readN (S + 40) 4 = Num.encodeLE 4 v)
    (hw0 : ∀ a, S ≤ a → a < S + 8 → μ.writable a = true)
    (hw : ∀ a, S + 40 ≤ a → a < S + 72 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 23643 ω μ x 58434 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 1102 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = ω[6] ∧ ω'[8] = UInt64.ofNat (S + 40) ∧ ω'[9] = UInt64.ofNat 32 ∧
      (μ'.readN S 8).take 4 = Num.encodeLE 4 v ∧
      (∀ a, a < 4294967296 → (a < S ∨ S + 8 ≤ a) → (a < S + 40 ∨ S + 72 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rv : rdN μ (S + 40) 4 = v := by
    show Num.decodeLE _ = _
    rw [sv, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (by simpa using hv)]
  have hr : ∀ a, S + 40 ≤ a → a < S + 72 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hS, hw, hw0, hr, rv, ↓rdN_fold, ↓loadI_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try exact UInt64.ofNat_toNat
    all_goals try (rw [take_encodeLE, encodeLE4_sxw v hv])

/-- 23679 … 23738: the hash read succeeded (ω₇ = 0): the helper moves it from S + 40 to S + 8, zeroes
    the octet at S + 40 and calls the reader for 1 octet into S + 40 (return address 1104). -/
theorem l3 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S : Nat)
    (hS : S + 72 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat 0)
    (hw : ∀ a, S + 8 ≤ a → a < S + 41 → μ.writable a = true)
    (hr : ∀ a, S + 40 ≤ a → a < S + 72 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 23679 ω μ x 58434 ω' μ' x 15 ∧
      ω'[0] = UInt64.ofNat 1104 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = ω[6] ∧ ω'[8] = UInt64.ofNat (S + 40) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (S + 8) 32 = μ.readN (S + 40) 32 ∧
      (∀ a, a < 4294967296 → (a < S + 8 ∨ S + 41 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hS, hw, hr, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try exact UInt64.ofNat_toNat
    all_goals try (rw [show S + 16 = S + 8 + 8 by omega, show S + 24 = S + 8 + 16 by omega,
      show S + 32 = S + 8 + 24 by omega, show S + 48 = S + 40 + 8 by omega, show S + 56 = S + 40 + 16 by omega,
      show S + 64 = S + 40 + 24 by omega]; exact copy4g μ μ (S + 40) (S + 8) (by omega))

set_option maxHeartbeats 32000000 in
/-- 23745 … 23829 then 21961 … 21973: the octet read succeeded (ω₇ = 0) and is a bool b ∈ {0, 1}: the
    helper stores `Lookup`'s discriminant word 2^63 + 7 at O, the `u32` (the low four octets of the word
    at S) at O + 8, the hash (S + 8 … S + 40) at O + 12 and b at O + 44, pops its frame and returns to
    21961, and the decoder returns through its frame at A = S + 96. -/
theorem l4 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S O ret t v5 v6 w b o6 : Nat) (hA : S + 96 + 56 < 4294967296) (hO : O + 45 ≤ 4294967296)
    (hOS : O + 45 ≤ S ∨ S + 152 ≤ O)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat O) (h7 : ω[7] = UInt64.ofNat 0)
    (hw64 : w < 18446744073709551616) (hb : b < 2)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (ho6 : o6 < 18446744073709551616) (hOv : O < 18446744073709551616)
    (sw : μ.readN S 8 = Num.encodeLE 8 w) (sb : μ.read (S + 40) = UInt8.ofNat b)
    (sr : μ.readN (S + 88) 8 = Num.encodeLE 8 1014) (sO : μ.readN (S + 80) 8 = Num.encodeLE 8 O)
    (so6 : μ.readN (S + 72) 8 = Num.encodeLE 8 o6)
    (s0 : μ.readN (S + 144) 8 = Num.encodeLE 8 ret) (s5 : μ.readN (S + 136) 8 = Num.encodeLE 8 v5)
    (s6 : μ.readN (S + 128) 8 = Num.encodeLE 8 v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hw : ∀ x, O ≤ x → x < O + 45 → μ.writable x = true)
    (hr : ∀ x, S ≤ x → x < S + 152 → μ.readable x = true) :
    ∃ ω' μ', FreeStepsH p R 23745 ω μ x t ω' μ' x 34 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (S + 152) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775815 ∧ μ'.readN (O + 8) 4 = Num.encodeLE 4 w ∧
      μ'.readN (O + 12) 32 = μ.readN (S + 8) 32 ∧ μ'.read (O + 44) = UInt8.ofNat b ∧
      (∀ x, x < 4294967296 → (x < O ∨ O + 45 ≤ x) → μ'.read x = μ.read x) ∧
      (∀ x, μ'.readable x = μ.readable x) ∧ (∀ x, μ'.writable x = μ.writable x) := by
  have rd : ∀ a w, w < 2 ^ 64 → μ.readN a 8 = Num.encodeLE 8 w → rdN μ a 8 = w := by
    intro a w hw h
    show Num.decodeLE _ = _
    rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hw]
  have rw0 := rd _ w hw64 sw
  have rr := rd _ 1014 (by decide) sr
  have rO := rd _ O hOv sO
  have ro6 := rd _ o6 ho6 so6
  have r0 : rdN μ (S + 96 + 48) 8 = ret := by rw [show S + 96 + 48 = S + 144 by omega]; exact rd _ ret (by omega) s0
  have r5 : rdN μ (S + 96 + 40) 8 = v5 := by rw [show S + 96 + 40 = S + 136 by omega]; exact rd _ v5 hv5 s5
  have r6 : rdN μ (S + 96 + 32) 8 = v6 := by rw [show S + 96 + 32 = S + 128 by omega]; exact rd _ v6 hv6 s6
  have rbb : rdN μ (S + 40) 1 = b := by
    simp only [rdN, Memory.readN, List.range_one, List.map_cons, List.map_nil, Nat.add_zero, sb, Num.decodeLE]
    simp; omega
  rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;>
  · rw [show ω = regsNF ω [] from rfl]
    refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h5, h7, hA, hO, hOS, hw, hr, rw0, rr, rO, ro6, r0, r5, r6, rbb, hret, hjt, hbt,
        rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x ha0 ha1 => ?_, fun x => ?_, fun x => ?_⟩
      post_simp
      all_goals try exact encodeLE_mod 4 w
      all_goals try (simp (disch := omega) only [Memory.writeN_cons, Memory.writeN_nil, PVM.read_write_eq'])
      all_goals try (rw [show O + 20 = O + 12 + 8 by omega, show O + 28 = O + 12 + 16 by omega,
        show O + 36 = O + 12 + 24 by omega, show S + 16 = S + 8 + 8 by omega, show S + 24 = S + 8 + 16 by omega,
        show S + 32 = S + 8 + 24 by omega]; exact copy4g μ _ (S + 8) (O + 12) (by omega))

end Services.Bootstrap.Decode.Lookup
