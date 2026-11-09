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

end Services.Bootstrap.Decode.Lookup
