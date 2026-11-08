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

end Services.Bootstrap.Decode.U32Hash
