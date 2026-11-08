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

end Services.Bootstrap.Decode.HashU64
