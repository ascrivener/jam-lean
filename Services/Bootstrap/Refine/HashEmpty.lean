import Services.Bootstrap.Decode.VecHash
import Services.Bootstrap.Decode.VecHash32

/-!
# Decoding no hashes (function 1764 with n = 0)

`VecHash` proves the hash reader at 1764 for 1 ≤ n ≤ 512. With n = 0 it opens its 152-octet frame at S = ω₁ − 152,
takes the branch at 1800 to 2123, allocates nothing and stores the empty `Vec` {cap 0, ptr 1, len 0} to the slot
(ω₇), then returns (`vec_hash_empty`); `vec_hash32_empty` is the same for its copy at 907. This is the reader `AssignForGasCost` with q = [] and
`RandomStorageAccumulate(Some [])` call (GP v0.8.0 B.7).
-/

namespace Services.Bootstrap.Decode.VecHash

open PVM Services.Bootstrap Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **No hashes** (1764, n = 0): the empty `Vec` {0, 1, 0} at out, nothing read or allocated; returns to t with
    ω₁, ω₅, ω₆ restored. Memory changes only in the frame [S, S + 152) and out … out + 24. -/
theorem vec_hash_empty {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S out rd ret t v5 v6 : Nat) (hS : 65536 ≤ S ∧ S + 152 < 4294967296)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat (S + 152)) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat out) (h8 : ω[8] = UInt64.ofNat rd)
    (h9 : ω[9] = UInt64.ofNat 0) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hrd : rd < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hO : out + 24 ≤ 4294967296) (hOS : out + 24 ≤ S ∨ S + 152 ≤ out)
    (hw : ∀ a, S ≤ a → a < S + 152 → μ.writable a = true)
    (hwO : ∀ a, out ≤ a → a < out + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 1764 ω μ x t ω' μ' x 40 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (S + 152) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN out 8 = Num.encodeLE 8 0 ∧ μ'.readN (out + 8) 8 = Num.encodeLE 8 1 ∧
      μ'.readN (out + 16) 8 = Num.encodeLE 8 0 ∧
      (∀ a, a < 4294967296 → (a < S ∨ S + 152 ≤ a) → (a < out ∨ out + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S ≤ a → a < S + 152 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, h9, hS, hw, hr, hwO, hO, hOS, hret, hjt, hbt,
      rdN_writeN_disjoint, VecU8.rdN_writeN_same8, VecU8.rdN_writeN_lit, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals (try simp only [show S + 152 - 152 = S by omega])
    post_simp
    all_goals try decide

end Services.Bootstrap.Decode.VecHash

namespace Services.Bootstrap.Decode.VecHash32

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **No hashes** (907, n = 0): the empty `Vec` {0, 1, 0} at out, nothing read or allocated; returns to t with
    ω₁, ω₅, ω₆ restored. Memory changes only in the frame [S, S + 152) and out … out + 24. -/
theorem vec_hash32_empty {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (S out rd ret t v5 v6 : Nat) (hS : 65536 ≤ S ∧ S + 152 < 4294967296)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat (S + 152)) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat out) (h8 : ω[8] = UInt64.ofNat rd)
    (h9 : ω[9] = UInt64.ofNat 0) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hrd : rd < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hO : out + 24 ≤ 4294967296) (hOS : out + 24 ≤ S ∨ S + 152 ≤ out)
    (hw : ∀ a, S ≤ a → a < S + 152 → μ.writable a = true)
    (hwO : ∀ a, out ≤ a → a < out + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 907 ω μ x t ω' μ' x 40 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (S + 152) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN out 8 = Num.encodeLE 8 0 ∧ μ'.readN (out + 8) 8 = Num.encodeLE 8 1 ∧
      μ'.readN (out + 16) 8 = Num.encodeLE 8 0 ∧
      (∀ a, a < 4294967296 → (a < S ∨ S + 152 ≤ a) → (a < out ∨ out + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S ≤ a → a < S + 152 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, h9, hS, hw, hr, hwO, hO, hOS, hret, hjt, hbt,
      rdN_writeN_disjoint, VecU8.rdN_writeN_same8, VecU8.rdN_writeN_lit, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals (try simp only [show S + 152 - 152 = S by omega])
    post_simp
    all_goals try decide

end Services.Bootstrap.Decode.VecHash32
