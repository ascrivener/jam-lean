import Services.Bootstrap.Decode.Tag
import Services.Bootstrap.ReaderBig

/-!
# `Instruction::decode`: variants with a 32-octet hash field

A hash is read with the reader straight into the decoder's frame at A (`read_big_sp`), then copied
word by word into the result slot. This file proves `Yield { hash }` (tag 14).
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

end Services.Bootstrap.Decode.Hash
