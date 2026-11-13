import Services.Bootstrap.CodeAAll
import Services.Bootstrap.Alloc.Register
import PVM.Logic.Go

/-!
# `AccumulateItem::decode` (45126), the operand arm: a work error

A work result with tag t ∈ 1 … 6 (GP v0.8.0 Appendix C, O(l): ∞, ☇, ⊚, ⊖, BAD, BIG) carries no
more octets. The code re-reads t from a one-octet reader over b + 135 (`WorkError::decode`),
checks 1 ≤ t ≤ 6, and records the result as −1 at b + 8 (no output) and t at b + 16.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- Or with 0 cuts to 64 bits. -/
theorem bitwise_or_zero (a : Nat) : Exec.bitwise (fun x1 x2 => x1 || x2) 0 a = a % 18446744073709551616 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Exec.bitwise, Num.testBit_ofBits, Num.bit_eq_testBit, Nat.zero_testBit, Bool.false_or]
  rw [show (18446744073709551616 : Nat) = 2 ^ 64 by decide, Nat.testBit_mod_two_pow]

/-- **46920 … 46968**, a tag octet t ≠ 0 read (ω₇ = 0): t kept at b + 135, a one-octet reader
    {b + 135, 1} at b + 272, a zero octet at b + 271 and the read of t again into it (ω₇ = b + 272,
    ω₈ = b + 271, ω₉ = 1, return address 2110). -/
theorem op_te1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (b t : Nat) (h1 : ω[1] = UInt64.ofNat b) (h7 : ω[7] = UInt64.ofNat 0) (mt : rdN μ (b + 272) 1 = t)
    (ht : t ≠ 0)
    (hb : 65536 ≤ b ∧ b + 424 < 4294967296)
    (hwf : ∀ a, b ≤ a → a < b + 424 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 46920 ω μ x 58434 ω' μ' x 30 ∧
      ω'[0] = UInt64.ofNat 2110 ∧ ω'[1] = UInt64.ofNat b ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (b + 272) ∧ ω'[8] = UInt64.ofNat (b + 271) ∧ ω'[9] = UInt64.ofNat 1 ∧
      rdN μ' (b + 135) 1 = t ∧ μ'.readN (b + 272) 8 = Num.encodeLE 8 (b + 135) ∧
      μ'.readN (b + 280) 8 = Num.encodeLE 8 1 ∧
      (∀ a, a < 4294967296 → (a < b + 135 ∨ b + 136 ≤ a) → (a < b + 271 ∨ b + 288 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, b ≤ a → a < b + 424 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have ht256 : t < 256 := by rw [← mt]; exact rdN_lt μ _ 1
  have htm : t % 18446744073709551616 ≠ 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h7, mt, htm, hwf, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1]
    all_goals try with_reducible rfl
    all_goals try first
      | (rd_simp []; done)
      | rd_simp []
    all_goals try first
      | with_reducible rfl
      | exact Nat.mod_eq_of_lt (by omega)
    all_goals first
      | decide
      | rfl

/-- **46974 … 47152**, t read again (ω₇ = 0) and 1 ≤ t ≤ 6: −1 at b + 8 (no output), t at b + 16, and
    the auth trace, a `Vec<u8>`, decoded by 39634 into b + 272 (ω₇ = b + 272, ω₈ = the reader,
    return address 2116). -/
theorem op_te2 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (b t : Nat) (h1 : ω[1] = UInt64.ofNat b) (h7 : ω[7] = UInt64.ofNat 0) (mt : rdN μ (b + 271) 1 = t)
    (ht : 1 ≤ t ∧ t ≤ 6)
    (hb : 65536 ≤ b ∧ b + 424 < 4294967296)
    (hwf : ∀ a, b ≤ a → a < b + 424 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 46974 ω μ x 39634 ω' μ' x 40 ∧
      ω'[0] = UInt64.ofNat 2116 ∧ ω'[1] = UInt64.ofNat b ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (b + 272) ∧ ω'[8] = ω[6] ∧
      rdN μ' (b + 8) 8 = 18446744073709551615 ∧ rdN μ' (b + 16) 8 = t ∧
      (∀ a, a < 4294967296 → (a < b + 8 ∨ b + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, b ≤ a → a < b + 424 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have e1 : Exec.bitwise (fun x1 x2 => x1 && x2) (t + 18446744073709551609) 255 = t + 249 := by
    rw [bitwise_and_m255]; omega
  have e2 : Exec.bitwise (fun x1 x2 => x1 && x2) t 255 = t := by rw [bitwise_and_m255]; omega
  have e2' : Exec.bitwise (fun x1 x2 => x1 && x2) (t % 18446744073709551616) 255 = t := by
    rw [bitwise_and_m255]; omega
  have hm : (t + 249) % 18446744073709551616 = t + 249 := by omega
  have hl : ¬ t + 249 < 250 := by omega
  have htm : t % 18446744073709551616 = t := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h7, mt, e1, e2, e2', hm, hl, htm, bitwise_or_zero, hwf, hr, rdN_writeN_disjoint,
    ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1]
    all_goals try with_reducible rfl
    all_goals try first
      | (rd_simp []; done)
      | rd_simp []
    all_goals try first
      | with_reducible rfl
      | exact Nat.mod_eq_of_lt (by omega)
    all_goals first
      | decide
      | (rw [bitwise_or_comm, bitwise_or_zero]; simp only [Nat.reduceMul, Nat.reducePow]; omega)
      | rfl

end Services.Bootstrap.Acc
