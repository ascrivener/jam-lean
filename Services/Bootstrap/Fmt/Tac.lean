import Services.Bootstrap.CodeFAll
import PVM.Logic.Go

/-!
# Shared tactics of the logging proofs

`post_simp [hs]` closes the register and memory goals a `pvm_go` run leaves, with the extra facts
`hs`. `rdN_writeN_same8` reads back a word just written.
-/

namespace Services.Bootstrap.Fmt

open PVM

/-- A word read back where it was just written. -/
theorem rdN_writeN_same8 (μ : Memory) (a v : Nat) (ha : a + 8 ≤ 4294967296) :
    rdN (μ.writeN a (Num.encodeLE 8 v)) a 8 = v % 18446744073709551616 := by
  unfold rdN
  rw [Memory.readN_writeN_same _ _ _ _ (by simp) (by simp [two32]), Num.decodeLE_encodeLE]

/-- The word 1, just written at F, read back. -/
theorem rdN_one (μ : Memory) (F : Nat) (hF : F + 8 ≤ 4294967296) :
    rdN (μ.writeN F [UInt8.ofNat 1, UInt8.ofNat 0, UInt8.ofNat 0, UInt8.ofNat 0, UInt8.ofNat 0,
      UInt8.ofNat 0, UInt8.ofNat 0, UInt8.ofNat 0]) F 8 = 1 := by
  unfold rdN
  rw [Memory.readN_writeN_same _ _ _ _ (by simp) (by simp [two32] <;> omega)]
  decide

/-- The word 0, just written at F, read back. -/
theorem rdN_zero (μ : Memory) (F : Nat) (hF : F + 8 ≤ 4294967296) :
    rdN (μ.writeN F [UInt8.ofNat 0, UInt8.ofNat 0, UInt8.ofNat 0, UInt8.ofNat 0, UInt8.ofNat 0,
      UInt8.ofNat 0, UInt8.ofNat 0, UInt8.ofNat 0]) F 8 = 0 := by
  unfold rdN
  rw [Memory.readN_writeN_same _ _ _ _ (by simp) (by simp [two32] <;> omega)]
  decide

syntax "post_simp" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| post_simp) => `(tactic| (
  all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
    ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, PVM.Memory.readN_writeN_same,
    PVM.Memory.readN_writeN_disjoint, PVM.Memory.read_writeN_disjoint, PVM.Memory.readable_writeN,
    PVM.Memory.writable_writeN, PVM.Num.length_encodeLE, List.length_cons, List.length_nil, PVM.two32]
  all_goals try (congr 1; omega)
  all_goals try rfl))
  | `(tactic| post_simp [$hs,*]) => `(tactic| (
  all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, $hs,*,
    ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, PVM.Memory.readN_writeN_same,
    PVM.Memory.readN_writeN_disjoint, PVM.Memory.read_writeN_disjoint, PVM.Memory.readable_writeN,
    PVM.Memory.writable_writeN, PVM.Num.length_encodeLE, List.length_cons, List.length_nil, PVM.two32]
  all_goals try (congr 1; omega)
  all_goals try rfl))

end Services.Bootstrap.Fmt
