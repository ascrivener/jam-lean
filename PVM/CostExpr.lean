/-!
# Cells of the gas cost tables (GP v0.8.0 §A.10)

The generated `PVM.Tables` records each row of the paper's gas cost table as written,
before evaluation; `PVM.Gas` evaluates the cells for a concrete instruction.
-/

namespace PVM

/-- One cell of the gas cost table of GP §A.10 (`sec:gascosttables`). -/
inductive CostExpr where
  /-- A literal number. -/
  | const (n : Nat)
  /-- 𝔓(a, b): `a` if the instruction's source and destination registers overlap, else `b`. -/
  | overlap (a b : Nat)
  /-- 𝔓_S(a, b): `a` if r_A = r_D, else `b` (non-immediate shifts and rotates). -/
  | overlapShift (a b : Nat)
  /-- 𝔪, the cost of a memory access. -/
  | memory
  /-- 𝔟, the cost of a branch. -/
  | branch
  deriving DecidableEq, Repr

/-- A row of the gas cost table: `(č, ď, x̌_A, x̌_L, x̌_S, x̌_M, x̌_D)` (GP §A.10). -/
structure CostRow where
  /-- č: cycles to finish execution. -/
  cycles : CostExpr
  /-- ď: decode slots. -/
  decodeSlots : CostExpr
  /-- x̌_A: ALU units. -/
  alu : CostExpr
  /-- x̌_L: load units. -/
  load : CostExpr
  /-- x̌_S: store units. -/
  store : CostExpr
  /-- x̌_M: multiply units. -/
  mul : CostExpr
  /-- x̌_D: divide units. -/
  div : CostExpr
  deriving DecidableEq, Repr

end PVM
