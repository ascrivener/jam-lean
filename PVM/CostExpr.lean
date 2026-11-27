/-!
# Cells of the gas cost tables (GP v0.8.1 §A.10)

The generated `PVM.Tables` records each row of the paper's gas cost table as written,
before evaluation; `PVM.Gas` evaluates the cells for a concrete instruction.
-/

namespace PVM

/-- One cell of the gas cost table of GP §A.10 (`sec:gascosttables`). -/
inductive CostExpr where
  /-- A literal number. -/
  | const (n : Nat)
  /-- $\mathfrak{P}(a, b)$: `a` if the instruction's source and destination registers overlap, else `b`. -/
  | overlap (a b : Nat)
  /-- $\mathfrak{P}_S(a, b)$: `a` if $r_A = r_D$, else `b` (non-immediate shifts and rotates). -/
  | overlapShift (a b : Nat)
  /-- $\mathfrak{m}$, the cost of a memory access. -/
  | memory
  /-- $\mathfrak{b}$, the cost of a branch. -/
  | branch
  deriving DecidableEq, Repr

/-- A row of the gas cost table: $(\check{c}, \check{d}, \check{x}_A, \check{x}_L, \check{x}_S, \check{x}_M, \check{x}_D)$ (GP §A.10). -/
structure CostRow where
  /-- $\check{c}$: cycles to finish execution. -/
  cycles : CostExpr
  /-- $\check{d}$: decode slots. -/
  decodeSlots : CostExpr
  /-- $\check{x}_A$: ALU units. -/
  alu : CostExpr
  /-- $\check{x}_L$: load units. -/
  load : CostExpr
  /-- $\check{x}_S$: store units. -/
  store : CostExpr
  /-- $\check{x}_M$: multiply units. -/
  mul : CostExpr
  /-- $\check{x}_D$: divide units. -/
  div : CostExpr
  deriving DecidableEq, Repr

end PVM
