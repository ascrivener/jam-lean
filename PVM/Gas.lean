import PVM.Instr

/-!
# The gas cost model ϱ^Δ (GP v0.8.0 §A.9 `sec:gascostmodel`, §A.10 `sec:gascosttables`)

The cost of a basic block is the number of cycles a simulated out-of-order CPU needs to
retire every instruction of the block: ϱ^Δ(**c**, **k**, ı) = max(𝔛(**c**, **k**, **x**^init)_c − 3, 1).

The per-opcode table (č, ď, x̌) is generated from the paper's LaTeX into `PVM.Tables`; here
we evaluate its cells (𝔓, 𝔓_S, 𝔪, 𝔟) and run the simulation 𝔛 with its decode (𝔛', 𝔛^mov,
𝔛^dec), start (𝔛'', 𝔖) and cycle (𝔛''') steps.
-/

namespace PVM

/-! ## Source and destination registers š, ř (GP §A.9) -/

/-- A set of register indices, as a bit mask over ℕ_13. -/
structure RegSet where
  bits : Nat
  deriving DecidableEq, Repr, Inhabited

namespace RegSet
/-- ∅ -/
def empty : RegSet := ⟨0⟩
/-- {r₁, …, rₙ} -/
def ofList (rs : List RegIdx) : RegSet := ⟨rs.foldl (fun acc r => acc ||| 2 ^ r.val) 0⟩
/-- s ∪ t -/
def union (s t : RegSet) : RegSet := ⟨s.bits ||| t.bits⟩
/-- s ∖ t -/
def diff (s t : RegSet) : RegSet := ⟨s.bits &&& (8191 ^^^ t.bits)⟩
/-- s ∩ t ≠ ∅ -/
def meets (s t : RegSet) : Bool := s.bits &&& t.bits != 0
end RegSet

namespace Instr

/-- š: the registers read by an instruction, "as described by the equations in §A.5", i.e.
    every ω_X (unprimed) that its mutation mentions, regardless of whether it would be needed
    at runtime. `ecalli` reads none (§A.9). -/
def srcRegs : Instr → List RegIdx
  | .noArgs _ => []
  | .oneImm _ _ => []
  | .regExtImm _ _ _ => []
  | .twoImm _ _ _ => []
  | .oneOffset _ _ => []
  | .regImm op a _ =>
    match op with
    | .jumpInd | .storeU8 | .storeU16 | .storeU32 | .storeU64 => [a]
    | _ => []
  | .regTwoImm _ a _ _ => [a]
  | .regImmOffset op a _ _ => if op = .loadImmJump then [] else [a]
  | .twoReg _ _ a => [a]
  | .twoRegImm op a b _ =>
    match op with
    | .storeIndU8 | .storeIndU16 | .storeIndU32 | .storeIndU64 => [a, b]
    | .cmovIzImm | .cmovNzImm => [a, b]
    | _ => [b]
  | .twoRegOffset _ a b _ => [a, b]
  | .twoRegTwoImm _ _ b _ _ => [b]
  | .threeReg op a b d =>
    match op with
    | .cmovIz | .cmovNz => [a, b, d]
    | _ => [a, b]

/-- ř: the registers written by an instruction (every ω'_X its mutation mentions). -/
def dstRegs : Instr → List RegIdx
  | .noArgs _ => []
  | .oneImm _ _ => []
  | .regExtImm _ a _ => [a]
  | .twoImm _ _ _ => []
  | .oneOffset _ _ => []
  | .regImm op a _ =>
    match op with
    | .jumpInd | .storeU8 | .storeU16 | .storeU32 | .storeU64 => []
    | _ => [a]
  | .regTwoImm _ _ _ _ => []
  | .regImmOffset op a _ _ => if op = .loadImmJump then [a] else []
  | .twoReg _ d _ => [d]
  | .twoRegImm op a _ _ =>
    match op with
    | .storeIndU8 | .storeIndU16 | .storeIndU32 | .storeIndU64 => []
    | _ => [a]
  | .twoRegOffset _ _ _ _ => []
  | .twoRegTwoImm _ a _ _ _ => [a]
  | .threeReg _ _ _ d => [d]

/-- š as a `RegSet`. -/
def src (i : Instr) : RegSet := .ofList i.srcRegs
/-- ř as a `RegSet`. -/
def dst (i : Instr) : RegSet := .ofList i.dstRegs

/-- The (r_A, r_D) operands used by 𝔓_S, for the formats that have both. -/
def regsAD? : Instr → Option (RegIdx × RegIdx)
  | .twoReg _ d a => some (a, d)
  | .threeReg _ a _ d => some (a, d)
  | _ => none

/-- The static target of a branch (ı_target in 𝔟, GP §A.10). -/
def branchTarget? : Instr → Option Int
  | .regImmOffset _ _ _ y => some y
  | .twoRegOffset _ _ _ x => some x
  | _ => none

end Instr

/-! ## Evaluating the cost table (GP §A.10) -/

/-- Execution-unit counts 𝔼 = (A, L, S, M, D), with memberwise +, − and ≤ (GP §A.9). -/
structure Units where
  alu : Nat
  load : Nat
  store : Nat
  mul : Nat
  div : Nat
  deriving DecidableEq, Repr, Inhabited

namespace Units
instance : Add Units := ⟨fun a b => ⟨a.alu + b.alu, a.load + b.load, a.store + b.store, a.mul + b.mul, a.div + b.div⟩⟩
instance : Sub Units := ⟨fun a b => ⟨a.alu - b.alu, a.load - b.load, a.store - b.store, a.mul - b.mul, a.div - b.div⟩⟩
/-- a ≤ b memberwise. -/
def le (a b : Units) : Bool :=
  a.alu ≤ b.alu && a.load ≤ b.load && a.store ≤ b.store && a.mul ≤ b.mul && a.div ≤ b.div
/-- The zero tuple. -/
def zero : Units := ⟨0, 0, 0, 0, 0⟩
/-- The initial units (4, 4, 4, 1, 1) of **x**^init (GP eq. `gascostforblock`). -/
def initial : Units := ⟨4, 4, 4, 1, 1⟩
end Units

/-- The evaluated cost of one instruction: č, ď, x̌. -/
structure InstrCost where
  cycles : Nat
  decodeSlots : Nat
  units : Units
  deriving Repr

namespace Program

/-- 𝔟(**c**, ı) (GP §A.10): 1 if ζ_{ı+1+skip(ı)} or ζ_{ı_target} is `unlikely` or `trap`, else 20. -/
def branchCost (P : Program) (i : Nat) (target : Int) : Nat :=
  let cheap (n : Nat) : Bool := n == unlikelyOpcode || n == trapOpcode
  if cheap (P.zeta (P.next i)) || cheap (P.zetaInt target) then 1 else 20

/-- Evaluate a cell of the cost table for the instruction `ins` at `ı`. -/
def evalCost (P : Program) (i : Nat) (ins : Instr) : CostExpr → Nat
  | .const n => n
  | .overlap a b => if ins.src.meets ins.dst then a else b
  | .overlapShift a b =>
    -- The paper writes ω_A = ω_D; the gas model has no register values, so we compare the
    -- register indices r_A = r_D (README, note 1).
    match ins.regsAD? with
    | some (ra, rd) => if ra = rd then a else b
    | none => b
  | .memory => memoryCost
  -- Only branches have a 𝔟 cell; the fallback target is never used.
  | .branch => P.branchCost i ((ins.branchTarget?).getD (-1))

/-- (č, ď, x̌) of the instruction at `ı` (GP §A.10), if ζ_ı ∈ U. -/
def instrCost? (P : Program) (i : Nat) : Option (Instr × InstrCost) := do
  let ins ← P.decode i
  let row ← costRow? (P.zeta i)
  let e := P.evalCost i ins
  return (ins, ⟨e row.cycles, e row.decodeSlots, ⟨e row.alu, e row.load, e row.store, e row.mul, e row.div⟩⟩)

end Program

/-! ## The simulation 𝔛 (GP §A.9) -/

/-- Reorder-buffer entry states {DEC, WAIT, EXE, FIN, ∅}. -/
inductive RobState where
  | dec | wait | exe | fin | none
  deriving DecidableEq, Repr, Inhabited

/-- A reorder-buffer entry ℝ = (s, c, p, r, t) (GP §A.9). -/
structure RobEntry where
  /-- s, the state. -/
  state : RobState
  /-- c, the cycles left. -/
  cycles : Nat
  /-- p, the indices of the entries it depends on. -/
  deps : List Nat
  /-- r, the clobbered registers. -/
  regs : RegSet
  /-- t, the execution units used. -/
  units : Units
  deriving Repr, Inhabited

/-- A simulation state 𝕊 = (ı, c, d, e, t, **r**) (GP §A.9). -/
structure SimState where
  /-- ı, the next instruction to decode, or ∅. -/
  pc : Option Nat
  /-- c, the cycle counter. -/
  cycle : Nat
  /-- d, decode slots left in this cycle. -/
  decodeSlots : Nat
  /-- e, instructions still allowed to start this cycle. -/
  startSlots : Nat
  /-- t, available execution units. -/
  units : Units
  /-- **r**, the reorder buffer. -/
  rob : Array RobEntry
  deriving Repr

namespace Sim

/-- The number of decode slots per cycle (4) and starts per cycle (5) (GP §A.9). -/
def maxDecode : Nat := 4
/-- See `maxDecode`. -/
def maxStart : Nat := 5

/-- **x**^init = (ı, 0, 4, 5, (4, 4, 4, 1, 1), []) (GP eq. `gascostforblock`). -/
def init (i : Nat) : SimState := ⟨some i, 0, maxDecode, maxStart, .initial, #[]⟩

/-- l = |[r | r ∈ **x**_**r**, r_s ≠ ∅]| (GP §A.9). -/
def live (x : SimState) : Nat := x.rob.foldl (fun n e => if e.state != .none then n + 1 else n) 0

/-- 𝔖(**x**): the least index of a WAIT entry whose units fit and whose dependencies all have
    zero cycles left, if any (GP §A.9). -/
def readyToStart (x : SimState) : Option Nat :=
  (List.range x.rob.size).find? fun j =>
    let e := x.rob[j]!
    e.state == .wait && e.units.le x.units && e.deps.all fun k => x.rob[k]!.cycles == 0

/-- 𝔛^mov (GP §A.9): `move_reg` is handled by the front end and renames registers. -/
def decodeMove (P : Program) (x : SimState) (i : Nat) (ins : Instr) : SimState :=
  { x with
    pc := some (P.next i)
    decodeSlots := x.decodeSlots - 1
    rob := x.rob.map fun e =>
      { e with regs := if e.regs.meets ins.src then e.regs.union ins.dst else e.regs.diff ins.dst } }

/-- 𝔛^dec (GP §A.9): decode an instruction into a new reorder-buffer entry. -/
def decodeInstr (P : Program) (x : SimState) (i : Nat) (ins : Instr) (cost : InstrCost) : SimState :=
  let deps := (List.range x.rob.size).filter fun k => ins.src.meets x.rob[k]!.regs
  let rob := x.rob.map fun e => { e with regs := e.regs.diff ins.dst }
  { x with
    pc := if isTerminator (P.zeta i) then none else some (P.next i)
    decodeSlots := x.decodeSlots - cost.decodeSlots
    rob := rob.push ⟨.dec, cost.cycles, deps, ins.dst, cost.units⟩ }

/-- 𝔛' (GP §A.9): `move_reg` (when ı < |**c**|) goes to 𝔛^mov, everything else to 𝔛^dec. -/
def decodeStep (P : Program) (x : SimState) (i : Nat) (ins : Instr) (cost : InstrCost) : SimState :=
  if i < P.code.size && P.zeta i == moveRegOpcode then decodeMove P x i ins
  else decodeInstr P x i ins cost

/-- 𝔛'' (GP §A.9): start executing entry `n = 𝔖(**x**)`. -/
def startStep (x : SimState) (n : Nat) : SimState :=
  { x with
    startSlots := x.startSlots - 1
    units := x.units - x.rob[n]!.units
    rob := x.rob.modify n fun e => { e with state := .exe } }

/-- 𝔛''' (GP §A.9): advance one cycle. -/
def cycleStep (x : SimState) : SimState :=
  let freed := x.rob.foldl (fun u e => if e.state == .exe && e.cycles == 1 then u + e.units else u) Units.zero
  -- retired j: every entry k ≤ j is FIN or ∅ (in the state before this step)
  let retired : Array Bool := (x.rob.foldl (fun (acc : Array Bool × Bool) e =>
      let ok := acc.2 && (e.state == .fin || e.state == .none)
      (acc.1.push ok, ok)) (#[], true)).1
  { x with
    decodeSlots := maxDecode
    startSlots := maxStart
    cycle := x.cycle + 1
    units := x.units + freed
    rob := x.rob.mapIdx fun j e =>
      { e with
        state :=
          if retired[j]! then .none
          else if e.state == .dec then .wait
          else if e.state == .exe && e.cycles == 0 then .fin
          else e.state
        cycles := if e.state == .exe && e.cycles > 0 then e.cycles - 1 else e.cycles } }

/-- One transition of 𝔛 (GP §A.9). `.inl x'` continues with x'; `.inr x` is the final state;
    `none` means ď(**x**_ı) is undefined because ζ at **x**_ı is not in U (impossible for the
    blocks of valid programs). The cases are tried in the paper's order: decode (𝔛') if
    **x**_ı ≠ ∅, ď(**x**_ı) ≤ **x**_d and l < 32; else start (𝔛'') if 𝔖(**x**) ≠ ∅ and **x**_e > 0;
    else stop if **x**_ı = ∅ and l = 0; else advance a cycle (𝔛'''). -/
def transition (P : Program) (x : SimState) : Option (SimState ⊕ SimState) := do
  let l := live x
  if let some i := x.pc then
    let (ins, c) ← P.instrCost? i
    if c.decodeSlots ≤ x.decodeSlots && l < 32 then
      return .inl (decodeStep P x i ins c)
  if let some n := readyToStart x then
    if x.startSlots > 0 then
      return .inl (startStep x n)
  if x.pc.isNone && l == 0 then
    return .inr x
  return .inl (cycleStep x)

/-- 𝔛 with at most `fuel` transitions; `none` if the fuel runs out or an invalid opcode is met. -/
def run (P : Program) : Nat → SimState → Option SimState
  | 0, _ => none
  | fuel + 1, x =>
    match transition P x with
    | some (.inl x') => run P fuel x'
    | some (.inr x') => some x'
    | none => none

/-- The fuel given to 𝔛: `256 · (|**c**| − ı + 2)` transitions, at least 256 per instruction of
    the block. Each instruction is decoded once and started once, and the longest single
    instruction (č = 60 for the divisions) keeps the pipeline busy for about 64 cycles, so the
    simulation should always finish well within this. **This bound is argued, not proved.**
    Over every block of the test vectors the simulation uses at most 54 transitions per
    instruction and under 5% of this fuel; `PVM.Program.blockCost?` returns `none` if the fuel
    is ever exhausted, and the gas checker reports it. -/
def fuel (P : Program) (i : Nat) : Nat := 256 * (P.code.size - i + 2)

end Sim

namespace Program

/-- ϱ^Δ(**c**, **k**, ı) = max(**x**^final_c − 3, 1) (GP eq. `gascostforblock`); `none` if the
    simulation does not finish within its fuel or meets an opcode outside U. -/
def blockCost? (P : Program) (i : Nat) : Option Nat :=
  (Sim.run P (Sim.fuel P i) (Sim.init i)).map fun x => max (x.cycle - 3) 1

/-- ϱ^Δ as a total function: the simulated cost, or 1 in the cases where `blockCost?` has no
    value (which do not arise for the blocks of valid programs). -/
def blockCost (P : Program) (i : Nat) : Nat := (P.blockCost? i).getD 1

end Program

end PVM
