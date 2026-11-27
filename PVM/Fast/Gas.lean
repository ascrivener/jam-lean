import PVM.Gas

/-!
# A fast gas simulation 𝔛, proved equal to the paper's

`Sim.run` follows GP v0.8.1 §A.9 literally: each cycle (𝔛''') builds a list of retirement flags and
zips it with the reorder buffer; each start check (𝔖) builds `List.finRange` and indexes the buffer
(a list) once per dependency; each decode recomputes š and ř (a power of two per register) for
every buffer entry. `Sim.runFast` is the same simulation with:

* `cycleStepFast`: one pass over the buffer, computing each entry's retirement flag as it goes
  (`cycleStep_eq_cycleStepFast`);
* `readyFast`: the start check reading the buffer through an array (`readyToStart_eq_readyFast`);
* `decodeStepFast`: š and ř computed once per decode, with shifts (`decodeStep_eq_decodeStepFast`).

`Program.blockCost?_eq_blockCost?Fast` and `Program.blockCost_eq_blockCostFast` are registered with
`@[csimp]`, so compiled code that imports this module (the interpreter's block-cost tables and the
gas checker) runs the fast simulation. The kernel and every theorem still see the paper-literal
definitions.
-/

namespace PVM

namespace RegSet

/-- `RegSet.ofList` with shifts instead of powers. -/
def ofListFast (rs : List RegIdx) : RegSet := ⟨rs.foldl (fun acc r => acc ||| (1 <<< r.val)) 0⟩

theorem ofList_eq_ofListFast (rs : List RegIdx) : ofList rs = ofListFast rs := by
  simp [ofList, ofListFast, Nat.one_shiftLeft]

end RegSet

namespace RobState

/-- Pattern-matching state tests: the derived `==` on `RobState` dispatches through closures in
    compiled code. -/
@[inline] def isDec : RobState → Bool | .dec => true | _ => false
@[inline] def isWait : RobState → Bool | .wait => true | _ => false
@[inline] def isExe : RobState → Bool | .exe => true | _ => false
@[inline] def isFinOrNone : RobState → Bool | .fin | .none => true | _ => false
@[inline] def isLive : RobState → Bool | .none => false | _ => true

@[simp] theorem beq_dec (s : RobState) : (s == .dec) = s.isDec := by cases s <;> rfl
@[simp] theorem beq_wait (s : RobState) : (s == .wait) = s.isWait := by cases s <;> rfl
@[simp] theorem beq_exe (s : RobState) : (s == .exe) = s.isExe := by cases s <;> rfl
theorem fin_or_none (s : RobState) : (s == .fin || s == .none) = s.isFinOrNone := by cases s <;> rfl
theorem bne_none (s : RobState) : (s != .none) = s.isLive := by cases s <;> rfl

end RobState

namespace Sim

/-- l (`live`) with `RobState.isLive`. -/
def liveFast (x : SimState) : Nat := x.rob.foldl (fun n e => if e.state.isLive then n + 1 else n) 0

@[csimp] theorem live_eq_liveFast : @live = @liveFast := by
  funext x
  simp only [live, liveFast, RobState.bne_none]

/-- 𝔛^mov with š and ř computed once (cf. `decodeMove`). -/
def decodeMoveFast (P : Program) (x : SimState) (i : Nat) (ins : Instr) : SimState :=
  let s := RegSet.ofListFast ins.srcRegs
  let d := RegSet.ofListFast ins.dstRegs
  { x with
    pc := some (P.next i)
    decodeSlots := x.decodeSlots - 1
    rob := x.rob.map fun e =>
      { e with regs := if e.regs.meets s then e.regs.union d else e.regs.diff d } }

/-- 𝔛^dec with š and ř computed once (cf. `decodeInstr`). -/
def decodeInstrFast (P : Program) (x : SimState) (i : Nat) (ins : Instr) (cost : InstrCost) :
    SimState :=
  let s := RegSet.ofListFast ins.srcRegs
  let d := RegSet.ofListFast ins.dstRegs
  let deps := (x.rob.zipIdx.filter fun (e, _) => s.meets e.regs).map (·.2)
  let rob := x.rob.map fun e => { e with regs := e.regs.diff d }
  { x with
    pc := if isTerminator (P.zeta i) then none else some (P.next i)
    decodeSlots := x.decodeSlots - cost.decodeSlots
    rob := rob ++ [⟨.dec, cost.cycles, deps, d, cost.units⟩] }

/-- 𝔛' with `decodeMoveFast` and `decodeInstrFast`. -/
def decodeStepFast (P : Program) (x : SimState) (i : Nat) (ins : Instr) (cost : InstrCost) :
    SimState :=
  if i < P.code.size && P.zeta i == moveRegOpcode then decodeMoveFast P x i ins
  else decodeInstrFast P x i ins cost

@[csimp] theorem decodeStep_eq_decodeStepFast : @decodeStep = @decodeStepFast := by
  funext P x i ins cost
  simp [decodeStep, decodeStepFast, decodeMove, decodeMoveFast, decodeInstr, decodeInstrFast,
    Instr.src, Instr.dst, RegSet.ofList_eq_ofListFast]

/-- 𝔖 reading the buffer through an array (cf. `readyToStart`). -/
def readyFast (x : SimState) : Option (Fin x.rob.length) :=
  let arr := x.rob.toArray
  let dd (k : Nat) : Bool := if h : k < arr.size then arr[k].cycles == 0 else true
  (List.finRange x.rob.length).find? fun j =>
    let e := arr[j.val]'j.isLt
    e.state.isWait && e.units.le x.units && e.deps.all dd

@[csimp] theorem readyToStart_eq_readyFast : @readyToStart = @readyFast := by
  funext x
  unfold readyToStart readyFast
  simp only [RobState.beq_wait]
  -- the array reads are the list reads (`List.toArray`), definitionally
  rfl

/-- The new state of a buffer entry in 𝔛''', given whether it retires. -/
@[inline] def cycleEntry (e : RobEntry) (r : Bool) : RobEntry :=
  { e with
    state :=
      if r then .none
      else if e.state.isDec then .wait
      else if e.state.isExe && e.cycles == 0 then .fin
      else e.state
    cycles := if e.state.isExe && e.cycles > 0 then e.cycles - 1 else e.cycles }

/-- 𝔛''' on the buffer, one pass: `ok` says that every entry before is FIN or ∅. -/
def cycleRob : List RobEntry → Bool → List RobEntry
  | [], _ => []
  | e :: es, ok =>
    let ok' := ok && e.state.isFinOrNone
    cycleEntry e ok' :: cycleRob es ok'

theorem zipWith_retiredPrefix (rob : List RobEntry) (ok : Bool) :
    rob.zipWith cycleEntry (retiredPrefix rob ok) = cycleRob rob ok := by
  induction rob generalizing ok with
  | nil => rfl
  | cons e es ih => simp [retiredPrefix, cycleRob, ih, RobState.fin_or_none]

/-- 𝔛''' with one pass over the buffer (cf. `cycleStep`). -/
def cycleStepFast (x : SimState) : SimState :=
  let freed := x.rob.foldl (fun u e => if e.state.isExe && e.cycles == 1 then u + e.units else u) Units.zero
  { x with
    decodeSlots := maxDecode
    startSlots := maxStart
    cycle := x.cycle + 1
    units := x.units + freed
    rob := cycleRob x.rob true }

@[csimp] theorem cycleStep_eq_cycleStepFast : @cycleStep = @cycleStepFast := by
  funext x
  unfold cycleStep cycleStepFast
  rw [← zipWith_retiredPrefix]
  simp only [RobState.beq_dec, RobState.beq_exe]
  rfl

/-- One transition of 𝔛 (`transition`), restated so that its compiled code uses the fast steps
    (`@[csimp]` lemmas above). -/
def transitionFast (P : Program) (x : SimState) : Option (SimState ⊕ SimState) := do
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

theorem transition_eq_transitionFast (P : Program) (x : SimState) :
    transition P x = transitionFast P x := rfl

/-- 𝔛 with at most `fuel` fast transitions (cf. `run`). -/
def runFast (P : Program) : Nat → SimState → Option SimState
  | 0, _ => none
  | fuel + 1, x =>
    match transitionFast P x with
    | some (.inl x') => runFast P fuel x'
    | some (.inr x') => some x'
    | none => none

theorem run_eq_runFast (P : Program) : ∀ n x, run P n x = runFast P n x := by
  intro n
  induction n with
  | zero => intro; rfl
  | succ n ih =>
    intro x
    simp only [run, runFast, transition_eq_transitionFast, ih]
    rcases transitionFast P x with _ | _ | _ <;> rfl

end Sim

namespace Program

/-- ϱ^Δ? with the fast simulation (cf. `blockCost?`). -/
def blockCost?Fast (P : Program) (i : Nat) : Option Nat :=
  (Sim.runFast P (Sim.fuel P i) (Sim.init i)).map fun x => max (x.cycle - 3) 1

/-- **The fast simulation gives the paper's block costs.** -/
@[csimp] theorem blockCost?_eq_blockCost?Fast : @blockCost? = @blockCost?Fast := by
  funext P i
  simp [blockCost?, blockCost?Fast, Sim.run_eq_runFast]

/-- ϱ^Δ, restated so that its compiled code uses `blockCost?Fast`. -/
def blockCostFast (P : Program) (i : Nat) : Nat := (P.blockCost? i).getD 1

@[csimp] theorem blockCost_eq_blockCostFast : @blockCost = @blockCostFast := rfl

end Program

end PVM
