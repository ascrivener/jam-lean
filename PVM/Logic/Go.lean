import PVM.Logic.Words
import PVM.Logic.StepsH

/-!
# `pvm_go`: stepping a run through decoded code facts

`pvm_go [hs]` steps a `FreeStepsH p R i … i' …` goal one instruction at a time, using the decode
fact `d_i` the code-facts generator emits for every pc (in scope by `open`), each step's
equation closed by `pvm_simp [hs]`, until the pc is `i'`. `copy_bytes` proves that a word read
back from memory equals a source range, octet by octet through the writes.
-/

namespace PVM

/-- Octets of a word assembled from copies: `μ'.readN a n = μ.readN b n` index by index, each read
    stepping back through the writes (copies by their source, others by disjointness). -/
macro "copy_bytes" : tactic => `(tactic| (
  apply PVM.readN_congr2
  intro j hj
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  obtain h | h | h | h | h | h | h | h := this <;> subst h <;>
  (try omega) <;>
  (try simp (disch := omega) only [PVM.Memory.writeN_cons, PVM.Memory.writeN_nil, PVM.read_write_eq',
    PVM.read_write_ne']) <;>
  (try (apply PVM.read_congr_addr; omega))))

open Lean Elab Tactic Meta in
/-- `pvm_go [hs]`: step a `FreeStepsH p R i … i' …` goal one decoded instruction at a time
    (`d_i` from the code facts, each step's equation by `pvm_simp [hs]`) until the pc is `i'`,
    then close it with `FreeStepsH.refl`. -/
elab "pvm_go" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  for _ in [0:400] do
    let g ← getMainGoal
    let t ← instantiateMVars (← g.getType)
    let args := t.getAppArgs
    unless t.getAppFn.constName? == some ``PVM.FreeStepsH && args.size ≥ 12 do
      throwError "pvm_go: not a FreeStepsH goal"
    let cur ← instantiateMVars args[3]!
    let tgt ← instantiateMVars args[7]!
    if cur == tgt then
      evalTactic (← `(tactic| first | exact PVM.FreeStepsH.refl | exact PVM.FreeStepsH.refl.mono (by omega)))
      return
    let some i := (← whnfR args[3]!).nat? | throwError "pvm_go: symbolic pc {args[3]!}"
    let j? := tgt.nat?
    if j? == some i then
      evalTactic (← `(tactic| first | exact PVM.FreeStepsH.refl | exact PVM.FreeStepsH.refl.mono (by omega)))
      return
    let nm := mkIdent (Name.mkSimple s!"d_{i}")
    let pId := mkIdent `p
    let PId := mkIdent `P
    evalTactic (← `(tactic| apply PVM.FreeStepsH.step_decode ($nm (p := $pId) (P := $PId))))
    evalTactic (← `(tactic| · pvm_simp [$hs,*]))
  throwError "pvm_go: too many steps"

end PVM
