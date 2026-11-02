import Lean
import PVM
import JAM

/-!
Fails unless every declaration in the `PVM` and `JAM` namespaces depends only on `propext`,
`Classical.choice` and `Quot.sound` (so in particular on no `sorryAx` and no
`Lean.ofReduceBool`/`Lean.trustCompiler`, which `native_decide` and `bv_decide` introduce).

Run with `lake env lean scripts/CheckAxioms.lean`.
-/

open Lean Elab Command in
elab "#check_pvm_axioms" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : Array String := #[]
  let mut n : Nat := 0
  for (name, _) in env.constants.toList do
    if ((`PVM).isPrefixOf name || (`JAM).isPrefixOf name) && !name.isInternal then
      n := n + 1
      let axs ← Lean.collectAxioms name
      for ax in axs do
        unless allowed.contains ax do
          bad := bad.push s!"{name} depends on {ax}"
  if bad.isEmpty then
    logInfo m!"checked {n} declarations: only propext, Classical.choice and Quot.sound"
  else
    throwError m!"disallowed axioms:\n{String.intercalate "\n" bad.toList}"

#check_pvm_axioms
