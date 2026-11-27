import Lean
import ErasureProofs

/-!
Fails unless every declaration of the Mathlib proofs (namespace `JAM.Erasure.Proofs`) depends only
on `propext`, `Classical.choice` and `Quot.sound` (so on no `sorryAx` and no
`Lean.ofReduceBool`/`Lean.trustCompiler`, which `native_decide` and `bv_decide` introduce). Mathlib
lemmas the proofs use are covered too: `collectAxioms` follows every constant a proof mentions.

Run from `proofs/` with `lake env lean CheckAxioms.lean`.
-/

open Lean Elab Command in
elab "#check_proofs_axioms" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let prefixes : List Name := [`JAM.Erasure.Proofs]
  let mut bad : Array String := #[]
  let mut n : Nat := 0
  for (name, _) in env.constants.toList do
    if prefixes.any (·.isPrefixOf name) && !name.isInternal then
      n := n + 1
      let axs ← Lean.collectAxioms name
      for ax in axs do
        unless allowed.contains ax do
          bad := bad.push s!"{name} depends on {ax}"
  if n == 0 then throwError "no declarations found"
  if bad.isEmpty then
    logInfo m!"checked {n} declarations: only propext, Classical.choice and Quot.sound"
  else
    throwError m!"disallowed axioms:\n{String.intercalate "\n" bad.toList}"

#check_proofs_axioms
