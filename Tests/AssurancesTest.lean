import Tests.StfRunner
import Tests.ReportsJson
import JAM.Assurances

/-!
# Assurances STF vectors (`lake build assurancestest`)

Runs the assurances transition of GP v0.8.0 §11.2 (`JAM.assurances`) on every vector of
davxy/jam-test-vectors `v0.8.0` `stf/assurances/{tiny,full}`, and compares:
* the output: the newly available reports **R**, or the error (the paper names no errors; we
  compare the vectors' names);
* ρ after assurances (on an error, the state is unchanged).

The pre-state's assignments are ρ^‡, after the disputes transition. Ed25519 verification uses the
signature oracle of README note 29: every signature is rejected exactly when the vector expects
`bad_signature`.
-/

namespace JAM.Tests.Assurances

open Lean (Json)
open PVM.Tests (field natField die)
open JAM.Tests.Json
open JAM.Tests.Stf (hexS)

def errName : AssurancesError → String
  | .badAttestationParent => "bad_attestation_parent"
  | .badValidatorIndex => "bad_validator_index"
  | .coreNotEngaged => "core_not_engaged"
  | .badSignature => "bad_signature"
  | .notSortedOrUniqueAssurers => "not_sorted_or_unique_assurers"

def check (params : Params) (j : Json) : Except String (List String) := do
  let pre ← field j "pre_state"
  let post ← field j "post_state"
  let inp ← field j "input"
  let xs ← list inp "assurances" (assurance params.coreCount)
  let expErr ← expectedErr j
  let i : AssurancesInput :=
    { slot := ← natField inp "slot", parent := ← hexField inp "parent",
      activeEd := ← edKeys pre "curr_validators",
      postActiveCount := (← arr pre "post_validators").size }
  let ρ ← rho (← field pre "avail_assignments")
  let res := JAM.assurances params (sigOracle expErr) i ρ xs
  let mut diffs := []
  match res, expErr with
  | .ok (R, _), none =>
    let exp ← list (← field (← field j "output") "ok") "reported" workReport
    let got := R.map fun r => hexS r.encode
    let want := exp.map fun r => hexS r.encode
    if got != want then diffs := diffs ++ [s!"R {got} ≠ {want}"]
  | .ok _, some e => diffs := diffs ++ [s!"output ok ≠ err {e}"]
  | .error e, exp =>
    if some (errName e) != exp then diffs := diffs ++ [s!"output err {errName e} ≠ {exp}"]
  let ρ' := match res with
    | .ok (_, ρ') => ρ'
    | .error _ => ρ
  let eρ ← rho (← field post "avail_assignments")
  if showRho ρ' != showRho eρ then
    diffs := diffs ++ [s!"ρ':\n    got      {showRho ρ'}\n    expected {showRho eρ}"]
  for k in ["curr_validators", "post_validators"] do
    if (← field pre k) != (← field post k) then diffs := diffs ++ [s!"{k} changed"]
  return diffs

end JAM.Tests.Assurances

def main (args : List String) : IO UInt32 :=
  JAM.Tests.Stf.runSuite "assurancestest"
    (JAM.Tests.Stf.defaultDirs args "vendor/jam-test-vectors/stf/assurances") JAM.Tests.Assurances.check
