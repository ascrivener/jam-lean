import Tests.StfRunner
import JAM.Statistics

/-!
# Statistics STF vectors (`lake build statstest`)

Runs the validator-statistics update of GP v0.8.0 §13.1 (`JAM.validatorStats`) on every vector of
davxy/jam-test-vectors `v0.8.0` `stf/statistics/{tiny,full}` and compares π_V' and π_L'. These
vectors cover only the validator records; the service records' provision counts are checked by
`preimagestest`.

The reporters set G (GP eq. `guarantorsig`) is built from κ': the Ed25519 key of each credential's
validator index. The paper draws the keys from the guarantor assignments M or M*, which need
entropy and λ' that the vector state does not carry; the vectors' guarantees are placeholders
(README "Extrinsic Semantic Validity").
-/

namespace JAM.Tests.Statistics

open Lean (Json)
open PVM.Tests (field natField die)
open JAM.Tests.Json

def record (j : Json) : Except String ValidatorRecord := do
  return { blocks := ← natField j "blocks", tickets := ← natField j "tickets",
           preimages := ← natField j "pre_images", preimagesSize := ← natField j "pre_images_size",
           guarantees := ← natField j "guarantees", assurances := ← natField j "assurances" }

def records (j : Json) (k : String) : Except String (List ValidatorRecord) := do
  return (← (← arr j k).mapM record).toList

def check (params : Params) (j : Json) : Except String (List String) := do
  let pre ← field j "pre_state"
  let post ← field j "post_state"
  let i ← field j "input"
  let x ← field i "extrinsic"
  let ed := (← (← arr pre "curr_validators").mapM fun v => do return (← hexField v "ed25519").toList).toList
  let preimages ← (← arr x "preimages").mapM fun p => do return (← natField p "requester", (← hexField p "blob").toList)
  let reporters ← (← arr x "guarantees").mapM fun g => do
    (← arr g "signatures").mapM fun s => do return ed.getD (← natField s "validator_index") []
  let input : ValidatorStatsInput :=
    { priorSlot := ← natField pre "slot", slot := ← natField i "slot", author := ← natField i "author_index",
      ticketCount := (← arr x "tickets").size, preimages := preimages.toList,
      assurers := (← (← arr x "assurances").mapM fun a => natField a "validator_index").toList,
      activeEd := ed, reporters := Std.ExtTreeSet.ofList (reporters.toList.flatMap (·.toList)) }
  let (curr, last) := validatorStats params (← records pre "vals_curr_stats") (← records pre "vals_last_stats") input
  let mut diffs := []
  let ec ← records post "vals_curr_stats"
  let el ← records post "vals_last_stats"
  if curr != ec then diffs := diffs ++ [s!"π_V':\n    got      {repr curr}\n    expected {repr ec}"]
  if last != el then diffs := diffs ++ [s!"π_L':\n    got      {repr last}\n    expected {repr el}"]
  return diffs

end JAM.Tests.Statistics

def main (args : List String) : IO UInt32 :=
  JAM.Tests.Stf.runSuite "statstest"
    (JAM.Tests.Stf.defaultDirs args "vendor/jam-test-vectors/stf/statistics") JAM.Tests.Statistics.check
