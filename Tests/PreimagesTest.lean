import Tests.StfRunner
import JAM.Preimages
import JAM.Statistics

/-!
# Preimages STF vectors (`lake build preimagestest`)

Runs the preimage transition of GP v0.8.0 §12.4 (`JAM.preimages`) on every vector of
davxy/jam-test-vectors `v0.8.0` `stf/preimages/{tiny,full}`, and compares:
* the output: ok, or the error (the paper does not name errors; we compare the vectors' names);
* each account's preimages and requests (on an error, the state is unchanged);
* the service statistics π_S' of §13.2 (`JAM.serviceStats`), with no reports and no accumulation.

No accumulation runs, so δ^† = δ.
-/

namespace JAM.Tests.Preimages

open Lean (Json)
open PVM.Tests (field natField die)
open JAM.Tests.Json
open JAM.Tests.Stf (hexS)

def accounts (j : Json) : Except String Accounts := do
  let as ← (← arr j "accounts").mapM fun e => do
    let d ← field e "data"
    let blobs ← (← arr d "preimage_blobs").mapM fun b => do
      return ((← hexField b "hash").toList, (← hexField b "blob").toList)
    let reqs ← (← arr d "preimage_requests").mapM fun r => do
      let k ← field r "key"
      return (((← hexField k "hash").toList, ← natField k "length"),
              (← (← arr r "value").mapM (·.getNat?)).toList)
    let a : ServiceAccount := { preimages := Std.ExtTreeMap.ofList blobs.toList,
                                requests := Std.ExtTreeMap.ofList reqs.toList, codeHash := [],
                                balance := 0, minAccGas := 0, minMemoGas := 0, gratis := 0,
                                created := 0, lastAcc := 0, parent := 0 }
    return (← natField e "id", a)
  return Std.ExtTreeMap.ofList as.toList

def showAccounts (d : Accounts) : List String :=
  d.toList.map fun (s, a) =>
    s!"{s}: preimages={a.preimages.toList.map fun (h, b) => (hexS h, hexS b)} requests={a.requests.toList.map fun ((h, l), v) => (hexS h, l, v)}"

def serviceRecord (j : Json) : Except String ServiceRecord := do
  return { provided := (← natField j "provided_count", ← natField j "provided_size"),
           refinement := (← natField j "refinement_count", ← natField j "refinement_gas_used"),
           imports := ← natField j "imports", xtCount := ← natField j "extrinsic_count",
           xtSize := ← natField j "extrinsic_size", exports := ← natField j "exports",
           accumulation := (← natField j "accumulate_count", ← natField j "accumulate_transfer_count",
                            ← natField j "accumulate_gas_used") }

def check (_ : Params) (j : Json) : Except String (List String) := do
  let pre ← field j "pre_state"
  let post ← field j "post_state"
  let i ← field j "input"
  let xs := (← (← arr i "preimages").mapM fun p => do
    return (← natField p "requester", (← hexField p "blob").toList)).toList
  let d ← accounts pre
  let res := preimages d d xs (← natField i "slot")
  let out ← field j "output"
  let mut diffs := []
  let expErr : Option String := match out.getObjVal? "err" with
    | .ok e => e.getStr?.toOption
    | .error _ => none
  let gotErr : Option String := match res with
    | .ok _ => none
    | .error .notSortedUnique => some "preimages_not_sorted_unique"
    | .error .unneeded => some "preimage_unneeded"
  if gotErr != expErr then diffs := diffs ++ [s!"output {gotErr} ≠ {expErr}"]
  let d' := match res with | .ok d' => d' | .error _ => d
  let ea ← accounts post
  if showAccounts d' != showAccounts ea then
    diffs := diffs ++ [s!"accounts:\n    got      {showAccounts d'}\n    expected {showAccounts ea}"]
  -- π_S': on an invalid extrinsic the block is invalid; the vectors keep the prior statistics.
  let stats := match res with
    | .ok _ => (serviceStats [] xs []).toList
    | .error _ => []
  let exp ← (← arr post "statistics").mapM fun e => do return (← natField e "id", ← serviceRecord (← field e "record"))
  let preStats ← arr pre "statistics"
  if !preStats.isEmpty then diffs := diffs ++ ["non-empty prior service statistics are not handled"]
  if stats != exp.toList then diffs := diffs ++ [s!"π_S' {repr stats} ≠ {repr exp.toList}"]
  return diffs

end JAM.Tests.Preimages

def main (args : List String) : IO UInt32 :=
  JAM.Tests.Stf.runSuite "preimagestest"
    (JAM.Tests.Stf.defaultDirs args "vendor/jam-test-vectors/stf/preimages") JAM.Tests.Preimages.check
