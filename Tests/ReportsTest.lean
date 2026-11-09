import Tests.StfRunner
import Tests.ReportsJson
import JAM.Reports
import JAM.Statistics

/-!
# Reports (guarantees) STF vectors (`lake build reportstest`)

Runs the guarantees transition of GP v0.8.0 §11.3–§11.5 (`JAM.guarantees`) on every vector of
davxy/jam-test-vectors `v0.8.0` `stf/reports/{tiny,full}`, and compares:
* the output: the reported packages and the reporters G, or the error (the paper names no
  errors; we compare the vectors' names);
* ρ' (on an error, the state is unchanged);
* the core statistics π_C' and service statistics π_S' of §13.2 (`JAM.coreStats`,
  `JAM.serviceStats`) from the incoming reports, with no available reports, no assurances, no
  preimages and no accumulation. The vectors' prior statistics are all zero.

The vectors' state carries what the transition reads:
* `recent_blocks` is taken as β_H^†;
* `known_packages` is the pipeline's package set (`JAM.knownPackages`);
* the vectors carry no ancestor set, so the ancestry condition on lookup anchors is taken to
  hold.

Ed25519 verification uses the signature oracle of README note 29: every signature is rejected
exactly when the vector expects `bad_signature`.
-/

namespace JAM.Tests.Reports

open Lean (Json)
open PVM.Tests (field natField die)
open JAM.Tests.Json
open JAM.Tests.Stf (hexS)

def errName : ReportsError → String
  | .badCoreIndex => "bad_core_index"
  | .futureReportSlot => "future_report_slot"
  | .reportEpochBeforeLast => "report_epoch_before_last"
  | .insufficientGuarantees => "insufficient_guarantees"
  | .outOfOrderGuarantee => "out_of_order_guarantee"
  | .notSortedOrUniqueGuarantors => "not_sorted_or_unique_guarantors"
  | .wrongAssignment => "wrong_assignment"
  | .coreEngaged => "core_engaged"
  | .anchorNotRecent => "anchor_not_recent"
  | .badServiceId => "bad_service_id"
  | .badCodeHash => "bad_code_hash"
  | .dependencyMissing => "dependency_missing"
  | .duplicatePackage => "duplicate_package"
  | .badStateRoot => "bad_state_root"
  | .badBeefyMmrRoot => "bad_beefy_mmr_root"
  | .coreUnauthorized => "core_unauthorized"
  | .badValidatorIndex => "bad_validator_index"
  | .workReportGasTooHigh => "work_report_gas_too_high"
  | .serviceItemGasTooLow => "service_item_gas_too_low"
  | .tooManyDependencies => "too_many_dependencies"
  | .segmentRootLookupInvalid => "segment_root_lookup_invalid"
  | .badSignature => "bad_signature"
  | .workReportTooBig => "work_report_too_big"
  | .bannedValidator => "banned_validator"
  | .lookupAnchorNotRecent => "lookup_anchor_not_recent"
  | .missingWorkResults => "missing_work_results"
  | .badAnchorSlot => "bad_anchor_slot"
  | .badErasureShards => "bad_erasure_shards"

def recentBlock (j : Json) : Except String RecentBlock := do
  let rep ← list j "reported" fun e => do
    return ((← hexField e "hash").toList, (← hexField e "exports_root").toList)
  return { headerHash := (← hexField j "header_hash").toList, stateRoot := (← hexField j "state_root").toList,
           accRoot := (← hexField j "beefy_root").toList, slot := ← natField j "slot",
           reported := Std.ExtTreeMap.ofList rep }

def accounts (j : Json) : Except String Accounts := do
  let as ← list j "accounts" fun e => do
    let s ← field (← field e "data") "service"
    let a : ServiceAccount := { codeHash := (← hexField s "code_hash").toList, balance := ← natField s "balance",
                                minAccGas := ← natField s "min_item_gas", minMemoGas := ← natField s "min_memo_gas" }
    return (← natField e "id", a)
  return Std.ExtTreeMap.ofList as

def coreRecord (j : Json) : Except String CoreRecord := do
  return { daLoad := ← natField j "da_load", popularity := ← natField j "popularity",
           imports := ← natField j "imports", xtCount := ← natField j "extrinsic_count",
           xtSize := ← natField j "extrinsic_size", exports := ← natField j "exports",
           bundleLen := ← natField j "bundle_size", gasUsed := ← natField j "gas_used" }

def serviceRecord (j : Json) : Except String ServiceRecord := do
  return { provided := (← natField j "provided_count", ← natField j "provided_size"),
           refinement := (← natField j "refinement_count", ← natField j "refinement_gas_used"),
           imports := ← natField j "imports", xtCount := ← natField j "extrinsic_count",
           xtSize := ← natField j "extrinsic_size", exports := ← natField j "exports",
           accumulation := (← natField j "accumulate_count", ← natField j "accumulate_transfer_count",
                            ← natField j "accumulate_gas_used") }

def check (params : Params) (j : Json) : Except String (List String) := do
  let pre ← field j "pre_state"
  let post ← field j "post_state"
  let inp ← field j "input"
  let xs ← list inp "guarantees" guarantee
  let expErr ← expectedErr j
  let η ← list pre "entropy" hex
  let i : ReportsInput :=
    { slot := ← natField inp "slot", activeEd := ← edKeys pre "curr_validators",
      previousEd := ← edKeys pre "prev_validators", entropy2 := η.getD 2 .empty,
      entropy3 := η.getD 3 .empty,
      offenders := Std.ExtTreeSet.ofList ((← list pre "offenders" hex).map (·.toList)),
      recent := ← list (← field pre "recent_blocks") "history" recentBlock,
      authPools := ← list pre "auth_pools" fun p => do return (← items p hex).map (·.toList),
      known := Std.ExtTreeSet.ofList ((← list inp "known_packages" hex).map (·.toList)),
      lookupAnchorKnown := fun _ => true }
  let ρ ← rho (← field pre "avail_assignments")
  let res := JAM.guarantees params (sigOracle expErr) i (← accounts pre) ρ xs
  let mut diffs := []
  match res, expErr with
  | .ok o, none =>
    let out ← field (← field j "output") "ok"
    let rep ← list out "reported" fun e => do
      return (hexS (← hexField e "work_package_hash").toList, hexS (← hexField e "segment_tree_root").toList)
    let got := o.reported.toList.map fun (k, v) => (hexS k, hexS v)
    if got != rep then diffs := diffs ++ [s!"reported {got} ≠ {rep}"]
    let reps ← list out "reporters" fun e => do return hexS (← hex e).toList
    let gotR := o.reporters.toList.map hexS
    if gotR != reps then diffs := diffs ++ [s!"reporters {gotR} ≠ {reps}"]
  | .ok _, some e => diffs := diffs ++ [s!"output ok ≠ err {e}"]
  | .error e, exp =>
    if some (errName e) != exp then diffs := diffs ++ [s!"output err {errName e} ≠ {exp}"]
  let ρ' := match res with
    | .ok o => o.assignments
    | .error _ => ρ
  let eρ ← rho (← field post "avail_assignments")
  if showRho ρ' != showRho eρ then
    diffs := diffs ++ [s!"ρ':\n    got      {showRho ρ'}\n    expected {showRho eρ}"]
  -- π_C' and π_S' (GP §13.2) from the incoming reports; on an error, the prior statistics.
  let preC ← list pre "cores_statistics" coreRecord
  let preS ← list pre "services_statistics" fun e => do return (← natField e "id", ← serviceRecord (← field e "record"))
  if preC.any (· != {}) || !preS.isEmpty then diffs := diffs ++ ["non-zero prior statistics are not handled"]
  let (cs, ss) := match res with
    | .ok _ => (coreStats params (xs.map (·.report)) [] [], (serviceStats (xs.map (·.report)) [] []).toList)
    | .error _ => (preC, preS)
  let eC ← list post "cores_statistics" coreRecord
  let eS ← list post "services_statistics" fun e => do return (← natField e "id", ← serviceRecord (← field e "record"))
  if cs != eC then diffs := diffs ++ [s!"π_C' {repr cs} ≠ {repr eC}"]
  if ss != eS then diffs := diffs ++ [s!"π_S' {repr ss} ≠ {repr eS}"]
  for k in ["curr_validators", "prev_validators", "entropy", "offenders", "recent_blocks", "auth_pools", "accounts"] do
    if (← field pre k) != (← field post k) then diffs := diffs ++ [s!"{k} changed"]
  return diffs

end JAM.Tests.Reports

def main (args : List String) : IO UInt32 :=
  JAM.Tests.Stf.runSuite "reportstest"
    (JAM.Tests.Stf.defaultDirs args "vendor/jam-test-vectors/stf/reports") JAM.Tests.Reports.check
