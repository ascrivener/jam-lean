import Tests.StfRunner
import JAM.History

/-!
# Recent-history STF vectors (`lake build historytest`)

Runs the recent-history transition of GP v0.8.0 §7 (`JAM.recentHistory`) on every vector of
davxy/jam-test-vectors `v0.8.0` `stf/history/{tiny,full}` and compares β' (β_H and the belt
β_B) with the post-state. The vectors give the accumulation-output root ℳ_B(**s**, ℋ_K) directly
as `accumulate_root`.
-/

namespace JAM.Tests.History

open Lean (Json)
open PVM.Tests (field natField die)
open JAM.Tests.Json
open JAM.Tests.Stf (hexS)

def reported (j : Json) : Except String (List (List UInt8 × List UInt8)) := do
  let a ← j.getArr?
  return (← a.mapM fun e => do return ((← hexField e "hash").toList, (← hexField e "exports_root").toList)).toList

def block (j : Json) : Except String RecentBlock := do
  return { headerHash := (← hexField j "header_hash").toList, stateRoot := (← hexField j "state_root").toList,
           accRoot := (← hexField j "beefy_root").toList, slot := ← natField j "slot",
           reported := Std.ExtTreeMap.ofList (← reported (← field j "reported")) }

def recent (j : Json) : Except String Recent := do
  let b ← field j "beta"
  let peaks ← (← field (← field b "mmr") "peaks").getArr?
  let belt ← peaks.mapM fun p => match p with
    | .null => pure none
    | p => do return some (← hex p).toList
  return { history := (← (← arr b "history").mapM block).toList, belt := belt.toList }

def showBlock (b : RecentBlock) : String :=
  s!"h={hexS b.headerHash} s={hexS b.stateRoot} b={hexS b.accRoot} t={b.slot} p={b.reported.toList.map fun (k, v) => (hexS k, hexS v)}"

def check (params : Params) (j : Json) : Except String (List String) := do
  let pre ← recent (← field j "pre_state")
  let post ← recent (← field j "post_state")
  let i ← field j "input"
  let input : HistoryInput :=
    { headerHash := (← hexField i "header_hash").toList, parentStateRoot := (← hexField i "parent_state_root").toList,
      accRoot := (← hexField i "accumulate_root").toList, slot := ← natField i "slot",
      reported := ← reported (← field i "work_packages") }
  let got := recentHistory params pre input
  let mut diffs := []
  let gh := got.history.map showBlock
  let eh := post.history.map showBlock
  if gh != eh then diffs := diffs ++ [s!"β_H:\n    got      {gh}\n    expected {eh}"]
  let sb (m : MMR) := m.map (·.map hexS)
  if sb got.belt != sb post.belt then diffs := diffs ++ [s!"β_B {sb got.belt} ≠ {sb post.belt}"]
  return diffs

end JAM.Tests.History

def main (args : List String) : IO UInt32 :=
  JAM.Tests.Stf.runSuite "historytest"
    (JAM.Tests.Stf.defaultDirs args "vendor/jam-test-vectors/stf/history") JAM.Tests.History.check
