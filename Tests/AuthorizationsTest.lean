import Tests.StfRunner
import JAM.Authorization

/-!
# Authorizations STF vectors (`lake build authtest`)

Runs the authorization transition of GP v0.8.0 §8 (`JAM.authorizations`) on every vector of
davxy/jam-test-vectors `v0.8.0` `stf/authorizations/{tiny,full}` and compares α' and φ' with the
post-state. The vectors give, in place of E_G, each guarantee's core and authorizer hash. No
accumulation runs, so φ' = φ.
-/

namespace JAM.Tests.Authorizations

open Lean (Json)
open PVM.Tests (field natField die)
open JAM.Tests.Json
open JAM.Tests.Stf (hexS)

def hashes2 (j : Json) (k : String) : Except String (List (List (List UInt8))) := do
  let a ← arr j k
  return (← a.mapM fun c => do return (← (← c.getArr?).mapM fun h => do return (← hex h).toList).toList).toList

def check (params : Params) (j : Json) : Except String (List String) := do
  let pre ← field j "pre_state"
  let post ← field j "post_state"
  let i ← field j "input"
  let used ← (← arr i "auths").mapM fun a => do return (← natField a "core", (← hexField a "auth_hash").toList)
  let queues ← hashes2 pre "auth_queues"
  let got := authorizations params (← hashes2 pre "auth_pools") queues (← natField i "slot") used.toList
  let exp ← hashes2 post "auth_pools"
  let s (x : List (List (List UInt8))) := x.map (·.map hexS)
  let mut diffs := []
  if s got != s exp then diffs := diffs ++ [s!"α' {s got} ≠ {s exp}"]
  if s queues != s (← hashes2 post "auth_queues") then diffs := diffs ++ ["φ' differs from φ"]
  return diffs

end JAM.Tests.Authorizations

def main (args : List String) : IO UInt32 :=
  JAM.Tests.Stf.runSuite "authtest"
    (JAM.Tests.Stf.defaultDirs args "vendor/jam-test-vectors/stf/authorizations") JAM.Tests.Authorizations.check
