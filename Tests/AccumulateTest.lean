import Tests.JamJson

/-!
# Accumulate STF vectors (`lake build acctest`)

Runs the accumulation state transition of GP v0.8.0 §12 (`JAM.accumulate`) on each vector of
davxy/jam-test-vectors `v0.8.0` `stf/accumulate/tiny`, and compares:
* the output (the Keccak Merkle root of the accumulation outputs);
* the ready queue and the accumulated history;
* the privileges;
* the accumulation statistics (N, T, G) per service;
* every service account: metadata (including the derived footprint terms), storage, preimages and
  requests.

The vector state carries no staging set or authorizer queue, which accumulation can also change;
we start them empty and do not compare them.
-/

namespace JAM.Tests.Accumulate

open Lean (Json)
open PVM.Tests (field natField die readJson)
open JAM.Tests.Json

def arrF (j : Json) (k : String) : Except String (Array Json) := do (← field j k).getArr?

def account (j : Json) : Except String ServiceAccount := do
  let s ← field j "service"
  let storage ← (← arrF j "storage").mapM fun e => do
    return ((← hexField e "key").toList, (← hexField e "value").toList)
  let preimages ← (← arrF j "preimage_blobs").mapM fun e => do
    return ((← hexField e "hash").toList, (← hexField e "blob").toList)
  let requests ← (← arrF j "preimage_requests").mapM fun e => do
    let k ← field e "key"
    let v ← (← field e "value").getArr?
    return (((← hexField k "hash").toList, ← natField k "length"), (← v.mapM (·.getNat?)).toList)
  return { storage := Std.ExtTreeMap.ofList storage.toList, preimages := Std.ExtTreeMap.ofList preimages.toList,
           requests := Std.ExtTreeMap.ofList requests.toList, gratis := ← natField s "deposit_offset",
           codeHash := (← hexField s "code_hash").toList, balance := ← natField s "balance",
           minAccGas := ← natField s "min_item_gas", minMemoGas := ← natField s "min_memo_gas",
           created := ← natField s "creation_slot", lastAcc := ← natField s "last_accumulation_slot",
           parent := ← natField s "parent_service" }

def state (params : Params) (j : Json) : Except String AccState := do
  let accounts ← (← arrF j "accounts").mapM fun e => do return (← natField e "id", ← account (← field e "data"))
  let p ← field j "privileges"
  let always ← (← arrF p "always_acc").mapM fun e => do return (← natField e "id", ← natField e "gas")
  let ready ← (← arrF j "ready_queue").mapM fun slotQ => do
    (← slotQ.getArr?).mapM fun e => do
      let deps ← (← arrF e "dependencies").mapM fun h => do return (← hex h).toList
      return ((← workReport (← field e "report")), deps.toList)
  let accumulated ← (← arrF j "accumulated").mapM fun slotA => do
    (← slotA.getArr?).mapM fun h => do return (← hex h).toList
  let assigners ← (← arrF p "assign").mapM (·.getNat?)
  return { slot := ← natField j "slot", entropy := (← hexField j "entropy").toList,
           ready := (ready.map (·.toList)).toList, accumulated := (accumulated.map (·.toList)).toList,
           pstate := { accounts := Std.ExtTreeMap.ofList accounts.toList, staging := [],
                       authQueue := List.replicate params.coreCount (List.replicate params.authQueueSize (List.replicate 32 0)),
                       manager := ← natField p "bless", assigners := assigners.toList,
                       delegator := ← natField p "designate", registrar := ← natField p "register",
                       alwaysAcc := Std.ExtTreeMap.ofList always.toList } }

def hexS (b : List UInt8) : String :=
  String.join (b.map fun x => let d := "0123456789abcdef".toList; String.ofList [d[x.toNat / 16]!, d[x.toNat % 16]!])

/-- A comparable rendering of an account, including the derived footprint terms. -/
def showAccount (a : ServiceAccount) : String :=
  s!"code={hexS a.codeHash} bal={a.balance} g={a.minAccGas} m={a.minMemoGas} o={a.octets} i={a.items} f={a.gratis} r={a.created} a={a.lastAcc} p={a.parent} " ++
  s!"storage={a.storage.toList.map fun (k, v) => (hexS k, hexS v)} preimages={a.preimages.toList.map fun (k, v) => (hexS k, v.length)} " ++
  s!"requests={a.requests.toList.map fun ((h, l), v) => (hexS h, l, v)}"

/-- Compare the computed post-state with the vector; the first differences found. -/
def compare (params : Params) (j : Json) (res : AccResult) : Except String (List String) := do
  let post ← state params (← field j "post_state")
  let mut diffs : List String := []
  let out ← field j "output"
  if let .ok h := hexField out "ok" then
    if h.toList != res.root then diffs := diffs ++ [s!"output root {hexS res.root} ≠ {hexS h.toList}"]
  let got := res.state
  let rq (q : List (List ReadyEntry)) := q.map fun l => l.map fun (w, d) => (hexS w.pkg, d.map hexS)
  if rq got.ready != rq post.ready then diffs := diffs ++ ["ready queue differs"]
  if (got.accumulated.map (·.map hexS)) != (post.accumulated.map (·.map hexS)) then
    diffs := diffs ++ ["accumulated history differs"]
  let pr (e : PartialState) := (e.manager, e.assigners, e.delegator, e.registrar, e.alwaysAcc.toList)
  if pr got.pstate != pr post.pstate then diffs := diffs ++ [s!"privileges {repr (pr got.pstate)} ≠ {repr (pr post.pstate)}"]
  -- statistics
  let expStats ← (← arrF (← field j "post_state") "statistics").mapM fun e => do
    let r ← field e "record"
    return (← natField e "id", ← natField r "accumulate_count", ← natField r "accumulate_transfer_count",
            ← natField r "accumulate_gas_used")
  let gotStats := res.stats.map fun (s, n, t, g) => (s, n, t, g)
  if gotStats != expStats.toList then diffs := diffs ++ [s!"statistics {gotStats} ≠ {expStats.toList}"]
  -- accounts
  let gk := got.pstate.accounts.keys
  let ek := post.pstate.accounts.keys
  if gk != ek then diffs := diffs ++ [s!"account ids {gk} ≠ {ek}"]
  for k in ek do
    match got.pstate.accounts.get? k, post.pstate.accounts.get? k with
    | some a, some b =>
      if showAccount a != showAccount b then
        diffs := diffs ++ [s!"account {k}:\n    got      {showAccount a}\n    expected {showAccount b}"]
    | _, _ => pure ()
  return diffs

def runVector (params : Params) (j : Json) : Except String (List String) := do
  let pre ← state params (← field j "pre_state")
  let input ← field j "input"
  let reports ← (← arrF input "reports").mapM workReport
  let res := accumulate params pre (← natField input "slot") reports.toList
  compare params j res

end JAM.Tests.Accumulate

open JAM.Tests.Accumulate in
def main (args : List String) : IO UInt32 := do
  let dir := args.headD "vendor/jam-test-vectors/stf/accumulate/tiny"
  let files ← PVM.Tests.jsonFiles dir
  let mut pass := 0
  let mut failed : Array String := #[]
  for f in files do
    let name := f.fileName.getD ""
    match runVector JAM.Params.tiny (← PVM.Tests.readJson f) with
    | .ok [] => pass := pass + 1
    | .ok diffs =>
      failed := failed.push name
      IO.eprintln s!"FAIL {name}:"
      for d in diffs.take 4 do IO.eprintln s!"  {d.take 1500}"
    | .error e =>
      failed := failed.push name
      IO.eprintln s!"ERROR {name}: {e}"
  IO.println s!"acctest: {pass} of {files.size} accumulate vectors pass"
  return if failed.isEmpty then 0 else 1
