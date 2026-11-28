import Tests.Examples.Basic
import Tests.HistoryHarness
import Tests.AuthorizationsHarness
import Tests.DisputesHarness
import Tests.AssurancesHarness
import Tests.ReportsHarness
import Tests.PreimagesHarness
import Tests.StatisticsHarness

/-!
# Worked examples: the block-level transitions of §7, §8, §10, §11, §12.4 and §13

Each generator runs one davxy/jam-test-vectors vector through its suite's own `check` (the
harnesses `Tests.*Harness`, as `lake build historytest` and the other suites do) and stops unless
it passes, then runs the model function on the same input and fills the box from the model's
result. Its list `stf` is registered in `Tests/Examples.lean`.
-/

namespace JAM.Tests.Examples

open Lean (Json)
open PVM.Tests (field natField readJson)
open JAM.Tests.Json

/-- A vector of `stf/<suite>/tiny`, read and checked with the suite's comparison `check` on the
    tiny chain; fails unless the model's result matches the vector. -/
def runStf (suite file : String) (check : Params → Json → Except String (List String)) : IO Json := do
  let j ← readJson (System.FilePath.mk "vendor/jam-test-vectors/stf" / suite / "tiny" / file)
  match check JAM.V080.tiny080 j with
  | .ok [] => return j
  | .ok diffs => throw <| IO.userError s!"examples: {suite}/{file}: the model disagrees with the vector: {diffs}"
  | .error e => throw <| IO.userError s!"examples: {suite}/{file}: cannot run the vector: {e}"

/-- An `Except String` read of the vector, as an `IO` action. -/
def readV {α} (file : String) (x : Except String α) : IO α :=
  match x with
  | .ok a => pure a
  | .error e => throw <| IO.userError s!"examples: {file}: cannot read the vector: {e}"

def stfCheck (suite : String) : String :=
  s!"The model's result equals the vector's expected output, compared as `lake build {suite}` \
    compares every vector of the suite; the generator repeats that comparison for this one."

/-- `before → after`, or the one value when it did not change. -/
def arrow {α} [BEq α] [ToString α] (a b : α) : String :=
  if a == b then toString a else s!"{a} → {b}"

def isZero (b : List UInt8) : Bool := !b.isEmpty && b.all (· == 0)

/-- A belt or mountain range: its slots in order, $\varnothing$ for an empty one. -/
def showMMR (m : MMR) : String :=
  "[" ++ ", ".intercalate (m.map fun | none => "$\\varnothing$" | some h => abbr h) ++ "]"

/-! ## §7 Recent history -/

def historyExample : IO Example := do
  let file := "progress_blocks_history-3.json"
  let j ← runStf "history" file JAM.Tests.History.check
  let params := JAM.V080.tiny080
  let (pre, input) ← readV file do
    let pre ← JAM.Tests.History.recent (← field j "pre_state")
    let i ← field j "input"
    let input : HistoryInput :=
      { headerHash := (← hexField i "header_hash").toList, parentStateRoot := (← hexField i "parent_state_root").toList,
        accRoot := (← hexField i "accumulate_root").toList, slot := ← natField i "slot",
        reported := ← JAM.Tests.History.reported (← field i "work_packages") }
    return (pre, input)
  let post := recentHistory params pre input
  let some last := pre.history.getLast? | throw <| IO.userError "examples: empty history"
  let some last' := post.history.find? (·.headerHash == last.headerHash)
    | throw <| IO.userError "examples: the parent's entry is not kept"
  let some entry := post.history.getLast? | throw <| IO.userError "examples: no new entry"
  let filled := (pre.belt.takeWhile Option.isSome).length
  let carried := filled == pre.belt.length && post.belt.length == filled + 1 &&
    (post.belt.take filled).all Option.isNone
  return {
    name := "history-append", title := "A block appended to recent history",
    source := jamSource s!"stf/history/tiny/{file}", params := tinyParams params ++ s!", $\\mathsf\{H}$ = {params.recentHistoryLen}",
    summary := s!"The block at slot {input.slot} is added to $\\beta_H$. First the previous entry's state root, \
      recorded as $\\zerohash$, is set to the parent state root $\\mathbf\{H}_R$ from the new header. Then \
      the block's accumulation root is appended to the belt $\\beta_B$, and the new entry records the belt's super-peak.",
    inputs := [
      { label := "Slot $\\mathbf{H}_T$", value := toString input.slot },
      { label := "Header hash $\\mathcal{H}(\\mathbf{H})$", value := abbr input.headerHash },
      { label := "Parent state root $\\mathbf{H}_R$", value := abbr input.parentStateRoot },
      { label := "Accumulation root $\\mathcal{M}_B(\\mathbf{s}, \\mathcal{H}_K)$", value := abbr input.accRoot },
      { label := "Guaranteed packages", value := toString input.reported.length }],
    columns := ["", "Before ($\\beta$)", "After ($\\beta'$)"],
    rows := [
      { label := "Entries in $\\beta_H$", cells := [toString pre.history.length, toString post.history.length] },
      { label := s!"State root of the slot-{last.slot} entry",
        cells := [abbr last.stateRoot ++ (if isZero last.stateRoot then " ($\\zerohash$)" else ""),
                  abbr last'.stateRoot ++ (if last'.stateRoot == input.parentStateRoot then " (= $\\mathbf{H}_R$)" else "")] },
      { label := "Belt $\\beta_B$", cells := [showMMR pre.belt, showMMR post.belt] },
      { label := "New entry: header hash $h$", cells := ["", abbr entry.headerHash] },
      { label := "New entry: state root $s$",
        cells := ["", abbr entry.stateRoot ++ (if isZero entry.stateRoot then " ($\\zerohash$)" else "")] },
      { label := "New entry: accumulation super-peak $b$",
        cells := ["", abbr entry.accRoot ++ (if entry.accRoot == MMR.superPeak post.belt then " (= $\\mathcal{M}_R(\\beta'_B)$)" else "")] },
      { label := "New entry: reported packages $\\mathbf{p}$", cells := ["", count entry.reported.size "package" "packages"] }],
    notes := (if carried then
      [s!"The belt's {filled} slots were all filled, so appending carries like adding 1 in binary (eq. E.8): \
        each filled slot is hashed with the value coming up and emptied, and the result lands in a new slot {filled}." ++
        (if (post.belt.filter Option.isSome).length == 1 then
          " With one peak left, the super-peak $\\mathcal{M}_R$ is that peak itself (eq. E.10)." else "")]
      else []),
    model := ["JAM.recentHistory", "JAM.Recent.withParentRoot", "JAM.MMR.append", "JAM.MMR.superPeak"],
    equations := ["7.5", "7.6", "7.7", "7.8", "E.8", "E.10"],
    check := stfCheck "historytest" }

/-! ## §8 Authorization -/

def authExample : IO Example := do
  let file := "progress_authorizations-3.json"
  let j ← runStf "authorizations" file JAM.Tests.Authorizations.check
  let params := JAM.V080.tiny080
  let (pools, queues, slot, used) ← readV file do
    let pre ← field j "pre_state"
    let i ← field j "input"
    let used ← (← arr i "auths").mapM fun a => do return (← natField a "core", (← hexField a "auth_hash").toList)
    return (← JAM.Tests.Authorizations.hashes2 pre "auth_pools", ← JAM.Tests.Authorizations.hashes2 pre "auth_queues",
      ← natField i "slot", used.toList)
  let post := authorizations params pools queues slot used
  let cores := List.range params.coreCount
  let cell (f : Nat → String) : List String := cores.map f
  let pool (c : Nat) := pools.getD c []
  let pool' (c : Nat) := post.getD c []
  let queue (c : Nat) := queues.getD c []
  let position (xs : List (List UInt8)) (h : List UInt8) : String :=
    match xs.findIdx? (· == h) with
    | some i => s!" (position {i})"
    | none => " (not in the pool)"
  let usedCell (c : Nat) : String :=
    match used.find? (·.1 == c) with
    | some (_, a) => abbr a ++ position (pool c) a
    | none => "none"
  let nextCell (c : Nat) : String :=
    let q := queue c
    if q.isEmpty then "none" else
      let k := slot % q.length
      s!"{abbr (q.getD k [])}, entry {k} = {slot} mod {q.length}" ++
        (if (pool' c).getLast? == some (q.getD k []) then " (now last)" else "")
  let droppedCell (c : Nat) : String :=
    let p := poolUsed (pool c) c used ++ (if (queue c).isEmpty then [] else [(queue c).getD (slot % (queue c).length) []])
    let d := p.take (p.length - params.authPoolSize)
    if d.isEmpty then "nothing" else ", ".intercalate (d.map abbr)
  return {
    name := "authorization-pools", title := "Authorizer pools after a block",
    source := jamSource s!"stf/authorizations/tiny/{file}",
    params := tinyParams params ++ s!", $\\mathsf\{O}$ = {params.authPoolSize}, $\\mathsf\{Q}$ = {params.authQueueSize}",
    summary := s!"The block at slot {slot} has {count used.length "guarantee" "guarantees"}, on core \
      {" and ".intercalate (used.map (toString ·.1))}. That core drops the authorizer its guarantee used. Every core \
      then appends its queue's entry for slot {slot}, and a pool that would exceed \
      $\\mathsf\{O}$ = {params.authPoolSize} loses its oldest entry.",
    inputs := [
      { label := "Slot $\\mathbf{H}_T$", value := toString slot },
      { label := "Guarantees $((g_\\mathbf{r})_c, (g_\\mathbf{r})_a)$",
        value := if used.isEmpty then "none" else ", ".intercalate (used.map fun (c, a) => s!"core {c}: {abbr a}") }],
    columns := [""] ++ cores.map (s!"Core {·}"),
    rows := [
      { label := "Pool size $|\\alpha[c]|$", cells := cell fun c => arrow (pool c).length (pool' c).length },
      { label := "Used by a guarantee, removed: $F(c)$", cells := cell usedCell },
      { label := "Appended from the queue $\\phi'[c][\\mathbf{H}_T]^{\\circlearrowleft}$", cells := cell nextCell },
      { label := s!"Dropped to keep the last $\\mathsf\{O}$", cells := cell droppedCell },
      { label := "First in the pool", cells := cell fun c => s!"{abbr ((pool c).headD [])} → {abbr ((pool' c).headD [])}" },
      { label := "Last in the pool", cells := cell fun c => s!"{abbr ((pool c).getLastD [])} → {abbr ((pool' c).getLastD [])}" }],
    notes := ["No accumulation runs in these vectors, so the queue $\\phi'$ is the prior queue $\\phi$."],
    model := ["JAM.authorizations", "JAM.poolNext", "JAM.poolUsed"],
    equations := ["8.2", "8.3"],
    check := stfCheck "authtest" }

/-! ## §10 Disputes -/

def outcomeName : Outcome → String
  | .good => "good"
  | .bad => "bad"
  | .wonky => "wonky"

def disputesExample : IO Example := do
  let file := "progress_invalidates_avail_assignments-1.json"
  let j ← runStf "disputes" file JAM.Tests.Disputes.check
  let params := JAM.V080.tiny080
  let (i, ψ, ρ, x) ← readV file do
    let pre ← field j "pre_state"
    let x ← JAM.Tests.Json.disputes (← field (← field j "input") "disputes")
    let i : DisputesInput :=
      { slot := ← natField pre "tau", activeEd := ← edKeys pre "kappa", previousEd := ← edKeys pre "lambda" }
    return (i, ← JAM.Tests.Disputes.psi (← field pre "psi"), ← rho (← field pre "rho"), x)
  let .ok o := JAM.disputesTransition params (sigOracle none) i ψ ρ x
    | throw <| IO.userError s!"examples: {file}: the model rejects the extrinsic"
  let ψ' := o.state
  let named (r : List UInt8) : String :=
    abbr r ++ (if ψ'.good.contains r then " (good)" else if ψ'.bad.contains r then " (bad)"
      else if ψ'.wonky.contains r then " (wonky)" else "")
  let verdictRow (v : Verdict) : Row :=
    let k := (judgeKeys params i v.age).length
    let yes := (v.votes.filter (·.valid)).length
    { label := s!"Verdict on report {abbr v.target.toList}",
      cells := ["", (match verdictOutcome k v.votes with
                     | some oc => outcomeName oc
                     | none => "undefined") ++ s!": {yes} of {v.votes.length} judgments say valid ({k} judges)"] }
  let set (s : OctetSet) : String :=
    if s.isEmpty then "empty" else ", ".intercalate (s.toList.map abbr)
  let reportHash (a : AvailAssignment) : List UInt8 :=
    (Blake2b.hash256 ⟨a.guarantee.report.encode.toArray⟩).toList
  let rhoCell (e : Option AvailAssignment) : String :=
    match e with
    | none => "empty"
    | some a => s!"report {named (reportHash a)}, since slot {a.time}"
  let rhoRows := (List.range ρ.length).map fun c =>
    { label := s!"Core {c}: pending report $\\rho[{c}]$",
      cells := [rhoCell (ρ.getD c none), rhoCell (o.assignments.getD c none)] : Row }
  return {
    name := "disputes-verdicts", title := "Two verdicts: a bad report's core is cleared",
    source := jamSource s!"stf/disputes/tiny/{file}", params := tinyParams params,
    summary := "The extrinsic brings one verdict that a report is good and one that another is bad. The \
      bad report is pending availability on a core, so that core is cleared and the report will not \
      be accumulated. The guarantors of the bad report (culprits) and a validator who judged the good \
      report invalid (a fault) become offenders.",
    inputs := [
      { label := "Prior timeslot $\\tau$", value := s!"{i.slot} (epoch {i.slot / params.epochLen})" },
      { label := "Verdicts $\\mathbf{v}$", value := toString x.verdicts.length },
      { label := "Culprits $\\mathbf{c}$", value := toString x.culprits.length },
      { label := "Faults $\\mathbf{f}$",
        value := ", ".intercalate (x.faults.map fun f =>
          s!"key {abbr f.key.toList} says report {named f.target.toList} is {if f.valid then "valid" else "invalid"}") }],
    columns := ["", "Before", "After"],
    rows := x.verdicts.map verdictRow ++ rhoRows ++ [
      { label := "Good reports $\\psi_G$", cells := [set ψ.good, set ψ'.good] },
      { label := "Bad reports $\\psi_B$", cells := [set ψ.bad, set ψ'.bad] },
      { label := "Wonky reports $\\psi_W$", cells := [set ψ.wonky, set ψ'.wonky] },
      { label := "Offenders $\\psi_O$", cells := [set ψ.offenders, set ψ'.offenders] },
      { label := "Offenders marker $\\mathbf{H}_O$", cells := ["", ", ".intercalate (o.offendersMark.map abbr)] }],
    notes := [s!"A verdict needs $\\lfloor 2/3 \\cdot {(judgeKeys params i 0).length} \\rfloor + 1$ = \
      {2 * (judgeKeys params i 0).length / 3 + 1} judgments. All valid makes it good, none valid bad. \
      The report of a pending core is matched by the hash of its encoding."],
    model := ["JAM.disputesTransition", "JAM.verdictOutcome", "JAM.clearNonPositive", "JAM.assimilate"],
    equations := ["10.12", "10.13", "10.14", "10.15", "10.16", "10.17", "10.18", "10.19"],
    check := stfCheck "disputestest" ++ " Signatures are checked by the suite's oracle, which accepts \
      them all for this vector." }

/-! ## §11 Assurances and guarantees -/

def assurancesExample : IO Example := do
  let file := "some_assurances-1.json"
  let j ← runStf "assurances" file JAM.Tests.Assurances.check
  let params := JAM.V080.tiny080
  let (i, ρ, xs) ← readV file do
    let pre ← field j "pre_state"
    let inp ← field j "input"
    let i : AssurancesInput :=
      { slot := ← natField inp "slot", parent := ← hexField inp "parent",
        activeEd := ← edKeys pre "curr_validators", postActiveCount := (← arr pre "post_validators").size }
    return (i, ← rho (← field pre "avail_assignments"), ← list inp "assurances" (assurance params.coreCount))
  let .ok (R, ρ') := JAM.assurances params (sigOracle none) i ρ xs
    | throw <| IO.userError s!"examples: {file}: the model rejects the extrinsic"
  let cores := List.range params.coreCount
  let pending (e : Option AvailAssignment) : String :=
    match e with
    | none => "empty"
    | some a => s!"package {abbrB a.guarantee.report.spec.packageHash}, since slot {a.time}"
  let available (c : Nat) := R.any (·.core == c)
  let bits (a : Assurance) : String :=
    let set := cores.filter (a.bitfield.getD · false)
    s!"validator {a.assurer}: " ++ (if set.isEmpty then "none" else "core " ++ " and ".intercalate (set.map toString))
  return {
    name := "assurances-available", title := "Assurances make a report available",
    source := jamSource s!"stf/assurances/tiny/{file}",
    params := tinyParams params ++ s!", $\\mathsf\{U}$ = {params.assuranceTimeout}",
    summary := s!"Both cores have a report pending availability. {xs.length} validators send assurances, each \
      setting a bit for every core whose chunk it holds. A report becomes available when more than two thirds \
      of the {i.activeEd.length} validators set its bit; its core is then cleared.",
    inputs := [
      { label := "Slot $\\mathbf{H}_T$", value := toString i.slot },
      { label := "Assurances $\\mathbf{E}_A$", value := "; ".intercalate (xs.map bits) }],
    columns := [""] ++ cores.map (s!"Core {·}"),
    rows := [
      { label := "Pending report $\\rho^\\dagger[c]$", cells := cores.map fun c => pending (ρ.getD c none) },
      { label := "Assurances setting the bit", cells := cores.map fun c =>
          s!"{(xs.filter (·.bitfield.getD c false)).length} of {i.activeEd.length}" },
      { label := "Available: in $\\mathbf{R}$", cells := cores.map fun c => if available c then "yes" else "no" },
      { label := "After: $\\rho^\\ddagger[c]$", cells := cores.map fun c => pending (ρ'.getD c none) }],
    notes := [s!"More than two thirds of {i.activeEd.length} means at least {2 * i.activeEd.length / 3 + 1}. \
      A report that is not yet available stays until it is, or until it times out at slot $t + \\mathsf\{U}$."],
    model := ["JAM.assurances", "JAM.checkAssurance"],
    equations := ["11.16", "11.17"],
    check := stfCheck "assurancestest" ++ " Signatures are checked by the suite's oracle, which accepts \
      them all for this vector." }

/-- The reports suite reads davxy/jam-test-vectors master at this commit (`scripts/fetch-jam-vectors.sh`). -/
def reportsRev : String := "5e8d2a2423256d6138a3f265a251429a4c63f66f"

def reportsSource (path : String) : Source :=
  { repo := "davxy/jam-test-vectors master 5e8d2a2 (the v0.8.0 vectors with corrected anchor slots)", path,
    url := vectorUrl "davxy/jam-test-vectors" reportsRev path }

/-- The guarantees of a reports vector and the model's result on them. -/
def runReports (file : String) : IO (List Guarantee × AvailAssignments × ReportsOutput × Nat) := do
  let j ← runStf "reports" file JAM.Tests.Reports.check
  let params := JAM.V080.tiny080
  let (i, δ, ρ, xs) ← readV file do
    let pre ← field j "pre_state"
    let inp ← field j "input"
    let η ← list pre "entropy" hex
    let i : ReportsInput :=
      { slot := ← natField inp "slot", activeEd := ← edKeys pre "curr_validators",
        previousEd := ← edKeys pre "prev_validators", entropy2 := η.getD 2 .empty,
        entropy3 := η.getD 3 .empty,
        offenders := Std.ExtTreeSet.ofList ((← list pre "offenders" hex).map (·.toList)),
        recent := ← list (← field pre "recent_blocks") "history" JAM.Tests.Reports.recentBlock,
        authPools := ← list pre "auth_pools" fun p => do return (← items p hex).map (·.toList),
        known := Std.ExtTreeSet.ofList ((← list inp "known_packages" hex).map (·.toList)),
        lookupAnchorKnown := fun _ => true }
    return (i, ← JAM.Tests.Reports.accounts pre, ← rho (← field pre "avail_assignments"), ← list inp "guarantees" guarantee)
  let .ok o := JAM.guarantees params (sigOracle none) i δ ρ xs
    | throw <| IO.userError s!"examples: {file}: the model rejects the guarantees"
  return (xs, ρ, o, i.slot)

def reportsExample : IO Example := do
  let file := "multiple_reports-1.json"
  let (xs, ρ, o, slot) ← runReports file
  let params := JAM.V080.tiny080
  let cores := List.range params.coreCount
  let g (c : Nat) := xs.find? (·.report.core == c)
  let gcell (f : Guarantee → String) (c : Nat) : String := match g c with
    | some x => f x
    | none => "none"
  let pending (e : Option AvailAssignment) : String :=
    match e with
    | none => "empty"
    | some a => s!"package {abbrB a.guarantee.report.spec.packageHash}, since slot {a.time}"
  let services (x : Guarantee) : String :=
    ", ".intercalate ((x.report.digests.map (·.service)).eraseDups.map toString)
  return {
    name := "reports-guarantees", title := "Two guarantees accepted onto their cores",
    source := reportsSource s!"stf/reports/tiny/{file}",
    params := tinyParams params ++ s!", $\\mathsf\{R}$ = {params.rotationPeriod}",
    summary := s!"The block carries {xs.length} guarantees, one for each core. Each report passes the checks of \
      §11.4: its guarantors are assigned to its core, its authorizer is in the core's pool, and its \
      anchor is a recent block. Each core then holds its report, stamped with the block's timeslot, until \
      it becomes available or times out.",
    inputs := [
      { label := "Slot $\\mathbf{H}_T$", value := toString slot },
      { label := "Guarantees $\\mathbf{E}_G$", value := toString xs.length }],
    columns := [""] ++ cores.map (s!"Core {·}"),
    rows := [
      { label := "Report's package $(r_\\mathbf{s})_p$", cells := cores.map (gcell fun x => abbrB x.report.spec.packageHash) },
      { label := "Work digests and their services", cells := cores.map (gcell fun x =>
          s!"{count x.report.digests.length "digest" "digests"}, service {services x}") },
      { label := "Signed by validators", cells := cores.map (gcell fun x =>
          ", ".intercalate (x.credential.map (toString ·.1))) },
      { label := "Before: $\\rho^\\ddagger[c]$", cells := cores.map fun c => pending (ρ.getD c none) },
      { label := "After: $\\rho'[c]$", cells := cores.map fun c => pending (o.assignments.getD c none) },
      { label := "Reported packages (for recent history)", cells := [count o.reported.size "package" "packages", ""] },
      { label := "Reporters $\\mathbf{G}$", cells := [count o.reporters.size "Ed25519 key" "Ed25519 keys", ""] }],
    notes := ["The reporters are the Ed25519 keys of every guarantee's signers; the validator statistics of §13 \
      credit each with a guarantee."],
    model := ["JAM.guarantees", "JAM.checkGuarantee"],
    equations := ["11.23", "11.24", "11.25", "11.26", "11.27", "11.46"],
    check := stfCheck "reportstest" ++ " Signatures are checked by the suite's oracle, which accepts \
      them all for this vector." }

/-! ## §12.4 Preimages -/

def preimagesExample : IO Example := do
  let file := "preimage_needed-2.json"
  let j ← runStf "preimages" file JAM.Tests.Preimages.check
  let (d, xs, slot, keys) ← readV file do
    let pre ← field j "pre_state"
    let i ← field j "input"
    let xs := (← (← arr i "preimages").mapM fun p => do
      return (← natField p "requester", (← hexField p "blob").toList)).toList
    -- which requests to show: the keys of the vector's prior requests
    let keys ← (← arr pre "accounts").toList.flatMapM fun e => do
      let s ← natField e "id"
      return (← (← arr (← field e "data") "preimage_requests").mapM fun r => do
        let k ← field r "key"
        return (s, (← hexField k "hash").toList, ← natField k "length")).toList
    return (← JAM.Tests.Preimages.accounts pre, xs, ← natField i "slot", keys)
  let .ok d' := preimages d d xs slot
    | throw <| IO.userError s!"examples: {file}: the model rejects the preimages"
  let req (a : Accounts) (s : Nat) (h : List UInt8) (z : Nat) : String :=
    match (a.get? s).bind (·.requestGet h z) with
    | some t => "[" ++ ", ".intercalate (t.map toString) ++ "]"
    | none => "none"
  let npre (a : Accounts) (s : Nat) : Nat := ((a.get? s).map (·.preimages.size)).getD 0
  let services := (xs.map (·.1) ++ keys.map (·.1)).eraseDups
  return {
    name := "preimages-provided", title := "A requested preimage is provided",
    source := jamSource s!"stf/preimages/tiny/{file}", params := tinyParams JAM.V080.tiny080,
    summary := s!"A service has asked for a preimage: its request for the pair (hash, length) is the empty \
      sequence $[]$. The block's preimages extrinsic supplies the data. The data is stored, and the request \
      records the slot it became available, {slot}.",
    inputs := [
      { label := "Slot $\\tau'$", value := toString slot },
      { label := "Preimages $\\mathbf{E}_P$", value := ", ".intercalate (xs.map fun (s, i) =>
          s!"service {s}: {i.length} octets, hash {abbrB (Blake2b.hash256 ⟨i.toArray⟩)}") }],
    columns := ["", "Before ($\\delta$)", "After ($\\delta'$)"],
    rows := services.flatMap (fun s =>
      [{ label := s!"Service {s}: preimages stored $a_\\mathbf\{p}$", cells := [toString (npre d s), toString (npre d' s)] : Row }] ++
      (keys.filter (·.1 == s)).map (fun (_, h, z) =>
        { label := s!"Service {s}: request $a_\\mathbf\{l}[({abbr h}, {z})]$", cells := [req d s h z, req d' s h z] : Row })),
    notes := ["Only a request whose value is $[]$ can be met. The other request, already provided at slots \
      shown in its value, is left as it was."],
    model := ["JAM.preimages", "JAM.providable", "JAM.integrateProvisions"],
    equations := ["12.36", "12.37", "12.38", "12.39"],
    check := stfCheck "preimagestest" }

/-! ## §13 Statistics -/

def statsExample : IO Example := do
  let file := "stats_with_some_extrinsic-1.json"
  let j ← runStf "statistics" file JAM.Tests.Statistics.check
  let params := JAM.V080.tiny080
  let (curr, last, input) ← readV file do
    let pre ← field j "pre_state"
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
    return (← JAM.Tests.Statistics.records pre "vals_curr_stats", ← JAM.Tests.Statistics.records pre "vals_last_stats", input)
  let (curr', last') := validatorStats params curr last input
  let row (v : Nat) : Row :=
    let a := curr.getD v {}
    let b := curr'.getD v {}
    { label := toString v ++ (if v == input.author then " (author)" else ""),
      cells := [arrow a.blocks b.blocks, arrow a.tickets b.tickets, arrow a.preimages b.preimages,
                arrow a.preimagesSize b.preimagesSize, arrow a.guarantees b.guarantees, arrow a.assurances b.assurances] }
  let sameEpoch := input.priorSlot / params.epochLen == input.slot / params.epochLen
  let gIdx := (List.range input.activeEd.length).filter fun v => input.reporters.contains (input.activeEd.getD v [])
  return {
    name := "statistics-validators", title := "Validator statistics: one block's counters",
    source := jamSource s!"stf/statistics/tiny/{file}", params := tinyParams params,
    summary := s!"The block at slot {input.slot} stays in the epoch of slot {input.priorSlot}, so $\\pi_V$ keeps \
      accumulating. The author is credited the block, its tickets and its preimages; each assurer an assurance; \
      each validator whose key signed a guarantee a guarantee. Each cell shows the counter before → after.",
    inputs := [
      { label := "Slot $\\mathbf{H}_T$ (prior $\\tau$)", value := s!"{input.slot} ({input.priorSlot})" },
      { label := "Author $\\mathbf{H}_I$", value := toString input.author },
      { label := "Tickets $\\mathbf{E}_T$", value := toString input.ticketCount },
      { label := "Preimages $\\mathbf{E}_P$", value := s!"{input.preimages.length}, {(input.preimages.map (·.2.length)).sum} octets" },
      { label := "Assurers", value := ", ".intercalate (input.assurers.map toString) },
      { label := "Reporters $\\mathbf{G}$", value := "validators " ++ ", ".intercalate (gIdx.map toString) }],
    columns := ["Validator", "Blocks $b$", "Tickets $t$", "Preimages $p$", "Preimage octets $d$", "Guarantees $g$", "Assurances $a$"],
    rows := (List.range curr'.length).map row,
    notes := [if sameEpoch && last' == last then "No epoch change: the previous epoch's record $\\pi_L$ is unchanged."
      else "An epoch change moved the record to $\\pi_L$."],
    model := ["JAM.validatorStats"],
    equations := ["13.4", "13.5", "13.6"],
    check := stfCheck "statstest" }

def coreStatsExample : IO Example := do
  let file := "multiple_reports-1.json"
  let (xs, _, _, _) ← runReports file
  let params := JAM.V080.tiny080
  let reports := xs.map (·.report)
  let cs := coreStats params reports [] []
  let ss := (serviceStats reports [] []).toList
  let cores := List.range params.coreCount
  let c (f : CoreRecord → Nat) : List String := cores.map fun k => toString (f (cs.getD k {}))
  let s (f : ServiceRecord → String) : List String := ss.map fun (_, r) => f r
  let dash : List String := ss.map fun _ => "—"
  return {
    name := "statistics-cores", title := "Core and service statistics of two guaranteed reports",
    source := reportsSource s!"stf/reports/tiny/{file}", params := tinyParams params,
    summary := "The core and service records count only the current block. Here the block guarantees one \
      report on each core, both for the same service. Each core sums its report's work digests; the service \
      sums the digests of both reports. No report became available and no assurances were made, so the \
      availability load $d$ and popularity $p$ are 0.",
    inputs := [
      { label := "Incoming reports $\\mathbf{I}$", value := ", ".intercalate (reports.map fun r =>
          s!"core {r.core}: {count r.digests.length "digest" "digests"}") },
      { label := "Available reports $\\mathbf{R}$", value := "none" },
      { label := "Assurances $\\mathbf{E}_A$", value := "none" }],
    columns := [""] ++ cores.map (s!"Core {·} $\\pi'_C$") ++ ss.map fun (k, _) => s!"Service {k} $\\pi'_S$",
    rows := [
      { label := "Imports $i$", cells := c (·.imports) ++ s (toString ·.imports) },
      { label := "Extrinsics $x$", cells := c (·.xtCount) ++ s (toString ·.xtCount) },
      { label := "Extrinsic octets $z$", cells := c (·.xtSize) ++ s (toString ·.xtSize) },
      { label := "Exports $e$", cells := c (·.exports) ++ s (toString ·.exports) },
      { label := "Refinement gas $u$", cells := c (·.gasUsed) ++ s (toString ·.refinement.2) },
      { label := "Digests refined $n$", cells := cores.map (fun _ => "—") ++ s (toString ·.refinement.1) },
      { label := "Bundle length $l$", cells := c (·.bundleLen) ++ dash },
      { label := "Availability load $d$", cells := c (·.daLoad) ++ dash },
      { label := "Popularity $p$", cells := c (·.popularity) ++ dash }],
    notes := [],
    model := ["JAM.coreStats", "JAM.serviceStats"],
    equations := ["13.9", "13.10", "13.11", "13.12", "13.13", "13.14"],
    check := stfCheck "reportstest" ++ " That suite compares $\\pi'_C$ and $\\pi'_S$ from the incoming reports." }

/-! ## The list -/

/-- The examples of this module, in the order of the book's chapters. -/
def stf : List (IO Example) :=
  [historyExample, authExample, disputesExample, assurancesExample, reportsExample, preimagesExample,
   statsExample, coreStatsExample]

end JAM.Tests.Examples
