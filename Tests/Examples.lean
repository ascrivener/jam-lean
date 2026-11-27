import Tests.SafroleHarness
import Tests.AccumulateHarness
import Tests.PvmHarness

/-!
# Worked examples for the companion book (`lake build examples-exe`)

Runs selected model functions on chosen test vectors and writes what they compute, as JSON, to
`docs/site/examples/<name>.json`. The book's `{example "<name>"}` block (`docs/site/Companion/Example.lean`)
renders each file as a box: which vector and parameters, the inputs, and a table of values before →
after. Every number in a box is the model's own result, never copied from the vector, and the
generator fails unless the vector's expected output matches. It uses the comparison the vector's
test suite uses (the harnesses in `Tests.SafroleHarness`, `Tests.AccumulateHarness` and `Tests.PvmHarness`).

```
lake build examples-exe && .lake/build/bin/examples [OUT_DIR]   # default docs/site/examples
```

CI regenerates the files and fails when they differ from the committed ones
(`scripts/check-examples.sh`), so the book's examples always show what the current model computes.

The vectors: davxy/jam-test-vectors `v0.8.0` (`scripts/fetch-jam-vectors.sh`), run with the tiny
chain the tests use (`JAM.V080.tiny080`), and koute/jamtestvectors `pvm/programs`
(`scripts/fetch-vectors.sh`). To add an example, write a function returning an `Example` and list it
in `examples` (see `docs/site/README.md`, "Worked examples").
-/

namespace JAM.Tests.Examples

open Lean (Json ToJson toJson)
open PVM.Tests (field natField readJson jsonFiles)

/-- One labelled value of a box's inputs line. -/
structure Item where
  label : String
  value : String
  deriving ToJson

/-- One table row: a label and one cell per column after the first. -/
structure Row where
  label : String
  cells : List String
  deriving ToJson

/-- Where a vector comes from. -/
structure Source where
  /-- The repository and its tag, as the box names it. -/
  repo : String
  /-- The vector's path inside the repository. -/
  path : String
  url : String
  deriving ToJson

/-- A worked example. Text fields may hold `$…$` (inline math, the paper's macros allowed) and
    `` `…` `` (code). -/
structure Example where
  name : String
  title : String
  source : Source
  /-- The chain parameters, in a phrase ("the tiny chain: …"). -/
  params : String
  /-- What the box shows, in a sentence or two. -/
  summary : String
  inputs : List Item
  /-- The column headings, the first over the row labels. -/
  columns : List String
  rows : List Row
  notes : List String := []
  /-- The model functions that computed the values (full names; the book links them). -/
  model : List String
  /-- The paper's equations the box illustrates (the book checks they exist). -/
  equations : List String
  /-- How the result was checked against the vector, in a sentence. -/
  check : String
  deriving ToJson

/-! ## Formatting -/

def hexd (b : List UInt8) : String := JAM.Tests.Stf.hexS b

/-- A hash or key, abbreviated to its first four octets: `0x1a2b3c4d…`. -/
def abbr (b : List UInt8) : String :=
  if b.length ≤ 4 then s!"`0x{hexd b}`" else s!"`0x{hexd (b.take 4)}…`"

def abbrB (b : ByteArray) : String := abbr b.toList

/-- `n` things, with the right plural. -/
def count (n : Nat) (one many : String) : String := if n == 1 then s!"1 {one}" else s!"{n} {many}"

/-- The label of the first candidate equal to `x`, as " (= label)". -/
def sameAs {α} [BEq α] (x : α) (cands : List (String × α)) : String :=
  match cands.find? (·.2 == x) with
  | some (l, _) => s!" (= {l} before)"
  | none => ""

def vectorUrl (repo tag path : String) : String := s!"https://github.com/{repo}/blob/{tag}/{path}"

def jamSource (path : String) : Source :=
  { repo := "davxy/jam-test-vectors v0.8.0", path,
    url := vectorUrl "davxy/jam-test-vectors" "v0.8.0" path }

def tinyParams (p : Params) : String :=
  s!"the tiny chain the v0.8.0 vectors were made with ($\\mathsf\{E}$ = {p.epochLen} slots per epoch, " ++
  s!"$\\mathsf\{Y}$ = {p.epochTailStart}, $\\mathsf\{C}$ = {p.coreCount} cores, 6 validators)"

/-! ## Safrole: an epoch change -/

def safroleDir : System.FilePath := "vendor/jam-test-vectors/stf/safrole/tiny"

/-- The oracle the Safrole test builds from every tiny vector (`Tests.SafroleHarness`). -/
def safroleOracle (params : Params) : IO JAM.Tests.Safrole.Oracle := do
  let mut o : JAM.Tests.Safrole.Oracle := {}
  for f in ← jsonFiles safroleDir do
    match o.add params (← readJson f) with
    | .ok o' => o := o'
    | .error e => throw <| IO.userError s!"examples: oracle {f}: {e}"
  return o

def epochSlot (p : Params) (t : Nat) : String :=
  s!"{t} (epoch {t / p.epochLen}, slot {t % p.epochLen})"

def sealDesc : SealKeys → String
  | .tickets t => s!"tickets: {count t.length "ticket" "tickets"}"
  | .keys k => s!"fallback: {count k.length "Bandersnatch key" "Bandersnatch keys"}"

/-- The first sealers of a ticket sequence, each named by its index in `acc` (`γ_A[i]`). -/
def sealOrder (acc : List Ticket) : SealKeys → String
  | .tickets t =>
    let idx := t.take 6 |>.map fun x =>
      match acc.findIdx? (·.id == x.id) with
      | some i => s!"$\\gamma_A[{i}]$"
      | none => abbrB x.id
    ", ".intercalate idx ++ (if t.length > 6 then ", …" else "")
  | .keys k => ", ".intercalate ((k.take 3).map abbr) ++ (if k.length > 3 then ", …" else "")

def keysDesc (ks : List ValidatorKey) : String :=
  s!"{count ks.length "key" "keys"}, the first {abbr (ks.headD []).bs}"

def safroleExample (name file : String) (title summary : String) (notes : List String) : IO Example := do
  let params := JAM.V080.tiny080
  let o ← safroleOracle params
  let path := safroleDir / file
  let j ← readJson path
  let some r := (do
      let diffs ← JAM.Tests.Safrole.check o.crypto params j
      let pre ← JAM.Tests.Safrole.state (← field j "pre_state")
      let inp ← JAM.Tests.Safrole.input j
      return (diffs, pre, inp)).toOption
    | throw <| IO.userError s!"examples: {file}: cannot read the vector"
  let (diffs, pre, inp) := r
  unless diffs.isEmpty do throw <| IO.userError s!"examples: {file}: the model disagrees with the vector: {diffs}"
  let .ok (post, out) := safrole params o.crypto pre inp
    | throw <| IO.userError s!"examples: {file}: the model rejects the block"
  let eta (s : SafroleState) (i : Nat) := s.eta.getD i []
  let etaPre := (List.range 4).map fun i => (s!"$\\eta_{i}$", eta pre i)
  let etaRow (i : Nat) : Row :=
    { label := if i == 0 then "Entropy accumulator $\\eta_0$" else s!"Earlier entropy $\\eta_{i}$",
      cells := [abbr (eta pre i), abbr (eta post i) ++ (if i == 0 then "" else sameAs (eta post i) etaPre)] }
  let keySets := [("$\\iota$", pre.staging), ("$\\gamma_P$", pre.pending), ("$\\kappa$", pre.active),
    ("$\\lambda$", pre.prev)]
  let keyRow (label : String) (b a : List ValidatorKey) : Row :=
    { label, cells := [keysDesc b, keysDesc a ++ sameAs a keySets] }
  let sealAfter := match post.sealKeys with
    | .tickets t =>
      if t.map (·.id) == (outsideIn pre.accumulator).map (·.id) then
        sealDesc post.sealKeys ++ ", in the order $Z(\\gamma_A)$ of the accumulator before"
      else sealDesc post.sealKeys
    | .keys _ => sealDesc post.sealKeys
  let mark := match out.epochMark with
    | none => "none"
    | some m =>
      s!"entropy {abbrB m.entropy}{sameAs m.entropy.toList etaPre}, tickets entropy " ++
      s!"{abbrB m.ticketsEntropy}{sameAs m.ticketsEntropy.toList etaPre}, " ++
      s!"{count m.validators.length "validator" "validators"} (the new $\\gamma_P$)"
  let wmark := match out.ticketsMark with
    | none => "none"
    | some t => count t.length "ticket" "tickets"
  return {
    name, title, source := jamSource s!"stf/safrole/tiny/{file}", params := tinyParams params, summary,
    inputs := [
      { label := "Slot $\\mathbf{H}_T$", value := epochSlot params inp.slot },
      { label := "VRF output $\\mathcal{Y}(\\mathbf{H}_V)$", value := abbr inp.entropy },
      { label := "Ticket proofs $\\mathbf{E}_T$", value := toString inp.tickets.length },
      { label := "Offenders $\\psi'_O$", value := toString inp.offenders.length }],
    columns := ["", s!"Before ($\\tau$ = {pre.tau})", s!"After ($\\tau'$ = {post.tau})"],
    rows := [
      { label := "Timeslot $\\tau$", cells := [epochSlot params pre.tau, epochSlot params post.tau] },
      etaRow 0, etaRow 1, etaRow 2, etaRow 3,
      { label := "Ticket accumulator $\\gamma_A$",
        cells := [count pre.accumulator.length "ticket" "tickets", count post.accumulator.length "ticket" "tickets"] },
      { label := "Sealer sequence $\\gamma_S$", cells := [sealDesc pre.sealKeys, sealAfter] },
      { label := "First sealers", cells := [sealOrder pre.accumulator pre.sealKeys, sealOrder pre.accumulator post.sealKeys] },
      keyRow "Pending keys $\\gamma_P$" pre.pending post.pending,
      keyRow "Active keys $\\kappa$" pre.active post.active,
      keyRow "Previous keys $\\lambda$" pre.prev post.prev,
      { label := "Ring root $\\gamma_Z$", cells := [abbr pre.ringRoot, abbr post.ringRoot] },
      { label := "Epoch marker $\\mathbf{H}_E$", cells := ["", mark] },
      { label := "Tickets marker $\\mathbf{H}_W$", cells := ["", wmark] }],
    notes,
    model := ["JAM.safrole", "JAM.outsideIn"],
    equations := ["6.15", "6.24", "6.25", "6.26", "6.29", "6.36"],
    check := "The model's posterior state and markers equal the vector's expected output: \
      `lake build safroletest` makes this comparison on every Safrole vector, and the generator \
      repeats it for this one. Bandersnatch is the test's oracle, read from the vectors, so the \
      ring root and ticket identifiers are the vectors' own." }

/-! ## Accumulation -/

def accDir : System.FilePath := "vendor/jam-test-vectors/stf/accumulate/tiny"

/-- Run one accumulate vector; fails unless the model's result matches it. -/
def runAcc (file : String) : IO (Json × AccState × List WorkReport × AccResult) := do
  let params := JAM.V080.tiny080
  let j ← readJson (accDir / file)
  let some r := (do
      let pre ← JAM.Tests.Accumulate.state params (← field j "pre_state")
      let input ← field j "input"
      let reports ← (← JAM.Tests.Accumulate.arrF input "reports").mapM JAM.Tests.Json.workReport
      let res ← (accumulate params pre (← natField input "slot") reports.toList).mapError (fun e => s!"{repr e}")
      let diffs ← JAM.Tests.Accumulate.compare params j res
      return (pre, reports.toList, res, diffs)).toOption
    | throw <| IO.userError s!"examples: {file}: cannot run the vector"
  let (pre, reports, res, diffs) := r
  unless diffs.isEmpty do throw <| IO.userError s!"examples: {file}: the model disagrees with the vector: {diffs}"
  return (j, pre, reports, res)

def accCheck : String :=
  "The model's posterior state, statistics and output root equal the vector's expected output \
   (the comparison `acctest` makes). The accumulate suite as a whole is suspended until v0.8.1 \
   vectors exist, because most of its services are v0.8.0 programs; this vector is one of those that pass."

def accAlways : IO Example := do
  let file := "always_accumulate-1.json"
  let (_, pre, reports, res) ← runAcc file
  let params := JAM.V080.tiny080
  let post := res.state
  let svcs := pre.pstate.alwaysAcc.toList
  let some (s, gas) := svcs.head? | throw <| IO.userError "examples: no always-accumulate service"
  let some a := pre.pstate.accounts.get? s | throw <| IO.userError "examples: no account"
  let some a' := post.pstate.accounts.get? s | throw <| IO.userError "examples: no account after"
  let stat := res.stats.lookup s
  let statS := match stat with
    | some (n, t, g) => s!"$N$ = {n}, $T$ = {t}, $G$ = {g}"
    | none => "none"
  let qlen (q : List (List ReadyEntry)) := (q.map List.length).sum
  return {
    name := "accumulate-always", title := "Accumulation with no reports: an always-accumulate service",
    source := jamSource s!"stf/accumulate/tiny/{file}", params := tinyParams params,
    summary := s!"The block brings no work reports, but service {s} is in the always-accumulate list \
      $\\chi_Z$ with {gas} gas. Its accumulation code runs anyway (the model executes the service's \
      real PVM code), uses some of that gas, and the service's last-accumulation slot moves to the \
      new timeslot.",
    inputs := [
      { label := "Slot $\\mathbf{H}_T$", value := toString post.slot },
      { label := "New reports $\\mathbf{R}$", value := toString reports.length },
      { label := "Always-accumulate $\\chi_Z$", value := ", ".intercalate (svcs.map fun (s, g) => s!"service {s} ↦ {g} gas") }],
    columns := ["", s!"Before ($\\tau$ = {pre.slot})", s!"After ($\\tau'$ = {post.slot})"],
    rows := [
      { label := "Ready queue $\\omega$ (reports waiting)", cells := [toString (qlen pre.ready), toString (qlen post.ready)] },
      { label := "Accumulated this block $\\xi'_{\\mathsf{E}-1}$", cells := ["", count (post.accumulated.getLastD ∅).toList.length "package" "packages"] },
      { label := s!"Service {s}: last accumulation $a_a$", cells := [toString a.lastAcc, toString a'.lastAcc] },
      { label := s!"Service {s}: balance $a_b$", cells := [toString a.balance, toString a'.balance] },
      { label := s!"Service {s}: storage items $a_i$, octets $a_o$", cells := [s!"{a.items}, {a.octets}", s!"{a'.items}, {a'.octets}"] },
      { label := s!"Statistics for service {s}", cells := ["", statS] },
      { label := "Accumulation outputs $\\theta'$", cells := ["", s!"{count res.outputs.length "output" "outputs"}; root {abbr res.root}"] }],
    notes := [s!"$G$ is the gas the service's accumulation used, out of the {gas} that $\\chi_Z$ grants it; \
      $N$ = 0 because it accumulated no report. A service with statistics gets $a'_a = \\tau'$."],
    model := ["JAM.accumulate", "JAM.accSeq"],
    equations := ["12.25", "12.29", "12.30", "12.31"],
    check := accCheck }

def accQueue : IO Example := do
  let file := "enqueue_and_unlock_chain-2.json"
  let (_, pre, reports, res) ← runAcc file
  let params := JAM.V080.tiny080
  let post := res.state
  let accAll : OctetSet := pre.accumulated.foldl .union ∅
  let m := post.slot % params.epochLen
  let known : List (String × List UInt8) :=
    ((pre.ready.flatten.map (·.1)) ++ reports).map fun w => (abbr w.pkg, w.pkg)
  let queued : List (List UInt8) := pre.ready.flatten.map (·.1.pkg)
  let name (h : List UInt8) := (match known.find? (·.2 == h) with
    | some (s, _) => s
    | none => abbr h) ++ (if queued.contains h then " (itself in the queue)" else "")
  let reportRow (w : WorkReport) : Row :=
    let pre : List (List UInt8) := w.context.prerequisites.toList
    let waiting := pre.filter fun h => !accAll.contains h
    let entry := (post.ready.getD m []).find? (·.1.pkg == w.pkg)
    { label := s!"Report for package {abbr w.pkg}",
      cells := [", ".intercalate (pre.map name),
                s!"{waiting.length} of {pre.length}",
                match entry with
                | some (_, d) => s!"queued in $\\omega'_{m}$, waiting on {", ".intercalate (d.toList.map name)}"
                | none => "not queued"] }
  let qlen (q : List (List ReadyEntry)) := (q.map List.length).sum
  return {
    name := "accumulate-queue", title := "Reports that must wait: the ready queue",
    source := jamSource s!"stf/accumulate/tiny/{file}", params := tinyParams params,
    summary := "Two new work reports arrive, each naming a prerequisite package that has not been \
      accumulated yet. Neither is accumulatable, so both join the ready queue with their \
      unmet dependencies. One depends on a report already in the queue, so this forms a chain that \
      unlocks in order once its first link accumulates.",
    inputs := [
      { label := "Slot $\\mathbf{H}_T$", value := s!"{post.slot} (slot {m} of the epoch)" },
      { label := "New reports $\\mathbf{R}$", value := toString reports.length },
      { label := "Reports already queued", value := toString (qlen pre.ready) }],
    columns := ["", "Prerequisites", "Unmet", "Outcome"],
    rows := reports.map reportRow ++ [
      { label := "Ready queue $\\omega$, all slots", cells := [s!"before: {qlen pre.ready}", "", s!"after: {qlen post.ready}"] },
      { label := "Accumulated this block $\\xi'_{\\mathsf{E}-1}$", cells := ["", "", count (post.accumulated.getLastD ∅).toList.length "package" "packages"] }],
    notes := ["A report with no prerequisites and no segment-root lookups is accumulatable at once ($\\mathbf{R}^!$); \
      the others go to the queue with their dependencies minus what is already accumulated, and leave it \
      when the last dependency is accumulated."],
    model := ["JAM.accumulate", "JAM.editQueue"],
    equations := ["12.4", "12.5", "12.6", "12.7", "12.10", "12.11"],
    check := accCheck }

/-! ## The PVM: a short program run, one step at a time -/

def pvmDir : System.FilePath := "vendor/jamtestvectors/pvm/programs"

def reg (r : PVM.RegIdx) : String := s!"$\\varphi_\{{r}}$"

def imm (x : UInt64) : String := if x.toNat < 1024 then toString x.toNat else s!"0x{String.ofList (Nat.toDigits 16 x.toNat)}"

/-- An instruction as `name operands`, the registers as $\varphi_r$. -/
def showInstr : PVM.Instr → String
  | .noArgs op => s!"`{op.name}`"
  | .oneImm op x => s!"`{op.name}` {imm x}"
  | .regExtImm op a x => s!"`{op.name}` {reg a}, {imm x}"
  | .twoImm op x y => s!"`{op.name}` {imm x}, {imm y}"
  | .oneOffset op x => s!"`{op.name}` → {x}"
  | .regImm op a x => s!"`{op.name}` {reg a}, {imm x}"
  | .regTwoImm op a x y => s!"`{op.name}` {reg a}, {imm x}, {imm y}"
  | .regImmOffset op a x y => s!"`{op.name}` {reg a}, {imm x}, → {y}"
  | .twoReg op d a => s!"`{op.name}` {reg d}, {reg a}"
  | .twoRegImm op a b x => s!"`{op.name}` {reg a}, {reg b}, {imm x}"
  | .twoRegOffset op a b x => s!"`{op.name}` {reg a}, {reg b}, → {x}"
  | .twoRegTwoImm op a b x y => s!"`{op.name}` {reg a}, {reg b}, {imm x}, {imm y}"
  | .threeReg op a b d => s!"`{op.name}` {reg a}, {reg b}, {reg d}"

def statusDesc : PVM.Status → String
  | .cont => "continue"
  | .halt => "halt ∎"
  | .panic => "panic ☇"
  | .oog => "out of gas ∞"
  | .fault a => s!"page fault at {a}"
  | .host h => s!"host call {h}"

def regChanges (a b : PVM.Regs) : String :=
  let ch := (List.range 13).filter fun k => a[k]! != b[k]!
  if ch.isEmpty then "—" else ", ".intercalate (ch.map fun k => s!"$\\varphi_\{{k}}$ = {imm b[k]!}")

def pvmExample (file : String) (summary : String) (notes : List String) : IO Example := do
  let j ← readJson (pvmDir / file)
  match PVM.Tests.runVector j with
  | .ok () => pure ()
  | .error e => throw <| IO.userError s!"examples: {file}: the model disagrees with the vector: {e}"
  let some (p, pc0, gas0, regs0) := (do
      let p ← PVM.Tests.programOf j
      let pc ← natField j "initial-pc"
      let gas ← PVM.Tests.intField j "initial-gas"
      -- registers set by the vector's `set-reg` steps before its run
      let mut regs : PVM.Regs := Vector.replicate 13 0
      for s in ← (← field j "steps").getArr? do
        if let .ok b := s.getObjVal? "set-reg" then
          let k ← natField b "reg"
          let v ← natField b "value"
          if h : k < 13 then regs := regs.set k (UInt64.ofNat v)
      return (p, pc, UInt64.ofInt gas, regs)).toOption
    | throw <| IO.userError s!"examples: {file}: cannot read the vector"
  -- Ψ₁, one step at a time, as Ψ runs it (`PVM.runFuel`).
  let mut rows : Array Row := #[]
  let mut i := pc0
  let mut gas := gas0
  let mut charged := false
  let mut regs := regs0
  let mut mem : PVM.Memory := .empty
  let mut final := PVM.Status.cont
  for n in [0:64] do
    let some P := PVM.deblob p i
      | final := .panic
        break
    let ins := (P.decode i).getD (.noArgs .trap)
    let r := P.step i gas charged regs mem
    let gasCell := s!"{gas} → {r.gas}" ++ (if r.gas != gas then s!" (block cost {gas - r.gas})" else "")
    let cells := [toString i, showInstr ins, gasCell, regChanges regs r.regs, statusDesc r.status]
    let row : Row := ⟨toString (n + 1), cells⟩
    rows := rows.push row
    gas := r.gas
    charged := r.charged
    regs := r.regs
    mem := r.mem
    i := r.pc
    if r.status != .cont then
      final := r.status
      break
  -- The stepping must agree with Ψ itself.
  let res := PVM.psi p pc0 gas0 false regs0 .empty
  unless res.status == final && res.gas == gas && res.regs == regs do
    throw <| IO.userError s!"examples: {file}: stepping Ψ₁ disagrees with Ψ"
  let some P0 := PVM.deblob p pc0 | throw <| IO.userError "examples: no program"
  let nz := (List.range 13).filter fun k => regs0[k]! != 0
  return {
    name := "pvm-" ++ (file.dropEnd 5).copy, title := "A short PVM program, one instruction at a time",
    source := { repo := "koute/jamtestvectors (pvm/programs)", path := file,
                url := vectorUrl "koute/jamtestvectors" "master" s!"pvm/programs/{file}" },
    params := "no chain parameters: the PVM alone", summary,
    inputs := [
      { label := "Code $\\mathbf{c}$", value := count P0.code.size "octet" "octets" },
      { label := "Start $\\imath$", value := toString pc0 },
      { label := "Gas $\\varrho$", value := toString gas0 },
      { label := "Registers $\\varphi$",
        value := if nz.isEmpty then "all 0" else ", ".intercalate (nz.map fun k => s!"$\\varphi_\{{k}}$ = {imm regs0[k]!}") ++ ", the rest 0" }],
    columns := ["Step", "$\\imath$", "Instruction", "Gas $\\varrho$", "Registers changed", "Status $\\varepsilon$"],
    rows := rows.toList,
    notes,
    model := ["PVM.Program.step", "PVM.psi", "PVM.Program.chargeGas"],
    equations := ["A.1", "A.7", "A.8", "A.10"],
    check := s!"Running $\\Psi$ on the whole program gives the same status, gas and registers as the steps above, and \
      they equal the vector's expected result (the comparison `lake build pvmtest` makes on every program vector)." }

/-! ## The examples -/

def examples : List (IO Example) := [
  safroleExample "safrole-epoch-change" "publish-tickets-with-mark-5.json"
    "A Safrole epoch change that switches to tickets"
    "The block at slot 12 opens epoch 1. The ticket accumulator filled up during epoch 0, so the new \
     epoch's sealers are tickets rather than fallback keys; the entropy and the validator key sets rotate."
    ["Each rotated value is the one named in brackets: $\\eta'_1 = \\eta_0$, $\\kappa' = \\gamma_P$, $\\lambda' = \\kappa$, \
      and $\\gamma'_P = \\Phi(\\iota)$, which is $\\iota$ itself because there are no offenders."],
  safroleExample "safrole-epoch-change-fallback" "enact-epoch-change-with-no-tickets-4.json"
    "A Safrole epoch change with fallback sealers"
    "The block at slot 15 opens epoch 1, but no tickets were submitted during epoch 0, so the new \
     epoch is sealed by the fallback keys $F(\\eta'_2, \\kappa')$."
    [],
  accAlways,
  accQueue,
  pvmExample "inst_branch_eq_ok.json"
    "Two `load_imm` instructions put equal values in two registers, and `branch_eq` compares them; \
     the branch is taken, and the program ends at a trap. Gas is charged once per basic block, \
     at the block's first instruction."
    ["The vector reports the exit at the instruction that caused it; $\\Psi$ itself returns $\\imath = 0$ on ☇."]]

end JAM.Tests.Examples

open JAM.Tests.Examples in
def main (args : List String) : IO UInt32 := do
  let out : System.FilePath := args.headD "docs/site/examples"
  IO.FS.createDirAll out
  for mk in examples do
    let e ← mk
    let file := out / s!"{e.name}.json"
    IO.FS.writeFile file ((Lean.toJson e).pretty 100 ++ "\n")
    IO.println s!"examples: wrote {file}"
  return 0
