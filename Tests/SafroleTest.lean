import Tests.StfRunner
import JAM.Safrole

/-!
# Safrole STF vectors (`lake build safroletest`)

Runs the Safrole transition of GP v0.8.0 §6 (`JAM.safrole`) on every vector of
davxy/jam-test-vectors `v0.8.0` `stf/safrole/{tiny,full}`. Where the vector expects success it
compares the posterior state (τ', η', λ', κ', γ_P', ι', γ_A', γ_S', γ_Z') and the markers H_E and
H_W. Where it expects an error, it checks that the model returns the same error and leaves the
state unchanged.

## The cryptography

The model takes the Bandersnatch primitives as parameters (`JAM.Crypto`). No implementation is
used here. Instead, each chain (tiny, full) gets a closed-world oracle read from that chain's
vectors:

* Ring VRF verification is true exactly on the (root, context, proof) triples of tickets that
  some vector accepts. The vectors' tickets carry no identifiers, but the paper requires **n** ⊆
  γ_A' (§6.7), so in every vector that expects success the new tickets' identifiers are the
  identifiers of γ_A' not in γ_A (or, on an epoch change, all of γ_A'), in the extrinsic's order.
  The triple's root is the vector's posterior γ_Z' and its context `$jam_ticket_seal ⌢ η_2' ⌢ e`
  with the posterior η_2'.
* Ring VRF output Y maps each such proof to that identifier.
* The ring root O maps the Bandersnatch keys of γ_P' to γ_Z' for each vector that expects success
  and changes epoch.
* The IETF VRF primitives are unused: the vectors give Y(H_V) directly.

So the vectors check every part of §6 that is not cryptography: rotation and Φ, η and its
rotation, F and Z, the markers, the merge into γ_A', and the extrinsic's conditions. They also
check that the model asks the primitives the right questions. A model that verified a proof against
the wrong root or context, or computed O over the wrong keys, would miss the oracle's table.
They do not check any Bandersnatch arithmetic. "Valid" here means "accepted by some vector", so a
proof the oracle has not seen is invalid. Each error vector's proofs are either seen with a different
attempt or root (rejected as bad proofs) or rejected before the proof is checked.
-/

namespace JAM.Tests.Safrole

open Lean (Json)
open PVM.Tests (field natField die)
open JAM.Tests.Json
open JAM.Tests.Stf (hexS)

def hexL (j : Json) : Except String (List UInt8) := do return (← hex j).toList
def hexFieldL (j : Json) (k : String) : Except String (List UInt8) := do hexL (← field j k)

def validator (j : Json) : Except String ValidatorKey := do
  return (← hexFieldL j "bandersnatch") ++ (← hexFieldL j "ed25519") ++ (← hexFieldL j "bls") ++
    (← hexFieldL j "metadata")

def validators (j : Json) (k : String) : Except String (List ValidatorKey) := do
  return (← (← arr j k).mapM validator).toList

def ticket (j : Json) : Except String Ticket := do
  return { id := ← hexField j "id", attempt := ← natField j "attempt" }

def ticketList (j : Json) : Except String (List Ticket) := do
  let a ← j.getArr?
  return (← a.mapM ticket).toList

def sealKeys (j : Json) : Except String SealKeys := do
  match j.getObjVal? "tickets", j.getObjVal? "keys" with
  | .ok t, _ => return .tickets (← ticketList t)
  | _, .ok k => return .keys (← (← k.getArr?).mapM hexL).toList
  | _, _ => die "bad gamma_s"

def state (j : Json) : Except String SafroleState := do
  return { tau := ← natField j "tau", eta := (← (← arr j "eta").mapM hexL).toList,
           prev := ← validators j "lambda", active := ← validators j "kappa",
           pending := ← validators j "gamma_k", staging := ← validators j "iota",
           accumulator := ← ticketList (← field j "gamma_a"), sealKeys := ← sealKeys (← field j "gamma_s"),
           ringRoot := ← hexFieldL j "gamma_z" }

def input (j : Json) : Except String SafroleInput := do
  let i ← field j "input"
  let xs ← (← arr i "extrinsic").mapM fun t => do
    return ({ attempt := ← natField t "attempt", proof := ← hexField t "signature" } : TicketProof)
  return { slot := ← natField i "slot", entropy := ← hexFieldL i "entropy", tickets := xs.toList,
           offenders := (← (← arr (← field j "pre_state") "post_offenders").mapM hexL).toList }

def epochMark (j : Json) : Except String (Option EpochMark) := do
  match j with
  | .null => return none
  | j =>
    let vs ← (← arr j "validators").mapM fun v => do return (← hexField v "bandersnatch", ← hexField v "ed25519")
    return some { entropy := ← hexField j "entropy", ticketsEntropy := ← hexField j "tickets_entropy",
                  validators := vs.toList }

def ticketsMark (j : Json) : Except String (Option (List Ticket)) := do
  match j with
  | .null => return none
  | j => return some (← ticketList j)

/-- Printable forms, for comparison and failure reports. -/
def showTicket (t : Ticket) : String := s!"({hexS t.id.toList}, {t.attempt})"
def showTickets (t : List Ticket) : String := toString (t.map showTicket)
def showSealKeys : SealKeys → String
  | .tickets t => s!"tickets {showTickets t}"
  | .keys k => s!"keys {k.map hexS}"
def showKeys (k : List ValidatorKey) : String := toString (k.map hexS)
def showState (s : SafroleState) : List (String × String) :=
  [("τ", toString s.tau), ("η", toString (s.eta.map hexS)), ("λ", showKeys s.prev),
   ("κ", showKeys s.active), ("γ_P", showKeys s.pending), ("ι", showKeys s.staging),
   ("γ_A", showTickets s.accumulator), ("γ_S", showSealKeys s.sealKeys), ("γ_Z", hexS s.ringRoot)]
def showOutput (o : SafroleOutput) : List (String × String) :=
  [("H_E", match o.epochMark with
      | none => "none"
      | some m => s!"({hexS m.entropy.toList}, {hexS m.ticketsEntropy.toList}, {m.validators.map fun (b, e) => (hexS b.toList, hexS e.toList)})"),
   ("H_W", match o.ticketsMark with | none => "none" | some t => showTickets t)]

/-- The components that differ. -/
def diff (got expected : List (String × String)) : List String :=
  (got.zip expected).filterMap fun ((k, g), (_, e)) =>
    if g == e then none else some s!"{k}:\n    got      {g}\n    expected {e}"

/-- The expected output: the markers, or an error name. -/
def output (j : Json) : Except String (Except String SafroleOutput) := do
  let o ← field j "output"
  match o.getObjVal? "ok", o.getObjVal? "err" with
  | .ok ok, _ => return .ok { epochMark := ← epochMark (← field ok "epoch_mark"),
                              ticketsMark := ← ticketsMark (← field ok "tickets_mark") }
  | _, .ok e => return .error (← e.getStr?)
  | _, _ => die "bad output"

/-- The oracle's tables, read from every vector of one chain that expects success. -/
structure Oracle where
  /-- Accepted (root, context, proof) triples. -/
  valid : List (List UInt8 × List UInt8 × List UInt8) := []
  /-- Proof ↦ ticket identifier. -/
  out : List (List UInt8 × List UInt8) := []
  /-- Bandersnatch keys of γ_P' ↦ γ_Z'. -/
  roots : List (List (List UInt8) × List UInt8) := []

/-- Add one vector's facts to the oracle. -/
def Oracle.add (params : Params) (o : Oracle) (j : Json) : Except String Oracle := do
  let .ok _ ← output j | return o
  let pre ← state (← field j "pre_state")
  let post ← state (← field j "post_state")
  let i ← input j
  let change := pre.tau / params.epochLen < post.tau / params.epochLen
  let newIds := if change then post.accumulator
    else post.accumulator.filter fun t => !pre.accumulator.any (·.id == t.id)
  let o := if change then { o with roots := (post.pending.map ValidatorKey.bs, post.ringRoot) :: o.roots } else o
  if i.tickets.isEmpty then return o
  if newIds.length != i.tickets.length then die "new tickets are not all in γ_A'"
  let eta2 := post.eta.getD 2 []
  let mut o := o
  for (x, t) in i.tickets.zip newIds do
    o := { o with valid := (post.ringRoot, ticketContext eta2 x.attempt, x.proof.toList) :: o.valid,
                  out := (x.proof.toList, t.id.toList) :: o.out }
  return o

def Oracle.crypto (o : Oracle) : Crypto :=
  { edVerify := fun _ _ _ => false
    bsVerify := fun _ _ _ _ => false
    bsOut := fun _ => []
    bsRingRoot := fun ks => (o.roots.lookup ks).getD []
    bsRingVerify := fun r ctx msg p => msg.isEmpty && o.valid.contains (r, ctx, p)
    bsRingOut := fun p => (o.out.lookup p).getD [] }

def errName : SafroleError → String
  | .badSlot => "bad_slot"
  | .unexpectedTicket => "unexpected_ticket"
  | .badTicketOrder => "bad_ticket_order"
  | .badTicketProof => "bad_ticket_proof"
  | .badTicketAttempt => "bad_ticket_attempt"
  | .duplicateTicket => "duplicate_ticket"
  | .uselessTicket => "useless_ticket"

def check (crypto : Crypto) (params : Params) (j : Json) : Except String (List String) := do
  let pre ← state (← field j "pre_state")
  let post ← state (← field j "post_state")
  let expected ← output j
  let got := safrole params crypto pre (← input j)
  match got, expected with
  | .ok (s, out), .ok eo =>
    return diff (showState s) (showState post) ++ diff (showOutput out) (showOutput eo)
  | .ok _, .error e => return [s!"accepted; expected error {e}"]
  | .error e, .ok _ => return [s!"rejected with {errName e}; expected success"]
  | .error e, .error ee =>
    let mut diffs := []
    if errName e != ee then diffs := diffs ++ [s!"error {errName e}; expected {ee}"]
    if showState pre != showState post then diffs := diffs ++ ["the vector's post-state differs from its pre-state"]
    return diffs

/-- Vectors whose outcome differs from GP 0.8.0 as modelled; none so far. -/
def known : List (String × String) := []

end JAM.Tests.Safrole

open JAM.Tests in
def main (args : List String) : IO UInt32 := do
  let base : System.FilePath := args.headD "vendor/jam-test-vectors/stf/safrole"
  let mut code : UInt32 := 0
  for (label, params) in [("tiny", JAM.Params.tiny), ("full", JAM.Params.full)] do
    let dir := base / label
    let mut o : Safrole.Oracle := {}
    for f in ← PVM.Tests.jsonFiles dir do
      match o.add params (← PVM.Tests.readJson f) with
      | .ok o' => o := o'
      | .error e => IO.eprintln s!"oracle {f}: {e}"; return 1
    let r ← Stf.runSuite "safroletest" [(label, params, dir)] (Safrole.check o.crypto) Safrole.known
    if r != 0 then code := r
  return code
