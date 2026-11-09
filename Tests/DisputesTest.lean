import Tests.StfRunner
import Tests.BlockJson
import JAM.Disputes

/-!
# Disputes STF vectors (`lake build disputestest`)

Runs the disputes transition of GP v0.8.0 §10 (`JAM.disputes`) on every vector of
davxy/jam-test-vectors `v0.8.0` `stf/disputes/{tiny,full}`, and compares:
* the output: the offenders marker H_O, or the error (the paper names no errors; we compare the
  vectors' names);
* ψ' and ρ^‡ (on an error, the state is unchanged).

Ed25519 verification is a parameter of the model (`JAM.Crypto`). The oracle here is read from the
vector's expected output: when it is `bad_signature`, every signature is rejected; otherwise every
signature is accepted. So these vectors check where the model looks for a bad signature, not the
signatures themselves.
-/

namespace JAM.Tests.Disputes

open Lean (Json)
open PVM.Tests (field natField die)
open JAM.Tests.Json
open JAM.Tests.Stf (hexS)

def octetSet (j : Json) (k : String) : Except String OctetSet := do
  return Std.ExtTreeSet.ofList ((← list j k hex).map (·.toList))

def psi (j : Json) : Except String DisputesState := do
  return { good := ← octetSet j "good", bad := ← octetSet j "bad", wonky := ← octetSet j "wonky",
           offenders := ← octetSet j "offenders" }

def assignment (j : Json) : Except String AvailAssignment := do
  return { guarantee := ← guarantee (← field j "guarantee"), time := ← natField j "registered_slot" }

def rho (j : Json) : Except String AvailAssignments := do
  items j fun e => match e with
    | .null => pure none
    | v => do return some (← assignment v)

def edKeys (j : Json) (k : String) : Except String (List (List UInt8)) :=
  list j k fun v => do return (← hexField v "ed25519").toList

def showPsi (s : DisputesState) : String :=
  s!"good={s.good.toList.map hexS} bad={s.bad.toList.map hexS} wonky={s.wonky.toList.map hexS} offenders={s.offenders.toList.map hexS}"

def showRho (ρ : AvailAssignments) : List String :=
  ρ.map fun
    | none => "none"
    | some a => s!"{hexS (a.guarantee.encode)}@{a.time}"

def errName : DisputesError → String
  | .alreadyJudged => "already_judged"
  | .badVoteSplit => "bad_vote_split"
  | .verdictsNotSortedUnique => "verdicts_not_sorted_unique"
  | .judgementsNotSortedUnique => "judgements_not_sorted_unique"
  | .culpritsNotSortedUnique => "culprits_not_sorted_unique"
  | .faultsNotSortedUnique => "faults_not_sorted_unique"
  | .notEnoughFaults => "not_enough_faults"
  | .culpritsVerdictNotBad => "culprits_verdict_not_bad"
  | .faultVerdictWrong => "fault_verdict_wrong"
  | .offenderAlreadyReported => "offender_already_reported"
  | .badJudgementAge => "bad_judgement_age"
  | .badValidatorIndex => "bad_validator_index"
  | .badSignature => "bad_signature"
  | .badGuarantorKey => "bad_guarantor_key"
  | .badAuditorKey => "bad_auditor_key"
  | .badVotesCount => "bad_votes_count"

/-- The expected error of a vector, if any. -/
def expectedErr (j : Json) : Except String (Option String) := do
  let out ← field j "output"
  match out.getObjVal? "err" with
  | .ok e => return some (← e.getStr?)
  | .error _ => return none

/-- The signature oracle: reject everything exactly when the vector expects `bad_signature`. -/
def oracle (expErr : Option String) : Crypto :=
  { edVerify := fun _ _ _ => expErr != some "bad_signature" }

def check (params : Params) (j : Json) : Except String (List String) := do
  let pre ← field j "pre_state"
  let post ← field j "post_state"
  let x ← JAM.Tests.Json.disputes (← field (← field j "input") "disputes")
  let expErr ← expectedErr j
  let input : DisputesInput :=
    { slot := ← natField pre "tau", activeEd := ← edKeys pre "kappa", previousEd := ← edKeys pre "lambda" }
  let ψ ← psi (← field pre "psi")
  let ρ ← rho (← field pre "rho")
  let res := JAM.disputes params (oracle expErr) input ψ ρ x
  let mut diffs := []
  match res, expErr with
  | .ok o, none =>
    let exp ← list (← field (← field j "output") "ok") "offenders_mark" hex
    if o.offendersMark != exp.map (·.toList) then
      diffs := diffs ++ [s!"H_O {o.offendersMark.map hexS} ≠ {exp.map fun h => hexS h.toList}"]
  | .ok _, some e => diffs := diffs ++ [s!"output ok ≠ err {e}"]
  | .error e, exp =>
    if some (errName e) != exp then diffs := diffs ++ [s!"output err {errName e} ≠ {exp}"]
  let (ψ', ρ') := match res with
    | .ok o => (o.state, o.assignments)
    | .error _ => (ψ, ρ)
  let eψ ← psi (← field post "psi")
  if showPsi ψ' != showPsi eψ then diffs := diffs ++ [s!"ψ':\n    got      {showPsi ψ'}\n    expected {showPsi eψ}"]
  let eρ ← rho (← field post "rho")
  if showRho ρ' != showRho eρ then diffs := diffs ++ [s!"ρ‡:\n    got      {showRho ρ'}\n    expected {showRho eρ}"]
  -- κ, λ and τ are not changed by this transition.
  for k in ["tau", "kappa", "lambda"] do
    if (← field pre k) != (← field post k) then diffs := diffs ++ [s!"{k} changed"]
  return diffs

end JAM.Tests.Disputes

def main (args : List String) : IO UInt32 :=
  JAM.Tests.Stf.runSuite "disputestest"
    (JAM.Tests.Stf.defaultDirs args "vendor/jam-test-vectors/stf/disputes") JAM.Tests.Disputes.check
