import Tests.StfRunner
import Tests.ReportsJson
import JAM.Disputes

/-!
# Disputes STF vectors (`lake build disputestest`)

Runs the disputes transition of GP v0.8.0 §10 (`JAM.disputesTransition`) on every vector of
davxy/jam-test-vectors `v0.8.0` `stf/disputes/{tiny,full}`, and compares:
* the output: the offenders marker H_O, or the error (the paper names no errors; we compare the
  vectors' names);
* ψ' and ρ^† (on an error, the state is unchanged).

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

def showPsi (s : DisputesState) : String :=
  s!"good={s.good.toList.map hexS} bad={s.bad.toList.map hexS} wonky={s.wonky.toList.map hexS} offenders={s.offenders.toList.map hexS}"

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
  -- The model's own names (GP v0.8.1 eq. (10.2)); no vector names these errors.
  | .tooManyVerdicts => "too_many_verdicts (GP v0.8.1, unnamed)"
  | .tooManyCulprits => "too_many_culprits (GP v0.8.1, unnamed)"
  | .tooManyFaults => "too_many_faults (GP v0.8.1, unnamed)"

def check (params : Params) (j : Json) : Except String (List String) := do
  let pre ← field j "pre_state"
  let post ← field j "post_state"
  let x ← JAM.Tests.Json.disputes (← field (← field j "input") "disputes")
  let expErr ← expectedErr j
  let input : DisputesInput :=
    { slot := ← natField pre "tau", activeEd := ← edKeys pre "kappa", previousEd := ← edKeys pre "lambda" }
  let ψ ← psi (← field pre "psi")
  let ρ ← rho (← field pre "rho")
  let res := JAM.disputesTransition params (sigOracle expErr) input ψ ρ x
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

/-! ### The length bounds of $\mathbf{E}_D$ (GP v0.8.1 eq. (10.2)): $|\mathbf{E}_V| \le \mathsf{N}_V$, $|\mathbf{E}_C|, |\mathbf{E}_F| \le \mathsf{N}_O$

At the bound, the bound check passes and the next check (order and uniqueness) fails on the
repeated items; one over, the bound check fails first. -/

private def zeros (n : Nat) : ByteArray := ⟨(List.replicate n (0 : UInt8)).toArray⟩
private def aVerdict : Verdict := { target := zeros 32, age := 0, votes := [] }
private def aCulprit : Culprit := { target := zeros 32, key := zeros 32, signature := zeros 64 }
private def aFault : Fault := { target := zeros 32, valid := true, key := zeros 32, signature := zeros 64 }

private def dErr (x : Disputes) : Option DisputesError :=
  match JAM.disputesTransition .tiny (sigOracle none) { slot := 0, activeEd := [], previousEd := [] } {} [] x with
  | .ok _ => none
  | .error e => some e

#guard dErr { verdicts := [], culprits := [], faults := [] } == none
#guard dErr { verdicts := List.replicate Constants.Cmaxextrinsicverdicts aVerdict, culprits := [], faults := [] }
  == some .verdictsNotSortedUnique
#guard dErr { verdicts := List.replicate (Constants.Cmaxextrinsicverdicts + 1) aVerdict, culprits := [], faults := [] }
  == some .tooManyVerdicts
#guard dErr { verdicts := [], culprits := List.replicate Constants.Cmaxextrinsicoffenses aCulprit, faults := [] }
  == some .culpritsNotSortedUnique
#guard dErr { verdicts := [], culprits := List.replicate (Constants.Cmaxextrinsicoffenses + 1) aCulprit, faults := [] }
  == some .tooManyCulprits
#guard dErr { verdicts := [], culprits := [], faults := List.replicate Constants.Cmaxextrinsicoffenses aFault }
  == some .faultsNotSortedUnique
#guard dErr { verdicts := [], culprits := [], faults := List.replicate (Constants.Cmaxextrinsicoffenses + 1) aFault }
  == some .tooManyFaults

end JAM.Tests.Disputes

def main (args : List String) : IO UInt32 :=
  JAM.Tests.Stf.runSuite "disputestest"
    (JAM.Tests.Stf.defaultDirs args "vendor/jam-test-vectors/stf/disputes") JAM.Tests.Disputes.check
