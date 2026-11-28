import JAM.Fast.Blake2b
import JAM.Block
import JAM.Blake2b
import JAM.Crypto

/-!
# Disputes, verdicts and judgments (GP v0.8.1 §10, `sec:disputes`)

The disputes state $\psi = (\psi_G, \psi_B, \psi_W, \psi_O)$ (eq. `disputesspec`) and its transition under the
disputes extrinsic $\mathbf{E}_D = (\mathbf{E}_V, \mathbf{E}_C, \mathbf{E}_F)$ (eq. `disputesextrinsics`): the validity conditions on
verdicts, culprits and faults, the verdict sequence $\mathbf{v}$ (eq. `verdicts`), the cleared availability
assignments $\availassignmentspostjudgment$ (eq. `removenonpositive`), $\psi'$ (eqs. `goodsetdef`–`offendersdef`) and the offenders
marker $\mathbf{H}_O$ (§10.3).

Signatures are checked with `Crypto.edVerify`. The validator sets $\kappa$ and $\lambda$ enter only through their
Ed25519 keys.

The paper states the conditions but names no errors and gives no order between them. The errors
here are the test vectors' names. The order is not §10's: first the length bounds of eq. (10.2) on
$\mathbf{E}_V$, $\mathbf{E}_C$ and $\mathbf{E}_F$; then each list's ordering is checked before its
elements. The verdicts are strictly ordered by report hash; then, verdict by verdict: its age,
the ordering of its judgments, the vote count, each judgment's validator index and signature, that
the report is not already judged, and the vote split. Then the culprits' ordering and each
culprit's conditions (its verdict is bad, it is not already an offender, the key is a guarantor
key, the signature), then the same for the faults, and last that every good verdict has a fault.
-/

namespace JAM

/-- The disputes state $\psi = (\psi_G, \psi_B, \psi_W, \psi_O)$ (GP eq. `disputesspec`): the good, bad and wonky
    report hashes, and the punished Ed25519 keys. -/
structure DisputesState where
  good : OctetSet := ∅
  bad : OctetSet := ∅
  wonky : OctetSet := ∅
  offenders : OctetSet := ∅

/-- An availability assignment $(g, t)$ (GP eq. `reportingstate`): a guarantee and the timeslot at
    which it was reported. -/
structure AvailAssignment where
  guarantee : Guarantee
  time : Nat

/-- $\rho \in [\![ (\mathbb{G}, \mathbb{N}_T)? ]\!]_{\mathsf{C}}$. -/
abbrev AvailAssignments := List (Option AvailAssignment)

/-- Why a disputes extrinsic is invalid. The paper names no errors; these are the vectors'. -/
inductive DisputesError where
  | alreadyJudged
  | badVoteSplit
  | verdictsNotSortedUnique
  | judgementsNotSortedUnique
  | culpritsNotSortedUnique
  | faultsNotSortedUnique
  | notEnoughFaults
  | culpritsVerdictNotBad
  | faultVerdictWrong
  | offenderAlreadyReported
  | badJudgementAge
  | badValidatorIndex
  | badSignature
  | badGuarantorKey
  | badAuditorKey
  | badVotesCount
  /-- $|\mathbf{E}_V| > \mathsf{N}_V$ (GP v0.8.1 eq. `disputesextrinsics`, (10.2):
      $\mathbf{E}_V \in \llbracket\dots\rrbracket_{:\mathsf{N}_V}$). The model's own name: neither the paper nor the
      v0.8.0 vectors name this error. -/
  | tooManyVerdicts
  /-- $|\mathbf{E}_C| > \mathsf{N}_O$ (GP v0.8.1 eq. `disputesextrinsics`, (10.2)). The model's own name:
      neither the paper nor the v0.8.0 vectors name this error. -/
  | tooManyCulprits
  /-- $|\mathbf{E}_F| > \mathsf{N}_O$ (GP v0.8.1 eq. `disputesextrinsics`, (10.2)). The model's own name:
      neither the paper nor the v0.8.0 vectors name this error. -/
  | tooManyFaults
  deriving BEq, Repr

/-- $\mathsf{X}_V$ = `$jam_valid`, $\mathsf{X}_I$ = `$jam_invalid` (GP §10.2). -/
def Xvalid : List UInt8 := contextString "$jam_valid"
def Xinvalid : List UInt8 := contextString "$jam_invalid"
/-- $\mathsf{X}_G$ = `$jam_guarantee` (GP eq. `guarantorsig`). -/
def Xguarantee : List UInt8 := contextString "$jam_guarantee"

#guard Xguarantee = "jam_guarantee".toUTF8.toList

/-- $\mathsf{X}_v$: $\mathsf{X}_V$ for $\top$ and $\mathsf{X}_I$ for $\bot$. -/
def Xvalidif (v : Bool) : List UInt8 := if v then Xvalid else Xinvalid

/-- A sequence is strictly ascending under a key: $[x \in \mathbf{s}]$-ordered-unique by that key
    (GP §3.7, `sqorderuniqby`). -/
def orderedUniqBy {α : Type} (key : α → List UInt8) : List α → Bool
  | a :: b :: rest => decide (key a < key b) && orderedUniqBy key (b :: rest)
  | _ => true

/-- The same for natural-number keys. -/
def orderedUniqByNat {α : Type} (key : α → Nat) : List α → Bool
  | a :: b :: rest => key a < key b && orderedUniqByNat key (b :: rest)
  | _ => true

/-- A verdict's outcome: good ($\top$), bad ($\bot$) or wonky ($\varnothing$) (GP eq. `verdicts`). -/
inductive Outcome where
  | good
  | bad
  | wonky
  deriving BEq, Repr

/-- What the disputes transition reads from the prior state. -/
structure DisputesInput where
  /-- $\tau$, the prior timeslot. -/
  slot : Nat
  /-- $(\kappa_v)_e$, the active set's Ed25519 keys. -/
  activeEd : List (List UInt8)
  /-- $(\lambda_v)_e$, the previous epoch's Ed25519 keys. -/
  previousEd : List (List UInt8)

/-- The posterior of the disputes transition: $\psi'$, $\availassignmentspostjudgment$ and the offenders marker $\mathbf{H}_O$. -/
structure DisputesOutput where
  state : DisputesState
  assignments : AvailAssignments
  offendersMark : List (List UInt8)

/-- $K(a)$ (GP §10.2): $\kappa$ when $a = \lfloor \tau/\mathsf{E} \rfloor$, $\lambda$ otherwise. -/
def judgeKeys (params : Params) (i : DisputesInput) (a : Nat) : List (List UInt8) :=
  if a = i.slot / params.epochLen then i.activeEd else i.previousEd

/-- $V(a, \mathbf{j})$ (GP eq. `verdicts`): $\top$ when the positive judgments number $\lfloor 2/3 \cdot |\mathbf{k}| \rfloor + 1$, $\bot$ when
    they are none, $\varnothing$ when they number $\lfloor 1/3 \cdot |\mathbf{k}| \rfloor$, and undefined otherwise. -/
def verdictOutcome (k : Nat) (votes : List Judgment) : Option Outcome :=
  let t := (votes.filter (·.valid)).length
  if t = 2 * k / 3 + 1 then some .good
  else if t = 0 then some .bad
  else if t = k / 3 then some .wonky
  else none

/-- The conditions on one verdict $(r, a, \mathbf{j})$ (GP §10.2): $a \in \lfloor \tau/\mathsf{E} \rfloor - \mathbb{N}_2$, $\mathbf{j}$ ordered and
    unique by judge index, $|\mathbf{j}| = \lfloor 2/3 \cdot |\mathbf{k}| \rfloor + 1$, every judge index below $|\mathbf{k}|$ and every
    signature valid, $r$ not already judged, and $V(a, \mathbf{j})$ defined. It only validates: the
    verdict's entry of $\mathbf{v}$ is `verdicts`. -/
def checkVerdict (params : Params) (crypto : Crypto) (i : DisputesInput) (ψ : DisputesState)
    (v : Verdict) : Except DisputesError Unit := do
  let e := i.slot / params.epochLen
  unless v.age = e ∨ v.age + 1 = e do throw .badJudgementAge
  unless orderedUniqByNat (·.index) v.votes do throw .judgementsNotSortedUnique
  let k := judgeKeys params i v.age
  unless v.votes.length = 2 * k.length / 3 + 1 do throw .badVotesCount
  let r := v.target.toList
  for j in v.votes do
    unless j.index < k.length do throw .badValidatorIndex
    unless crypto.edVerify (k.getD j.index []) (Xvalidif j.valid ++ r) j.signature.toList do
      throw .badSignature
  if ψ.good.contains r || ψ.bad.contains r || ψ.wonky.contains r then throw .alreadyJudged
  if (verdictOutcome k.length v.votes).isNone then throw .badVoteSplit

/-- $\mathbf{v} \equiv [(r, V(a, \mathbf{j})) \mid (r, a, \mathbf{j}) \in \mathbf{E}_V]$ (GP eq. `verdicts`), with $\mathbf{k} = K(a)$. It is
    `none` when some $V(a, \mathbf{j})$ is undefined, which `checkVerdict` has already rejected. -/
def verdicts (params : Params) (i : DisputesInput) (xv : List Verdict) :
    Option (List (List UInt8 × Outcome)) :=
  xv.mapM fun v =>
    (verdictOutcome (judgeKeys params i v.age).length v.votes).map (v.target.toList, ·)

/-- $\{r \mid (r, o) \in \mathbf{v}\}$: the report hashes of the verdicts with outcome $o$. -/
def judgedAs (v : List (List UInt8 × Outcome)) (o : Outcome) : OctetSet :=
  .ofList ((v.filter (·.2 == o)).map (·.1))

/-- $\psi'$ (GP eqs. `goodsetdef`–`offendersdef`):
    $\psi'_G \equiv \psi_G \cup \{r \mid (r, \top) \in \mathbf{v}\}$, $\psi'_B \equiv \psi_B \cup \{r \mid (r, \bot) \in \mathbf{v}\}$,
    $\psi'_W \equiv \psi_W \cup \{r \mid (r, \varnothing) \in \mathbf{v}\}$ and
    $\psi'_O \equiv \psi_O \cup \{f \mid (f, \dots) \in \mathbf{E}_C\} \cup \{f \mid (f, \dots) \in \mathbf{E}_F\}$. -/
def disputesPosterior (ψ : DisputesState) (v : List (List UInt8 × Outcome)) (x : Disputes) :
    DisputesState where
  good := ψ.good.union (judgedAs v .good)
  bad := ψ.bad.union (judgedAs v .bad)
  wonky := ψ.wonky.union (judgedAs v .wonky)
  offenders := (ψ.offenders.union (.ofList (x.culprits.map (·.key.toList)))).union
    (.ofList (x.faults.map (·.key.toList)))

/-- $\mathbf{H}_O \equiv [f \mid (f, \dots) \in \mathbf{E}_C] \frown [f \mid (f, \dots) \in \mathbf{E}_F]$ (GP §10.3, `sec:judgmentmarker`). -/
def offendersMark (x : Disputes) : List (List UInt8) :=
  x.culprits.map (·.key.toList) ++ x.faults.map (·.key.toList)

/-- $\mathbf{k} = \{i_e \mid i \in \lambda \cup \kappa\} \setminus \psi_O$ (GP §10.2, eqs. `culprits`/`faults`): the keys a culprit or
    fault may name. -/
def offenceKeys (i : DisputesInput) (ψ : DisputesState) : List (List UInt8) :=
  (i.previousEd ++ i.activeEd).filter (!ψ.offenders.contains ·)

/-- $\availassignmentspostjudgment$ (GP eq. `removenonpositive`): clear each core whose assigned report's hash
    $\mathcal{H}((\rho[c]_g)_r)$ has a bad or wonky verdict. -/
def clearNonPositive (ρ : AvailAssignments) (verdicts : List (List UInt8 × Outcome)) :
    AvailAssignments :=
  ρ.map fun
    | none => none
    | some a =>
      let h := (Blake2b.hash256 ⟨a.guarantee.report.encode.toArray⟩).toList
      if verdicts.any fun (r, o) => r == h && (o == .bad || o == .wonky) then none else some a

/-- The disputes transition (GP §10): check $\mathbf{E}_D$ against $\tau$, $\kappa$, $\lambda$ and $\psi$, and give $\psi'$, $\availassignmentspostjudgment$ and $\mathbf{H}_O$.

    * The length bounds of eq. (10.2), checked first: $|\mathbf{E}_V| \le \mathsf{N}_V$, $|\mathbf{E}_C| \le \mathsf{N}_O$ and
      $|\mathbf{E}_F| \le \mathsf{N}_O$ (`Constants.Cmaxextrinsicverdicts`, `Constants.Cmaxextrinsicoffenses`).
    * Verdicts are ordered and unique by report hash, and each satisfies `checkVerdict`.
    * Culprits are ordered and unique by key; each $(r, f, s)$ has $r \in \psi'_B$, $f \in \mathbf{k}$ and
      $s \in \edsignaturebase_f\langle \mathsf{X}_G \frown r \rangle$.
    * Faults are ordered and unique by key; each $(r, v, f, s)$ has $r \in \psi'_B \Leftrightarrow r \notin \psi'_G \Leftrightarrow v$ (read as
      a chain of two equivalences), $f \in \mathbf{k}$ and $s \in \edsignaturebase_f\langle \mathsf{X}_v \frown r \rangle$.
    * Every good verdict has a fault for its report.

    $\mathbf{k}$ is `offenceKeys`. A key outside it is reported as already an offender when it is in
    $\psi_O$, and as an unknown guarantor or auditor otherwise. -/
def disputesTransition (params : Params) (crypto : Crypto) (i : DisputesInput) (ψ : DisputesState)
    (ρ : AvailAssignments) (x : Disputes) : Except DisputesError DisputesOutput := do
  if x.verdicts.length > Constants.Cmaxextrinsicverdicts then throw .tooManyVerdicts
  if x.culprits.length > Constants.Cmaxextrinsicoffenses then throw .tooManyCulprits
  if x.faults.length > Constants.Cmaxextrinsicoffenses then throw .tooManyFaults
  unless orderedUniqBy (·.target.toList) x.verdicts do throw .verdictsNotSortedUnique
  x.verdicts.forM (checkVerdict params crypto i ψ)
  let some v := verdicts params i x.verdicts | throw .badVoteSplit
  let ψ' := disputesPosterior ψ v x
  let k := offenceKeys i ψ
  let offenceKeyError (f : List UInt8) (e : DisputesError) : DisputesError :=
    if ψ.offenders.contains f then .offenderAlreadyReported else e
  unless orderedUniqBy (·.key.toList) x.culprits do throw .culpritsNotSortedUnique
  for c in x.culprits do
    let r := c.target.toList
    let f := c.key.toList
    unless ψ'.bad.contains r do throw .culpritsVerdictNotBad
    unless k.contains f do throw (offenceKeyError f .badGuarantorKey)
    unless crypto.edVerify f (Xguarantee ++ r) c.signature.toList do throw .badSignature
  unless orderedUniqBy (·.key.toList) x.faults do throw .faultsNotSortedUnique
  for flt in x.faults do
    let r := flt.target.toList
    let f := flt.key.toList
    let inBad := ψ'.bad.contains r
    let notGood := !ψ'.good.contains r
    unless inBad == notGood && notGood == flt.valid do throw .faultVerdictWrong
    unless k.contains f do throw (offenceKeyError f .badAuditorKey)
    unless crypto.edVerify f (Xvalidif flt.valid ++ r) flt.signature.toList do throw .badSignature
  for (r, o) in v do
    if o == .good && !x.faults.any (·.target.toList == r) then throw .notEnoughFaults
  return { state := ψ', assignments := clearNonPositive ρ v, offendersMark := offendersMark x }

end JAM
