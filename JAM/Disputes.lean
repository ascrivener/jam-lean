import JAM.Block
import JAM.Blake2b
import JAM.Crypto

/-!
# Disputes, verdicts and judgments (GP v0.8.0 §10, `sec:disputes`)

The disputes state ψ = (ψ_G, ψ_B, ψ_W, ψ_O) (eq. `disputesspec`) and its transition under the
disputes extrinsic 𝔼_D = (𝔼_V, 𝔼_C, 𝔼_F) (eq. `disputesextrinsics`): the validity conditions on
verdicts, culprits and faults, the verdict sequence **v** (eq. `verdicts`), the cleared availability
assignments ρ^‡ (eq. `removenonpositive`), ψ' (eqs. `goodsetdef`–`offendersdef`) and the offenders
marker H_O (§10.4).

Signatures are checked with `Crypto.edVerify`. The validator sets κ and λ enter only through their
Ed25519 keys.

The paper states the conditions but names no errors and gives no order between them. The errors
here are the test vectors' names; the order is the one in which the conditions appear in §10,
with each verdict's or offence's conditions checked together.
-/

namespace JAM

/-- The disputes state ψ = (ψ_G, ψ_B, ψ_W, ψ_O) (GP eq. `disputesspec`): the good, bad and wonky
    report hashes, and the punished Ed25519 keys. -/
structure DisputesState where
  good : OctetSet := ∅
  bad : OctetSet := ∅
  wonky : OctetSet := ∅
  offenders : OctetSet := ∅

/-- An availability assignment (g, t) (GP eq. `reportingstate`): a guarantee and the timeslot at
    which it was reported. -/
structure AvailAssignment where
  guarantee : Guarantee
  time : Nat

/-- ρ ∈ ⟦(𝔾, ℕ_T)?⟧_𝖢. -/
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
  deriving BEq, Repr

/-- X_V = `$jam_valid`, X_I = `$jam_invalid` (GP §10.2). -/
def Xvalid : List UInt8 := contextString "$jam_valid"
def Xinvalid : List UInt8 := contextString "$jam_invalid"
/-- X_G = `$jam_guarantee` (GP eq. `guarantorsig`). -/
def Xguarantee : List UInt8 := contextString "$jam_guarantee"

/-- X_v: X_V for ⊤ and X_I for ⊥. -/
def Xvalidif (v : Bool) : List UInt8 := if v then Xvalid else Xinvalid

/-- A sequence is strictly ascending under a key: [x ∈ **s**]-ordered-unique by that key
    (GP §3.7, `sqorderuniqby`). -/
def orderedUniqBy {α : Type} (key : α → List UInt8) : List α → Bool
  | a :: b :: rest => decide (key a < key b) && orderedUniqBy key (b :: rest)
  | _ => true

/-- The same for natural-number keys. -/
def orderedUniqByNat {α : Type} (key : α → Nat) : List α → Bool
  | a :: b :: rest => key a < key b && orderedUniqByNat key (b :: rest)
  | _ => true

/-- A verdict's outcome: good (⊤), bad (⊥) or wonky (∅) (GP eq. `verdicts`). -/
inductive Outcome where
  | good
  | bad
  | wonky
  deriving BEq, Repr

/-- What the disputes transition reads from the prior state. -/
structure DisputesInput where
  /-- τ, the prior timeslot. -/
  slot : Nat
  /-- (κ_v)_e, the active set's Ed25519 keys. -/
  activeEd : List (List UInt8)
  /-- (λ_v)_e, the previous epoch's Ed25519 keys. -/
  previousEd : List (List UInt8)

/-- The posterior of the disputes transition: ψ', ρ^‡ and the offenders marker H_O. -/
structure DisputesOutput where
  state : DisputesState
  assignments : AvailAssignments
  offendersMark : List (List UInt8)

/-- K(a) (GP §10.2): κ when a = ⌊τ/𝖤⌋, λ otherwise. -/
def judgeKeys (params : Params) (i : DisputesInput) (a : Nat) : List (List UInt8) :=
  if a = i.slot / params.epochLen then i.activeEd else i.previousEd

/-- V(a, **j**) (GP eq. `verdicts`): ⊤ when the positive judgments number ⌊2/3·|**k**|⌋ + 1, ⊥ when
    they are none, ∅ when they number ⌊1/3·|**k**|⌋, and undefined otherwise. -/
def verdictOutcome (k : Nat) (votes : List Judgment) : Option Outcome :=
  let t := (votes.filter (·.valid)).length
  if t = 2 * k / 3 + 1 then some .good
  else if t = 0 then some .bad
  else if t = k / 3 then some .wonky
  else none

/-- The conditions on one verdict (r, a, **j**) (GP §10.2): a ∈ ⌊τ/𝖤⌋ − ℕ_2, **j** ordered and
    unique by judge index, |**j**| = ⌊2/3·|**k**|⌋ + 1, every judge index below |**k**| and every
    signature valid, r not already judged, and V(a, **j**) defined. Returns (r, V(a, **j**)). -/
def checkVerdict (params : Params) (crypto : Crypto) (i : DisputesInput) (ψ : DisputesState)
    (v : Verdict) : Except DisputesError (List UInt8 × Outcome) := do
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
  let some o := verdictOutcome k.length v.votes | throw .badVoteSplit
  return (r, o)

/-- ψ_G', ψ_B', ψ_W' (GP eqs. `goodsetdef`–`wonkysetdef`): each set assimilates the report
    hashes of its verdicts. -/
def assimilate (ψ : DisputesState) (verdicts : List (List UInt8 × Outcome)) : DisputesState :=
  verdicts.foldl (init := ψ) fun s (r, o) =>
    match o with
    | .good => { s with good := s.good.insert r }
    | .bad => { s with bad := s.bad.insert r }
    | .wonky => { s with wonky := s.wonky.insert r }

/-- ρ^‡ (GP eq. `removenonpositive`): clear each core whose assigned report's hash
    ℋ((ρ[c]_g)_r) has a bad or wonky verdict. -/
def clearNonPositive (ρ : AvailAssignments) (verdicts : List (List UInt8 × Outcome)) :
    AvailAssignments :=
  ρ.map fun
    | none => none
    | some a =>
      let h := (Blake2b.hash256 ⟨a.guarantee.report.encode.toArray⟩).toList
      if verdicts.any fun (r, o) => r == h && (o == .bad || o == .wonky) then none else some a

/-- The disputes transition (GP §10): check 𝔼_D against τ, κ, λ and ψ, and give ψ', ρ^‡ and H_O.

    * Verdicts are ordered and unique by report hash, and each satisfies `checkVerdict`.
    * Culprits are ordered and unique by key; each (r, f, s) has r ∈ ψ_B', f ∈ **k** and
      s ∈ 𝕍̄_f⟨X_G ⌢ r⟩.
    * Faults are ordered and unique by key; each (r, v, f, s) has r ∈ ψ_B' ⇔ r ∉ ψ_G' ⇔ v (read as
      a chain of two equivalences), f ∈ **k** and s ∈ 𝕍̄_f⟨X_v ⌢ r⟩.
    * Every good verdict has a fault for its report.

    **k** = {i_e | i ∈ λ ∪ κ} ∖ ψ_O. A key outside it is reported as already an offender when it is
    in ψ_O, and as an unknown guarantor or auditor otherwise. -/
def disputesTransition (params : Params) (crypto : Crypto) (i : DisputesInput) (ψ : DisputesState)
    (ρ : AvailAssignments) (x : Disputes) : Except DisputesError DisputesOutput := do
  unless orderedUniqBy (·.target.toList) x.verdicts do throw .verdictsNotSortedUnique
  let verdicts ← x.verdicts.mapM (checkVerdict params crypto i ψ)
  let ψ' := assimilate ψ verdicts
  let keys := i.previousEd ++ i.activeEd
  unless orderedUniqBy (·.key.toList) x.culprits do throw .culpritsNotSortedUnique
  for c in x.culprits do
    let r := c.target.toList
    let f := c.key.toList
    unless ψ'.bad.contains r do throw .culpritsVerdictNotBad
    if ψ.offenders.contains f then throw .offenderAlreadyReported
    unless keys.contains f do throw .badGuarantorKey
    unless crypto.edVerify f (Xguarantee ++ r) c.signature.toList do throw .badSignature
  unless orderedUniqBy (·.key.toList) x.faults do throw .faultsNotSortedUnique
  for flt in x.faults do
    let r := flt.target.toList
    let f := flt.key.toList
    let inBad := ψ'.bad.contains r
    let notGood := !ψ'.good.contains r
    unless inBad == notGood && notGood == flt.valid do throw .faultVerdictWrong
    if ψ.offenders.contains f then throw .offenderAlreadyReported
    unless keys.contains f do throw .badAuditorKey
    unless crypto.edVerify f (Xvalidif flt.valid ++ r) flt.signature.toList do throw .badSignature
  for (r, o) in verdicts do
    if o == .good && !x.faults.any (·.target.toList == r) then throw .notEnoughFaults
  let mark := x.culprits.map (·.key.toList) ++ x.faults.map (·.key.toList)
  return { state := { ψ' with offenders := mark.foldl (·.insert ·) ψ.offenders },
           assignments := clearNonPositive ρ verdicts, offendersMark := mark }

end JAM
