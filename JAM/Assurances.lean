import JAM.Fast.Blake2b
import JAM.Disputes

/-!
# Package availability assurances (GP v0.8.1 §11.2)

The assurances extrinsic $\mathbf{E}_A$ (eq. `xtassurances`), the newly available reports $\mathbf{R}$ (eq.
`availableworkreports`) and the intermediate assignments $\availassignmentspostassurances = \rho$ after assurances (eq.
`availassignmentspostassurancesdef`), from the assignments $\availassignmentspostjudgment$ left by the disputes transition
(`JAM.disputesTransition`).

Signatures are checked with `Crypto.edVerify`; the validator sets enter through $\kappa$'s Ed25519 keys
and the size of $\kappa'$.

The paper names no errors and gives no order between the conditions. The errors are the test
vectors' names. Each assurance is checked in turn, its conditions in the order §11.2.1 states
them: the order of assurers, the signature, then the bits. The assurer index's range comes first,
as the signature's key depends on it.

v0.8.1 removes the anchor $a_a$ and its condition $a_a = \mathbf{H}_P$ (GP #562): the signature already covers
$\mathbf{H}_P$. The order condition is $\mathbf{E}_A = [a \in \mathbf{E}_A \text{ ordered and unique by } a_v]$ (GP #574), the same strict
increase of $a_v$ as v0.8.0's.
-/

namespace JAM

/-- $\mathsf{X}_A$ = `$jam_available` (GP eq. `assurancesig`). -/
def Xavailable : List UInt8 := contextString "$jam_available"

/-- Why an assurances extrinsic is invalid. The paper names no errors; these are the vectors'. -/
inductive AssurancesError where
  | badValidatorIndex
  | coreNotEngaged
  | badSignature
  | notSortedOrUniqueAssurers
  deriving BEq, Repr

/-- What the assurances transition reads besides $\availassignmentspostjudgment$ and $\mathbf{E}_A$. -/
structure AssurancesInput where
  /-- $\mathbf{H}_T$, the block's timeslot. -/
  slot : Nat
  /-- $\mathbf{H}_P$, the parent header hash. -/
  parent : Hash
  /-- $(\kappa_v)_e$, the prior active set's Ed25519 keys. -/
  activeEd : List (List UInt8)
  /-- $|\kappa'|$, the size of the posterior active set. -/
  postActiveCount : Nat

/-- The message an assurance signs: $\mathsf{X}_A \frown \mathcal{H}(\mathcal{E}(\mathbf{H}_P, a_f))$ (GP eq. `assurancesig`). -/
def assuranceMessage (parent : Hash) (bits : List Bool) : List UInt8 :=
  Xavailable ++ (Blake2b.hash256 ⟨(Codec.blob parent ++ encodeBits bits).toArray⟩).toList

/-- One assurance's conditions (GP v0.8.1 §11.2.1): $a_v \in \mathbb{N}_{|\kappa|}$ and above the previous assurer
    `prev` (eq. `xtassurances` and the ordered-unique condition);
    $a_s \in \edsignaturebase_{\kappa[a_v]_e}\langle \mathsf{X}_A \frown \mathcal{H}(\mathcal{E}(\mathbf{H}_P, a_f)) \rangle$; and a set bit only on a core with an assignment
    in $\availassignmentspostjudgment$. -/
def checkAssurance (crypto : Crypto) (i : AssurancesInput) (ρ : AvailAssignments)
    (prev : Option Nat) (a : Assurance) : Except AssurancesError Unit := do
  unless a.assurer < i.activeEd.length do throw .badValidatorIndex
  if let some p := prev then unless p < a.assurer do throw .notSortedOrUniqueAssurers
  unless crypto.edVerify (i.activeEd.getD a.assurer []) (assuranceMessage i.parent a.bitfield)
      a.signature.toList do throw .badSignature
  for c in List.range ρ.length do
    if a.bitfield.getD c false && (ρ.getD c none).isNone then throw .coreNotEngaged

/-- The assurances transition (GP v0.8.1 §11.2): check $\mathbf{E}_A$, then give $\mathbf{R}$, the reports of the cores
    (in core order) that more than two thirds of $|\kappa|$ assure, and $\rho$ after assurances, which clears
    a core when it was empty, its report is in $\mathbf{R}$ (reports compared by their encoding), it timed out
    ($\mathbf{H}_T \ge t + \mathsf{U}$) or $|\kappa| \ne |\kappa'|$. -/
def assurances (params : Params) (crypto : Crypto) (i : AssurancesInput) (ρ : AvailAssignments)
    (xs : List Assurance) : Except AssurancesError (List WorkReport × AvailAssignments) := do
  let mut prev : Option Nat := none
  for a in xs do
    checkAssurance crypto i ρ prev a
    prev := some a.assurer
  let count (c : Nat) := (xs.filter fun a => a.bitfield.getD c false).length
  let available (c : Nat) := 3 * count c > 2 * i.activeEd.length
  let R := (List.range ρ.length).filterMap fun c =>
    if available c then (ρ.getD c none).map (·.guarantee.report) else none
  let ρ' := (List.range ρ.length).map fun c =>
    match ρ.getD c none with
    | none => none
    | some p =>
      if R.any (·.encode == p.guarantee.report.encode) || i.slot ≥ p.time + params.assuranceTimeout ||
          i.activeEd.length ≠ i.postActiveCount then none
      else some p
  return (R, ρ')

end JAM
