import JAM.Disputes

/-!
# Package availability assurances (GP v0.8.0 §11.2)

The assurances extrinsic 𝔼_A (eq. `xtassurances`), the newly available reports **R** (eq.
`availableworkreports`) and the intermediate assignments ρ^‡‡ = ρ after assurances (eq.
`availassignmentspostassurancesdef`), from the assignments ρ^‡ left by the disputes transition
(`JAM.disputesTransition`).

Signatures are checked with `Crypto.edVerify`; the validator sets enter through κ's Ed25519 keys
and the size of κ'.

The paper names no errors and gives no order between the conditions. The errors are the test
vectors' names. Each assurance is checked in turn, its conditions in the order §11.2.1 states
them: the anchor, the order of assurers, the signature, then the bits.
-/

namespace JAM

/-- X_A = `$jam_available` (GP eq. `assurancesig`). -/
def Xavailable : List UInt8 := contextString "$jam_available"

/-- Why an assurances extrinsic is invalid. The paper names no errors; these are the vectors'. -/
inductive AssurancesError where
  | badAttestationParent
  | badValidatorIndex
  | coreNotEngaged
  | badSignature
  | notSortedOrUniqueAssurers
  deriving BEq, Repr

/-- What the assurances transition reads besides ρ^‡ and 𝔼_A. -/
structure AssurancesInput where
  /-- H_T, the block's timeslot. -/
  slot : Nat
  /-- H_P, the parent header hash. -/
  parent : Hash
  /-- (κ_v)_e, the prior active set's Ed25519 keys. -/
  activeEd : List (List UInt8)
  /-- |κ'|, the size of the posterior active set. -/
  postActiveCount : Nat

/-- The message an assurance signs: X_A ⌢ ℋ(ℰ(H_P, a_f)) (GP eq. `assurancesig`). -/
def assuranceMessage (parent : Hash) (bits : List Bool) : List UInt8 :=
  Xavailable ++ (Blake2b.hash256 ⟨(Codec.blob parent ++ encodeBits bits).toArray⟩).toList

/-- One assurance's conditions (GP §11.2.1): a_a = H_P; a_v ∈ ℕ_{|κ|} and above the previous
    assurer `prev`; a_s ∈ 𝕍̄_{κ[a_v]_e}⟨X_A ⌢ ℋ(ℰ(H_P, a_f))⟩; and a set bit only on a core
    with an assignment in ρ^‡. -/
def checkAssurance (crypto : Crypto) (i : AssurancesInput) (ρ : AvailAssignments)
    (prev : Option Nat) (a : Assurance) : Except AssurancesError Unit := do
  unless a.anchor == i.parent do throw .badAttestationParent
  unless a.assurer < i.activeEd.length do throw .badValidatorIndex
  if let some p := prev then unless p < a.assurer do throw .notSortedOrUniqueAssurers
  unless crypto.edVerify (i.activeEd.getD a.assurer []) (assuranceMessage i.parent a.bitfield)
      a.signature.toList do throw .badSignature
  for c in List.range ρ.length do
    if a.bitfield.getD c false && (ρ.getD c none).isNone then throw .coreNotEngaged

/-- The assurances transition (GP §11.2): check 𝔼_A, then give **R**, the reports of the cores
    (in core order) that more than two thirds of |κ| assure, and ρ after assurances, which clears
    a core when it was empty, its report is in **R** (reports compared by their encoding), it timed out
    (H_T ≥ t + 𝖴) or |κ| ≠ |κ'|. -/
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
