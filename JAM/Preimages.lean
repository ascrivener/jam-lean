import JAM.Accumulation

/-!
# Preimage integration (GP v0.8.0 §12.4, `Preimage Integration`)

The preimages extrinsic E_P ∈ ⟦(ℕ_S, 𝔹)⟧ must be ordered and free of duplicates
(eq. `preimagesareordered`), and every pair must be providable in the prior state, Y(δ, s, **i**)
(§12.2). The posterior accounts are then I(δ^†, E_P), with I the integration function of §12.2
(`JAM.integrateProvisions`) applied to the accounts after accumulation.
-/

namespace JAM

/-- Why a preimages extrinsic is invalid. The paper does not name the errors; these are the
    vectors' names. -/
inductive PreimageError where
  /-- E_P ≠ [i ∈ E_P]-ordered-unique (eq. `preimagesareordered`). -/
  | notSortedUnique
  /-- Some (s, **i**) ∈ E_P fails Y(δ, s, **i**). -/
  | unneeded
  deriving BEq, Repr

/-- The order on E_P's pairs: by service index, then by the data, lexicographically. -/
def preimageLt (a b : Nat × List UInt8) : Bool := a.1 < b.1 || (a.1 == b.1 && decide (a.2 < b.2))

/-- E_P = [i ∈ E_P]-ordered-unique: strictly ascending (GP eq. `preimagesareordered`). -/
def preimagesOrdered : List (Nat × List UInt8) → Bool
  | a :: b :: rest => preimageLt a b && preimagesOrdered (b :: rest)
  | _ => true

/-- Y(**d**, s, **i**) (GP §12.2): s has an account whose request for (ℋ(**i**), |**i**|) is []. -/
def providable (d : Accounts) (s : Nat) (i : List UInt8) : Bool :=
  match d.get? s with
  | some a => a.requests.get? ((Blake2b.hash256 ⟨i.toArray⟩).toList, i.length) == some []
  | none => false

/-- The preimage transition (GP §12.4): check E_P against the prior accounts δ, then integrate it
    into the accounts δ^† after accumulation at timeslot τ'. -/
def preimages (prior postAcc : Accounts) (xs : List (Nat × List UInt8)) (slot : Nat) :
    Except PreimageError Accounts :=
  if !preimagesOrdered xs then .error .notSortedUnique
  else if !xs.all fun (s, i) => providable prior s i then .error .unneeded
  else .ok (integrateProvisions slot postAcc (Std.ExtTreeSet.ofList xs))

end JAM
