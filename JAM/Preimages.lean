import JAM.Fast.Blake2b
import JAM.Accumulation

/-!
# Preimage integration (GP v0.8.1 §12.4, `Preimage Integration`)

The preimages extrinsic $\mathbf{E}_P \in [\![ (\mathbb{N}_S, \mathbb{B}) ]\!]$ must be ordered and
free of duplicates (eq. `preimagesareordered`), and every pair must be providable in the prior
state, $Y(\delta, s, \mathbf{i})$ (§12.2). The posterior accounts are then
$I(\delta^\dagger, \mathbf{E}_P)$, with $I$ the integration function of §12.2
(`JAM.integrateProvisions`) applied to the accounts after accumulation.
-/

namespace JAM

/-- Why a preimages extrinsic is invalid. The paper does not name the errors; these are the
    vectors' names. -/
inductive PreimageError where
  /-- $\mathbf{E}_P \neq [i \in \mathbf{E}_P]$-ordered-unique (eq. `preimagesareordered`). -/
  | notSortedUnique
  /-- Some $(s, \mathbf{i}) \in \mathbf{E}_P$ fails $Y(\delta, s, \mathbf{i})$. -/
  | unneeded
  /-- $|\mathbf{E}_P| > \mathsf{X}_P$'s length bound (GP v0.8.1 eq. `xtpreimages`). Not named by
      the paper or the v0.8.0 vectors. -/
  | tooMany
  /-- $\Sigma\, |\mathbf{i}|$ over $\mathbf{E}_P$ exceeds the data bound (GP v0.8.1 eq.
      `maxxtpreimagesdatasize`). Not named by the paper or the v0.8.0 vectors. -/
  | tooMuchData
  deriving BEq, Repr

/-- The order on $\mathbf{E}_P$'s pairs: by service index, then by the data, lexicographically. -/
def preimageLt (a b : Nat × List UInt8) : Bool := a.1 < b.1 || (a.1 == b.1 && decide (a.2 < b.2))

/-- $\mathbf{E}_P = [i \in \mathbf{E}_P]$-ordered-unique: strictly ascending
    (GP eq. `preimagesareordered`). -/
def preimagesOrdered : List (Nat × List UInt8) → Bool
  | a :: b :: rest => preimageLt a b && preimagesOrdered (b :: rest)
  | _ => true

/-- $Y(\mathbf{d}, s, \mathbf{i})$ (GP §12.2): $s$ has an account whose request for
    $(\mathcal{H}(\mathbf{i}), |\mathbf{i}|)$ is $[]$. -/
def providable (d : Accounts) (s : Nat) (i : List UInt8) : Bool :=
  match d.get? s with
  | some a => a.requestGet (Blake2b.hash256 ⟨i.toArray⟩).toList i.length == some []
  | none => false

/-- The preimage transition (GP v0.8.1 §12.4): check $\mathbf{E}_P$ (at most `Cmaxxtpreimageslen` pairs and
    `Cmaxxtpreimagesdatasize` data octets, eq. `xtpreimages` and `maxxtpreimagesdatasize`; ordered;
    providable) against the prior accounts $\delta$, then integrate it into the accounts $\delta^\dagger$ after
    accumulation at timeslot $\tau'$. The paper orders none of the checks (upstream note 25); the
    bounds are checked first. -/
def preimages (prior postAcc : Accounts) (xs : List (Nat × List UInt8)) (slot : Nat) :
    Except PreimageError Accounts :=
  if xs.length > Constants.Cmaxxtpreimageslen then .error .tooMany
  else if (xs.map (·.2.length)).sum > Constants.Cmaxxtpreimagesdatasize then .error .tooMuchData
  else if !preimagesOrdered xs then .error .notSortedUnique
  else if !xs.all fun (s, i) => providable prior s i then .error .unneeded
  else .ok (integrateProvisions slot postAcc (Std.ExtTreeSet.ofList xs))

end JAM
