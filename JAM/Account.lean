import Std.Data.ExtTreeMap
import JAM.Codec
import JAM.Constants

/-!
# Service accounts (GP v0.8.0 §9, `sec:accounts`)

𝔸 ≡ (**s**, **p**, **l**, f, c, b, g, m, r, a, p) with the dependent terms i, o and t
(eq. `serviceaccount`, eq. `deposits`), and the historical lookup Λ (eq. `historicallookup`).

Dictionaries are extensional finite maps (`Std.ExtTreeMap`) keyed by octet sequences as lists, so
two accounts with the same lookups are equal. Hashes are keys of the preimage dictionary and, with a
length, of the request dictionary.
-/

namespace JAM

/-- (hash, length) keys of the request dictionary, ordered lexicographically. -/
instance : Ord (List UInt8 × Nat) := lexOrd

/-- A service account 𝔸 (GP eq. `serviceaccount`). -/
structure ServiceAccount where
  /-- **s**: storage, 𝔹 → 𝔹 -/
  storage : Std.ExtTreeMap (List UInt8) (List UInt8) := ∅
  /-- **p**: preimages, ℍ → 𝔹 -/
  preimages : Std.ExtTreeMap (List UInt8) (List UInt8) := ∅
  /-- **l**: preimage requests, (ℍ, ℕ_L) → ⟦ℕ_T⟧_{:3} -/
  requests : Std.ExtTreeMap (List UInt8 × Nat) (List Nat) := ∅
  /-- f: gratis storage offset -/
  gratis : Nat := 0
  /-- c: code hash -/
  codeHash : List UInt8
  /-- b: balance -/
  balance : Nat
  /-- g: minimum gas per accumulated work item -/
  minAccGas : Nat
  /-- m: minimum gas per deferred transfer -/
  minMemoGas : Nat
  /-- r: creation timeslot -/
  created : Nat := 0
  /-- a: most recent accumulation timeslot -/
  lastAcc : Nat := 0
  /-- p: parent service -/
  parent : Nat := 0

namespace ServiceAccount

open Constants

/-- a_i = 2·|**l**| + |**s**| (GP eq. `deposits`). -/
def items (a : ServiceAccount) : Nat := 2 * a.requests.size + a.storage.size

/-- a_o = Σ_{(h, z) ∈ K(**l**)} (81 + z) + Σ_{(x, y) ∈ **s**} (34 + |y| + |x|) (GP eq. `deposits`). -/
def octets (a : ServiceAccount) : Nat :=
  (a.requests.keys.map fun (_, z) => 81 + z).sum +
    (a.storage.toList.map fun (x, y) => 34 + y.length + x.length).sum

/-- a_t = max(0, 𝖡_S + 𝖡_I·a_i + 𝖡_L·a_o − a_f), the threshold balance (GP eq. `deposits`). -/
def minBalance (a : ServiceAccount) : Nat :=
  Cbasedeposit + Citemdeposit * a.items + Cbytedeposit * a.octets - a.gratis

/-- I(**l**, t), whether a preimage with history **l** is available at t (GP eq. `historicallookup`). -/
def availableAt : List Nat → Nat → Bool
  | [], _ => false
  | [x], t => x ≤ t
  | [x, y], t => x ≤ t && t < y
  | [x, y, z], t => (x ≤ t && t < y) || z ≤ t
  | _, _ => false

/-- Λ(a, t, h): the preimage of h if a held it at timeslot t (GP eq. `historicallookup`). -/
def historicalLookup (a : ServiceAccount) (t : Nat) (h : List UInt8) : Option (List UInt8) := do
  let p ← a.preimages.get? h
  let l ← a.requests.get? (h, p.length)
  if availableAt l t then some p else none

end ServiceAccount

/-- 𝐝 ∈ ⟨ℕ_S → 𝔸⟩: the service accounts (GP eq. `serviceaccounts`). -/
abbrev Accounts := Std.ExtTreeMap Nat ServiceAccount

end JAM
