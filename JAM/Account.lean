import Std.Data.ExtTreeMap
import JAM.Codec
import JAM.Constants
import JAM.Blake2b

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

/-! ## Accessors for storage and requests

T2 and its lemmas state storage and request facts through these accessors rather than through the
dictionaries. The representation is then expected to change: storage and requests re-keyed by the
27-octet hash part of their state key, with a_o and a_i carried (`docs/storage-key-design.md`,
Adam's decision of 2026-11-15). After that change, only the definitions below and the
`*_eq` lemmas need to change. -/

/-- The 27 octets of ℋ(**x**) that a state key C(s, **x**) keeps (GP §D.1, merklization eq. C):
    C(s, **x**) interleaves ℰ_4(s) with the first 27 octets of ℋ(**x**). -/
def stateKeyHash (x : List UInt8) : List UInt8 := ((Blake2b.hash256 ⟨x.toArray⟩).toList).take 27

/-- The hash part of storage key **k**'s state key, C(s, ℰ_4(2³²−1) ⌢ **k**) (GP §D.1). -/
def storageKey (k : List UInt8) : List UInt8 := stateKeyHash (Codec.fixed 4 (2 ^ 32 - 1) ++ k)

/-- The hash part of request (h, z)'s state key, C(s, ℰ_4(z) ⌢ h) (GP §D.1). -/
def requestKey (h : List UInt8) (z : Nat) : List UInt8 := stateKeyHash (Codec.fixed 4 z ++ h)

/-- **s**[**k**]: the storage value under **k**, if any. -/
def storageGet (a : ServiceAccount) (k : List UInt8) : Option (List UInt8) := a.storage.get? k

/-- The account after Ω_W writes **v** under **k** (GP Appendix B, Ω_W): **k** is removed when
    **v** is empty, and set to **v** otherwise. -/
def storageWrite (a : ServiceAccount) (k v : List UInt8) : ServiceAccount :=
  if v.length = 0 then { a with storage := a.storage.erase k }
  else { a with storage := a.storage.insert k v }

/-- **l**[h, z]: the request history of (h, z), if any. -/
def requestGet (a : ServiceAccount) (h : List UInt8) (z : Nat) : Option (List Nat) :=
  a.requests.get? (h, z)

/-- The account with **l**[h, z] set to `t`. -/
def requestSet (a : ServiceAccount) (h : List UInt8) (z : Nat) (t : List Nat) : ServiceAccount :=
  { a with requests := a.requests.insert (h, z) t }

/-- The account with (h, z) removed from **l**. -/
def requestErase (a : ServiceAccount) (h : List UInt8) (z : Nat) : ServiceAccount :=
  { a with requests := a.requests.erase (h, z) }

/-- Representation lemma for the current k-keyed dictionary. It goes away when storage is
    re-keyed. -/
theorem storageGet_eq (a : ServiceAccount) (k : List UInt8) : a.storageGet k = a.storage.get? k := rfl

/-- Representation lemma for the current (h, z)-keyed dictionary. It goes away when requests are
    re-keyed. -/
theorem requestGet_eq (a : ServiceAccount) (h : List UInt8) (z : Nat) :
    a.requestGet h z = a.requests.get? (h, z) := rfl

theorem storageGet_write_same (a : ServiceAccount) (k v : List UInt8) :
    (a.storageWrite k v).storageGet k = if v.length = 0 then none else some v := by
  unfold storageWrite storageGet
  split
  · simp [Std.ExtTreeMap.get?_eq_getElem?, *]
  · simp [Std.ExtTreeMap.get?_eq_getElem?, *]

/-- Writing **k** leaves every key with a different state key unchanged. The hypothesis is on
    state keys, so the statement survives the re-keying. -/
theorem storageGet_write_other (a : ServiceAccount) (k k' v : List UInt8)
    (h : storageKey k ≠ storageKey k') : (a.storageWrite k v).storageGet k' = a.storageGet k' := by
  have hne : k ≠ k' := fun e => h (e ▸ rfl)
  unfold storageWrite storageGet
  split
  · simp [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_erase, hne]
  · simp [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert, hne]

theorem requestGet_set_same (a : ServiceAccount) (h : List UInt8) (z : Nat) (t : List Nat) :
    (a.requestSet h z t).requestGet h z = some t := by
  simp [requestSet, requestGet, Std.ExtTreeMap.get?_eq_getElem?]

theorem requestGet_set_other (a : ServiceAccount) (h h' : List UInt8) (z z' : Nat) (t : List Nat)
    (hk : requestKey h z ≠ requestKey h' z') :
    (a.requestSet h z t).requestGet h' z' = a.requestGet h' z' := by
  have hne : (h, z) ≠ (h', z') := fun e => hk (by cases e; rfl)
  simp [requestSet, requestGet, Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert, hne]

theorem requestGet_erase_same (a : ServiceAccount) (h : List UInt8) (z : Nat) :
    (a.requestErase h z).requestGet h z = none := by
  simp [requestErase, requestGet, Std.ExtTreeMap.get?_eq_getElem?]

theorem requestGet_erase_other (a : ServiceAccount) (h h' : List UInt8) (z z' : Nat)
    (hk : requestKey h z ≠ requestKey h' z') :
    (a.requestErase h z).requestGet h' z' = a.requestGet h' z' := by
  have hne : (h, z) ≠ (h', z') := fun e => hk (by cases e; rfl)
  simp [requestErase, requestGet, Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_erase, hne]

/-- Ω_W changes only the storage (and, once they are carried, a_o and a_i). -/
theorem storageWrite_frame (a : ServiceAccount) (k v : List UInt8) :
    let a' := a.storageWrite k v
    a'.preimages = a.preimages ∧ a'.requests = a.requests ∧ a'.gratis = a.gratis ∧
      a'.codeHash = a.codeHash ∧ a'.balance = a.balance ∧ a'.minAccGas = a.minAccGas ∧
      a'.minMemoGas = a.minMemoGas ∧ a'.created = a.created ∧ a'.lastAcc = a.lastAcc ∧
      a'.parent = a.parent := by
  unfold storageWrite; split <;> simp

/-- Setting or erasing a request leaves storage unchanged. -/
theorem storageGet_requestSet (a : ServiceAccount) (h : List UInt8) (z : Nat) (t : List Nat)
    (k : List UInt8) : (a.requestSet h z t).storageGet k = a.storageGet k := rfl

theorem storageGet_requestErase (a : ServiceAccount) (h : List UInt8) (z : Nat) (k : List UInt8) :
    (a.requestErase h z).storageGet k = a.storageGet k := rfl

end ServiceAccount

/-- 𝐝 ∈ ⟨ℕ_S → 𝔸⟩: the service accounts (GP eq. `serviceaccounts`). -/
abbrev Accounts := Std.ExtTreeMap Nat ServiceAccount

end JAM
