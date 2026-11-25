import Std.Data.ExtTreeMap
import JAM.Codec
import JAM.Constants
import JAM.Blake2b

/-!
# Service accounts (GP v0.8.0 §9, `sec:accounts`)

𝔸 ≡ (**s**, **p**, **l**, f, c, b, g, m, r, a, p) with the dependent terms i, o and t
(eq. `serviceaccount`, eq. `deposits`), and the historical lookup Λ (eq. `historicallookup`).

Dictionaries are extensional finite maps (`Std.ExtTreeMap`) keyed by octet sequences as lists, so
two accounts with the same lookups are equal. Hashes are keys of the preimage dictionary; storage
and requests share one dictionary keyed by the hash part of their state keys (see
`ServiceAccount`).
-/

namespace JAM

/-- (hash, length) pairs, ordered lexicographically. -/
instance : Ord (List UInt8 × Nat) := lexOrd

/-- A service account 𝔸 (GP eq. `serviceaccount`), in the form its state serialization T(σ) keeps
    (GP §D.1, merklization eq. C and the service rows of eq. `serialization`).

* **p** (preimages, ℍ → 𝔹) is kept as a dictionary keyed by hash.
* **s** (storage) and **l** (requests) share one dictionary `entries`, keyed by the 27 octets of
  ℋ(**x**) that the state key C(s, **x**) keeps: storage value **v** under **k** is held raw under
  `storageKey k` (**x** = ℰ_4(2³²−1) ⌢ **k**), and request history **t** of (h, z) is held as
  ℰ(↕[ℰ_4(x) | x ← **t**]) under `requestKey h z` (**x** = ℰ_4(z) ⌢ h), exactly as T(σ) holds them.
  The paper licenses this (merklization.tex:116: storage keys cannot be inspected or enumerated,
  so implementations need not store them) and it is faithful to σ given that C has no collision
  on the keys that occur, the paper's own assumption (merklization.tex:19); see
  `docs/storage-key-design.md`.
* a_i and a_o, dependent terms of **s** and **l** in GP eq. `deposits`, are carried as the fields
  `items` and `octets`, since |**k**| is no longer known. Every mutation (`storageWrite`,
  `requestSet`, `requestErase`) updates them by the change it makes to the formula's sums, so on
  every state built by the model's transitions they equal
  a_i = 2·|**l**| + |**s**| and a_o = Σ_{(h,z)∈K(**l**)} (81 + z) + Σ_{(x,y)∈**s**} (34 + |y| + |x|).
  The empty account has a_i = a_o = 0. -/
structure ServiceAccount where
  /-- **s** and **l**, keyed by the hash part of their state key (`storageKey`, `requestKey`) -/
  entries : Std.ExtTreeMap (List UInt8) (List UInt8) := ∅
  /-- **p**: preimages, ℍ → 𝔹 -/
  preimages : Std.ExtTreeMap (List UInt8) (List UInt8) := ∅
  /-- a_i: the number of items, 2·|**l**| + |**s**| (GP eq. `deposits`), carried -/
  items : Nat := 0
  /-- a_o: the octet footprint, Σ (81 + z) + Σ (34 + |y| + |x|) (GP eq. `deposits`), carried -/
  octets : Nat := 0
  /-- f: gratis storage offset -/
  gratis : Nat := 0
  /-- c: code hash -/
  codeHash : List UInt8
  /-- b: balance -/
  balance : Nat
  /-- u: supervisor (GP v0.8.1 eq. `serviceaccount`, §9 "Supervisors") -/
  supervisor : Nat := 0
  /-- the supervisor's creation slot, recorded with u (GP v0.8.1 eq. `serviceaccount`) -/
  supervisorCreated : Nat := 0
  /-- the supervisor balance, transferable only by the supervisor and counted with b against the
      threshold balance (GP v0.8.1 eq. `serviceaccount`, §9 "Supervisors") -/
  supervisorBalance : Nat := 0
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

/-! ## Accessors for storage and requests

Every use of **s** and **l** goes through these. Each takes the key the paper's caller supplies
(**k**, or (h, z)) and looks up the hash part of its state key. -/

/-- The 27 octets of ℋ(**x**) that a state key C(s, **x**) keeps (GP §D.1, merklization eq. C):
    C(s, **x**) interleaves ℰ_4(s) with the first 27 octets of ℋ(**x**). -/
def stateKeyHash (x : List UInt8) : List UInt8 := ((Blake2b.hash256 ⟨x.toArray⟩).toList).take 27

/-- The hash part of storage key **k**'s state key, C(s, ℰ_4(2³²−1) ⌢ **k**) (GP §D.1). -/
def storageKey (k : List UInt8) : List UInt8 := stateKeyHash (Codec.fixed 4 (2 ^ 32 - 1) ++ k)

/-- The hash part of request (h, z)'s state key, C(s, ℰ_4(z) ⌢ h) (GP §D.1). -/
def requestKey (h : List UInt8) (z : Nat) : List UInt8 := stateKeyHash (Codec.fixed 4 z ++ h)

/-- ℰ(↕[ℰ_4(x) | x ← **t**]), the serialized request history (GP §D.1, the request rows of T(σ)). -/
def encodeSlots (t : List Nat) : List UInt8 := Codec.varSeq (Codec.fixed 4) t

/-- The inverse of `encodeSlots` on ⟦ℕ_T⟧_{:3}: a length octet 0–3 followed by that many 4-octet
    little-endian timeslots, and nothing else. Any other value is not a request history. -/
def decodeSlots : List UInt8 → Option (List Nat)
  | [n] => if n = 0 then some [] else none
  | [n, a0, a1, a2, a3] => if n = 1 then some [PVM.Num.decodeLE [a0, a1, a2, a3]] else none
  | [n, a0, a1, a2, a3, b0, b1, b2, b3] =>
    if n = 2 then some [PVM.Num.decodeLE [a0, a1, a2, a3], PVM.Num.decodeLE [b0, b1, b2, b3]]
    else none
  | [n, a0, a1, a2, a3, b0, b1, b2, b3, c0, c1, c2, c3] =>
    if n = 3 then some [PVM.Num.decodeLE [a0, a1, a2, a3], PVM.Num.decodeLE [b0, b1, b2, b3],
      PVM.Num.decodeLE [c0, c1, c2, c3]]
    else none
  | _ => none

/-- **s**[**k**]: the storage value under **k**, if any. -/
def storageGet (a : ServiceAccount) (k : List UInt8) : Option (List UInt8) :=
  a.entries.get? (storageKey k)

/-- The account after Ω_W writes **v** under **k** (GP Appendix B, Ω_W): **k** is removed when
    **v** is empty, and set to **v** otherwise. a_i and a_o change as GP eq. `deposits` does: the
    old entry, if any, leaves |**s**| and the sum (34 + |**k**| + |old|); a non-empty **v** adds 1
    and (34 + |**k**| + |**v**|). -/
def storageWrite (a : ServiceAccount) (k v : List UInt8) : ServiceAccount :=
  let (i0, o0) := match a.storageGet k with
    | some old => (a.items - 1, a.octets - (34 + k.length + old.length))
    | none => (a.items, a.octets)
  if v.length = 0 then { a with entries := a.entries.erase (storageKey k), items := i0, octets := o0 }
  else { a with entries := a.entries.insert (storageKey k) v, items := i0 + 1,
                octets := o0 + (34 + k.length + v.length) }

/-- The bound of ℕ_L, the request lengths: ℕ_L = ℕ_{2³² − 2}, below the state-key discriminators
    2³² − 2 and 2³² − 1 (GP v0.8.1 eq. `serviceaccount` and its definition of ℕ_L, GP #542). -/
def requestLenBound : Nat := 2 ^ 32 - 2

/-- **l**[h, z]: the request history of (h, z), if any. The keys of **l** are (ℍ, ℕ_L)
    (`requestLenBound`, GP v0.8.1 eq. `serviceaccount`), so z ∉ ℕ_L has none. A stored value that does not
    decode as ⟦ℕ_T⟧_{:3} (only a state not built by the model can hold one) reads as none: Adam's
    decision of 2026-11-15 (`docs/storage-key-design.md`). -/
def requestGet (a : ServiceAccount) (h : List UInt8) (z : Nat) : Option (List Nat) :=
  if z < requestLenBound then (a.entries.get? (requestKey h z)).bind decodeSlots else none

/-- The account with **l**[h, z] set to `t`. A new key adds 2 to a_i and 81 + z to a_o
    (GP eq. `deposits`). "New" means `requestGet` finds none: an undecodable stored value (only an
    invalid loaded state holds one; GP v0.8.0 does not cover such states) counts as absent, so it
    is overwritten and a_i, a_o grow as for a new key, consistently with `requestGet`. -/
def requestSet (a : ServiceAccount) (h : List UInt8) (z : Nat) (t : List Nat) : ServiceAccount :=
  let (i0, o0) := match a.requestGet h z with
    | some _ => (a.items, a.octets)
    | none => (a.items + 2, a.octets + (81 + z))
  { a with entries := a.entries.insert (requestKey h z) (encodeSlots t), items := i0, octets := o0 }

/-- The account with (h, z) removed from **l**, which takes 2 from a_i and 81 + z from a_o
    (GP eq. `deposits`). Without a request for (h, z) the account is unchanged; an undecodable
    stored value (invalid loaded states only) counts as absent, as in `requestGet`, so it is kept
    and a_i, a_o do not change. -/
def requestErase (a : ServiceAccount) (h : List UInt8) (z : Nat) : ServiceAccount :=
  match a.requestGet h z with
  | some _ => { a with entries := a.entries.erase (requestKey h z), items := a.items - 2,
                       octets := a.octets - (81 + z) }
  | none => a

/-- Λ(a, t, h): the preimage of h if a held it at timeslot t (GP eq. `historicallookup`). -/
def historicalLookup (a : ServiceAccount) (t : Nat) (h : List UInt8) : Option (List UInt8) := do
  let p ← a.preimages.get? h
  let l ← a.requestGet h p.length
  if availableAt l t then some p else none

/-! ## Accessor lemmas -/

private theorem decodeLE_four (x : Nat) :
    PVM.Num.decodeLE (Codec.fixed 4 x) = x % 2 ^ 32 := by
  simp only [Codec.fixed, PVM.Num.encodeLE, PVM.Num.decodeLE, UInt8.toNat_ofNat']
  omega

private theorem fixed_four (x : Nat) : ∃ a0 a1 a2 a3, Codec.fixed 4 x = [a0, a1, a2, a3] :=
  ⟨_, _, _, _, rfl⟩

/-- `decodeSlots` inverts `encodeSlots` on ⟦ℕ_T⟧_{:3}. -/
theorem decodeSlots_encodeSlots (t : List Nat) (hl : t.length ≤ 3) (hx : ∀ x ∈ t, x < 2 ^ 32) :
    decodeSlots (encodeSlots t) = some t := by
  match t, hl with
  | [], _ => rfl
  | [x], _ =>
    obtain ⟨a0, a1, a2, a3, e⟩ := fixed_four x
    have h0 := decodeLE_four x
    rw [e] at h0
    rw [show encodeSlots [x] = [1, a0, a1, a2, a3] by
      simp only [encodeSlots, Codec.varSeq, List.map, List.flatten, e, List.length]; rfl]
    simp [decodeSlots, h0, Nat.mod_eq_of_lt (hx x (by simp))]
  | [x, y], _ =>
    obtain ⟨a0, a1, a2, a3, e⟩ := fixed_four x
    obtain ⟨b0, b1, b2, b3, f⟩ := fixed_four y
    have h0 := decodeLE_four x; have h1 := decodeLE_four y
    rw [e] at h0; rw [f] at h1
    rw [show encodeSlots [x, y] = [2, a0, a1, a2, a3, b0, b1, b2, b3] by
      simp only [encodeSlots, Codec.varSeq, List.map, List.flatten, e, f, List.length]; rfl]
    simp [decodeSlots, h0, h1, Nat.mod_eq_of_lt (hx x (by simp)), Nat.mod_eq_of_lt (hx y (by simp))]
  | [x, y, w], _ =>
    obtain ⟨a0, a1, a2, a3, e⟩ := fixed_four x
    obtain ⟨b0, b1, b2, b3, f⟩ := fixed_four y
    obtain ⟨c0, c1, c2, c3, g⟩ := fixed_four w
    have h0 := decodeLE_four x; have h1 := decodeLE_four y; have h2 := decodeLE_four w
    rw [e] at h0; rw [f] at h1; rw [g] at h2
    rw [show encodeSlots [x, y, w] = [3, a0, a1, a2, a3, b0, b1, b2, b3, c0, c1, c2, c3] by
      simp only [encodeSlots, Codec.varSeq, List.map, List.flatten, e, f, g, List.length]; rfl]
    simp [decodeSlots, h0, h1, h2, Nat.mod_eq_of_lt (hx x (by simp)),
      Nat.mod_eq_of_lt (hx y (by simp)), Nat.mod_eq_of_lt (hx w (by simp))]

/-- Representation lemma: **s**[**k**] is the `entries` value under **k**'s state key. -/
theorem storageGet_eq (a : ServiceAccount) (k : List UInt8) :
    a.storageGet k = a.entries.get? (storageKey k) := rfl

/-- Representation lemma: **l**[h, z] is the decoded `entries` value under (h, z)'s state key. -/
theorem requestGet_eq (a : ServiceAccount) (h : List UInt8) (z : Nat) :
    a.requestGet h z = if z < requestLenBound then (a.entries.get? (requestKey h z)).bind decodeSlots
      else none := rfl

theorem storageGet_write_same (a : ServiceAccount) (k v : List UInt8) :
    (a.storageWrite k v).storageGet k = if v.length = 0 then none else some v := by
  unfold storageWrite storageGet
  split <;> split <;> simp [Std.ExtTreeMap.get?_eq_getElem?, *]

/-- Writing **k** leaves every key with a different state key unchanged. -/
theorem storageGet_write_other (a : ServiceAccount) (k k' v : List UInt8)
    (h : storageKey k ≠ storageKey k') : (a.storageWrite k v).storageGet k' = a.storageGet k' := by
  unfold storageWrite storageGet
  split <;> split <;>
    simp [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_erase,
      Std.ExtTreeMap.getElem?_insert, h]

/-- Setting (h, z) to a history in ⟦ℕ_T⟧_{:3}, with z ∈ ℕ_L, reads back that history. -/
theorem requestGet_set_same (a : ServiceAccount) (h : List UInt8) (z : Nat) (t : List Nat)
    (hz : z < requestLenBound) (hl : t.length ≤ 3) (hx : ∀ x ∈ t, x < 2 ^ 32) :
    (a.requestSet h z t).requestGet h z = some t := by
  unfold requestSet
  split <;>
    simp [requestGet, hz, Std.ExtTreeMap.get?_eq_getElem?, decodeSlots_encodeSlots t hl hx]

theorem requestGet_set_other (a : ServiceAccount) (h h' : List UInt8) (z z' : Nat) (t : List Nat)
    (hk : requestKey h z ≠ requestKey h' z') :
    (a.requestSet h z t).requestGet h' z' = a.requestGet h' z' := by
  unfold requestSet
  split <;>
    simp [requestGet, Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert, hk]

theorem requestGet_erase_same (a : ServiceAccount) (h : List UInt8) (z : Nat) :
    (a.requestErase h z).requestGet h z = none := by
  unfold requestErase
  split
  · simp [requestGet, Std.ExtTreeMap.get?_eq_getElem?]
  · assumption

theorem requestGet_erase_other (a : ServiceAccount) (h h' : List UInt8) (z z' : Nat)
    (hk : requestKey h z ≠ requestKey h' z') :
    (a.requestErase h z).requestGet h' z' = a.requestGet h' z' := by
  unfold requestErase
  split
  · simp [requestGet, Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_erase, hk]
  · rfl

/-- Ω_W changes only **s**, a_o and a_i. -/
theorem storageWrite_frame (a : ServiceAccount) (k v : List UInt8) :
    let a' := a.storageWrite k v
    a'.preimages = a.preimages ∧ a'.gratis = a.gratis ∧
      a'.codeHash = a.codeHash ∧ a'.balance = a.balance ∧ a'.minAccGas = a.minAccGas ∧
      a'.minMemoGas = a.minMemoGas ∧ a'.created = a.created ∧ a'.lastAcc = a.lastAcc ∧
      a'.parent = a.parent := by
  unfold storageWrite; split <;> split <;> simp

/-- Setting a request leaves storage unchanged, for keys whose state keys differ. -/
theorem storageGet_requestSet (a : ServiceAccount) (h : List UInt8) (z : Nat) (t : List Nat)
    (k : List UInt8) (hk : requestKey h z ≠ storageKey k) :
    (a.requestSet h z t).storageGet k = a.storageGet k := by
  unfold requestSet
  split <;> simp [storageGet, Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert, hk]

theorem storageGet_requestErase (a : ServiceAccount) (h : List UInt8) (z : Nat) (k : List UInt8)
    (hk : requestKey h z ≠ storageKey k) :
    (a.requestErase h z).storageGet k = a.storageGet k := by
  unfold requestErase
  split
  · simp [storageGet, Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_erase, hk]
  · rfl

end ServiceAccount

/-- 𝐝 ∈ ⟨ℕ_S → 𝔸⟩: the service accounts (GP eq. `serviceaccounts`). -/
abbrev Accounts := Std.ExtTreeMap Nat ServiceAccount

/-- The effective supervisor of s in **d** (GP v0.8.1 eq. `effectivesupervisor`): the designated
    supervisor u = **d**[s]_u if u ∈ K(**d**) and **d**[u]_r equals the recorded creation slot,
    and s itself otherwise. Defined for s ∈ K(**d**); for any other s it is s. -/
def effectiveSupervisor (d : Accounts) (s : Nat) : Nat :=
  match d.get? s with
  | none => s
  | some a =>
    match d.get? a.supervisor with
    | some su => if su.created = a.supervisorCreated then a.supervisor else s
    | none => s

end JAM
