import JAM.Blake2b
import JAM.Codec

/-!
# State Merklization (GP v0.8.0 Appendix D)

The state-key constructor C (§D.1), the node encodings B and L, and the binary Patricia Merkle
trie root M (§D.2). Nodes are 64 octets; bit strings are read most significant bit first
(GP §3, `bits`), so a node's leading bits are the high bits of its first octet.

The serialization T(σ) itself (which state component goes under which key) is not here: it
needs the full state σ. M takes the serialized dictionary, a map from 31-octet state keys to
values.
-/

namespace JAM.Trie

/-- The zero hash ℍ⁰. -/
def zeroHash : List UInt8 := List.replicate 32 0

/-- ℰ_4 of a service index, as four octets. -/
def n4 (s : Nat) : List UInt8 := PVM.Num.encodeLE 4 s

/-- C(i) for i ∈ ℕ_{2^8}: [i, 0, 0, …] (GP §D.1). -/
def keyOfIndex (i : Nat) : List UInt8 := UInt8.ofNat i :: List.replicate 30 0

/-- C(i, s): [i, n₀, 0, n₁, 0, n₂, 0, n₃, 0, 0, …] where n = ℰ_4(s) (GP §D.1). -/
def keyOfService (i s : Nat) : List UInt8 :=
  let n := n4 s
  [UInt8.ofNat i, n[0]!, 0, n[1]!, 0, n[2]!, 0, n[3]!] ++ List.replicate 23 0

/-- C(s, h): [n₀, a₀, n₁, a₁, n₂, a₂, n₃, a₃, a₄, a₅, …, a₂₆] where n = ℰ_4(s) and a = ℋ(h)
    (GP §D.1). -/
def keyOfServiceData (s : Nat) (h : List UInt8) : List UInt8 :=
  let n := n4 s
  let a := (Blake2b.hash256 ⟨h.toArray⟩).toList
  [n[0]!, a[0]!, n[1]!, a[1]!, n[2]!, a[2]!, n[3]!, a[3]!] ++ (a.drop 4).take 23

/-- C(s, **x**) from the 27 octets of ℋ(**x**) it keeps (merklization eq. C), the form in which
    service accounts hold their storage and request keys (`ServiceAccount.entries`). -/
def keyOfServiceHash (s : Nat) (a : List UInt8) : List UInt8 :=
  let n := n4 s
  [n[0]!, a[0]!, n[1]!, a[1]!, n[2]!, a[2]!, n[3]!, a[3]!] ++ (a.drop 4).take 23

/-- B(l, r) = [0] ⌢ bits(l)_{1…} ⌢ bits(r) (GP §D.2), as 64 octets: the first bit of l is
    replaced by the branch marker 0. -/
def branch (l r : List UInt8) : List UInt8 :=
  match l with
  | b :: rest => (b &&& 0x7f) :: rest ++ r
  | [] => r

/-- L(k, v) (GP §D.2), as 64 octets. For |v| ≤ 32 an embedded-value leaf: [1, 0] ⌢ bits(ℰ_1(|v|))_{2…}
    in the first octet, then k, then v padded with zeroes to 32 octets. Otherwise a regular leaf:
    [1, 1, 0, 0, 0, 0, 0, 0], then k, then ℋ(v). -/
def leaf (k v : List UInt8) : List UInt8 :=
  if v.length ≤ 32 then
    UInt8.ofNat (0x80 + v.length) :: k ++ v ++ List.replicate (32 - v.length) 0
  else
    0xc0 :: k ++ (Blake2b.hash256 ⟨v.toArray⟩).toList

/-- The hash of a node's octets. -/
def hashNode (n : List UInt8) : List UInt8 := (Blake2b.hash256 ⟨n.toArray⟩).toList

/-- bit i of a key, most significant first (GP `bits`). -/
def bit (k : List UInt8) (i : Nat) : Bool :=
  (k.getD (i / 8) 0).toNat.testBit (7 - i % 8)

/-- M at bit depth `depth` (GP §D.2): ℍ⁰ for no entries, ℋ(L(k, v)) for one, and otherwise
    ℋ(B(M(l), M(r))) where l and r hold the entries whose next bit is 0 and 1.

    The paper's M strips one bit per level from the dictionary's bit-string keys; here the keys
    stay whole and `depth` counts the bits stripped. `fuel` bounds the depth: distinct 31-octet
    keys separate within 248 bits, so with `fuel = 248` it never runs out on a dictionary of them
    (`root`); on longer keys that agree in their first 248 bits it gives ℍ⁰ there. -/
def merkle : Nat → Nat → List (List UInt8 × List UInt8) → List UInt8
  | _, _, [] => zeroHash
  | _, _, [(k, v)] => hashNode (leaf k v)
  | 0, _, _ => zeroHash
  | fuel + 1, depth, d =>
    let l := d.filter fun (k, _) => !bit k depth
    let r := d.filter fun (k, _) => bit k depth
    hashNode (branch (merkle fuel (depth + 1) l) (merkle fuel (depth + 1) r))

/-! ## Faster compiled form

`merkle` works on `List UInt8` throughout: every leaf value is measured (`List.length`) and copied
into an array for hashing, and every hash comes back as a list. `merkleB` builds the nodes as
`ByteArray`s instead, converting each value once. `merkle_eq_merkleFast` proves the two equal and is
registered with `@[csimp]`, so compiled code (`root`, hence `State.root`) uses `merkleB` while the
kernel and every theorem see `merkle`.
-/

private theorem toList_mk (l : List UInt8) : (⟨l.toArray⟩ : ByteArray) = l.toByteArray :=
  ByteArray.ext (by rw [List.data_toByteArray])

private theorem toList_eq (b : ByteArray) : b.toList = b.data.toList :=
  Blake2b.toList_eq_data_toList b

/-- ℍ⁰ as octets. -/
def zeroHashB : ByteArray := ⟨Array.replicate 32 0⟩

/-- `leaf` as octets, converting the value once. -/
def leafB (k v : List UInt8) : ByteArray :=
  let vb := v.toByteArray
  if vb.size ≤ 32 then
    (UInt8.ofNat (0x80 + vb.size) :: k).toByteArray ++ vb
      ++ (List.replicate (32 - vb.size) 0).toByteArray
  else
    (0xc0 :: k).toByteArray ++ Blake2b.hash256 vb

theorem leafB_toList (k v : List UInt8) : (leafB k v).toList = leaf k v := by
  unfold leafB leaf
  simp only [List.size_toByteArray]
  split
  · simp [toList_eq, ByteArray.data_append, List.data_toByteArray]
  · simp [toList_eq, ByteArray.data_append, List.data_toByteArray, toList_mk]

/-- `branch` on octets. -/
def branchB (l r : ByteArray) : ByteArray :=
  if h : 0 < l.size then l.set 0 (l[0] &&& 0x7f) h ++ r else r

theorem branchB_toList (l r : ByteArray) : (branchB l r).toList = branch l.toList r.toList := by
  unfold branchB branch
  simp only [toList_eq]
  split
  · rename_i h
    rw [ByteArray.data_append, Array.toList_append, ByteArray.data_set, Array.toList_set]
    match e : l.data.toList, h with
    | b :: rest, h =>
      simp only [List.set_cons_zero, List.cons_append]
      congr
      simp only [ByteArray.getElem_eq_getElem_data, ← Array.getElem_toList, e]
      rfl
    | [], h => simp [ByteArray.size, ← Array.length_toList, e] at h
  · rename_i h
    have : l.data.toList = [] := by
      simpa [ByteArray.size, ← Array.length_toList] using h
    rw [this]

/-- `merkle` on octets. -/
def merkleB : Nat → Nat → List (List UInt8 × List UInt8) → ByteArray
  | _, _, [] => zeroHashB
  | _, _, [(k, v)] => Blake2b.hash256 (leafB k v)
  | 0, _, _ => zeroHashB
  | fuel + 1, depth, d =>
    let l := d.filter fun (k, _) => !bit k depth
    let r := d.filter fun (k, _) => bit k depth
    Blake2b.hash256 (branchB (merkleB fuel (depth + 1) l) (merkleB fuel (depth + 1) r))

theorem hash_toList (b : ByteArray) : hashNode b.toList = (Blake2b.hash256 b).toList := by
  have : (⟨b.toList.toArray⟩ : ByteArray) = b := by rw [toList_eq, Array.toArray_toList]
  rw [hashNode, this]

theorem zeroHashB_toList : zeroHashB.toList = zeroHash := by
  simp [toList_eq, zeroHashB, zeroHash]

theorem merkleB_toList (fuel depth : Nat) (d : List (List UInt8 × List UInt8)) :
    (merkleB fuel depth d).toList = merkle fuel depth d := by
  induction fuel generalizing depth d with
  | zero =>
    match d with
    | [] => simp only [merkleB, merkle, zeroHashB_toList]
    | [(k, v)] => simp only [merkleB, merkle, ← hash_toList, leafB_toList]
    | _ :: _ :: _ => simp only [merkleB, merkle, zeroHashB_toList]
  | succ fuel ih =>
    match d with
    | [] => simp only [merkleB, merkle, zeroHashB_toList]
    | [(k, v)] => simp only [merkleB, merkle, ← hash_toList, leafB_toList]
    | a :: b :: rest =>
      simp only [merkleB, merkle, ← hash_toList, branchB_toList, ih]

/-- `merkle` through `merkleB`. -/
def merkleFast (fuel depth : Nat) (d : List (List UInt8 × List UInt8)) : List UInt8 :=
  (merkleB fuel depth d).toList

@[csimp] theorem merkle_eq_merkleFast : @merkle = @merkleFast := by
  funext fuel depth d
  exact (merkleB_toList fuel depth d).symm

/-- M(d) for a dictionary from 31-octet state keys to values (GP §D.2). -/
def root (d : OctetDict) : List UInt8 := merkle 248 0 d.toList

end JAM.Trie
