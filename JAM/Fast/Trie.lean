import JAM.Trie
import JAM.Fast.Blake2b

/-!
# Fast compiled Merklization, proved equal to `JAM.Trie`

The faster implementation, moved out of the spec file `JAM/Trie.lean`, with its `@[csimp]` equality.
The thin spec wrappers defined after it in the spec file are restated here (`rfl`) so that their
compiled code uses the fast form too.
-/

namespace JAM.Trie

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

/-- $\zerohash$ as octets. -/
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

/-- `root`, restated so that its compiled code uses `merkleFast`. -/
def rootFast (d : OctetDict) : List UInt8 := merkle 248 0 d.toList

@[csimp] theorem root_eq_rootFast : @root = @rootFast := rfl

end JAM.Trie
