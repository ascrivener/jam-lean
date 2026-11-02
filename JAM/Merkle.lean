import JAM.Blake2b
import JAM.Keccak

/-!
# Binary Merkle trees (GP v0.8.0 Appendix E, "Binary Merkle Trees")

The node function N (eq. `merklenode`) and the well-balanced root ℳ_B (eq. `simplemerkleroot`),
parameterized by the hash function H.
-/

namespace JAM.Merkle

/-- The prefix $node. -/
def nodePrefix : List UInt8 := "node".toUTF8.toList

/-- N(**v**, H) (GP eq. `merklenode`): the zero hash for no items, the item itself for one, and
    H($node ⌢ N(first ⌈n/2⌉) ⌢ N(rest)) otherwise. `fuel` bounds the recursion depth; each level
    shortens **v**, so |**v**| suffices (`root` supplies it). -/
def node (H : ByteArray → ByteArray) : Nat → List (List UInt8) → List UInt8
  | _, [] => List.replicate 32 0
  | _, [v] => v
  | 0, _ => List.replicate 32 0
  | fuel + 1, v =>
    let h := (v.length + 1) / 2
    (H ⟨(nodePrefix ++ node H fuel (v.take h) ++ node H fuel (v.drop h)).toArray⟩).toList

/-- ℳ_B(**v**, H) (GP eq. `simplemerkleroot`): H(**v**_0) for one item, N(**v**, H) otherwise. -/
def root (H : ByteArray → ByteArray) (v : List (List UInt8)) : List UInt8 :=
  match v with
  | [x] => (H ⟨x.toArray⟩).toList
  | _ => node H v.length v

end JAM.Merkle
