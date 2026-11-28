import JAM.Blake2b
import JAM.Keccak
import JAM.Codec

/-!
# Binary Merkle trees (GP v0.8.1 Appendix E, "Binary Merkle Trees")

The node function $N$ (eq. `merklenode`) and the well-balanced root $\mathcal{M}_B$
(eq. `simplemerkleroot`), parameterized by the hash function $H$.
-/

namespace JAM.Merkle

/-- The prefix `$node`. -/
def nodePrefix : List UInt8 := "node".toUTF8.toList

/-- $N(\mathbf{v}, H)$ (GP eq. `merklenode`): the zero hash for no items, the item itself for one,
    and $H(p \frown N(\text{first } \lceil n/2 \rceil) \frown N(\text{rest}))$ with the prefix
    $p$ = `$node` otherwise. `fuel` bounds the recursion depth; each level shortens $\mathbf{v}$, so
    $|\mathbf{v}|$ suffices (`root` supplies it). -/
def node (H : ByteArray → ByteArray) : Nat → List (List UInt8) → List UInt8
  | _, [] => zeroHash
  | _, [v] => v
  | 0, _ => zeroHash
  | fuel + 1, v =>
    let h := (v.length + 1) / 2
    (H ⟨(nodePrefix ++ node H fuel (v.take h) ++ node H fuel (v.drop h)).toArray⟩).toList

/-- $\mathcal{M}_B(\mathbf{v}, H)$ (GP eq. `simplemerkleroot`): $H(\mathbf{v}_0)$ for one item,
    $N(\mathbf{v}, H)$ otherwise. -/
def root (H : ByteArray → ByteArray) (v : List (List UInt8)) : List UInt8 :=
  match v with
  | [x] => (H ⟨x.toArray⟩).toList
  | _ => node H v.length v

end JAM.Merkle
