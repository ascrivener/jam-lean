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

/-- M(d) for a dictionary from 31-octet state keys to values (GP §D.2). -/
def root (d : OctetDict) : List UInt8 := merkle 248 0 d.toList

end JAM.Trie
