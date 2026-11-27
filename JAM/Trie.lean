import JAM.Blake2b
import JAM.Codec

/-!
# State Merklization (GP v0.8.1 Appendix D)

The state-key constructor $C$ (§D.1), the node encodings $B$ and $L$, and the binary Patricia Merkle
trie root $M$ (§D.2). Nodes are 64 octets; bit strings are read most significant bit first
(GP §3, `bits`), so a node's leading bits are the high bits of its first octet.

The serialization $T(\sigma)$ itself (which state component goes under which key) is not here: it
needs the full state $\sigma$. $M$ takes the serialized dictionary, a map from 31-octet state keys to
values.
-/

namespace JAM.Trie

/-- The zero hash $\mathbb{H}^0$. -/
def zeroHash : List UInt8 := List.replicate 32 0

/-- $\mathcal{E}_4$ of a service index, as four octets. -/
def n4 (s : Nat) : List UInt8 := PVM.Num.encodeLE 4 s

theorem length_n4 (s : Nat) : (n4 s).length = 4 := by simp [n4, PVM.Num.encodeLE]

/-- $C(i)$ for $i \in \mathbb{N}_{2^8}$: $[i, 0, 0, \dots]$ (GP §D.1). -/
def keyOfIndex (i : Nat) : List UInt8 := UInt8.ofNat i :: List.replicate 30 0

/-- $C(i, s)$: $[i, n_0, 0, n_1, 0, n_2, 0, n_3, 0, 0, \dots]$ where $n = \mathcal{E}_4(s)$
    (GP §D.1). -/
def keyOfService (i s : Nat) : List UInt8 :=
  let n := n4 s
  have hn : n.length = 4 := length_n4 s
  [UInt8.ofNat i, n[0], 0, n[1], 0, n[2], 0, n[3]] ++ List.replicate 23 0

/-- $C(s, \mathbf{x})$ from the 27 octets of $\mathcal{H}(\mathbf{x})$ it keeps (merklization eq.
    C), the form in which service accounts hold their storage and request keys
    (`ServiceAccount.entries`): $[n_0, a_0, n_1, a_1, n_2, a_2, n_3, a_3, a_4, a_5, \dots, a_{26}]$
    where $n = \mathcal{E}_4(s)$. The octets $a_0 \dots a_3$ are read with `getD`, which never uses
    its default: the keys are 27 octets (`keyOfServiceHash_eq`). -/
def keyOfServiceHash (s : Nat) (a : List UInt8) : List UInt8 :=
  let n := n4 s
  have hn : n.length = 4 := length_n4 s
  [n[0], a.getD 0 0, n[1], a.getD 1 0, n[2], a.getD 2 0, n[3], a.getD 3 0] ++ (a.drop 4).take 23

/-- On a key of at least four octets (`ServiceAccount.entries` holds 27), `keyOfServiceHash`
    reads $a_0 \dots a_3$ in bounds. -/
theorem keyOfServiceHash_eq (s : Nat) (a : List UInt8) (ha : 4 ≤ a.length) :
    keyOfServiceHash s a =
      [(n4 s)[0]'(by simp [length_n4]), a[0], (n4 s)[1]'(by simp [length_n4]), a[1],
        (n4 s)[2]'(by simp [length_n4]), a[2], (n4 s)[3]'(by simp [length_n4]), a[3]]
        ++ (a.drop 4).take 23 := by
  simp [keyOfServiceHash, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 0 < a.length by omega),
    List.getElem?_eq_getElem (show 1 < a.length by omega), List.getElem?_eq_getElem (show 2 < a.length by omega),
    List.getElem?_eq_getElem (show 3 < a.length by omega)]

/-- $C(s, h)$: $[n_0, a_0, n_1, a_1, n_2, a_2, n_3, a_3, a_4, a_5, \dots, a_{26}]$ where
    $n = \mathcal{E}_4(s)$ and $a = \mathcal{H}(h)$ (GP §D.1), i.e. `keyOfServiceHash` of
    $\mathcal{H}(h)$. -/
def keyOfServiceData (s : Nat) (h : List UInt8) : List UInt8 :=
  keyOfServiceHash s (Blake2b.hash256 ⟨h.toArray⟩).toList

/-- $B(l, r) = [0] \frown \text{bits}(l)_{1 \dots} \frown \text{bits}(r)$ (GP §D.2), as 64 octets:
    the first bit of $l$ is replaced by the branch marker 0. -/
def branch (l r : List UInt8) : List UInt8 :=
  match l with
  | b :: rest => (b &&& 0x7f) :: rest ++ r
  | [] => r

/-- $L(k, v)$ (GP §D.2), as 64 octets. For $|v| \le 32$ an embedded-value leaf:
    $[1, 0] \frown \text{bits}(\mathcal{E}_1(|v|))_{2 \dots}$ in the first octet, then $k$, then $v$
    padded with zeroes to 32 octets. Otherwise a regular leaf: $[1, 1, 0, 0, 0, 0, 0, 0]$, then $k$,
    then $\mathcal{H}(v)$. -/
def leaf (k v : List UInt8) : List UInt8 :=
  if v.length ≤ 32 then
    UInt8.ofNat (0x80 + v.length) :: k ++ v ++ List.replicate (32 - v.length) 0
  else
    0xc0 :: k ++ (Blake2b.hash256 ⟨v.toArray⟩).toList

/-- The hash of a node's octets. -/
def hashNode (n : List UInt8) : List UInt8 := (Blake2b.hash256 ⟨n.toArray⟩).toList

/-- bit $i$ of a key, most significant first (GP `bits`). -/
def bit (k : List UInt8) (i : Nat) : Bool :=
  (k.getD (i / 8) 0).toNat.testBit (7 - i % 8)

/-- $M$ at bit depth `depth` (GP §D.2): $\mathbb{H}^0$ for no entries, $\mathcal{H}(L(k, v))$ for
    one, and otherwise $\mathcal{H}(B(M(l), M(r)))$ where $l$ and $r$ hold the entries whose next bit
    is 0 and 1.

    The paper's $M$ strips one bit per level from the dictionary's bit-string keys; here the keys
    stay whole and `depth` counts the bits stripped. `fuel` bounds the depth: distinct 31-octet
    keys separate within 248 bits, so with `fuel = 248` it never runs out on a dictionary of them
    (`root`); on longer keys that agree in their first 248 bits it gives $\mathbb{H}^0$ there. -/
def merkle : Nat → Nat → List (List UInt8 × List UInt8) → List UInt8
  | _, _, [] => zeroHash
  | _, _, [(k, v)] => hashNode (leaf k v)
  | 0, _, _ => zeroHash
  | fuel + 1, depth, d =>
    let l := d.filter fun (k, _) => !bit k depth
    let r := d.filter fun (k, _) => bit k depth
    hashNode (branch (merkle fuel (depth + 1) l) (merkle fuel (depth + 1) r))

/-- $M(d)$ for a dictionary from 31-octet state keys to values (GP §D.2). -/
def root (d : OctetDict) : List UInt8 := merkle 248 0 d.toList

end JAM.Trie
