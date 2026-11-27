import PVM.Blob
import Std.Data.ExtTreeSet
import Std.Data.ExtTreeMap

/-!
# The serialization codec $\mathcal{E}$ (GP v0.8.1 Appendix C)

Encoders for the terms Appendix B and its invocations need. Natural numbers use either the
general variable-length encoding $\mathcal{E}$ (`nat`) or a fixed-length little-endian $\mathcal{E}_l$ (`fixed`); octet
sequences encode as themselves; $\updownarrow x$ prefixes a length (`var`); $\text{¿}x$ is the optional discriminator
(`opt`); sets and dictionaries are encoded in ascending key order.

$\mathcal{E}$ and $\mathcal{E}_l$ are shared with the PVM model (`PVM.Blob.encodeNat`, `PVM.Num.encodeLE`), so deblob and
the rest of the protocol use one definition.
-/

namespace JAM

/-- An octet sequence $\mathbb{B}$. -/
abbrev Blob := ByteArray

/-- A 32-octet hash $\mathbb{H}$. Kept as an octet sequence; the type does not enforce the length. -/
abbrev Hash := ByteArray

/-- A set of octet sequences, such as a set of hashes $[\![ \mathbb{H} ]\!]$. Extensional: two sets with the same
    members are equal, so no order or multiplicity is observable. Iteration (`toList`) is in
    ascending lexicographic order, the order of set encoding. -/
abbrev OctetSet := Std.ExtTreeSet (List UInt8)

/-- A dictionary from octet sequences to octet sequences, such as $\mathbb{H} \to \mathbb{H}$. Extensional, like
    `OctetSet`; `toList` is in ascending key order. -/
abbrev OctetDict := Std.ExtTreeMap (List UInt8) (List UInt8)

namespace Codec

/-- $\mathcal{E}(x)$ for $x \in \mathbb{N}_{2^{64}}$: the general natural encoding (GP (C) "general natural number
    serialization"). -/
def nat (x : Nat) : List UInt8 := PVM.Blob.encodeNat x

/-- $\mathcal{E}_l(x)$: fixed-length little-endian (GP (C) "Fixed-length Integer Encoding"). -/
def fixed (l x : Nat) : List UInt8 := PVM.Num.encodeLE l x

/-- $\mathcal{E}(x)$ for an octet sequence: the identity (GP (C) "Trivial Encodings"). -/
def blob (b : ByteArray) : List UInt8 := b.toList

/-- $\mathcal{E}(\updownarrow x) = \mathcal{E}(|x|) \frown \mathcal{E}(x)$ (GP (C) "Discriminator Encoding"). -/
def var (b : ByteArray) : List UInt8 := nat b.size ++ b.toList

/-- $\mathcal{E}(\updownarrow[x_0, x_1, \dots]) = \mathcal{E}(n) \frown \mathcal{E}(x_0) \frown \mathcal{E}(x_1) \frown \dots$ for an element encoder `e`. -/
def varSeq {α : Type} (e : α → List UInt8) (xs : List α) : List UInt8 :=
  nat xs.length ++ (xs.map e).flatten

/-- $\mathcal{E}([x_0, x_1, \dots])$ without a length prefix (GP (C) "Sequence Encoding"). -/
def seq {α : Type} (e : α → List UInt8) (xs : List α) : List UInt8 := (xs.map e).flatten

/-- $\mathcal{E}(\text{¿}x)$: 0 for $\varnothing$, otherwise $1 \frown \mathcal{E}(x)$ (GP (C) "Discriminator Encoding"). -/
def opt {α : Type} (e : α → List UInt8) : Option α → List UInt8
  | none => [0]
  | some x => 1 :: e x

/-- Lexicographic order on octet sequences, used to order sets and dictionary keys. -/
def bytesLt (a b : ByteArray) : Bool := decide (a.toList < b.toList)

/-- $\mathcal{E}$ of a set of hashes: its elements in ascending order (GP (C) "Set Encoding"), with a length
    prefix where the term is variable-length ($\updownarrow$). The set's own order is ascending (`bytesLt`
    is the same lexicographic order), so no sort is needed. -/
def varHashSet (s : OctetSet) : List UInt8 :=
  varSeq id s.toList

/-- $\mathcal{E}(\updownarrow d)$ for a dictionary of hashes: ascending key order, each pair $\mathcal{E}(k) \frown \mathcal{E}(d[k])$
    (GP (C) "Dictionary Encoding"). -/
def varHashDict (d : OctetDict) : List UInt8 :=
  varSeq (fun (k, v) => k ++ v) d.toList

end Codec

end JAM
