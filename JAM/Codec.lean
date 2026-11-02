import PVM.Blob

/-!
# The serialization codec ℰ (GP v0.8.0 Appendix C)

Encoders for the terms Appendix B and its invocations need. Natural numbers use either the
general variable-length encoding ℰ (`nat`) or a fixed-length little-endian ℰ_l (`fixed`); octet
sequences encode as themselves; ↕x prefixes a length (`var`); ¿x is the optional discriminator
(`opt`); sets and dictionaries are encoded in ascending key order.

ℰ and ℰ_l are shared with the PVM model (`PVM.Blob.encodeNat`, `PVM.Num.encodeLE`), so deblob and
the rest of the protocol use one definition.
-/

namespace JAM

/-- An octet sequence 𝔹. -/
abbrev Blob := ByteArray

/-- A 32-octet hash ℍ. Kept as an octet sequence; the type does not enforce the length. -/
abbrev Hash := ByteArray

namespace Codec

/-- ℰ(x) for x ∈ ℕ_{2^64}: the general natural encoding (GP (C) "general natural number
    serialization"). -/
def nat (x : Nat) : List UInt8 := PVM.Blob.encodeNat x

/-- ℰ_l(x): fixed-length little-endian (GP (C) "Fixed-length Integer Encoding"). -/
def fixed (l x : Nat) : List UInt8 := PVM.Num.encodeLE l x

/-- ℰ(x) for an octet sequence: the identity (GP (C) "Trivial Encodings"). -/
def blob (b : ByteArray) : List UInt8 := b.toList

/-- ℰ(↕x) = ℰ(|x|) ⌢ ℰ(x) (GP (C) "Discriminator Encoding"). -/
def var (b : ByteArray) : List UInt8 := nat b.size ++ b.toList

/-- ℰ(↕[x₀, x₁, …]) = ℰ(n) ⌢ ℰ(x₀) ⌢ ℰ(x₁) ⌢ … for an element encoder `e`. -/
def varSeq {α : Type} (e : α → List UInt8) (xs : List α) : List UInt8 :=
  nat xs.length ++ (xs.map e).flatten

/-- ℰ([x₀, x₁, …]) without a length prefix (GP (C) "Sequence Encoding"). -/
def seq {α : Type} (e : α → List UInt8) (xs : List α) : List UInt8 := (xs.map e).flatten

/-- ℰ(¿x): 0 for ∅, otherwise 1 ⌢ ℰ(x) (GP (C) "Discriminator Encoding"). -/
def opt {α : Type} (e : α → List UInt8) : Option α → List UInt8
  | none => [0]
  | some x => 1 :: e x

/-- Lexicographic order on octet sequences, used to order sets and dictionary keys. -/
def bytesLt (a b : ByteArray) : Bool := decide (a.toList < b.toList)

/-- ℰ of a set of hashes: its elements in ascending order (GP (C) "Set Encoding"), with a length
    prefix where the term is variable-length (↕). -/
def varHashSet (s : List Hash) : List UInt8 :=
  varSeq blob (s.mergeSort fun a b => !bytesLt b a)

/-- ℰ(↕d) for a dictionary of hashes: ascending key order, each pair ℰ(k) ⌢ ℰ(d[k])
    (GP (C) "Dictionary Encoding"). -/
def varHashDict (d : List (Hash × Hash)) : List UInt8 :=
  varSeq (fun (k, v) => blob k ++ blob v) (d.mergeSort fun a b => !bytesLt b.1 a.1)

end Codec

end JAM
