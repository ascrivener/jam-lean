import JamCrypto.Bls12381G1

/-!
# The ring SRS (KZG powers of τ)

The structured reference string of the Bandersnatch ring VRF's KZG commitments over BLS12-381:
[τⁱ]G1 for i < 6145 and [τⁱ]G2 for i < 2, from the Zcash powers-of-τ ceremony, as shipped by
ark-vrf 0.1.0 (`data/srs/bls12-381-srs-2-11-uncompressed-zcash.bin`, committed here as
`JamCryptoTest/data/bls12-381-srs-2-11-uncompressed-zcash.bin`).

File format (arkworks `CanonicalSerialize`, uncompressed, of w3f-pcs `URS`): a little-endian u64
count of G1 points, the G1 points (96 octets each), a u64 count of G2 points, the G2 points (192
octets each). G2 points are kept as raw octets until the verifier needs them.
-/

namespace JamCrypto.Ring

/-- The parsed SRS. -/
structure Srs where
  /-- [τⁱ]G1. -/
  g1 : Array G1.Aff
  /-- The uncompressed encodings of [τⁱ]G2. -/
  g2Raw : Array ByteArray
  /-- Precomputed ring selector commitments by domain size (see `Ring.withSelectors`); a pure
      cache, never needed for correctness. -/
  selectors : List (Nat × List UInt8) := []

instance : Inhabited Srs := ⟨⟨#[], #[], []⟩⟩

private def u64LE (bs : ByteArray) (off : Nat) : Nat := Id.run do
  let mut v := 0
  for i in [0:8] do
    v := v + (bs.get! (off + i)).toNat * 256 ^ i
  return v

/-- Parses the SRS file contents. With `maxG1`, only the first `maxG1` G1 points are decoded. -/
def Srs.parse (bs : ByteArray) (maxG1 : Nat := 6145) : Except String Srs := do
  if bs.size < 8 then throw "SRS: truncated"
  let n1 := u64LE bs 0
  let off2 := 8 + 96 * n1
  if bs.size < off2 + 8 then throw "SRS: truncated G1"
  let mut g1 : Array G1.Aff := Array.mkEmpty (min n1 maxG1)
  for i in [0:min n1 maxG1] do
    match G1.decodeUncompressed bs (8 + 96 * i) with
    | some p => g1 := g1.push p
    | none => throw s!"SRS: bad G1 point {i}"
  let n2 := u64LE bs off2
  if bs.size < off2 + 8 + 192 * n2 then throw "SRS: truncated G2"
  let mut g2 : Array ByteArray := #[]
  for i in [0:n2] do
    let o := off2 + 8 + 192 * i
    g2 := g2.push (bs.extract o (o + 192))
  return ⟨g1, g2, []⟩

/-- Reads and parses an SRS file. -/
def Srs.load (path : System.FilePath) (maxG1 : Nat := 6145) : IO Srs := do
  let bs ← IO.FS.readBinFile path
  match Srs.parse bs maxG1 with
  | .ok s => pure s
  | .error e => throw (IO.userError e)

end JamCrypto.Ring
