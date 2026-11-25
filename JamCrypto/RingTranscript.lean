import JAM.Keccak

/-!
# SHAKE128 and the ring proof's Fiat–Shamir transcript

* `shake128 msg n`: SHAKE128 (FIPS 202; rate 168, domain bits 0x1F) with n output octets, on
  jam-lean's Keccak-f[1600] (`JAM.Keccak`).
* `Transcript`: the transcript of the ring proof (ark-transcript 0.0.3, as used by w3f ring-proof
  0.0.2 / ark-vrf 0.1.0). It is a SHAKE128 stream; the transcript keeps the octets written so far,
  which is all a challenge needs. Writes accumulate a length; `separate` writes it as a 32-bit
  big-endian number. `label`, `append` and `challenge` frame their octets with separators, and
  a challenge squeezes SHAKE128 of everything written, including `"challenge"`.
-/

namespace JamCrypto.Ring

/-- SHAKE128 of msg, n octets of output. -/
def shake128 (msg : List UInt8) (n : Nat) : List UInt8 := Id.run do
  let rate := 168
  let full := msg.length / rate
  let mut a := Array.replicate 25 (0 : UInt64)
  let mut rest := msg
  for _ in [0:full] do
    a := JAM.Keccak.absorb a (rest.take rate)
    rest := rest.drop rate
  let padded := (rest ++ [0x1f] ++ List.replicate (rate - rest.length - 1) 0).set (rate - 1)
    ((if rest.length = rate - 1 then 0x1f else 0) ||| 0x80)
  a := JAM.Keccak.absorb a padded
  let mut out : Array UInt8 := Array.mkEmpty n
  for _ in [0:(n + rate - 1) / rate] do
    for k in [0:rate] do
      if out.size < n then
        out := out.push (a[k / 8]! >>> (8 * (k % 8)).toUInt64).toUInt8
    if out.size < n then a := JAM.Keccak.permute a
  return out.toList

/-- The transcript: the octets written to the SHAKE128 stream (reversed) and the length of the
    current, not yet separated, write. -/
structure Transcript where
  rev : List UInt8 := []
  length : Option Nat := none

namespace Transcript

private def raw (t : Transcript) (bs : List UInt8) : Transcript := { t with rev := bs.reverse ++ t.rev }

def separate (t : Transcript) : Transcript :=
  match t.length with
  | some l =>
    let bs := [(l >>> 24) % 256, (l >>> 16) % 256, (l >>> 8) % 256, l % 256].map UInt8.ofNat
    { raw t bs with length := none }
  | none => t

/-- Writes octets (messages here are far below the 2³¹ limit at which ark-transcript splits). -/
def write (t : Transcript) (bs : List UInt8) : Transcript :=
  let t := raw t bs
  { t with length := some (t.length.getD 0 + bs.length) }

def label (t : Transcript) (l : List UInt8) : Transcript := ((t.separate).write l).separate

/-- Appends a (serialized, uncompressed) item. -/
def append (t : Transcript) (item : List UInt8) : Transcript := ((t.separate).write item).separate

def new (l : List UInt8) : Transcript := ({} : Transcript).label l

/-- The challenge for a label: n octets of the XOF, and the transcript after it. -/
def challenge (t : Transcript) (l : List UInt8) (n : Nat) : List UInt8 × Transcript :=
  let t := (t.label l).write "challenge".toUTF8.toList
  (shake128 t.rev.reverse n, t.separate)

end Transcript

end JamCrypto.Ring
