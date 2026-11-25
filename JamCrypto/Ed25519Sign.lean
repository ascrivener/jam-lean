import JamCrypto.Ed25519

/-!
# Ed25519 key generation and signing (RFC 8032 §5.1.5–§5.1.6)

The secret key is the 32-octet seed of RFC 8032. Signing is deterministic by construction: the
nonce r = SHA-512(prefix ⌢ M) mod L, where prefix is the upper half of SHA-512(seed). Every
signature produced here is canonical (R and A are canonical encodings, S < L), so it verifies under
all three `Ed25519.Rules`.
-/

namespace JamCrypto.Ed25519

open JamCrypto.Modular

/-- The canonical 32-octet encoding of a point (RFC 8032 §5.1.2): y little-endian, the top bit
    the low bit of x. -/
def encode (P : Point) : List UInt8 :=
  let (x, y) := curve.toAffine P
  natToLE 32 (y + (x % 2) * 2 ^ 255)

/-- The secret scalar a (clamped lower half of SHA-512(seed)) and the prefix (upper half). -/
def expand (seed : List UInt8) : Nat × List UInt8 :=
  let h := JAM.Sha512.hash seed
  let lo := leToNat (h.take 32)
  -- clear the 3 lowest bits and bit 255, set bit 254
  let a := (lo - lo % 8) % 2 ^ 254 + 2 ^ 254
  (a, h.drop 32)

/-- The public key A = [a]B of a secret seed (RFC 8032 §5.1.5). -/
def publicKey (seed : List UInt8) : List UInt8 := encode (curve.smul (expand seed).1 B)

/-- The signature R ⌢ S of the message under the secret seed (RFC 8032 §5.1.6). -/
def sign (seed msg : List UInt8) : List UInt8 :=
  let (a, prefix_) := expand seed
  let A := encode (curve.smul a B)
  let r := leToNat (JAM.Sha512.hash (prefix_ ++ msg)) % L
  let R := encode (curve.smul r B)
  let k := leToNat (JAM.Sha512.hash (R ++ A ++ msg)) % L
  R ++ natToLE 32 ((r + k * a) % L)

end JamCrypto.Ed25519
