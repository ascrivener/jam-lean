import JamCrypto.Bandersnatch

/-!
# Bandersnatch secret keys and IETF VRF signing

The prover side of the IETF VRF that `Bandersnatch.ietfVerify` checks (Bandersnatch VRF-AD
specification §2.2, as ark-vrf 0.1.0 implements it, which produces the spec's vectors):

* a secret from a seed: x = SHA-512(seed) read little-endian mod r, with 0 replaced by 1
  (ark-vrf `Secret::from_seed`);
* the nonce of RFC 9381 §5.4.2.2 (the RFC 8032 style): k = SHA-512(h[32..64] ⌢ point(I)) read
  little-endian mod r, with h = SHA-512(x as 32 little-endian octets);
* O = [x]I, U = [k]G, V = [k]I, c = challenge(Y, I, O, U, V, ad), s = k + c·x mod r; the signature
  is O ⌢ c ⌢ s with c and s as 32 little-endian octets.
-/

namespace JamCrypto.Bandersnatch

open JamCrypto.Modular

/-- The secret scalar of a seed (ark-vrf 0.1.0 `Secret::from_seed`). -/
def secretOfSeed (seed : List UInt8) : Nat :=
  let x := leToNat (JAM.Sha512.hash seed) % r
  if x == 0 then 1 else x

/-- The public key [x]G. -/
def publicKey (x : Nat) : List UInt8 := encode (curve.smul x G)

/-- The deterministic nonce (RFC 9381 §5.4.2.2, ark-vrf `nonce_rfc_8032`). -/
def nonce (x : Nat) (I : Point) : Nat :=
  let h := (JAM.Sha512.hash (natToLE 32 x)).drop 32
  leToNat (JAM.Sha512.hash (h ++ encode I)) % r

/-- The IETF VRF signature of the secret x for VRF input data `ctx` and additional data `msg`;
    `none` only if `ctx` does not hash to the curve (no input does in practice). -/
def ietfSign (x : Nat) (ctx msg : List UInt8) : Option (List UInt8) := do
  let I ← hashToCurve ctx
  let E := curve
  let Y := E.smul x G
  let O := E.smul x I
  let k := nonce x I
  let c := challenge [Y, I, O, E.smul k G, E.smul k I] msg
  return encode O ++ natToLE 32 c ++ natToLE 32 ((k + c * x) % r)

/-- Y of the signature `ietfSign x ctx _` would give, without signing: the output depends only on
    the secret and the input (needed to sign a header's entropy source before its seal). -/
def ietfOutput (x : Nat) (ctx : List UInt8) : Option (List UInt8) := do
  let I ← hashToCurve ctx
  return (pointToHash (curve.smul x I)).take 32

end JamCrypto.Bandersnatch
