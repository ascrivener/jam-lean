import JamCrypto.Edwards
import JAM.Sha512

/-!
# Ed25519 signature verification (RFC 8032 §5.1)

s ∈ 𝕍̄_k⟨m⟩ (GP v0.8.0 §3.8.2) is "a valid Ed25519 signature, defined by RFC 8032". RFC 8032 leaves
open whether the verification equation is multiplied by the cofactor 8, and implementations differ
in whether they accept non-canonical point encodings. Those choices are the `Rules`. The model
uses `zip215` (ZIP 215: any encoding of a curve point, S < L, cofactored equation; Adam's decision
2026-11-15), the behaviour the JAM conformance vectors target. `rfc8032Strict` and
`rfc8032Cofactorless` reject non-canonical encodings (§5.1.3 steps 1 and 4); they are kept for the
test vectors.

The message is taken as given: a GP context such as `$jam_valid` stands for the octets
"jam_valid", without the `$` (see docs/crypto-notes.md).
-/

namespace JamCrypto.Ed25519

open JamCrypto.Modular

/-- p = 2^255 − 19. -/
def p : Nat := 2 ^ 255 - 19

/-- The order L of the base point. -/
def L : Nat := 2 ^ 252 + 27742317777372353535851937790883648493

/-- d = −121665/121666. -/
def d : Nat := subMod 0 (121665 * invMod 121666 p % p) p

/-- edwards25519: a = −1. -/
def curve : Curve := { p := p, a := p - 1, d := d }

/-- √−1 = 2^((p−1)/4). -/
def sqrtM1 : Nat := powMod 2 ((p - 1) / 4) p

/-- The base point B (RFC 8032 §5.1). -/
def B : Point :=
  curve.ofAffine 15112221349535400772501151409588531511454012693041857206046113283949847762202
    46316835694926478169428394003475163141307993866256225615783033603165251855960

/-- Which signatures are accepted. -/
structure Rules where
  /-- Reject point encodings whose y is not below p, or with sign bit 1 on x = 0
      (RFC 8032 §5.1.3 steps 1 and 4). -/
  canonicalPoints : Bool
  /-- Check [8][S]B = [8]R + [8][k]A instead of [S]B = R + [k]A. -/
  cofactored : Bool
deriving Repr, BEq

/-- ZIP 215. -/
def zip215 : Rules := { canonicalPoints := false, cofactored := true }

/-- RFC 8032 decoding with the cofactored equation. -/
def rfc8032Strict : Rules := { canonicalPoints := true, cofactored := true }

/-- RFC 8032 decoding with the cofactorless equation. -/
def rfc8032Cofactorless : Rules := { canonicalPoints := true, cofactored := false }

/-- Decode a 32-octet point encoding (RFC 8032 §5.1.3). -/
def decode (rules : Rules) (bs : List UInt8) : Option Point := do
  guard (bs.length == 32)
  let n := leToNat bs
  let sign := n / 2 ^ 255
  let yy := n % 2 ^ 255
  if rules.canonicalPoints && yy ≥ p then none
  let y := yy % p
  let y2 := y * y % p
  let u := subMod y2 1 p
  let v := (d * y2 + 1) % p
  let w := u * invMod v p % p
  let x0 := powMod w ((p + 3) / 8) p
  let x ← if x0 * x0 % p == w then some x0
    else if x0 * x0 % p == subMod 0 w p then some (x0 * sqrtM1 % p)
    else none
  if x == 0 && sign == 1 && rules.canonicalPoints then none
  let x := if x % 2 != sign then subMod 0 x p else x
  return curve.ofAffine x y

/-- s ∈ 𝕍̄_k⟨m⟩ under the given rules. -/
def verifyWith (rules : Rules) (key msg sig : List UInt8) : Bool := Id.run do
  if key.length != 32 || sig.length != 64 then return false
  let Rb := sig.take 32
  let S := leToNat (sig.drop 32)
  if S ≥ L then return false
  let some A := decode rules key | return false
  let some R := decode rules Rb | return false
  let k := leToNat (JAM.Sha512.hash (Rb ++ key ++ msg)) % L
  let E := curve
  if rules.cofactored then
    return E.isZero (E.smul 8 (E.sub (E.sub (E.smul S B) R) (E.smul k A)))
  else
    return E.eq (E.smul S B) (E.add R (E.smul k A))

/-- s ∈ 𝕍̄_k⟨m⟩ (GP §3.8.2) under ZIP 215. -/
def verify (key msg sig : List UInt8) : Bool := verifyWith zip215 key msg sig

end JamCrypto.Ed25519
