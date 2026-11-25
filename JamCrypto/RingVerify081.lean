import JamCrypto.RingVerify
import JamCrypto.PedersenVrf

/-!
# Ring VRF verification for GP v0.8.1 (VRF spec Draft 35 §5)

x ∈ 𝔹̄°_r⟨c⟩⟨m⟩ under GP v0.8.1: the 784-octet x is the output point O (32 octets), a Draft 35
Pedersen VRF proof (160 octets, `Bandersnatch.Pedersen`) and a ring proof (592 octets). Verification
(§5.2) is Pedersen verify for (I, O) = (hash_to_curve(c), O) and additional data m, then the ring
proof for the key commitment Ȳ of the Pedersen proof.

Against v0.8.0 (`Ring.verify`) the ring proof itself is unchanged except for its constants
(`Consts.v081`: blinding base, padding point, accumulator seed, and the transcript label, which is
Draft 35's suite id as its ring vectors require — §5's prose says a "ring-proof" label). The
Pedersen proof, hash to curve and output hash are Draft 35's.

The domain is `domainSize ringSize`, as for v0.8.0; the caller chooses the ring size. `Ring.crypto`
passes the ring size of the fixed domain 2048 of Draft 35 §5 (`Ring.domain081`).
-/

namespace JamCrypto.Ring

/-- x ∈ 𝔹̄°_r⟨c⟩⟨m⟩ (GP v0.8.1) for rings of up to `ringSize` keys. -/
def verify081 (srs : Srs) (ringSize : Nat) (root ctx msg proof : List UInt8) : Bool := Id.run do
  if root.length != 144 || proof.length != 784 then return false
  let some cx := G1.decompress (root.take 48) | return false
  let some cy := G1.decompress ((root.drop 48).take 48) | return false
  let some csel := G1.decompress (root.drop 96) | return false
  let some output := Bandersnatch.decode (proof.take 32) | return false
  let some ped := Bandersnatch.Pedersen.Proof.decode ((proof.drop 32).take 160) | return false
  let some rp := decodeRingProof (proof.drop 192) | return false
  let some input := Bandersnatch.Thin.hashToCurve ctx | return false
  if !Bandersnatch.Pedersen.verify input output msg ped then return false
  -- Ȳ as a point of the ring code's curve type (the same subgroup point)
  let some pkCom := Curve.decode ((proof.drop 32).take 32) | return false
  let dom := domainSize ringSize
  if srs.g1.size < dom then return false
  return ringProofOk srs dom cx cy csel pkCom rp .v081

/-- Y(x) (GP v0.8.1): the 32-octet Draft 35 output hash of the signature's output point. -/
def output081 (proof : List UInt8) : List UInt8 := Bandersnatch.Thin.vrfOutput proof

end JamCrypto.Ring
