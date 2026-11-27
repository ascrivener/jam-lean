import JamCrypto.RingVerify
import JamCrypto.PedersenVrf

/-!
# Ring VRF verification for GP v0.8.1 (VRF spec Draft 35 §5)

$x \in \bsringproofbase{}_r^{m}\langle c\rangle$ under GP v0.8.1: the 784-octet
$x$ is the output point $O$ (32 octets), a Draft 35 Pedersen VRF proof (160 octets,
`Bandersnatch.Pedersen`) and a ring proof (592 octets). Verification (§5.2) is Pedersen verify for
$(I, O) = (\text{hash}\_\text{to}\_\text{curve}(c), O)$ and additional data $m$, then the ring proof for the key
commitment $\bar{Y}$ of the Pedersen proof.

Against v0.8.0 (`Ring.verify`) the ring proof itself is unchanged except for its constants
(`Consts.v081`: blinding base, padding point, accumulator seed, and the transcript label, which is
Draft 35's suite id under `Reading.vectors`, "ring-proof" under `Reading.prose`). The Pedersen
proof, hash to curve and output hash are Draft 35's. The `Reading` (default `.prose`) selects the
hash to curve of the input, the Pedersen blinding base and the ring constants together.

The domain is `domainSize ringSize`, as for v0.8.0; the caller chooses the ring size. `Ring.crypto`
passes the ring size of the fixed domain 2048 of Draft 35 §5 (`Ring.domain081`).
-/

namespace JamCrypto.Ring

/-- $x \in \bsringproofbase{}_r^{m}\langle c\rangle$ (GP v0.8.1) for rings of up to
    `ringSize` keys, under the reading `rd`. -/
def verify081 (srs : Srs) (ringSize : Nat) (root ctx msg proof : List UInt8)
    (rd : Reading := .prose) : Bool := Id.run do
  if root.length != 144 || proof.length != 784 then return false
  let some cx := G1.decompress (root.take 48) | return false
  let some cy := G1.decompress ((root.drop 48).take 48) | return false
  let some csel := G1.decompress (root.drop 96) | return false
  let some output := Bandersnatch.decode (proof.take 32) | return false
  let some ped := Bandersnatch.Pedersen.Proof.decode ((proof.drop 32).take 160) | return false
  let some rp := decodeRingProof (proof.drop 192) | return false
  let some input := Bandersnatch.Thin.hashToCurve ctx rd | return false
  if !Bandersnatch.Pedersen.verify input output msg ped rd then return false
  -- Ȳ as a point of the ring code's curve type (the same subgroup point)
  let some pkCom := Curve.decode ((proof.drop 32).take 32) | return false
  let dom := domainSize ringSize
  if srs.g1.size < dom then return false
  return ringProofOk srs dom cx cy csel pkCom rp (Consts.v081 rd)

/-- $\mathcal{Y}(x)$ (GP v0.8.1): the 32-octet Draft 35 output hash of the signature's output point. -/
def output081 (proof : List UInt8) : List UInt8 := Bandersnatch.Thin.vrfOutput proof

end JamCrypto.Ring
