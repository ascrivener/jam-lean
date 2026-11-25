import JamCrypto.Ed25519
import JamCrypto.Bandersnatch
import JamCrypto.ThinVrf
import JAM.Crypto

/-!
# The `JAM.Crypto` fields this library implements

`withSignatures base` is `base` with Ed25519 verification (ZIP 215 rules, see `Ed25519.Rules`), the
Bandersnatch VRF signature verification and its output Y; the ring fields (`bsRingRoot`,
`bsRingVerify`, `bsRingOut`) stay those of `base`.

The Bandersnatch signature scheme depends on the Gray Paper version (`GpVersion`): v0.8.0 uses
the IETF VRF (`Bandersnatch.ietfVerify`), v0.8.1 the Thin VRF of the VRF spec's Draft 35
(`Bandersnatch.Thin.verify`, GP #550). The default stays v0.8.0, the version of the pinned
jam-lean model. The ring VRF and ring root of each version are selected the same way by
`Ring.crypto`.
-/

namespace JamCrypto

/-- The Gray Paper version whose cryptography to use. -/
inductive GpVersion where
  | v080
  | v081
  deriving DecidableEq, Repr, Inhabited

/-- `base` with `edVerify`, `bsVerify` and `bsOut` implemented for Gray Paper version `gp`. -/
def withSignatures (base : JAM.Crypto) (rules : Ed25519.Rules := Ed25519.zip215)
    (gp : GpVersion := .v080) : JAM.Crypto :=
  match gp with
  | .v080 =>
    { base with
      edVerify := Ed25519.verifyWith rules
      bsVerify := Bandersnatch.ietfVerify
      bsOut := Bandersnatch.vrfOutput }
  | .v081 =>
    { base with
      edVerify := Ed25519.verifyWith rules
      bsVerify := Bandersnatch.Thin.verify
      bsOut := Bandersnatch.Thin.vrfOutput }

end JamCrypto
