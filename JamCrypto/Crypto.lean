import JamCrypto.Ed25519
import JamCrypto.Bandersnatch
import JamCrypto.ThinVrf
import JamCrypto.Fast.Ed25519
import JamCrypto.Fast.Bandersnatch
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
`Ring.crypto`. The v0.8.1 path also takes the `Reading` of the VRF spec's Draft 35 (default
`.prose`; `.vectors` is what the published vectors check, see `JamCrypto.Reading`).

With `fast := true` (the default) the fields are computed by `JamCrypto.Fast` (fixed-limb field
arithmetic), which computes the same functions as the reference implementations (`fast := false`);
that equality is tested (`JamCryptoTest/Fast.lean`, all vectors and randomized inputs), not proved.
-/

namespace JamCrypto

/-- The Gray Paper version whose cryptography to use. -/
inductive GpVersion where
  | v080
  | v081
  deriving DecidableEq, Repr, Inhabited

/-- `base` with `edVerify`, `bsVerify` and `bsOut` implemented for Gray Paper version `gp`, and for
    v0.8.1 the reading `rd` of Draft 35 (v0.8.0 ignores `rd`); by `JamCrypto.Fast` unless
    `fast := false` selects the reference implementations. -/
def withSignatures (base : JAM.Crypto) (rules : Ed25519.Rules := Ed25519.zip215)
    (gp : GpVersion := .v080) (rd : Reading := .prose) (fast : Bool := true) : JAM.Crypto :=
  match fast, gp with
  | true, .v080 =>
    { base with
      edVerify := Fast.Ed25519.verifyWith rules
      bsVerify := Fast.Bandersnatch.ietfVerify
      bsOut := Fast.Bandersnatch.vrfOutput }
  | true, .v081 =>
    { base with
      edVerify := Fast.Ed25519.verifyWith rules
      bsVerify := fun key ctx msg sig => Fast.Bandersnatch.Thin.verify key ctx msg sig rd
      bsOut := Fast.Bandersnatch.Thin.vrfOutput }
  | false, .v080 =>
    { base with
      edVerify := Ed25519.verifyWith rules
      bsVerify := Bandersnatch.ietfVerify
      bsOut := Bandersnatch.vrfOutput }
  | false, .v081 =>
    { base with
      edVerify := Ed25519.verifyWith rules
      bsVerify := fun key ctx msg sig => Bandersnatch.Thin.verify key ctx msg sig rd
      bsOut := Bandersnatch.Thin.vrfOutput }

end JamCrypto
