import JAM.Crypto
import JamCrypto.RingRoot
import JamCrypto.RingVerify
import JamCrypto.RingVerify081
import JamCrypto.Crypto

/-!
# Bandersnatch ring VRF primitives for `JAM.Crypto`

`JamCrypto.Ring.crypto srs V c` is `c` with the ring root $\mathcal{O}$, ring VRF verification and
output $\mathcal{Y}$ (GP Appendix G) computed in Lean, for a chain of $V$ validators. `gp` selects
the Gray Paper version (default v0.8.0; v0.8.1 uses the VRF spec's Draft 35, see `RingVerify081`).
Load the SRS once at startup:

```
let srs := JamCrypto.Ring.withSelectors (← JamCrypto.Ring.Srs.load "JamCryptoTest/data/bls12-381-srs-2-11-uncompressed-zcash.bin")
```
-/

namespace JamCrypto.Ring

/-- The ring domain of GP v0.8.1: fixed at 2048 by the VRF spec's Draft 35 §5, which GP v0.8.1
    cites (our reading of the cited spec, to be confirmed by 0.8.1 vectors or fuzzer blocks). -/
def domain081 : Nat := 2048

/-- `c` with the ring VRF primitives for a chain of `validators` = $V$ validators: `bsRingRoot` :=
    $\mathcal{O}$ (`Ring.root`), `bsRingVerify` := $\bsringproofbase$ (`Ring.verify`),
    `bsRingOut` := $\mathcal{Y}$ (`Ring.output`). v0.8.0 sizes the ring domain by $V$; v0.8.1 uses
    the domain `dom081` (default `domain081` = 2048, whatever $V$ is; the ring then holds up to $N -
    257$ keys) and the reading `rd` of the VRF spec's Draft 35 (default `.prose`; `.vectors` is what
    the published vectors check, see `JamCrypto.Reading`). v0.8.0 ignores `dom081` and `rd`. -/
def crypto (srs : Srs) (validators : Nat) (c : JAM.Crypto) (gp : GpVersion := .v080)
    (dom081 : Nat := domain081) (rd : Reading := .prose) : JAM.Crypto :=
  match gp with
  | .v080 =>
    { c with
      bsRingRoot := root srs validators
      bsRingVerify := verify srs validators
      bsRingOut := output }
  | .v081 =>
    { c with
      bsRingRoot := fun keys => root srs (keysetSize dom081) keys (Consts.v081 rd)
      bsRingVerify := fun root ctx msg proof => verify081 srs (keysetSize dom081) root ctx msg proof rd
      bsRingOut := output081 }

end JamCrypto.Ring
