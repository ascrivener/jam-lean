import JAM.BlockImport
import JamCrypto.Crypto
import JamCrypto.Ring

/-!
# The closed state-transition function: Υ with JamCrypto's crypto fixed

The model (`JAM`) takes its cryptography as a parameter, `JAM.Crypto`, and never imports this
library (a standing decision; see
[`docs/jamcrypto.md`](https://github.com/ascrivener/jam-lean/blob/main/docs/jamcrypto.md)). This
module closes that parameter: `JamCrypto.Model.crypto srs` is the full plain-Lean crypto of GP
v0.8.1, and `JamCrypto.Model.importBlock srs` is Υ (`JAM.importBlock`, GP §4–§5) with it fixed.
**This is the closed function a conformance proof targets.**

The spec readings it fixes:

* **GP version:** the v0.8.1 path of every primitive (`GpVersion.v081`).
* **Ed25519** (GP §3.8.2): ZIP 215 rules (`Ed25519.zip215`: any encoding of a curve point,
  $S < L$, the cofactored equation; a project decision).
* **Bandersnatch VRF signatures** $\bssignaturebase$ and their output $\mathcal{Y}$ (GP v0.8.1
  Appendix G): the Thin VRF of the VRF spec's Draft 35 (`Bandersnatch.Thin`, GP #550).
* **Ring root** $\mathcal{O}$, **Ring VRF** $\bsringproofbase$ and its output $\mathcal{Y}$ (GP
  v0.8.1 Appendix G): Draft 35, over the fixed ring domain of 2048 (`Ring.domain081`), whatever the
  validator count.
* **Reading of Draft 35:** `Reading.vectors`, the reading its own test vectors check, where the
  draft's prose and vectors disagree ($Z_{\text{pad}}$ and the ring transcript label; see
  `JamCrypto.Reading` and `docs/jamcrypto.md`). This is an assumption: the published vectors and
  the fuzzer's blocks follow it. It is not JamCrypto's default reading (`Reading.prose`, which no
  published vector follows).

Every field of `crypto srs` is computed by JamCrypto: `withSignatures` (v0.8.1) sets `edVerify`,
`bsVerify` and `bsOut`, and `Ring.crypto` (v0.8.1) sets `bsRingRoot`, `bsRingVerify` and
`bsRingOut`. The base record `unset` only fills the structure; none of its fields survives
(`crypto_eq_compose` shows the result does not depend on the base).

`Fast.withSignatures` computes the same signature fields faster (`Fast.withSignatures_eq`).
-/

namespace JamCrypto.Model

/-- A placeholder `JAM.Crypto` to build on: rejects every signature. Every field is overridden in
    `crypto`. -/
def unset : JAM.Crypto := { edVerify := fun _ _ _ => false }

/-- The cryptographic primitives of GP v0.8.1, all in plain Lean: Ed25519 under ZIP 215, the
    Bandersnatch Thin VRF, and the Draft 35 ring root and Ring VRF (GP #550, Appendix G), in the
    reading of Draft 35's test vectors (`Reading.vectors`). See the module note for the readings
    fixed.

    `srs` is the KZG structured reference string of the Bandersnatch ring VRF: the fixed public
    SRS from the Zcash BLS12-381 powers-of-τ ceremony, published with the VRF specification
    (`assets/srs/zcash-srs-2-11-uncompressed.bin` of davxy/bandersnatch-vrf-spec) and checked in,
    byte-identical, as `JamCryptoTest/data/bls12-381-srs-2-11-uncompressed-zcash.bin` (sha256 in
    `JamCryptoTest/data/README.md` and `docs/jamcrypto.md`; load it with `Ring.Srs.load`; `Ring.withSelectors` only adds a
    cache). It is public data, not a choice: a conformance statement fixes it to that SRS. -/
def crypto (srs : Ring.Srs) : JAM.Crypto :=
  withSignatures (Ring.crypto srs 0 unset (gp := .v081) (rd := .vectors))
    Ed25519.zip215 (gp := .v081) (rd := .vectors)

/-- `crypto srs` is the composition `withSignatures (Ring.crypto srs V c)` on the v0.8.1 path with
    the `vectors` reading, for any validator count `V` and any base `c`: the v0.8.1 ring domain
    does not depend on `V`, and every field of `c` is overridden. -/
theorem crypto_eq_compose (srs : Ring.Srs) (validators : Nat) (c : JAM.Crypto) :
    withSignatures (Ring.crypto srs validators c (gp := .v081) (rd := .vectors))
      Ed25519.zip215 (gp := .v081) (rd := .vectors) = crypto srs := rfl

/-- **The closed state-transition function.** Υ (`JAM.importBlock`, GP §4–§5) with the crypto
    fixed to `crypto srs` (GP v0.8.1: Ed25519 under ZIP 215, Thin VRF, Draft 35 ring root and Ring
    VRF, `Reading.vectors`). This is the function a conformance proof targets.

    The remaining arguments are data. A conformance statement must fix:
    * `srs`: the ring VRF's public SRS (see `crypto`);
    * `params`: the protocol constants of the chain (`JAM.Params.full` for GP v0.8.1's full chain;
      `JAM.Params.tiny` for the vectors' tiny chain);
    * `chain`: the retained ancestor headers $\mathcal{A}$ (GP §11.4.1), ending with the parent's
      header;
    * `σ` and `B`: the prior state and the block. -/
def importBlock (srs : Ring.Srs) (params : JAM.Params) (chain : JAM.Chain) (σ : JAM.State)
    (B : JAM.Block) : Except JAM.BlockError (JAM.State × JAM.ImportTrace) :=
  JAM.importBlock params (crypto srs) chain σ B

/-- The closed function is the parametric one at `crypto srs`. -/
theorem importBlock_eq (srs : Ring.Srs) (params : JAM.Params) (chain : JAM.Chain) (σ : JAM.State)
    (B : JAM.Block) : importBlock srs params chain σ B = JAM.importBlock params (crypto srs) chain σ B :=
  rfl

end JamCrypto.Model
