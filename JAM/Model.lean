import JAM.BlockImport
import JamCrypto.Crypto
import JamCrypto.Ring

/-!
# The closed model: Υ with JamCrypto's GP v0.8.1 crypto fixed

`JAM.importBlockWith params c` (`JAM/BlockImport.lean`) is Υ (GP §4–§5) for any crypto `c`, the
parametric core that proofs are stated over. This module fixes `c`: `JAM.crypto srs` is the full
plain-Lean crypto of GP v0.8.1 (`JamCrypto`), and `JAM.importBlock srs` is Υ with it fixed: the
closed model, the function a conformance proof targets.

This is the only model module that imports `JamCrypto` (Adam, 2026-11-28); the paper-shaped
modules never do (see [`docs/jamcrypto.md`](https://github.com/ascrivener/jam-lean/blob/main/docs/jamcrypto.md)).

The spec readings `JAM.crypto` fixes:

* **GP version:** the v0.8.1 path of every primitive (`JamCrypto.GpVersion.v081`).
* **Ed25519** (GP §3.8.2): ZIP 215 rules (`JamCrypto.Ed25519.zip215`: any encoding of a curve
  point, $S < L$, the cofactored equation; a project decision).
* **Bandersnatch VRF signatures** $\bssignaturebase$ and their output $\mathcal{Y}$ (GP v0.8.1
  Appendix G): the Thin VRF of the VRF spec's Draft 35 (`JamCrypto.Bandersnatch.Thin`, GP #550).
* **Ring root** $\mathcal{O}$, **Ring VRF** $\bsringproofbase$ and its output $\mathcal{Y}$ (GP
  v0.8.1 Appendix G): Draft 35, over the fixed ring domain of 2048 (`JamCrypto.Ring.domain081`),
  whatever the validator count.
* **Reading of Draft 35:** `JamCrypto.Reading.vectors`, the reading its own test vectors check,
  where the draft's prose and vectors disagree ($Z_{\text{pad}}$ and the ring transcript label; see
  `JamCrypto.Reading` and `docs/jamcrypto.md`). This is an assumption: the published vectors and
  the fuzzer's blocks follow it. It is not JamCrypto's default reading (`Reading.prose`, which no
  published vector follows).

Every field of `crypto srs` is computed by JamCrypto: `JamCrypto.withSignatures` (v0.8.1) sets
`edVerify`, `bsVerify` and `bsOut`, and `JamCrypto.Ring.crypto` (v0.8.1) sets `bsRingRoot`,
`bsRingVerify` and `bsRingOut`. The base record `cryptoBase` only fills the structure; none of its
fields survives (`crypto_eq_compose` shows the result does not depend on the base).
-/

namespace JAM

/-- A placeholder `Crypto` to build `crypto` on: rejects every signature. Every field is
    overridden in `crypto`. -/
def cryptoBase : Crypto := { edVerify := fun _ _ _ => false }

/-- The cryptographic primitives of GP v0.8.1, all in plain Lean (`JamCrypto`): Ed25519 under
    ZIP 215, the Bandersnatch Thin VRF, and the Draft 35 ring root and Ring VRF (GP #550, Appendix
    G), in the reading of Draft 35's test vectors (`JamCrypto.Reading.vectors`). See the module note
    for the readings fixed.

    `srs` is the KZG structured reference string of the Bandersnatch ring VRF: the fixed public
    SRS from the Zcash BLS12-381 powers-of-τ ceremony, published with the VRF specification
    (`assets/srs/zcash-srs-2-11-uncompressed.bin` of davxy/bandersnatch-vrf-spec) and checked in,
    byte-identical, as `JamCryptoTest/data/bls12-381-srs-2-11-uncompressed-zcash.bin` (sha256 in
    `JamCryptoTest/data/README.md` and `docs/jamcrypto.md`; load it with
    `JamCrypto.Ring.Srs.load`; `JamCrypto.Ring.withSelectors` only adds a cache). It is public
    data, not a choice: a conformance statement fixes it to that SRS. -/
def crypto (srs : JamCrypto.Ring.Srs) : Crypto :=
  JamCrypto.withSignatures (JamCrypto.Ring.crypto srs 0 cryptoBase (gp := .v081) (rd := .vectors))
    JamCrypto.Ed25519.zip215 (gp := .v081) (rd := .vectors)

/-- `crypto srs` is the composition `withSignatures (Ring.crypto srs V c)` on the v0.8.1 path with
    the `vectors` reading, for any validator count `V` and any base `c`: the v0.8.1 ring domain
    does not depend on `V`, and every field of `c` is overridden. -/
theorem crypto_eq_compose (srs : JamCrypto.Ring.Srs) (validators : Nat) (c : Crypto) :
    JamCrypto.withSignatures
      (JamCrypto.Ring.crypto srs validators c (gp := .v081) (rd := .vectors))
      JamCrypto.Ed25519.zip215 (gp := .v081) (rd := .vectors) = crypto srs := rfl

/-- **$\Upsilon(\sigma, B)$, the closed model** (GP eq. `transitionfunctioncomposition`):
    `importBlockWith` with the crypto fixed to `crypto srs` (GP v0.8.1: Ed25519 under ZIP 215,
    Thin VRF, Draft 35 ring root and Ring VRF, `Reading.vectors`). This is the function a
    conformance proof targets; proofs about Υ are stated over the parametric `importBlockWith`.

    The remaining arguments are data. A conformance statement must fix:
    * `srs`: the ring VRF's public SRS (see `crypto`);
    * `params`: the protocol constants of the chain (`Params.full` for GP v0.8.1's full chain;
      `Params.tiny` for the vectors' tiny chain);
    * `chain`: the retained ancestor headers $\mathbf{A}$ (GP eq. 5.3), ending with the parent's
      header;
    * `σ` and `B`: the prior state and the block. -/
def importBlock (srs : JamCrypto.Ring.Srs) (params : Params) (chain : Chain) (σ : State)
    (B : Block) : Except BlockError (State × ImportTrace) :=
  importBlockWith params (crypto srs) chain σ B

/-- The closed model is the parametric core at `crypto srs`. -/
theorem importBlock_eq (srs : JamCrypto.Ring.Srs) (params : Params) (chain : Chain) (σ : State)
    (B : Block) : importBlock srs params chain σ B = importBlockWith params (crypto srs) chain σ B :=
  rfl

end JAM
