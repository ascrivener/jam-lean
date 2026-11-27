import JamCrypto.Crypto
import JamCrypto.Fast.Ed25519
import JamCrypto.Fast.Bandersnatch

/-!
# The `JAM.Crypto` signature fields on the fast implementations

`Fast.withSignatures` is `JamCrypto.withSignatures` with `edVerify`, `bsVerify` and `bsOut` computed by
`JamCrypto.Fast` (fixed-limb field arithmetic). It is proved equal to `JamCrypto.withSignatures`
(`withSignatures_eq`), so executables may use it in its place. The spec modules never import this
file.
-/

namespace JamCrypto.Fast

/-- `JamCrypto.withSignatures`, computed by the fast implementations. -/
def withSignatures (base : JAM.Crypto) (rules : JamCrypto.Ed25519.Rules := JamCrypto.Ed25519.zip215)
    (gp : GpVersion := .v080) (rd : Reading := .prose) : JAM.Crypto :=
  match gp with
  | .v080 =>
    { base with
      edVerify := Fast.Ed25519.verifyWith rules
      bsVerify := Fast.Bandersnatch.ietfVerify
      bsOut := Fast.Bandersnatch.vrfOutput }
  | .v081 =>
    { base with
      edVerify := Fast.Ed25519.verifyWith rules
      bsVerify := fun key ctx msg sig => Fast.Bandersnatch.Thin.verify key ctx msg sig rd
      bsOut := Fast.Bandersnatch.Thin.vrfOutput }

/-- The fast fields are the reference ones. -/
theorem withSignatures_eq (base : JAM.Crypto) (rules : JamCrypto.Ed25519.Rules) (gp : GpVersion)
    (rd : Reading) : withSignatures base rules gp rd = JamCrypto.withSignatures base rules gp rd := by
  have he : Fast.Ed25519.verifyWith rules = JamCrypto.Ed25519.verifyWith rules :=
    funext fun k => funext fun m => funext fun s => Fast.Ed25519.verifyWith_eq rules k m s
  cases gp
  · have hv : Fast.Bandersnatch.ietfVerify = JamCrypto.Bandersnatch.ietfVerify :=
      funext fun k => funext fun c => funext fun m => funext fun s => Fast.Bandersnatch.ietfVerify_eq k c m s
    have ho : Fast.Bandersnatch.vrfOutput = JamCrypto.Bandersnatch.vrfOutput :=
      funext Fast.Bandersnatch.vrfOutput_eq
    simp only [withSignatures, JamCrypto.withSignatures, he, hv, ho]
  · have hv : (fun key ctx msg sig => Fast.Bandersnatch.Thin.verify key ctx msg sig rd) =
        (fun key ctx msg sig => JamCrypto.Bandersnatch.Thin.verify key ctx msg sig rd) :=
      funext fun k => funext fun c => funext fun m => funext fun s => Fast.Bandersnatch.Thin.verify_eq k c m s rd
    have ho : Fast.Bandersnatch.Thin.vrfOutput = JamCrypto.Bandersnatch.Thin.vrfOutput :=
      funext Fast.Bandersnatch.Thin.vrfOutput_eq
    simp only [withSignatures, JamCrypto.withSignatures, he, hv, ho]

end JamCrypto.Fast
