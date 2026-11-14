import Services.Bootstrap.Encode.VariantsVec3Bless
import Services.Bootstrap.Encode.VariantsVec3Assign
import Services.Bootstrap.Encode.VariantsVec3Designate

/-!
# `Instruction::encode_to`: `Bless` (11), `Assign` (12) and `Designate` (13)

The three arms holding a heap sequence other than octets, each an `EncOkMD` element lifted to the depth
232 (`*_232`), its slot predicate the decode side's with the heap pointer q explicit, and a bridge
lemma from the decode side's ∃-pointer predicate:

* `Enc.bless` (`Encode.VariantsVec3Bless`) (index 11, arm 18163): 11 :: m ++ a ++ d ++ r ++ ℰ(n) ++ items,
  `BlessRepAt` (`blessRep_iff`), heap octets `BlessSrc q n` = [q, q + 16 n), depth 192.
* `Enc.assign` (`Encode.VariantsVec3Assign`) (index 12, arm 18429): 12 :: c2 ++ hb ++ w4, `AssignRepAt`
  (`assignRep_iff`), heap octets `VecSrc q (32 n)`, depth 136.
* `Enc.designate` (`Encode.VariantsVec3Designate`) (index 13, arm 19322): 13 :: ℰ(n) ++ ks, the keys stored
  rotated (`keysRot`) and emitted in the paper's order, `DesignateRepAt` (`designateRep_iff`), heap
  octets `VecSrc q (336 n)`, depth 192.

GP v0.8.0 Appendix C for the encodings.
-/
