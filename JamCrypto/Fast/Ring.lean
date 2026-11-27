import JamCrypto.Ring
import JamCrypto.Fast.RingCurve

/-!
# The ring VRF entry points, restated so that their compiled code uses the fast paths

The reference ring functions (`JamCrypto/RingRoot.lean`, `RingVerify.lean`, `RingVerify081.lean`,
`Ring.lean`) are compiled in their spec modules, before the `@[csimp]` replacements of
`Curve.decode`, `Curve.smulW` and `Ring.hashToCurve` (`JamCrypto/Fast/RingCurve.lean`) exist.
The definitions below are their
text, unchanged (`verify081` and `crypto`: their elaborated terms); each is equal to its
reference (by `rfl`, or by rewriting with the equalities of the ones it calls), and compiled here
they call the
replacements. `crypto_csimp` then replaces `Ring.crypto` as a whole. The namespace is
`JamCrypto.Ring.Fast`, so that every name in the restated text resolves as in the reference.
-/

namespace JamCrypto.Ring.Fast

open JamCrypto.Fr

def commitColumn (srs : Srs) (evals : Array Nat) : List UInt8 :=
  G1.compress (G1.msm srs.g1 (interpolate evals)).toAff

def commitPoints (srs : Srs) (dom : Nat) (keys : List Curve.Aff) (k : Consts := .v080) : List UInt8 :=
  let pts := pointsColumn dom keys k
  let zeros := Array.replicate (dom - pts.size) 0
  let xs := pts.map (·.x) ++ zeros
  let ys := pts.map (·.y) ++ zeros
  let sel := match srs.selectors.lookup dom with
    | some c => c
    | none => commitColumn srs (selectorColumn dom)
  commitColumn srs xs ++ commitColumn srs ys ++ sel

def root (srs : Srs) (ringSize : Nat) (keys : List (List UInt8)) (k : Consts := .v080) : List UInt8 :=
  let dom := domainSize ringSize
  if srs.g1.size < dom then [] else
  commitPoints srs dom (keys.map fun key => (Curve.decode key).getD k.padding) k

def withSelectors (srs : Srs) (ringSizes : List Nat := [6, 1023]) : Srs :=
  let doms := (ringSizes.map domainSize).eraseDups.filter (· ≤ srs.g1.size)
  { srs with selectors := doms.map fun d => (d, commitColumn srs (selectorColumn d)) }

def decodeRingProof (bs : List UInt8) : Option RingProof := do
  if bs.length != 592 then none
  let g (i : Nat) := G1.decompress ((bs.drop i).take 48)
  let f (i : Nat) := decodeFr ((bs.drop i).take 32)
  let cBits ← g 0
  let cIpa ← g 48
  let cAx ← g 96
  let cAy ← g 144
  let evals ← (List.range 7).mapM fun k => f (192 + 32 * k)
  let cQuot ← g 416
  let lin ← f 464
  let p1 ← g 496
  let p2 ← g 544
  some ⟨cBits, cIpa, cAx, cAy, evals.toArray, cQuot, lin, p1, p2⟩

def combine (pts : List G1.Aff) (ks : List Nat) : G1.Jac :=
  (pts.zip ks).foldl (fun acc (p, k) => G1.addJ acc (G1.smul p.toJac k)) G1.Jac.zero

def ringProofOk (srs : Srs) (dom : Nat) (cx cy csel : G1.Aff) (result : Curve.Aff)
    (p : RingProof) (k : Consts := .v080) : Bool := Id.run do
  let some g2 := srs.g2Raw[0]? |>.bind Pairing.G2.decode | return false
  let some tg2 := srs.g2Raw[1]? |>.bind Pairing.G2.decode | return false
  let some g1 := srs.g1[0]? | return false
  let unc := G1.encodeUncompressed
  let lbl (s : String) := s.toUTF8.toList
  -- transcript
  let vk := unc g1 ++ (srs.g2Raw[0]!).toList ++ (srs.g2Raw[1]!).toList ++ unc cx ++ unc cy ++ unc csel
  let t := (Transcript.new k.label).label (lbl "vk") |>.append vk
  let t := t.label (lbl "instance") |>.append (frLE result.x ++ frLE result.y)
  let t := t.label (lbl "committed_cols") |>.append (unc p.cBits ++ unc p.cIpa ++ unc p.cAx ++ unc p.cAy)
  let (alphas, t) := frChallenges t "constraints_aggregation" 7
  let t := t.label (lbl "quotient") |>.append (unc p.cQuot)
  let (zeta, t) := frChallenge t "evaluation_point"
  let t := t.label (lbl "register_evaluations") |>.append (p.evals.toList.map frLE).flatten
  let t := t.label (lbl "shifted_linearization_evaluation") |>.append (frLE p.linAtZetaOmega)
  let (nus, t) := frChallenges t "kzg_aggregation" 8
  let t := t.label (lbl "kzg_proof_zeta") |>.append (unc p.proofZeta)
  let t := t.label (lbl "kzg_proof_zeta_omega") |>.append (unc p.proofZetaOmega)
  let (rbs, _) := t.challenge (lbl "transcript_rng") 16
  let rnd := Field.ofLE rbs
  -- the domain evaluated at ζ (3 zero-knowledge rows)
  let om := omega dom
  let omInv := inv om
  let zn1 := sub (pow zeta dom) 1
  let prod := mul (mul (sub zeta omInv) (sub zeta (pow omInv 2))) (sub zeta (pow omInv 3))
  let notLast := sub zeta (pow omInv 4)
  let vanInv := mul prod (inv zn1)
  let znN := mul zn1 (inv dom)
  let lFirst := mul znN (inv (sub zeta 1))
  let lLast := mul znN (inv (sub (mul (pow om 4) zeta) 1))
  -- constraints
  let e := p.evals
  let (px, py, sel, b, ipa, ax, ay) := (e[0]!, e[1]!, e[2]!, e[3]!, e[4]!, e[5]!, e[6]!)
  let seed := k.seed
  let sr := (Curve.addE seed.toExt result.toExt).toAff
  let nb := sub 1 b
  let c0 := mul (sub (Fr.neg ipa) (mul sel b)) notLast
  let c1 := mul (sub (Fr.neg (mul b (add (mul ax ay) (mul px py)))) (mul nb ax)) notLast
  let c2 := mul (sub (Fr.neg (mul b (sub (mul ax ay) (mul px py)))) (mul nb ay)) notLast
  let c3 := mul b nb
  let c4 := add (mul (sub ax seed.x) lFirst) (mul (sub ax sr.x) lLast)
  let c5 := add (mul (sub ay seed.y) lFirst) (mul (sub ay sr.y) lLast)
  let c6 := add (mul ipa lFirst) (mul (sub ipa 1) lLast)
  let cs := [c0, c1, c2, c3, c4, c5, c6]
  let ev := (alphas.zip cs).foldl (fun acc (a, c) => add acc (mul a c)) 0
  let qZeta := mul (add ev p.linAtZetaOmega) vanInv
  -- aggregated opening at ζ
  let cols := [cx, cy, csel, p.cBits, p.cIpa, p.cAx, p.cAy, p.cQuot]
  let ys := e.toList ++ [qZeta]
  let cl := combine cols nus
  let aggY := (nus.zip ys).foldl (fun acc (n, y) => add acc (mul n y)) 0
  -- linearization commitment, opened at ζω
  let cAccX1 := mul (add (mul b (add (mul ay py) (mul Curve.A (mul ax px)))) nb) notLast
  let cAccY2 := mul (add (mul b (sub (mul ax py) (mul px ay))) nb) notLast
  let a := alphas.toArray
  let lin := combine [p.cIpa, p.cAx, p.cAy]
    [mul a[0]! notLast, mul a[1]! cAccX1, mul a[2]! cAccY2]
  let zetaOmega := mul zeta om
  -- KZG: e(Σ rᵢ(yᵢ·G − xᵢ·πᵢ − Cᵢ), G2) · e(Σ rᵢ·πᵢ, τG2) = 1, r = (1, rnd)
  let accA := G1.addJ (G1.smul g1.toJac (add aggY (mul rnd p.linAtZetaOmega)))
    (G1.negJ (G1.addJ (G1.addJ (G1.smul p.proofZeta.toJac zeta) cl)
      (G1.smul (G1.addJ (G1.smul p.proofZetaOmega.toJac zetaOmega) lin) rnd)))
  let accP := G1.addJ p.proofZeta.toJac (G1.smul p.proofZetaOmega.toJac rnd)
  return Pairing.pairingCheck [(accA.toAff, g2), (accP.toAff, tg2)]

/-- The Pedersen VRF equations. -/
def pedersenOk (input output pkCom r ok : Curve.Aff) (s sb : Nat) (ad : List UInt8) : Bool :=
  let c := challenge [pkCom, input, output, r, ok] ad
  let lhs1 := Curve.addE (Curve.smulW output.toExt c) ok.toExt
  let rhs1 := Curve.smulW input.toExt s
  let lhs2 := Curve.addE (Curve.smulW pkCom.toExt c) r.toExt
  let rhs2 := Curve.addE (Curve.smulW generator.toExt s) (Curve.smulW Curve.blindingBase.toExt sb)
  lhs1.eq rhs1 && lhs2.eq rhs2

def verify (srs : Srs) (ringSize : Nat) (root ctx msg proof : List UInt8) : Bool := Id.run do
  if root.length != 144 || proof.length != 784 then return false
  let some cx := G1.decompress (root.take 48) | return false
  let some cy := G1.decompress ((root.drop 48).take 48) | return false
  let some csel := G1.decompress (root.drop 96) | return false
  let pt (i : Nat) := Curve.decode ((proof.drop i).take 32)
  let some output := pt 0 | return false
  let some pkCom := pt 32 | return false
  let some r := pt 64 | return false
  let some ok := pt 96 | return false
  let some s := decodeScalar ((proof.drop 128).take 32) | return false
  let some sb := decodeScalar ((proof.drop 160).take 32) | return false
  let some rp := decodeRingProof (proof.drop 192) | return false
  let input := hashToCurve ctx
  if !pedersenOk input output pkCom r ok s sb msg then return false
  let dom := domainSize ringSize
  if srs.g1.size < dom then return false
  return ringProofOk srs dom cx cy csel pkCom rp

/-- `Ring.verify081`, as its elaborated term (with the reference's own match auxiliaries, so that it
    is equal to the reference by rewriting; restated from its source text, the two definitions'
    matchers make the kernel's comparison time out). -/
def verify081 (srs : Srs) (ringSize : Nat) (root ctx msg proof : List UInt8)
    (rd : Reading := .prose) : Bool :=
  (if (root.length != 144 || proof.length != 784) = Bool.true then Pure.pure Bool.false
    else
      JamCrypto.Ring.verify081.match_10 (fun (_ : Option JamCrypto.G1.Aff) => Id Bool)
        (JamCrypto.G1.decompress (List.take 48 root))
        (fun (cx : JamCrypto.G1.Aff) =>
          JamCrypto.Ring.verify081.match_10 (fun (_ : Option JamCrypto.G1.Aff) => Id Bool)
            (JamCrypto.G1.decompress (List.take 48 (List.drop 48 root)))
            (fun (cy : JamCrypto.G1.Aff) =>
              JamCrypto.Ring.verify081.match_10 (fun (_ : Option JamCrypto.G1.Aff) => Id Bool)
                (JamCrypto.G1.decompress (List.drop 96 root))
                (fun (csel : JamCrypto.G1.Aff) =>
                  JamCrypto.Ring.verify081.match_4 (fun (_ : Option JamCrypto.Point) => Id Bool)
                    (JamCrypto.Bandersnatch.decode (List.take 32 proof))
                    (fun (output : JamCrypto.Point) =>
                      JamCrypto.Ring.verify081.match_8
                        (fun (_ : Option JamCrypto.Bandersnatch.Pedersen.Proof) => Id Bool)
                        (JamCrypto.Bandersnatch.Pedersen.Proof.decode (List.take 160 (List.drop 32 proof)))
                        (fun (ped : JamCrypto.Bandersnatch.Pedersen.Proof) =>
                          JamCrypto.Ring.verify081.match_6 (fun (_ : Option JamCrypto.Ring.RingProof) => Id Bool)
                            (decodeRingProof (List.drop 192 proof))
                            (fun (rp : JamCrypto.Ring.RingProof) =>
                              JamCrypto.Ring.verify081.match_4 (fun (_ : Option JamCrypto.Point) => Id Bool)
                                (JamCrypto.Bandersnatch.Thin.hashToCurve ctx rd)
                                (fun (input : JamCrypto.Point) =>
                                  if (!JamCrypto.Bandersnatch.Pedersen.verify input output msg ped rd) = Bool.true then
                                    Pure.pure Bool.false
                                  else
                                    JamCrypto.Ring.verify081.match_1
                                      (fun (_ : Option JamCrypto.Ring.Curve.Aff) => Id Bool)
                                      (JamCrypto.Ring.Curve.decode (List.take 32 (List.drop 32 proof)))
                                      (fun (pkCom : JamCrypto.Ring.Curve.Aff) =>
                                        have dom : Nat := JamCrypto.Ring.domainSize ringSize
                                        if srs.g1.size < dom then Pure.pure Bool.false
                                        else
                                          Pure.pure
                                            (ringProofOk srs dom cx cy csel pkCom rp
                                              (JamCrypto.Ring.Consts.v081 rd)))
                                      fun (_ : Option JamCrypto.Ring.Curve.Aff) => Pure.pure Bool.false)
                                fun (_ : Option JamCrypto.Point) => Pure.pure Bool.false)
                            fun (_ : Option JamCrypto.Ring.RingProof) => Pure.pure Bool.false)
                        fun (_ : Option JamCrypto.Bandersnatch.Pedersen.Proof) => Pure.pure Bool.false)
                    fun (_ : Option JamCrypto.Point) => Pure.pure Bool.false)
                fun (_ : Option JamCrypto.G1.Aff) => Pure.pure Bool.false)
            fun (_ : Option JamCrypto.G1.Aff) => Pure.pure Bool.false)
        fun (_ : Option JamCrypto.G1.Aff) => Pure.pure Bool.false).run

/-- `Ring.crypto`, as its elaborated term (with the reference's match auxiliary). -/
def crypto (srs : Srs) (validators : Nat) (c : JAM.Crypto) (gp : GpVersion := .v080)
    (dom081 : Nat := domain081) (rd : Reading := .prose) : JAM.Crypto :=
  JamCrypto.Ring.crypto.match_1 (fun (_ : JamCrypto.GpVersion) => JAM.Crypto) gp
    (fun (_ : Unit) =>
      { edVerify := c.edVerify, bsVerify := c.bsVerify, bsOut := c.bsOut,
        bsRingRoot := fun (keys : List (List UInt8)) => root srs validators keys,
        bsRingVerify := verify srs validators, bsRingOut := JamCrypto.Ring.output })
    fun (_ : Unit) =>
    { edVerify := c.edVerify, bsVerify := c.bsVerify, bsOut := c.bsOut,
      bsRingRoot := fun (keys : List (List UInt8)) =>
        root srs (JamCrypto.Ring.keysetSize dom081) keys (JamCrypto.Ring.Consts.v081 rd),
      bsRingVerify := fun (root ctx msg proof : List UInt8) =>
        verify081 srs (JamCrypto.Ring.keysetSize dom081) root ctx msg proof rd,
      bsRingOut := JamCrypto.Ring.output081 }


theorem commitColumn_eq : @commitColumn = @JamCrypto.Ring.commitColumn := rfl
theorem commitPoints_eq : @commitPoints = @JamCrypto.Ring.commitPoints := rfl
theorem root_eq : @root = @JamCrypto.Ring.root := rfl
theorem withSelectors_eq : @withSelectors = @JamCrypto.Ring.withSelectors := rfl
theorem decodeRingProof_eq : @decodeRingProof = @JamCrypto.Ring.decodeRingProof := rfl
theorem combine_eq : @combine = @JamCrypto.Ring.combine := rfl
theorem ringProofOk_eq : @ringProofOk = @JamCrypto.Ring.ringProofOk := rfl
theorem pedersenOk_eq : @pedersenOk = @JamCrypto.Ring.pedersenOk := rfl
theorem verify_eq : @verify = @JamCrypto.Ring.verify := rfl
theorem verify081_eq : @verify081 = @JamCrypto.Ring.verify081 := by
  funext srs n root ctx msg proof rd
  delta verify081 JamCrypto.Ring.verify081
  rewrite [ringProofOk_eq, decodeRingProof_eq]
  rfl

theorem crypto_eq : @crypto = @JamCrypto.Ring.crypto := by
  funext srs n c gp dom rd
  delta crypto JamCrypto.Ring.crypto
  rewrite [root_eq, verify_eq, verify081_eq]
  rfl

/-! ## Compiled replacements (`@[csimp]`, see docs/fast-paths.md) -/

@[csimp] theorem root_csimp : @JamCrypto.Ring.root = @root := root_eq.symm
@[csimp] theorem withSelectors_csimp : @JamCrypto.Ring.withSelectors = @withSelectors := withSelectors_eq.symm
@[csimp] theorem verify_csimp : @JamCrypto.Ring.verify = @verify := verify_eq.symm
@[csimp] theorem verify081_csimp : @JamCrypto.Ring.verify081 = @verify081 := verify081_eq.symm
@[csimp] theorem crypto_csimp : @JamCrypto.Ring.crypto = @crypto := crypto_eq.symm

end JamCrypto.Ring.Fast
