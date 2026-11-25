import JAM.Sha512
import JamCrypto.RingRoot
import JamCrypto.RingTranscript
import JamCrypto.Bls12381Pairing

/-!
# Ring VRF verification (GP v0.8.0 Appendix G)

x ∈ 𝔹̄°_r⟨c⟩⟨m⟩ for a ring root r, context c and message m: the 784-octet x is the VRF output
point O (32 octets) followed by a ring VRF proof (Bandersnatch VRF spec, ring VRF; as ark-vrf
0.1.0 serializes it), which is a Pedersen VRF proof (160 octets) and a ring proof (592 octets,
eprint 2023/002 as implemented by w3f ring-proof 0.0.2). The VRF input is I = H2C(c) and m is the
additional data.

Verification:
1. Pedersen VRF (Bandersnatch VRF spec §4): the proof (Y_b, R, O_k, s, s_b) satisfies
   O_k + c·O = s·I and R + c·Y_b = s·G + s_b·B, with c = challenge(Y_b, I, O, R, O_k, m).
2. Ring proof: the key commitment Y_b is the blinded key of a ring member. The verifier replays
   the Fiat–Shamir transcript (`Transcript`), evaluates the seven PIOP constraints at the
   challenge point ζ, and checks the two KZG openings (at ζ and ζω) with one pairing product.

Hash to curve: RFC 9380 hash_to_curve with expand_message_xmd(SHA-512) and the Elligator 2 map
of the curve's Montgomery form, as arkworks 0.5 implements it (suite
`Bandersnatch_XMD:SHA-512_ELL2_RO_`, DST `ECVRF_` ⌢ suite ⌢ `Bandersnatch_SHA-512_ELL2`; note
arkworks pads with 48 zero octets, its field-element length, where RFC 9380 says the hash block
size).
-/

namespace JamCrypto.Ring

open JamCrypto.Fr

/-- The suite string. -/
def suiteId : List UInt8 := "Bandersnatch_SHA-512_ELL2".toUTF8.toList

def sha512 (bs : List UInt8) : List UInt8 := JAM.Sha512.hash bs

/-! ## Hash to curve -/

/-- The Montgomery form B·v² = u³ + A·u² + u of Bandersnatch (arkworks `MontCurveConfig`). -/
def montA : Nat := 29978822694968839326280996386011761570173833766074948509196803838190355340952
def montB : Nat := 25465760566081946422412445027709227188579564747101592991722834452325077642517
/-- The non-square Z of the Elligator 2 map. -/
def ell2Z : Nat := 5

/-- expand_message_xmd(SHA-512) to 96 octets, then two field elements (48 octets each, big
    endian, reduced). -/
def hashToField (msg : List UInt8) : Nat × Nat :=
  let dst := "ECVRF_Bandersnatch_XMD:SHA-512_ELL2_RO_".toUTF8.toList ++ suiteId
  let dstPrime := dst ++ [UInt8.ofNat dst.length]
  let b0 := sha512 (List.replicate 48 0 ++ msg ++ [0, 96, 0] ++ dstPrime)
  let b1 := sha512 (b0 ++ [1] ++ dstPrime)
  let b2 := sha512 ((List.zipWith (· ^^^ ·) b0 b1) ++ [2] ++ dstPrime)
  let u := b1 ++ b2
  (Field.ofBE (u.take 48) % R, Field.ofBE ((u.drop 48).take 48) % R)

/-- a is a non-zero square. -/
def isQR (a : Nat) : Bool := a % R != 0 && pow a ((R - 1) / 2) == 1

/-- The Elligator 2 map to the twisted Edwards curve (arkworks `Elligator2Map`). -/
def ell2Map (e : Nat) : Curve.Aff :=
  let k := montB
  let jk := mul montA (inv montB)
  let ksqInv := inv (sq montB)
  let den1 := add 1 (mul ell2Z (sq e))
  let x1 := Fr.neg (mul jk (inv (if den1 == 0 then 1 else den1)))
  let g (x : Nat) := add (add (mul (sq x) x) (mul jk (sq x))) (mul x ksqInv)
  let gx1 := g x1
  let x2 := sub (Fr.neg x1) jk
  let (x, y0, sgn0) :=
    if isQR gx1 then (x1, (sqrt? gx1).getD 0, true) else (x2, (sqrt? (g x2)).getD 0, false)
  let y := if (y0 % 2 == 1) != sgn0 then Fr.neg y0 else y0
  let s := mul x k
  let t := mul y k
  let tv1 := add s 1
  let tv2 := mul tv1 t
  if tv2 == 0 then Curve.Aff.zero else
  let i := inv tv2
  ⟨mul (mul i tv1) s, mul (mul i t) (sub s 1)⟩

/-- The VRF input point of the data: hash to curve, then clear the cofactor 4. -/
def hashToCurve (data : List UInt8) : Curve.Aff :=
  let (u0, u1) := hashToField data
  let p := Curve.addE (ell2Map u0).toExt (ell2Map u1).toExt
  (Curve.dblE (Curve.dblE p)).toAff

/-! ## Pedersen VRF -/

/-- The Bandersnatch generator G. -/
def generator : Curve.Aff :=
  ⟨18886178867200960497001835917649091219057080094937609519140440539760939937304,
   19188667384257783945677642223292697773471335439753913231509108946878080696678⟩

/-- challenge(P₁ … Pₙ, ad): SHA-512(suite ⌢ 2 ⌢ points ⌢ ad ⌢ 0), first 32 octets as a big-endian
    number mod the subgroup order. -/
def challenge (pts : List Curve.Aff) (ad : List UInt8) : Nat :=
  let h := sha512 (suiteId ++ [2] ++ (pts.map Curve.encode).flatten ++ ad ++ [0])
  Field.ofBE (h.take 32) % Curve.N

/-- A Bandersnatch scalar: 32 octets little endian, below the subgroup order. -/
def decodeScalar (bs : List UInt8) : Option Nat :=
  let v := Field.ofLE bs
  if bs.length == 32 && v < Curve.N then some v else none

/-- An element of 𝔽_r (BLS12-381 scalar): 32 octets little endian, below r. -/
def decodeFr (bs : List UInt8) : Option Nat :=
  let v := Field.ofLE bs
  if bs.length == 32 && v < R then some v else none

/-- The Pedersen VRF equations. -/
def pedersenOk (input output pkCom r ok : Curve.Aff) (s sb : Nat) (ad : List UInt8) : Bool :=
  let c := challenge [pkCom, input, output, r, ok] ad
  let lhs1 := Curve.addE (Curve.smulW output.toExt c) ok.toExt
  let rhs1 := Curve.smulW input.toExt s
  let lhs2 := Curve.addE (Curve.smulW pkCom.toExt c) r.toExt
  let rhs2 := Curve.addE (Curve.smulW generator.toExt s) (Curve.smulW Curve.blindingBase.toExt sb)
  lhs1.eq rhs1 && lhs2.eq rhs2

/-! ## Ring proof -/

/-- The ring proof (w3f ring-proof `RingProof`, in serialization order). -/
structure RingProof where
  /-- Commitments to the bits, inner-product accumulator, and accumulator x, y columns. -/
  cBits : G1.Aff
  cIpa : G1.Aff
  cAx : G1.Aff
  cAy : G1.Aff
  /-- Evaluations at ζ: points x, y, selector, bits, inner-product accumulator, accumulator x, y. -/
  evals : Array Nat
  cQuot : G1.Aff
  linAtZetaOmega : Nat
  proofZeta : G1.Aff
  proofZetaOmega : G1.Aff

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

/-- Σ kᵢ·Pᵢ for a few points. -/
def combine (pts : List G1.Aff) (ks : List Nat) : G1.Jac :=
  (pts.zip ks).foldl (fun acc (p, k) => G1.addJ acc (G1.smul p.toJac k)) G1.Jac.zero

/-- 32 little-endian octets of an 𝔽_r element. -/
def frLE (x : Nat) : List UInt8 := Field.toLE 32 x

/-- A challenge in 𝔽_r: 48 XOF octets as a big-endian number, reduced. -/
def frChallenge (t : Transcript) (l : String) : Nat × Transcript :=
  let (bs, t) := t.challenge l.toUTF8.toList 48
  (Field.ofBE bs % R, t)

def frChallenges (t : Transcript) (l : String) (n : Nat) : List Nat × Transcript := Id.run do
  let mut t := t
  let mut out : Array Nat := #[]
  for _ in [0:n] do
    let (c, t') := frChallenge t l
    out := out.push c
    t := t'
  return (out.toList, t)

/-- The ring proof verifier: the ring with commitment (cx, cy, csel) over domain size N holds a
    key k with k + b·H = `result` for some b. -/
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

/-- x ∈ 𝔹̄°_r⟨c⟩⟨m⟩ (GP Appendix G) for rings of up to `ringSize` keys (JAM: V). -/
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

/-- Y(x) (GP Appendix G): the 32-octet VRF output of a ring VRF signature, the hash of its output
    point: SHA-512(suite ⌢ 3 ⌢ O ⌢ 0), first 32 octets. -/
def output (proof : List UInt8) : List UInt8 :=
  (sha512 (suiteId ++ [3] ++ proof.take 32 ++ [0])).take 32

end JamCrypto.Ring
