import JamCrypto.Fast.Fr
import JamCrypto.Fast.EdwardsF
import JamCrypto.Bandersnatch
import JamCrypto.ThinVrf

/-!
# Bandersnatch on fixed-limb field arithmetic: IETF and Thin VRF verification, proved equal to the
reference

The functions here perform the same sequence of operations as `JamCrypto.Bandersnatch` and
`JamCrypto.Bandersnatch.Thin` (the reference implementations, unchanged), on `Fast.Fr` ($\mathbb{F}_q$
on 29-bit limbs) instead of `Nat` $\bmod q$. Each is proved equal to its reference (`ietfVerify_eq`,
`vrfOutput_eq`, `Thin.verify_eq`, `Thin.vrfOutput_eq`), from the field laws of `Fast.Fr` and the
curve lemmas of `Fast.EdwardsF`.
-/

namespace JamCrypto.Fast.Bandersnatch

open JamCrypto.Fast
open JamCrypto.Modular (leToNat beToNat natToLE slice subMod invMod isSquare)

/- The reference's exponentiations, inversions and square roots are proved equal to the fast ones
once (`Fast.EdwardsF`); here they stay folded, so that definitional unfolding never evaluates their
loops on symbolic arguments. -/
attribute [local irreducible] JamCrypto.Modular.powMod JamCrypto.Modular.isSquare
  JamCrypto.Modular.invMod JamCrypto.Modular.sqrtTS JamCrypto.Bandersnatch.sqrt

attribute [local irreducible] Fr.mul Fr.sq Fr.add Fr.sub Fr.ofNat Fr.toNat Fr.isZero Fr.beq Fr.inv
  JamCrypto.Fast.powF JamCrypto.Fast.sqrtF

abbrev F := Fr.Elem

local notation "p" => Field.p F

/-- The curve constants $a = -5$ and $d$. -/
@[irreducible] def C : CurveF F := ⟨Field.ofNat JamCrypto.Bandersnatch.curve.a, Field.ofNat JamCrypto.Bandersnatch.curve.d⟩

theorem curve_p : JamCrypto.Bandersnatch.curve.p = p := rfl

theorem q_eq : JamCrypto.Bandersnatch.q = p := rfl

theorem hC : C.Rel JamCrypto.Bandersnatch.curve := by
  unfold C; exact ⟨VRel.ofNat _, VRel.ofNat _, curve_p⟩

theorem vofNat (x : Nat) : VRel (Field.ofNat x : F) x := VRel.ofNat x
theorem vone : VRel (Field.one : F) 1 := VRel.one
theorem vzero : VRel (Field.zero : F) 0 := VRel.zero
theorem vmod {a : F} {n : Nat} (h : VRel a n) : VRel a (n % p) := VRel.mod.mpr h

/-- An optional point stands for an optional reference point. -/
abbrev OP : Option (Pt F) → Option JamCrypto.Point → Prop := OR PRel

/-- $q - 1 = 2^{32} \cdot t$. -/
def tOdd : Nat := 12208678567578594777604504606729831043093128246378069236549469339647

/-- $\sqrt{n}$ (as `Bandersnatch.sqrt`). -/
def sqrt (n : F) : Option F := sqrtF 32 tOdd (Field.ofNat 7) n

theorem sqrt_rel {n : F} {n' : Nat} (hn : VRel n n') : ORel (sqrt n) (JamCrypto.Bandersnatch.sqrt n') := by
  unfold JamCrypto.Bandersnatch.sqrt; exact sqrtF_rel (VRel.ofNat 7) hn

/-- The 32-octet encoding of a valid point (as `Bandersnatch.encode`). -/
def encode (P : Pt F) : List UInt8 :=
  let (x, y) := CurveF.toAffine P
  natToLE 32 (y + (if x > (JamCrypto.Bandersnatch.q - 1) / 2 then 2 ^ 255 else 0))

theorem encode_eq {P : Pt F} {P' : JamCrypto.Point} (h : PRel P P') :
    encode P = JamCrypto.Bandersnatch.encode P' := by
  unfold encode JamCrypto.Bandersnatch.encode
  rw [toAffine_eq curve_p h]

/-- As `Bandersnatch.decodeOnCurve`. -/
def decodeOnCurve (bs : List UInt8) : Option (Pt F) := do
  guard (bs.length == 32)
  let n := leToNat bs
  let negative := n / 2 ^ 255 == 1
  let y := n % 2 ^ 255
  guard (y < JamCrypto.Bandersnatch.q)
  let yF : F := Field.ofNat y
  let y2 := Field.mul yF yF
  let den := Field.sub C.a (Field.mul C.d y2)
  guard (!Field.isZero den)
  let x ← sqrt (Field.mul (Field.sub Field.one y2) (invF den))
  let xn := Field.toNat x
  let mn := Field.toNat (Field.sub Field.zero x)
  let small := min xn mn
  let large := max xn mn
  return ofAffineF (Field.ofNat (if negative then large else small)) yF

theorem decodeOnCurve_rel (bs : List UInt8) :
    OP (decodeOnCurve bs) (JamCrypto.Bandersnatch.decodeOnCurve bs) := by
  unfold decodeOnCurve JamCrypto.Bandersnatch.decodeOnCurve
  refine OR.guard Iff.rfl fun _ => OR.guard Iff.rfl fun _ => ?_
  have hy := VRel.ofNat (F := F) (leToNat bs % 2 ^ 255)
  have hy2 := VRel.mod.mpr (hy.mul hy)
  have hden := hC.1.sub (VRel.mod.mpr (hC.2.1.mul hy2))
  refine OR.guard ?_ fun _ => ?_
  · rw [hden.isZero]; simp only [q_eq, subMod, Nat.mod_mod]; simp [bne]
  refine OR.bind (sqrt_rel (VRel.mod.mpr ((VRel.one.sub hy2).mul (invF_rel hden)))) ?_
  rintro x x' ⟨hx, hx'⟩
  have hm := VRel.zero.sub hx
  rw [hx.toNat, hm.toNat, Nat.mod_eq_of_lt hx']
  simp only [q_eq, subMod, Nat.mod_mod]
  exact ofAffine_rel curve_p (VRel.ofNat _) hy

/-- As `Bandersnatch.inSubgroup`. -/
def inSubgroup (P : Pt F) : Bool := CurveF.eq (C.smul (JamCrypto.Bandersnatch.r - 1) P) (CurveF.neg P)

theorem inSubgroup_eq {P : Pt F} {P' : JamCrypto.Point} (h : PRel P P') :
    inSubgroup P = JamCrypto.Bandersnatch.inSubgroup P' := by
  unfold inSubgroup JamCrypto.Bandersnatch.inSubgroup
  exact eq_eq curve_p (smul_rel hC _ h) (neg_rel curve_p h)

/-- As `Bandersnatch.decode`. -/
def decode (bs : List UInt8) : Option (Pt F) := do
  let P ← decodeOnCurve bs
  guard (inSubgroup P)
  return P

theorem decode_rel (bs : List UInt8) : OP (decode bs) (JamCrypto.Bandersnatch.decode bs) := by
  unfold decode JamCrypto.Bandersnatch.decode
  refine OR.bind (decodeOnCurve_rel bs) fun P P' h => ?_
  exact OR.guard (by rw [inSubgroup_eq h]) fun _ => h

/-! ### Hash to curve -/

/-- As `Bandersnatch.elligator2`. -/
def elligator2 (u : Nat) : Option (Pt F) := do
  let k : F := Field.ofNat JamCrypto.Bandersnatch.montB
  let j : F := Field.ofNat JamCrypto.Bandersnatch.montAoverB
  let uF : F := Field.ofNat u
  let den1 := Field.add Field.one (Field.mul (Field.ofNat 5) (Field.mul uF uF))
  let x1 := Field.sub Field.zero (Field.mul j (invF (if Field.isZero den1 then Field.one else den1)))
  let g := fun (x : F) => Field.add (Field.add (Field.mul (Field.mul x x) x) (Field.mul j (Field.mul x x)))
    (Field.mul x (Field.ofNat JamCrypto.Bandersnatch.oneOverB2))
  let gx1 := g x1
  let x2 := Field.sub (Field.sub Field.zero x1) j
  let odd := isSquareF gx1
  let x := if odd then x1 else x2
  let y0 ← sqrt (g x)
  let y := if (Field.toNat y0 % 2 == 1) != odd then Field.sub Field.zero y0 else y0
  let s := Field.mul x k
  let t := Field.mul y k
  let tv1 := Field.add s Field.one
  let tv2 := Field.mul tv1 t
  if Field.isZero tv2 then return ofAffineF Field.zero Field.one
  let inv := invF tv2
  return ofAffineF (Field.mul (Field.mul inv tv1) s) (Field.mul (Field.mul inv t) (Field.sub s Field.one))

theorem elligator2_rel (u : Nat) : OP (elligator2 u) (JamCrypto.Bandersnatch.elligator2 u) := by
  unfold elligator2 JamCrypto.Bandersnatch.elligator2
  extract_lets k j uF den1 x1 g gx1 x2 odd x s tv1 k' j' den1' x1' g' gx1' x2' odd' x' s' tv1'
  have vk : VRel k k' := vofNat _
  have vj : VRel j j' := vofNat _
  have vu : VRel uF u := vofNat _
  have vden1 : VRel den1 den1' := vmod (vone.add ((vofNat 5).mul (vmod (vu.mul vu))))
  have hlt : ∀ n, n % JamCrypto.Bandersnatch.q < p := fun n => lt_of_mod (F := F) (n := n)
  have hden1 : den1' < p := hlt _
  have hd0 : Field.isZero den1 = (den1' == 0) := by rw [vden1.isZero, Nat.mod_eq_of_lt hden1]
  have vsel : VRel (if Field.isZero den1 = true then Field.one else den1)
      (if (den1' == 0) = true then 1 else den1') := by
    rw [hd0]; split
    · exact vone
    · exact vden1
  have vx1 : VRel x1 x1' := vzero.sub (vmod (vj.mul (invF_rel vsel)))
  have hg : ∀ {a : F} {a' : Nat}, VRel a a' → VRel (g a) (g' a') := fun ha =>
    vmod ((((vmod (ha.mul ha)).mul ha).add (vj.mul (vmod (ha.mul ha)))).add (ha.mul (vofNat _)))
  have vgx1 : VRel gx1 gx1' := hg vx1
  have vx2 : VRel x2 x2' := (vzero.sub vx1).sub vj
  have hodd : odd = odd' := isSquareF_eq vgx1 (hlt _)
  have vx : VRel x x' := by
    show VRel (if odd = true then x1 else x2) (if odd' = true then x1' else x2')
    rw [hodd]; split
    · exact vx1
    · exact vx2
  have vs : VRel s s' := vmod (vx.mul vk)
  have vtv1 : VRel tv1 tv1' := vmod (vs.add vone)
  refine OR.bind (sqrt_rel (hg vx)) ?_
  rintro y0 y0' ⟨hy0, hy0'⟩
  extract_lets y t tv2 inv y' t' tv2' inv'
  have vy : VRel y y' := by
    show VRel (if ((Field.toNat y0 % 2 == 1) != odd) = true then Field.sub Field.zero y0 else y0)
      (if ((y0' % 2 == 1) != odd') = true then subMod 0 y0' JamCrypto.Bandersnatch.q else y0')
    rw [hy0.toNat, Nat.mod_eq_of_lt hy0', hodd]; split
    · exact vzero.sub hy0
    · exact hy0
  have vt : VRel t t' := vmod (vy.mul vk)
  have vtv2 : VRel tv2 tv2' := vmod (vtv1.mul vt)
  have htv2 : tv2' < p := hlt _
  rw [vtv2.isZero, Nat.mod_eq_of_lt htv2]
  refine OR.ite (fun _ => ofAffine_rel curve_p vzero vone) fun _ => ?_
  exact ofAffine_rel curve_p (vmod ((vmod ((invF_rel vtv2).mul vtv1)).mul vs))
    (vmod ((vmod ((invF_rel vtv2).mul vt)).mul (vs.sub vone)))

/-- As `Bandersnatch.hashToCurve`. -/
def hashToCurve (data : List UInt8) : Option (Pt F) := do
  let u := JamCrypto.Bandersnatch.expandMessage data
  let P0 ← elligator2 (beToNat (u.take 48) % JamCrypto.Bandersnatch.q)
  let P1 ← elligator2 (beToNat (u.drop 48) % JamCrypto.Bandersnatch.q)
  let P := C.smul 4 (C.add P0 P1)
  guard (CurveF.valid P)
  return P

theorem hashToCurve_rel (data : List UInt8) : OP (hashToCurve data) (JamCrypto.Bandersnatch.hashToCurve data) := by
  unfold hashToCurve JamCrypto.Bandersnatch.hashToCurve
  refine OR.bind (elligator2_rel _) fun P0 P0' h0 => OR.bind (elligator2_rel _) fun P1 P1' h1 => ?_
  have hP := smul_rel hC 4 (add_rel hC h0 h1)
  exact OR.guard (by rw [valid_eq curve_p hP]) fun _ => hP

/-! ### IETF VRF -/

/-- The generator. -/
@[irreducible] def G : Pt F := ofAffineF (Field.ofNat 18886178867200960497001835917649091219057080094937609519140440539760939937304)
  (Field.ofNat 19188667384257783945677642223292697773471335439753913231509108946878080696678)

theorem G_rel : PRel G JamCrypto.Bandersnatch.G := by
  unfold G; exact ofAffine_rel curve_p (vofNat _) (vofNat _)

/-- As `Bandersnatch.challenge`. -/
def challenge (pts : List (Pt F)) (ad : List UInt8) : Nat :=
  let h := JAM.Sha512.hash (JamCrypto.Bandersnatch.suiteString ++ [2] ++ pts.flatMap encode ++ ad ++ [0])
  beToNat (h.take 32) % JamCrypto.Bandersnatch.r

theorem challenge_eq5 {a b c d e : Pt F} {a' b' c' d' e' : JamCrypto.Point} (ha : PRel a a')
    (hb : PRel b b') (hc : PRel c c') (hd : PRel d d') (he : PRel e e') (ad : List UInt8) :
    challenge [a, b, c, d, e] ad = JamCrypto.Bandersnatch.challenge [a', b', c', d', e'] ad := by
  unfold challenge JamCrypto.Bandersnatch.challenge
  simp only [List.flatMap_cons, List.flatMap_nil, encode_eq ha, encode_eq hb, encode_eq hc, encode_eq hd,
    encode_eq he]

/-- As `Bandersnatch.ietfVerify`. -/
def ietfVerify (key ctx msg sig : List UInt8) : Bool := Id.run do
  if key.length != 32 || sig.length != 96 then return false
  let s := leToNat (slice sig 64 32)
  if s ≥ JamCrypto.Bandersnatch.r then return false
  let c := leToNat (slice sig 32 32) % JamCrypto.Bandersnatch.r
  let some Y := decode key | return false
  let some O := decode (sig.take 32) | return false
  let some I := hashToCurve ctx | return false
  let U := C.sub (C.smul s G) (C.smul c Y)
  let V := C.sub (C.smul s I) (C.smul c O)
  if !(CurveF.valid U && CurveF.valid V) then return false
  return challenge [Y, I, O, U, V] msg == c

theorem ietfVerify_eq (key ctx msg sig : List UInt8) :
    ietfVerify key ctx msg sig = JamCrypto.Bandersnatch.ietfVerify key ctx msg sig := by
  unfold ietfVerify JamCrypto.Bandersnatch.ietfVerify
  rw [Id.run, Id.run]
  by_cases h1 : (key.length != 32 || sig.length != 96) = true
  · rw [if_pos h1, if_pos h1]
  rw [if_neg h1, if_neg h1]
  -- the match discriminants first, so that no check ever reduces them
  have hY := decode_rel key
  have hO := decode_rel (sig.take 32)
  have hI := hashToCurve_rel ctx
  generalize decode key = a at hY ⊢
  generalize JamCrypto.Bandersnatch.decode key = a' at hY ⊢
  generalize decode (sig.take 32) = b at hO ⊢
  generalize JamCrypto.Bandersnatch.decode (sig.take 32) = b' at hO ⊢
  generalize hashToCurve ctx = i at hI ⊢
  generalize JamCrypto.Bandersnatch.hashToCurve ctx = i' at hI ⊢
  cases a <;> cases a' <;> simp only [OR] at hY
  all_goals cases b <;> cases b' <;> simp only [OR] at hO
  all_goals cases i <;> cases i' <;> simp only [OR] at hI
  all_goals dsimp (config := {zeta := false}) only
  rename_i Y Y' O O' I I'
  extract_lets s c U V E U' V'
  by_cases h2 : s ≥ JamCrypto.Bandersnatch.r
  · rw [if_pos h2, if_pos h2]
  rw [if_neg h2, if_neg h2]
  have hU : PRel U U' := sub_rel hC (smul_rel hC s G_rel) (smul_rel hC c hY)
  have hV : PRel V V' := sub_rel hC (smul_rel hC s hI) (smul_rel hC c hO)
  rw [valid_eq (E := E) curve_p hU, valid_eq (E := E) curve_p hV, challenge_eq5 hY hI hO hU hV]

/-- As `Bandersnatch.vrfOutput`. -/
def vrfOutput (sig : List UInt8) : List UInt8 :=
  match decodeOnCurve (sig.take 32) with
  | some O => (JAM.Sha512.hash (JamCrypto.Bandersnatch.suiteString ++ [3] ++ encode O ++ [0])).take 32
  | none => JamCrypto.Bandersnatch.octetOutput sig

theorem vrfOutput_eq (sig : List UInt8) : vrfOutput sig = JamCrypto.Bandersnatch.vrfOutput sig := by
  unfold vrfOutput JamCrypto.Bandersnatch.vrfOutput JamCrypto.Bandersnatch.pointToHash
  have h := decodeOnCurve_rel (sig.take 32)
  generalize decodeOnCurve (sig.take 32) = a at h ⊢
  generalize JamCrypto.Bandersnatch.decodeOnCurve (sig.take 32) = a' at h ⊢
  cases a <;> cases a' <;> simp only [OR] at h <;> try rfl
  dsimp only
  rw [encode_eq h]

/-! ## Thin VRF (GP v0.8.1) -/

namespace Thin

open JamCrypto.Bandersnatch.Thin (Transcript tagThinVrf tagDelinearize tagChallenge tagPointToHash
  challengeLen enc64 decScalarMod)

/-- As `Bandersnatch.Thin.hashToCurve`. -/
def hashToCurve (data : List UInt8) (rd : Reading) : Option (Pt F) := do
  let u := JamCrypto.Bandersnatch.Thin.expandMessage data rd
  let P0 ← elligator2 (beToNat (u.take 48) % JamCrypto.Bandersnatch.q)
  let P1 ← elligator2 (beToNat (u.drop 48) % JamCrypto.Bandersnatch.q)
  let P := C.smul 4 (C.add P0 P1)
  guard (CurveF.valid P)
  return P

theorem hashToCurve_rel (data : List UInt8) (rd : Reading) :
    OP (hashToCurve data rd) (JamCrypto.Bandersnatch.Thin.hashToCurve data rd) := by
  unfold hashToCurve JamCrypto.Bandersnatch.Thin.hashToCurve
  refine OR.bind (elligator2_rel _) fun P0 P0' h0 => OR.bind (elligator2_rel _) fun P1 P1' h1 => ?_
  have hP := smul_rel hC 4 (add_rel hC h0 h1)
  exact OR.guard (by rw [valid_eq curve_p hP]) fun _ => hP

/-- As `Bandersnatch.Thin.output`. -/
def output (O : Pt F) (n : Nat := 32) : List UInt8 :=
  (Transcript.new.absorb ([tagPointToHash] ++ encode O)).squeeze n

theorem output_eq {O : Pt F} {O' : JamCrypto.Point} (h : PRel O O') (n : Nat) :
    output O n = JamCrypto.Bandersnatch.Thin.output O' n := by
  unfold output JamCrypto.Bandersnatch.Thin.output
  rw [encode_eq h]

/-- As `Bandersnatch.Thin.vrfTranscript`. -/
def vrfTranscript (Y I O : Pt F) (ad : List UInt8) : Transcript × Pt F × Pt F :=
  let t := Transcript.new.absorb
    ([tagThinVrf] ++ enc64 2 ++ encode G ++ encode Y ++ encode I ++ encode O ++ enc64 ad.length ++ ad)
  let z := decScalarMod ((t.absorb [tagDelinearize]).squeeze challengeLen)
  (t, C.add G (C.smul z I), C.add Y (C.smul z O))

/-- The transcripts agree and the merged pairs are related. -/
def TRel (a : Transcript × Pt F × Pt F) (b : Transcript × JamCrypto.Point × JamCrypto.Point) : Prop :=
  a.1 = b.1 ∧ PRel a.2.1 b.2.1 ∧ PRel a.2.2 b.2.2

theorem vrfTranscript_rel {Y I O : Pt F} {Y' I' O' : JamCrypto.Point} (hY : PRel Y Y') (hI : PRel I I')
    (hO : PRel O O') (ad : List UInt8) :
    TRel (vrfTranscript Y I O ad) (JamCrypto.Bandersnatch.Thin.vrfTranscript Y' I' O' ad) := by
  unfold vrfTranscript JamCrypto.Bandersnatch.Thin.vrfTranscript
  rw [encode_eq G_rel, encode_eq hY, encode_eq hI, encode_eq hO]
  exact ⟨rfl, add_rel hC G_rel (smul_rel hC _ hI), add_rel hC hY (smul_rel hC _ hO)⟩

/-- As `Bandersnatch.Thin.challenge`. -/
def challenge (R : Pt F) (t : Transcript) : Nat :=
  decScalarMod ((t.absorb ([tagChallenge] ++ encode R)).squeeze challengeLen)

theorem challenge_eq {R : Pt F} {R' : JamCrypto.Point} (h : PRel R R') (t : Transcript) :
    challenge R t = JamCrypto.Bandersnatch.Thin.challenge R' t := by
  unfold challenge JamCrypto.Bandersnatch.Thin.challenge
  rw [encode_eq h]

/-- As `Bandersnatch.Thin.thinDecode`. -/
def thinDecode (sig : List UInt8) : Option (Pt F × Pt F × Nat) := do
  guard (sig.length == 96)
  let O ← decode (sig.take 32)
  let R ← decode (slice sig 32 32)
  let s := leToNat (slice sig 64 32)
  guard (s < JamCrypto.Bandersnatch.r)
  return (O, R, s)

/-- Decoded signatures agree. -/
def DRel (a : Pt F × Pt F × Nat) (b : JamCrypto.Point × JamCrypto.Point × Nat) : Prop :=
  PRel a.1 b.1 ∧ PRel a.2.1 b.2.1 ∧ a.2.2 = b.2.2

theorem thinDecode_rel (sig : List UInt8) :
    OR DRel (thinDecode sig) (JamCrypto.Bandersnatch.Thin.thinDecode sig) := by
  unfold thinDecode JamCrypto.Bandersnatch.Thin.thinDecode
  refine OR.guard Iff.rfl fun _ => ?_
  refine OR.bind (decode_rel _) fun O O' hO => ?_
  refine OR.bind (decode_rel _) fun R R' hR => ?_
  exact OR.guard Iff.rfl fun _ => ⟨hO, hR, rfl⟩

/-- As `Bandersnatch.Thin.verify`. -/
def verify (key ctx msg sig : List UInt8) (rd : Reading := .prose) : Bool := Id.run do
  if key.length != 32 then return false
  let some Y := decode key | return false
  let some (O, R, s) := thinDecode sig | return false
  let some I := hashToCurve ctx rd | return false
  if CurveF.isZero Y || CurveF.isZero I || CurveF.isZero O then return false
  let (t, Im, Om) := vrfTranscript Y I O msg
  let c := challenge R t
  let lhs := C.smul s Im
  let rhs := C.add R (C.smul c Om)
  return CurveF.valid lhs && CurveF.valid rhs && CurveF.eq lhs rhs

theorem verify_eq (key ctx msg sig : List UInt8) (rd : Reading) :
    verify key ctx msg sig rd = JamCrypto.Bandersnatch.Thin.verify key ctx msg sig rd := by
  unfold verify JamCrypto.Bandersnatch.Thin.verify
  rw [Id.run, Id.run]
  by_cases h1 : (key.length != 32) = true
  · rw [if_pos h1, if_pos h1]
  rw [if_neg h1, if_neg h1]
  have hY := decode_rel key
  have hD := thinDecode_rel sig
  have hI := hashToCurve_rel ctx rd
  generalize decode key = a at hY ⊢
  generalize JamCrypto.Bandersnatch.decode key = a' at hY ⊢
  generalize thinDecode sig = d at hD ⊢
  generalize JamCrypto.Bandersnatch.Thin.thinDecode sig = d' at hD ⊢
  generalize hashToCurve ctx rd = i at hI ⊢
  generalize JamCrypto.Bandersnatch.Thin.hashToCurve ctx rd = i' at hI ⊢
  cases a <;> cases a' <;> simp only [OR] at hY
  all_goals cases d <;> cases d' <;> simp only [OR] at hD
  all_goals cases i <;> cases i' <;> simp only [OR] at hI
  all_goals dsimp (config := {zeta := false}) only
  rename_i Y Y' D D' I I'
  obtain ⟨O, R, s⟩ := D
  obtain ⟨O', R', s'⟩ := D'
  obtain ⟨hO, hR, hs⟩ := hD
  dsimp only at hs
  subst hs
  dsimp (config := {zeta := false}) only
  rw [isZero_eq curve_p hY, isZero_eq curve_p hI, isZero_eq curve_p hO]
  by_cases h2 : (JamCrypto.Bandersnatch.curve.isZero Y' || JamCrypto.Bandersnatch.curve.isZero I' ||
      JamCrypto.Bandersnatch.curve.isZero O') = true
  · rw [if_pos h2, if_pos h2]
  rw [if_neg h2, if_neg h2]
  have hT := vrfTranscript_rel hY hI hO msg
  generalize vrfTranscript Y I O msg = tr at hT ⊢
  generalize JamCrypto.Bandersnatch.Thin.vrfTranscript Y' I' O' msg = tr' at hT ⊢
  obtain ⟨t, Im, Om⟩ := tr
  obtain ⟨t', Im', Om'⟩ := tr'
  obtain ⟨ht, hIm, hOm⟩ := hT
  dsimp only at ht hIm hOm
  subst ht
  dsimp (config := {zeta := false}) only
  extract_lets c lhs rhs c' lhs' rhs'
  have hl : PRel lhs lhs' := smul_rel hC s hIm
  have hr : PRel rhs rhs' := by
    show PRel (C.add R (C.smul c Om)) (JamCrypto.Bandersnatch.curve.add R' (JamCrypto.Bandersnatch.curve.smul c' Om'))
    rw [show c = c' from challenge_eq hR t]
    exact add_rel hC hR (smul_rel hC _ hOm)
  rw [valid_eq curve_p hl, valid_eq curve_p hr, eq_eq curve_p hl hr]

/-- As `Bandersnatch.Thin.vrfOutput`. -/
def vrfOutput (sig : List UInt8) : List UInt8 :=
  match decodeOnCurve (sig.take 32) with
  | some O => output O
  | none => (Transcript.new.absorb ([tagPointToHash] ++ sig.take 32)).squeeze 32

theorem vrfOutput_eq (sig : List UInt8) :
    vrfOutput sig = JamCrypto.Bandersnatch.Thin.vrfOutput sig := by
  unfold vrfOutput JamCrypto.Bandersnatch.Thin.vrfOutput
  have h := decodeOnCurve_rel (sig.take 32)
  generalize decodeOnCurve (sig.take 32) = a at h ⊢
  generalize JamCrypto.Bandersnatch.decodeOnCurve (sig.take 32) = a' at h ⊢
  cases a <;> cases a' <;> simp only [OR] at h <;> try rfl
  dsimp only
  rw [output_eq h]

end Thin

end JamCrypto.Fast.Bandersnatch
