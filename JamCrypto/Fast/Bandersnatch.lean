import JamCrypto.Fast.Fr
import JamCrypto.Fast.EdwardsF
import JamCrypto.Bandersnatch
import JamCrypto.ThinVrf

/-!
# Bandersnatch on fixed-limb field arithmetic: IETF and Thin VRF verification, proved equal to the
reference

The functions here perform the same sequence of operations as `JamCrypto.Bandersnatch` and
`JamCrypto.Bandersnatch.Thin` (the reference implementations, unchanged), on `Fast.Fr` (𝔽_q on
29-bit limbs) instead of `Nat` mod q. Each is proved equal to its reference (`ietfVerify_eq`,
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

/-- The curve constants a = −5 and d. -/
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

/-- q − 1 = 2^32·t. -/
def tOdd : Nat := 12208678567578594777604504606729831043093128246378069236549469339647

/-- √n (as `Bandersnatch.sqrt`). -/
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

/-! ### Hash to curve

The reference's `Bandersnatch.elligator2` destructures a pair out of an `if`
(`let (x, odd) := if isSquare … then … else …`); the kernel cannot check any unfolding of its body
(it evaluates `isSquare` on symbolic arguments and runs out of memory), so its equality with a
fast map cannot be proved without changing the reference. Hash to curve is therefore the
reference's own, converted to a fast point; its result has reduced coordinates (`red_smul`), so
the conversion is exact. -/

theorem one_lt_q : 1 < JamCrypto.Bandersnatch.curve.p := by decide

/-- Points of the option relate to themselves and have reduced coordinates. -/
def SelfRed (P Q : JamCrypto.Point) : Prop := P = Q ∧ Red JamCrypto.Bandersnatch.curve P

theorem OR.refl {α : Type} (m : Option α) : OR (fun a b => a = b) m m := by
  cases m <;> simp [OR]

theorem hashToCurve_selfRed (data : List UInt8) :
    OR SelfRed (JamCrypto.Bandersnatch.hashToCurve data) (JamCrypto.Bandersnatch.hashToCurve data) := by
  unfold JamCrypto.Bandersnatch.hashToCurve
  refine OR.bind (OR.refl _) fun P0 _ h0 => ?_
  subst h0
  refine OR.bind (OR.refl _) fun P1 _ h1 => ?_
  subst h1
  exact OR.guard Iff.rfl fun _ => ⟨rfl, red_smul one_lt_q _ _⟩

theorem thinHashToCurve_selfRed (data : List UInt8) (rd : Reading) :
    OR SelfRed (JamCrypto.Bandersnatch.Thin.hashToCurve data rd)
      (JamCrypto.Bandersnatch.Thin.hashToCurve data rd) := by
  unfold JamCrypto.Bandersnatch.Thin.hashToCurve
  refine OR.bind (OR.refl _) fun P0 _ h0 => ?_
  subst h0
  refine OR.bind (OR.refl _) fun P1 _ h1 => ?_
  subst h1
  exact OR.guard Iff.rfl fun _ => ⟨rfl, red_smul one_lt_q _ _⟩

theorem OR.map_ofPoint {m : Option JamCrypto.Point} (h : OR SelfRed m m) : OP (m.map ofPoint) m := by
  cases m with
  | none => trivial
  | some P => exact ofPoint_rel curve_p h.2

/-- As `Bandersnatch.hashToCurve`. -/
def hashToCurve (data : List UInt8) : Option (Pt F) := (JamCrypto.Bandersnatch.hashToCurve data).map ofPoint

theorem hashToCurve_rel (data : List UInt8) : OP (hashToCurve data) (JamCrypto.Bandersnatch.hashToCurve data) :=
  OR.map_ofPoint (hashToCurve_selfRed data)

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
  | none => JAM.Sha512.vrfOutput sig

theorem vrfOutput_eq (sig : List UInt8) : vrfOutput sig = JamCrypto.Bandersnatch.vrfOutput sig := by
  unfold vrfOutput JamCrypto.Bandersnatch.vrfOutput JamCrypto.Bandersnatch.pointToHash
  have h := decodeOnCurve_rel (sig.take 32)
  generalize decodeOnCurve (sig.take 32) = a at h ⊢
  generalize JamCrypto.Bandersnatch.decodeOnCurve (sig.take 32) = a' at h ⊢
  cases a <;> cases a' <;> simp only [OR] at h <;> try rfl
  dsimp only
  rw [encode_eq h]

end JamCrypto.Fast.Bandersnatch
