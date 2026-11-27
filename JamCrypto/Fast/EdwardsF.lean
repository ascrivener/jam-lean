import JamCrypto.Edwards
import JamCrypto.Fast.FieldClass
import JamCrypto.Fast.Sim

/-!
# Twisted Edwards curves over a fast field, proved to compute what `JamCrypto.Curve` computes

Each operation performs the same sequence of field operations as its reference in
`JamCrypto/Edwards.lean` (and `Modular.lean`), on a `Fast.Field` instead of `Nat` mod p. The
theorems relate a fast point to the reference point whose coordinates are its values (`Rel`) and
show that every operation preserves the relation; decisions (`valid`, `eq`, `isZero`) agree.
-/

namespace JamCrypto.Fast

open JamCrypto.Modular

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [LawfulField F]

local notation "p" => Field.p F

/-- `a` stands for n: reduced, with value n mod p. -/
def VRel (a : F) (n : Nat) : Prop := Field.Ok a ∧ Field.value a = n % p

namespace VRel

theorem mod {a : F} {n : Nat} : VRel a (n % p) ↔ VRel a n := by
  simp [VRel, Nat.mod_mod]

theorem mul {a b : F} {x y : Nat} (ha : VRel a x) (hb : VRel b y) : VRel (Field.mul a b) (x * y) :=
  ⟨LawfulField.ok_mul ha.1 hb.1, by rw [LawfulField.value_mul ha.1 hb.1, ha.2, hb.2, ← Nat.mul_mod]⟩

theorem sq {a : F} {x : Nat} (ha : VRel a x) : VRel (Field.sq a) (x * x) :=
  ⟨LawfulField.ok_sq ha.1, by rw [LawfulField.value_sq ha.1, ha.2, ← Nat.mul_mod]⟩

theorem add {a b : F} {x y : Nat} (ha : VRel a x) (hb : VRel b y) : VRel (Field.add a b) (x + y) :=
  ⟨LawfulField.ok_add ha.1 hb.1, by rw [LawfulField.value_add ha.1 hb.1, ha.2, hb.2, ← Nat.add_mod]⟩

theorem sub {a b : F} {x y : Nat} (ha : VRel a x) (hb : VRel b y) :
    VRel (Field.sub a b) (subMod x y p) := by
  refine ⟨LawfulField.ok_sub ha.1 hb.1, ?_⟩
  rw [LawfulField.value_sub ha.1 hb.1, ha.2, hb.2, subMod, Nat.mod_mod]
  have hp : 0 < p := Nat.lt_trans Nat.zero_lt_one LawfulField.one_lt_p
  have := Nat.mod_lt y hp
  have e1 : x % p + p - y % p = x % p + (p - y % p) := by omega
  have e2 : x + p - y % p = x + (p - y % p) := by omega
  rw [e1, e2, Nat.mod_add_mod]

theorem ofNat (x : Nat) : VRel (Field.ofNat x : F) x :=
  ⟨LawfulField.ok_ofNat x, LawfulField.value_ofNat x⟩

theorem zero : VRel (Field.zero : F) 0 := ⟨LawfulField.ok_zero, by rw [LawfulField.value_zero]; simp⟩

theorem one : VRel (Field.one : F) 1 :=
  ⟨LawfulField.ok_one, by rw [LawfulField.value_one, Nat.mod_eq_of_lt LawfulField.one_lt_p]⟩

theorem isZero {a : F} {x : Nat} (ha : VRel a x) : Field.isZero a = (x % p == 0) := by
  rw [LawfulField.isZero_eq ha.1, ha.2]

theorem beq {a b : F} {x y : Nat} (ha : VRel a x) (hb : VRel b y) :
    Field.beq a b = (x % p == y % p) := by
  rw [LawfulField.beq_eq ha.1 hb.1, ha.2, hb.2]

theorem toNat {a : F} {x : Nat} (ha : VRel a x) : Field.toNat a = x % p := by
  rw [LawfulField.toNat_eq ha.1, ha.2]

end VRel

/-- A point in extended coordinates over F. -/
structure Pt (F : Type) where
  X : F
  Y : F
  Z : F
  T : F

/-- A curve over F: the constants a and d. -/
structure CurveF (F : Type) where
  a : F
  d : F

/-- The fast curve has the reference curve's constants and modulus. -/
def CurveF.Rel (C : CurveF F) (E : Curve) : Prop :=
  VRel C.a E.a ∧ VRel C.d E.d ∧ E.p = p

/-- The fast point stands for the reference point (whose coordinates are reduced). -/
def PRel (P : Pt F) (Q : Point) : Prop :=
  VRel P.X Q.X ∧ VRel P.Y Q.Y ∧ VRel P.Z Q.Z ∧ VRel P.T Q.T ∧
    Q.X < p ∧ Q.Y < p ∧ Q.Z < p ∧ Q.T < p

namespace CurveF

variable (C : CurveF F)

def zero : Pt F := ⟨Field.zero, Field.one, Field.one, Field.zero⟩
def invalid : Pt F := ⟨Field.zero, Field.zero, Field.zero, Field.zero⟩

/-- `Curve.add`, operation for operation. -/
def add (P Q : Pt F) : Pt F :=
  let A := Field.mul P.X Q.X
  let B := Field.mul P.Y Q.Y
  let Cc := Field.mul C.d (Field.mul P.T Q.T)
  let D := Field.mul P.Z Q.Z
  let Ee := Field.sub (Field.mul (Field.add P.X P.Y) (Field.add Q.X Q.Y)) (Field.add A B)
  let Ff := Field.sub D Cc
  let G := Field.add D Cc
  let H := Field.sub B (Field.mul C.a A)
  let Z3 := Field.mul Ff G
  if Field.isZero Z3 then invalid else ⟨Field.mul Ee Ff, Field.mul G H, Z3, Field.mul Ee H⟩

end CurveF

namespace CurveF
variable (C : CurveF F)

/-- `Curve.neg`. -/
def neg (P : Pt F) : Pt F := ⟨Field.sub Field.zero P.X, P.Y, P.Z, Field.sub Field.zero P.T⟩

/-- `Curve.sub`. -/
def sub (P Q : Pt F) : Pt F := C.add P (neg Q)

/-- `Curve.smul`: double-and-add from the most significant bit, as the reference. -/
def smul (k : Nat) (P : Pt F) : Pt F := Id.run do
  let mut R := zero
  let n := k.log2 + 1
  for j in [0:n] do
    R := C.add R R
    if k.testBit (n - 1 - j) then R := C.add R P
  return R

/-- `Curve.valid`. -/
def valid (P : Pt F) : Bool := !Field.isZero P.Z

/-- `Curve.eq`. -/
def eq (P Q : Pt F) : Bool :=
  valid P && valid Q && Field.beq (Field.mul P.X Q.Z) (Field.mul Q.X P.Z) &&
    Field.beq (Field.mul P.Y Q.Z) (Field.mul Q.Y P.Z)

/-- `Curve.isZero`. -/
def isZero (P : Pt F) : Bool := eq P zero

end CurveF

theorem pRel_zero (E : Curve) (hE : E.p = p) : PRel (CurveF.zero : Pt F) Curve.zero := by
  have h1 := (LawfulField.one_lt_p : 1 < p)
  refine ⟨VRel.zero, VRel.one, VRel.one, VRel.zero, ?_, ?_, ?_, ?_⟩ <;> simp [Curve.zero] <;> omega

theorem pRel_invalid (E : Curve) : PRel (CurveF.invalid : Pt F) Curve.invalid := by
  have h1 := (LawfulField.one_lt_p : 1 < p)
  refine ⟨VRel.zero, VRel.zero, VRel.zero, VRel.zero, ?_, ?_, ?_, ?_⟩ <;> simp [Curve.invalid] <;> omega

theorem lt_of_mod {n : Nat} : n % p < p :=
  Nat.mod_lt _ (Nat.lt_trans Nat.zero_lt_one LawfulField.one_lt_p)

theorem VRel.of_lt {a : F} {n : Nat} (h : VRel a n) (hn : n < p) : Field.value a = n := by
  rw [h.2, Nat.mod_eq_of_lt hn]

theorem add_rel {C : CurveF F} {E : Curve} (hC : C.Rel E) {P Q : Pt F} {P' Q' : Point}
    (hP : PRel P P') (hQ : PRel Q Q') : PRel (C.add P Q) (E.add P' Q') := by
  obtain ⟨ha, hd, hp⟩ := hC
  obtain ⟨px, py, pz, pt, -⟩ := hP
  obtain ⟨qx, qy, qz, qt, -⟩ := hQ
  have hA := VRel.mod.mpr (px.mul qx)
  have hB := VRel.mod.mpr (py.mul qy)
  have hCc := VRel.mod.mpr (hd.mul (VRel.mod.mpr (pt.mul qt)))
  have hD := VRel.mod.mpr (pz.mul qz)
  have hEe := (VRel.mod.mpr ((px.add py).mul (qx.add qy))).sub (VRel.mod.mpr (hA.add hB))
  have hF := hD.sub hCc
  have hG := VRel.mod.mpr (hD.add hCc)
  have hH := hB.sub (VRel.mod.mpr (ha.mul hA))
  have hZ := VRel.mod.mpr (hF.mul hG)
  unfold CurveF.add Curve.add
  simp only [hp]
  rw [hZ.isZero, Nat.mod_mod]
  split
  · exact pRel_invalid E
  · exact ⟨VRel.mod.mpr (hEe.mul hF), VRel.mod.mpr (hG.mul hH), hZ, VRel.mod.mpr (hEe.mul hH),
      lt_of_mod, lt_of_mod, lt_of_mod, lt_of_mod⟩

/-- `Modular.powMod`, step for step. -/
def powF (a : F) (e : Nat) : F := Id.run do
  let mut r : F := Field.one
  let mut b := a
  let mut e := e
  for _ in [0:e.log2 + 1] do
    if e % 2 == 1 then r := Field.mul r b
    b := Field.sq b
    e := e / 2
  return r

/-- `Modular.invMod` (Fermat). -/
def invF (a : F) : F := powF a (p - 2)

theorem powF_rel' {a : F} {x : Nat} (ha : VRel a x) (e : Nat) :
    VRel (powF a e) (powMod x e p) ∧ powMod x e p < p := by
  unfold powF powMod
  simp only [Id.run, bind, pure]
  refine (forIn_range_rel (fun (s : F × F × Nat) (t : Nat × Nat × Nat) =>
      (VRel s.1 t.1 ∧ t.1 < p) ∧ VRel s.2.1 t.2.1 ∧ s.2.2 = t.2.2) _ _ _
    ⟨⟨VRel.mod.mpr VRel.one, lt_of_mod⟩, VRel.mod.mpr ha, rfl⟩ ?_).1
  rintro _ ⟨r, b, e⟩ ⟨r', b', e'⟩ ⟨hr, hb, rfl⟩
  simp only [Id.run]
  split
  · exact ⟨⟨VRel.mod.mpr (hr.1.mul hb), lt_of_mod⟩, VRel.mod.mpr hb.sq, rfl⟩
  · exact ⟨hr, VRel.mod.mpr hb.sq, rfl⟩

theorem powF_rel {a : F} {x : Nat} (ha : VRel a x) (e : Nat) : VRel (powF a e) (powMod x e p) := by
  unfold powF powMod
  simp only [Id.run, bind, pure]
  exact (powF_rel' ha e).1

theorem powMod_lt (x e : Nat) : powMod x e p < p := by
  have := powF_rel' (VRel.ofNat x : VRel (Field.ofNat x : F) x) e
  exact this.2

theorem invF_rel {a : F} {x : Nat} (ha : VRel a x) : VRel (invF a) (invMod x p) :=
  powF_rel ha (p - 2)

namespace CurveF

/-- `Curve.toAffine`. -/
def toAffine (P : Pt F) : Nat × Nat :=
  let zi := invF P.Z
  (Field.toNat (Field.mul P.X zi), Field.toNat (Field.mul P.Y zi))

end CurveF

theorem toAffine_eq {E : Curve} (hp : E.p = p) {P : Pt F} {P' : Point} (hP : PRel P P') :
    CurveF.toAffine P = E.toAffine P' := by
  unfold CurveF.toAffine Curve.toAffine
  have hz := invF_rel hP.2.2.1
  simp only [hp]
  rw [(hP.1.mul hz).toNat, (hP.2.1.mul hz).toNat]

theorem VRel.beq_lt {a b : F} {x y : Nat} (ha : VRel a x) (hb : VRel b y) (hx : x < p) (hy : y < p) :
    Field.beq a b = (x == y) := by
  rw [ha.beq hb, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

theorem one_lt : (1 : Nat) < p := LawfulField.one_lt_p

/-- `Modular.isSquare` (Euler's criterion). -/
def isSquareF (a : F) : Bool := Field.beq (powF a ((p - 1) / 2)) Field.one

theorem isSquareF_eq {a : F} {x : Nat} (ha : VRel a x) (hx : x < p) : isSquareF a = isSquare x p := by
  unfold isSquareF isSquare
  have h := powF_rel' ha ((p - 1) / 2)
  rw [h.1.beq_lt VRel.one h.2 one_lt]

/-- `Modular.sqrtTS p s t z n`, step for step (n given as an element; the reference reduces n). -/
def sqrtF (s t : Nat) (z n : F) : Option F := Id.run do
  if Field.isZero n then return some Field.zero
  if !isSquareF n then return none
  let mut m := s
  let mut c := powF z t
  let mut u := powF n t
  let mut r := powF n ((t + 1) / 2)
  for _ in [0:s] do
    if Field.beq u Field.one then break
    let mut i := 0
    let mut u2 := u
    for _ in [0:m] do
      if Field.beq u2 Field.one then break
      u2 := Field.mul u2 u2
      i := i + 1
    let b := powF c (2 ^ (m - i - 1))
    m := i
    c := Field.mul b b
    u := Field.mul u c
    r := Field.mul r b
  if Field.beq (Field.mul r r) n then return some r else return none

/-- An optional element stands for an optional reduced number. -/
def ORel : Option F → Option Nat → Prop
  | none, none => True
  | some a, some x => VRel a x ∧ x < p
  | _, _ => False

/-- The outer loop states of `sqrtF` and `sqrtTS` agree: m equal, c, u, r related and reduced. -/
def SOut (a : Nat × F × F × F) (b : Nat × Nat × Nat × Nat) : Prop :=
  a.1 = b.1 ∧ (VRel a.2.1 b.2.1 ∧ b.2.1 < p) ∧ (VRel a.2.2.1 b.2.2.1 ∧ b.2.2.1 < p) ∧
    (VRel a.2.2.2 b.2.2.2 ∧ b.2.2.2 < p)

theorem sqrt_fin {n : F} {n0 : Nat} (hn : VRel n n0) (hn0 : n0 < p) (X : Nat × F × F × F)
    (Y : Nat × Nat × Nat × Nat) (h : SOut X Y) :
    ORel (if Field.beq (Field.mul X.2.2.2 X.2.2.2) n = true then some X.2.2.2 else none)
      (if (Y.2.2.2 * Y.2.2.2 % p == n0) = true then some Y.2.2.2 else none) := by
  have hr := h.2.2.2
  rw [(VRel.mod.mpr (hr.1.mul hr.1)).beq_lt hn lt_of_mod hn0]
  split
  · exact hr
  · trivial

/-- The inner loop states agree: i equal, u2 related and reduced. -/
def SIn (a : Nat × F) (b : Nat × Nat) : Prop := a.1 = b.1 ∧ VRel a.2 b.2 ∧ b.2 < p

theorem sqrt_step {m : Nat} {c u r : F} {c' u' r' : Nat} (hc : VRel c c' ∧ c' < p)
    (hu : VRel u u' ∧ u' < p) (hr : VRel r r' ∧ r' < p) (I : Nat × F) (J : Nat × Nat) (h : SIn I J) :
    SOut (I.1, Field.mul (powF c (2 ^ (m - I.1 - 1))) (powF c (2 ^ (m - I.1 - 1))),
        Field.mul u (Field.mul (powF c (2 ^ (m - I.1 - 1))) (powF c (2 ^ (m - I.1 - 1)))),
        Field.mul r (powF c (2 ^ (m - I.1 - 1))))
      (J.1, powMod c' (2 ^ (m - J.1 - 1)) p * powMod c' (2 ^ (m - J.1 - 1)) p % p,
        u' * (powMod c' (2 ^ (m - J.1 - 1)) p * powMod c' (2 ^ (m - J.1 - 1)) p % p) % p,
        r' * powMod c' (2 ^ (m - J.1 - 1)) p % p) := by
  rw [h.1]
  have hb := (powF_rel' hc.1 (2 ^ (m - J.1 - 1))).1
  have hbb := VRel.mod.mpr (hb.mul hb)
  exact ⟨rfl, ⟨hbb, lt_of_mod⟩, ⟨VRel.mod.mpr (hu.1.mul hbb), lt_of_mod⟩,
    ⟨VRel.mod.mpr (hr.1.mul hb), lt_of_mod⟩⟩

theorem sqrtF_rel {s t : Nat} {z n : F} {z' n' : Nat} (hz : VRel z z') (hn : VRel n n') :
    ORel (sqrtF s t z n) (sqrtTS p s t z' n') := by
  have hn0 : VRel n (n' % p) := VRel.mod.mpr hn
  unfold sqrtF sqrtTS
  simp only [Id.run, bind, pure]
  rw [hn.isZero, isSquareF_eq hn0 lt_of_mod]
  split
  · exact ⟨VRel.zero, Nat.lt_trans Nat.zero_lt_one one_lt⟩
  split
  · trivial
  have hn1 : n' % p < p := lt_of_mod
  refine sqrt_fin hn0 hn1 _ _ (forIn_range_rel SOut _ _ _
    ⟨rfl, powF_rel' hz t, powF_rel' hn0 t, powF_rel' hn0 ((t + 1) / 2)⟩ ?_)
  rintro _ ⟨m, c, u, r⟩ ⟨m', c', u', r'⟩ ⟨rfl, hc, hu, hr⟩
  simp only [Id.run]
  rw [hu.1.beq_lt VRel.one hu.2 one_lt]
  split
  · exact ⟨rfl, hc, hu, hr⟩
  · refine sqrt_step hc hu hr _ _ (forIn_range_rel SIn _ _ _ ⟨rfl, hu⟩ ?_)
    rintro _ ⟨i, w⟩ ⟨i', w'⟩ ⟨rfl, hw⟩
    simp only [Id.run]
    rw [hw.1.beq_lt VRel.one hw.2 one_lt]
    split
    · exact ⟨rfl, hw⟩
    · exact ⟨rfl, VRel.mod.mpr (hw.1.mul hw.1), lt_of_mod⟩

theorem neg_rel {E : Curve} (hp : E.p = p) {P : Pt F} {P' : Point} (hP : PRel P P') :
    PRel (CurveF.neg P) (E.neg P') := by
  obtain ⟨px, py, pz, pt, lx, ly, lz, lt⟩ := hP
  unfold CurveF.neg Curve.neg
  simp only [hp]
  exact ⟨VRel.zero.sub px, py, pz, VRel.zero.sub pt, by unfold subMod; exact lt_of_mod, ly, lz,
    by unfold subMod; exact lt_of_mod⟩

theorem sub_rel {C : CurveF F} {E : Curve} (hC : C.Rel E) {P Q : Pt F} {P' Q' : Point}
    (hP : PRel P P') (hQ : PRel Q Q') : PRel (C.sub P Q) (E.sub P' Q') :=
  add_rel hC hP (neg_rel hC.2.2 hQ)

theorem smul_rel {C : CurveF F} {E : Curve} (hC : C.Rel E) (k : Nat) {P : Pt F} {P' : Point}
    (hP : PRel P P') : PRel (C.smul k P) (E.smul k P') := by
  unfold CurveF.smul Curve.smul
  simp only [Id.run, bind, pure]
  refine forIn_range_rel PRel _ _ _ (pRel_zero E hC.2.2) ?_
  intro j a b hab
  simp only [Id.run]
  split
  · exact add_rel hC (add_rel hC hab hab) hP
  · exact add_rel hC hab hab

theorem valid_eq {E : Curve} (hp : E.p = p) {P : Pt F} {P' : Point} (hP : PRel P P') :
    CurveF.valid P = E.valid P' := by
  unfold CurveF.valid Curve.valid
  rw [hP.2.2.1.isZero, hp]
  rfl

theorem eq_eq {E : Curve} (hp : E.p = p) {P Q : Pt F} {P' Q' : Point} (hP : PRel P P')
    (hQ : PRel Q Q') : CurveF.eq P Q = E.eq P' Q' := by
  unfold CurveF.eq Curve.eq
  rw [valid_eq hp hP, valid_eq hp hQ, (hP.1.mul hQ.2.2.1).beq (hQ.1.mul hP.2.2.1),
    (hP.2.1.mul hQ.2.2.1).beq (hQ.2.1.mul hP.2.2.1), hp]

theorem isZero_eq {E : Curve} (hp : E.p = p) {P : Pt F} {P' : Point} (hP : PRel P P') :
    CurveF.isZero P = E.isZero P' :=
  eq_eq hp hP (pRel_zero E hp)

end JamCrypto.Fast
