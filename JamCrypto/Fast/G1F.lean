import JamCrypto.Bls12381G1
import JamCrypto.Fast.EdwardsF

/-!
# The group G1 of BLS12-381 over a fast field, proved to compute what `JamCrypto.G1` computes

Each operation performs the same sequence of field operations as its reference in
`JamCrypto/Bls12381G1.lean` (unchanged), on a `Fast.Field` whose modulus is the BLS12-381 base
field modulus (`IsFq`), instead of `Nat` with `Fq.add`, `Fq.sub`, `Fq.mul`, … The theorems relate a
fast point to the reference point whose coordinates are its values (`JRel`, `ARel`; the reference
coordinates are reduced, as every reference operation keeps them) and show that every operation
preserves the relation.

An inversion (`toAff`) is the reference one, `Fq.inv` on the value: it is one per conversion.
-/

namespace JamCrypto.Fast.G1F

open JamCrypto.Fast
open JamCrypto.Fq (P)

set_option linter.unusedSectionVars false

/-- The field's modulus is the BLS12-381 base field modulus. -/
class IsFq (F : Type) [Field F] : Prop where
  p_eq : Field.p F = JamCrypto.Fq.P

variable {F : Type} [Field F] [LawfulField F] [IsFq F]

/-- `a` stands for the reduced value x. -/
def V (a : F) (x : Nat) : Prop := VRel a x ∧ x < P

namespace V

theorem hp : Field.p F = P := IsFq.p_eq

theorem P_pos : 0 < P := by decide

theorem of_mod {a : F} {x : Nat} (h : VRel a x) : V a (x % P) :=
  ⟨by rw [← hp (F := F)]; exact VRel.mod.mpr h, Nat.mod_lt _ P_pos⟩

theorem add_eq {x y : Nat} (hx : x < P) (hy : y < P) : JamCrypto.Fq.add x y = (x + y) % P := by
  unfold JamCrypto.Fq.add
  simp only
  split
  · have : x + y = (x + y - P) + P := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
  · rw [Nat.mod_eq_of_lt (by omega)]

theorem sub_eq {x y : Nat} (hx : x < P) (hy : y < P) :
    JamCrypto.Fq.sub x y = JamCrypto.Modular.subMod x y P := by
  unfold JamCrypto.Fq.sub JamCrypto.Modular.subMod
  rw [Nat.mod_eq_of_lt hy]
  split
  · have : x + P - y = (x - y) + P := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]

theorem add {a b : F} {x y : Nat} (ha : V a x) (hb : V b y) :
    V (Field.add a b) (JamCrypto.Fq.add x y) := by
  rw [add_eq ha.2 hb.2]; exact of_mod (ha.1.add hb.1)

theorem sub {a b : F} {x y : Nat} (ha : V a x) (hb : V b y) :
    V (Field.sub a b) (JamCrypto.Fq.sub x y) := by
  rw [sub_eq ha.2 hb.2]
  have h := ha.1.sub hb.1
  rw [hp (F := F)] at h
  unfold JamCrypto.Modular.subMod at h ⊢
  exact ⟨h, Nat.mod_lt _ P_pos⟩

theorem mul {a b : F} {x y : Nat} (ha : V a x) (hb : V b y) :
    V (Field.mul a b) (JamCrypto.Fq.mul x y) := of_mod (ha.1.mul hb.1)

theorem sq {a : F} {x : Nat} (ha : V a x) : V (Field.sq a) (JamCrypto.Fq.sq x) := of_mod ha.1.sq

theorem mulR {a b : F} {x y : Nat} (ha : VRel a x) (hb : VRel b y) :
    V (Field.mul a b) (JamCrypto.Fq.mul x y) := of_mod (ha.mul hb)

theorem sqR {a : F} {x : Nat} (ha : VRel a x) : V (Field.sq a) (JamCrypto.Fq.sq x) := of_mod ha.sq

theorem neg {a : F} {x : Nat} (ha : V a x) :
    V (Field.sub Field.zero a) (JamCrypto.Fq.neg x) := by
  have h := sub (⟨VRel.zero, P_pos⟩ : V (Field.zero : F) 0) ha
  have e : JamCrypto.Fq.sub 0 x = JamCrypto.Fq.neg x := by
    unfold JamCrypto.Fq.sub JamCrypto.Fq.neg
    by_cases hx : x = 0
    · subst hx; simp
    · have : ¬ (0 ≥ x) := by omega
      rw [if_neg this, show (x == 0) = false by simpa using hx]
      simp
  rwa [e] at h

theorem ofNat {x : Nat} (hx : x < P) : V (Field.ofNat x : F) x := ⟨VRel.ofNat x, hx⟩

theorem zero : V (Field.zero : F) 0 := ⟨VRel.zero, P_pos⟩

theorem one : V (Field.one : F) 1 := ⟨VRel.one, by decide⟩

theorem isZero {a : F} {x : Nat} (ha : V a x) : Field.isZero a = (x == 0) := by
  rw [ha.1.isZero, hp (F := F), Nat.mod_eq_of_lt ha.2]

theorem beq {a b : F} {x y : Nat} (ha : V a x) (hb : V b y) : Field.beq a b = (x == y) := by
  rw [ha.1.beq hb.1, hp (F := F), Nat.mod_eq_of_lt ha.2, Nat.mod_eq_of_lt hb.2]

theorem toNat {a : F} {x : Nat} (ha : V a x) : Field.toNat a = x := by
  rw [ha.1.toNat, hp (F := F), Nat.mod_eq_of_lt ha.2]

end V

/-- A Jacobian point (`G1.Jac`). -/
structure JF (F : Type) where
  x : F
  y : F
  z : F

/-- An affine point (`G1.Aff`). -/
structure AF (F : Type) where
  x : F
  y : F
  inf : Bool

def JRel (A : JF F) (B : JamCrypto.G1.Jac) : Prop := V A.x B.x ∧ V A.y B.y ∧ V A.z B.z

def ARel (A : AF F) (B : JamCrypto.G1.Aff) : Prop := V A.x B.x ∧ V A.y B.y ∧ A.inf = B.inf

instance : Inhabited (JF F) := ⟨⟨Field.zero, Field.zero, Field.zero⟩⟩
instance : Inhabited (AF F) := ⟨⟨Field.zero, Field.zero, false⟩⟩

theorem jrel_default : JRel (default : JF F) (default : JamCrypto.G1.Jac) := ⟨V.zero, V.zero, V.zero⟩
theorem arel_default : ARel (default : AF F) (default : JamCrypto.G1.Aff) := ⟨V.zero, V.zero, rfl⟩

/-- `Jac.zero`. -/
def zero : JF F := ⟨Field.one, Field.one, Field.zero⟩

theorem zero_rel : JRel (zero : JF F) JamCrypto.G1.Jac.zero := ⟨V.one, V.one, V.zero⟩

/-- `Aff.toJac`. -/
def toJac (p : AF F) : JF F := if p.inf then zero else ⟨p.x, p.y, Field.one⟩

theorem toJac_rel {p : AF F} {q : JamCrypto.G1.Aff} (h : ARel p q) : JRel (toJac p) q.toJac := by
  unfold toJac JamCrypto.G1.Aff.toJac
  rw [h.2.2]
  split
  · exact zero_rel
  · exact ⟨h.1, h.2.1, V.one⟩

/-- `dbl` (dbl-2009-l), operation for operation. -/
def dbl (p : JF F) : JF F :=
  if Field.isZero p.z || Field.isZero p.y then zero else
  let a := Field.sq p.x
  let b := Field.sq p.y
  let c := Field.sq b
  let t := Field.add p.x b
  let d := Field.add (Field.sub (Field.sub (Field.sq t) a) c) (Field.sub (Field.sub (Field.sq t) a) c)
  let e := Field.add (Field.add a a) a
  let f := Field.sq e
  let x3 := Field.sub f (Field.add d d)
  let c8 := Field.add (Field.add (Field.add c c) (Field.add c c)) (Field.add (Field.add c c) (Field.add c c))
  let y3 := Field.sub (Field.mul e (Field.sub d x3)) c8
  let z3 := Field.mul (Field.add p.y p.y) p.z
  ⟨x3, y3, z3⟩

theorem dbl_rel {p : JF F} {q : JamCrypto.G1.Jac} (h : JRel p q) : JRel (dbl p) (JamCrypto.G1.dbl q) := by
  obtain ⟨hx, hy, hz⟩ := h
  unfold dbl JamCrypto.G1.dbl
  rw [hz.isZero, hy.isZero]
  split
  · exact zero_rel
  extract_lets a b c t d e f x3 c8 y3 z3 a' b' c' t' d' e' f' x3' c8' y3' z3'
  have va : V a a' := hx.sq
  have vb : V b b' := hy.sq
  have vc : V c c' := vb.sq
  have vt : V t t' := hx.add vb
  have vd : V d d' := (((vt.sq).sub va).sub vc).add (((vt.sq).sub va).sub vc)
  have ve : V e e' := (va.add va).add va
  have vf : V f f' := ve.sq
  have vx3 : V x3 x3' := vf.sub (vd.add vd)
  have vc8 : V c8 c8' := ((vc.add vc).add (vc.add vc)).add ((vc.add vc).add (vc.add vc))
  have vy3 : V y3 y3' := (ve.mul (vd.sub vx3)).sub vc8
  have vz3 : V z3 z3' := (hy.add hy).mul hz
  exact ⟨vx3, vy3, vz3⟩

/-- `addMixed` (madd-2007-bl), operation for operation. -/
def addMixed (p : JF F) (q : AF F) : JF F :=
  if q.inf then p else
  if Field.isZero p.z then toJac q else
  let z1z1 := Field.sq p.z
  let u2 := Field.mul q.x z1z1
  let s2 := Field.mul (Field.mul q.y p.z) z1z1
  let h := Field.sub u2 p.x
  let r := Field.add (Field.sub s2 p.y) (Field.sub s2 p.y)
  if Field.isZero h then (if Field.isZero r then dbl p else zero) else
  let hh := Field.sq h
  let i := Field.add (Field.add hh hh) (Field.add hh hh)
  let j := Field.mul h i
  let v := Field.mul p.x i
  let x3 := Field.sub (Field.sub (Field.sq r) j) (Field.add v v)
  let yj := Field.mul p.y j
  let y3 := Field.sub (Field.mul r (Field.sub v x3)) (Field.add yj yj)
  let z3 := Field.sub (Field.sub (Field.sq (Field.add p.z h)) z1z1) hh
  ⟨x3, y3, z3⟩

theorem addMixed_rel {p : JF F} {q : AF F} {p' : JamCrypto.G1.Jac} {q' : JamCrypto.G1.Aff}
    (hp : JRel p p') (hq : ARel q q') : JRel (addMixed p q) (JamCrypto.G1.addMixed p' q') := by
  have hp0 := hp
  obtain ⟨px, py, pz⟩ := hp
  have hq0 := hq
  obtain ⟨qx, qy, qi⟩ := hq
  unfold addMixed JamCrypto.G1.addMixed
  rw [qi, pz.isZero]
  split
  · exact hp0
  split
  · exact toJac_rel hq0
  extract_lets z1z1 u2 s2 h r hh i j v x3 yj y3 z3 z1z1' u2' s2' h' r' hh' i' j' v' x3' yj' y3' z3'
  have vz1z1 : V z1z1 z1z1' := pz.sq
  have vu2 : V u2 u2' := qx.mul vz1z1
  have vs2 : V s2 s2' := (qy.mul pz).mul vz1z1
  have vh : V h h' := vu2.sub px
  have vr : V r r' := (vs2.sub py).add (vs2.sub py)
  rw [vh.isZero, vr.isZero]
  split
  · split
    · exact dbl_rel hp0
    · exact zero_rel
  have vhh : V hh hh' := vh.sq
  have vi : V i i' := (vhh.add vhh).add (vhh.add vhh)
  have vj : V j j' := vh.mul vi
  have vv : V v v' := px.mul vi
  have vx3 : V x3 x3' := (vr.sq.sub vj).sub (vv.add vv)
  have vyj : V yj yj' := py.mul vj
  have vy3 : V y3 y3' := (vr.mul (vv.sub vx3)).sub (vyj.add vyj)
  have vz3 : V z3 z3' := ((pz.add vh).sq.sub vz1z1).sub vhh
  exact ⟨vx3, vy3, vz3⟩

/-- `addJ` (add-2007-bl), operation for operation. -/
def addJ (p q : JF F) : JF F :=
  if Field.isZero p.z then q else if Field.isZero q.z then p else
  let z1z1 := Field.sq p.z
  let z2z2 := Field.sq q.z
  let u1 := Field.mul p.x z2z2
  let u2 := Field.mul q.x z1z1
  let s1 := Field.mul (Field.mul p.y q.z) z2z2
  let s2 := Field.mul (Field.mul q.y p.z) z1z1
  let h := Field.sub u2 u1
  let r := Field.add (Field.sub s2 s1) (Field.sub s2 s1)
  if Field.isZero h then (if Field.isZero r then dbl p else zero) else
  let i := Field.sq (Field.add h h)
  let j := Field.mul h i
  let v := Field.mul u1 i
  let x3 := Field.sub (Field.sub (Field.sq r) j) (Field.add v v)
  let sj := Field.mul s1 j
  let y3 := Field.sub (Field.mul r (Field.sub v x3)) (Field.add sj sj)
  let z3 := Field.mul (Field.sub (Field.sub (Field.sq (Field.add p.z q.z)) z1z1) z2z2) h
  ⟨x3, y3, z3⟩

theorem addJ_rel {p q : JF F} {p' q' : JamCrypto.G1.Jac} (hp : JRel p p') (hq : JRel q q') :
    JRel (addJ p q) (JamCrypto.G1.addJ p' q') := by
  have hp0 := hp
  obtain ⟨px, py, pz⟩ := hp
  have hq0 := hq
  obtain ⟨qx, qy, qz⟩ := hq
  unfold addJ JamCrypto.G1.addJ
  rw [pz.isZero, qz.isZero]
  split
  · exact hq0
  split
  · exact hp0
  extract_lets z1z1 z2z2 u1 u2 s1 s2 h r i j v x3 sj y3 z3 z1z1' z2z2' u1' u2' s1' s2' h' r' i' j' v' x3' sj' y3' z3'
  have vz1z1 : V z1z1 z1z1' := pz.sq
  have vz2z2 : V z2z2 z2z2' := qz.sq
  have vu1 : V u1 u1' := px.mul vz2z2
  have vu2 : V u2 u2' := qx.mul vz1z1
  have vs1 : V s1 s1' := (py.mul qz).mul vz2z2
  have vs2 : V s2 s2' := (qy.mul pz).mul vz1z1
  have vh : V h h' := vu2.sub vu1
  have vr : V r r' := (vs2.sub vs1).add (vs2.sub vs1)
  rw [vh.isZero, vr.isZero]
  split
  · split
    · exact dbl_rel hp0
    · exact zero_rel
  have vi : V i i' := (vh.add vh).sq
  have vj : V j j' := vh.mul vi
  have vv : V v v' := vu1.mul vi
  have vx3 : V x3 x3' := (vr.sq.sub vj).sub (vv.add vv)
  have vsj : V sj sj' := vs1.mul vj
  have vy3 : V y3 y3' := (vr.mul (vv.sub vx3)).sub (vsj.add vsj)
  have vz3 : V z3 z3' := ((((pz.add qz).sq).sub vz1z1).sub vz2z2).mul vh
  exact ⟨vx3, vy3, vz3⟩

/-- `negJ`. -/
def negJ (p : JF F) : JF F := ⟨p.x, Field.sub Field.zero p.y, p.z⟩

theorem negJ_rel {p : JF F} {p' : JamCrypto.G1.Jac} (hp : JRel p p') : JRel (negJ p) (JamCrypto.G1.negJ p') :=
  ⟨hp.1, hp.2.1.neg, hp.2.2⟩

/-- `Jac.toAff`; the inversion is the reference one on the value. -/
def toAff (p : JF F) : AF F :=
  if Field.isZero p.z then ⟨Field.zero, Field.zero, true⟩ else
  let zi : F := Field.ofNat (JamCrypto.Fq.inv (Field.toNat p.z))
  let zi2 := Field.sq zi
  ⟨Field.mul p.x zi2, Field.mul p.y (Field.mul zi2 zi), false⟩

theorem toAff_rel {p : JF F} {p' : JamCrypto.G1.Jac} (hp : JRel p p') :
    ARel (toAff p) p'.toAff := by
  obtain ⟨px, py, pz⟩ := hp
  unfold toAff JamCrypto.G1.Jac.toAff
  rw [pz.isZero]
  split
  · exact ⟨V.zero, V.zero, rfl⟩
  extract_lets zi zi2 zi' zi2'
  have vzi : VRel zi zi' := by
    show VRel (Field.ofNat _) _
    rw [pz.toNat]; exact VRel.ofNat _
  have vzi2 : V zi2 zi2' := V.sqR vzi
  exact ⟨px.mul vzi2, py.mul (V.mulR vzi2.1 vzi), rfl⟩

/-- `smul`: double-and-add from the most significant bit, as the reference. -/
def smul (p : JF F) (k : Nat) : JF F := Id.run do
  let mut acc := zero
  let n := k.log2 + 1
  for i in [0:n] do
    acc := dbl acc
    if (k >>> (n - 1 - i)) % 2 == 1 then acc := addJ acc p
  return acc

theorem smul_rel {p : JF F} {p' : JamCrypto.G1.Jac} (hp : JRel p p') (k : Nat) :
    JRel (smul p k) (JamCrypto.G1.smul p' k) := by
  unfold smul JamCrypto.G1.smul
  simp only [Id.run, bind, pure]
  refine forIn_range_rel JRel _ _ _ zero_rel ?_
  intro i a b hab
  simp only [Id.run]
  split
  · exact addJ_rel (dbl_rel hab) hp
  · exact dbl_rel hab


/-- Two arrays agree elementwise. -/
def ArrRel {α β : Type} (R : α → β → Prop) (a : Array α) (b : Array β) : Prop :=
  a.size = b.size ∧ ∀ i (h1 : i < a.size) (h2 : i < b.size), R a[i] b[i]

namespace ArrRel
variable {α β : Type} {R : α → β → Prop}

theorem replicate (n : Nat) {x : α} {y : β} (h : R x y) :
    ArrRel R (Array.replicate n x) (Array.replicate n y) :=
  ⟨by simp, fun i _ _ => by simp [h]⟩

theorem get! [Inhabited α] [Inhabited β] {a : Array α} {b : Array β} (h : ArrRel R a b) (hd : R default default) (i : Nat) :
    R a[i]! b[i]! := by
  by_cases hi : i < a.size
  · have hi' : i < b.size := h.1 ▸ hi
    rw [getElem!_pos a i hi, getElem!_pos b i hi']
    exact h.2 i hi hi'
  · have hi' : ¬ i < b.size := h.1 ▸ hi
    rw [getElem!_neg a i hi, getElem!_neg b i hi']
    exact hd

theorem modify {a : Array α} {b : Array β} (h : ArrRel R a b) (i : Nat) {f : α → α} {g : β → β}
    (hf : ∀ x y, R x y → R (f x) (g y)) : ArrRel R (a.modify i f) (b.modify i g) := by
  refine ⟨by simp [h.1], fun j h1 h2 => ?_⟩
  rw [Array.getElem_modify, Array.getElem_modify]
  have := h.2 j (by simpa using h1) (by simpa using h2)
  split <;> simp_all
end ArrRel

/-- `msm`: Pippenger's bucket method, step for step as the reference. -/
def msm (points : Array (AF F)) (scalars : Array Nat) : JF F := Id.run do
  let n := min points.size scalars.size
  let c := JamCrypto.G1.window n
  let nw := (JamCrypto.G1.scalarBits + c - 1) / c
  let mask := 2 ^ c - 1
  let mut acc := zero
  for wi in [0:nw] do
    let w := nw - 1 - wi
    for _ in [0:c] do
      acc := dbl acc
    let mut buckets : Array (JF F) := Array.replicate (2 ^ c) zero
    for i in [0:n] do
      let d := (scalars[i]! >>> (w * c)) &&& mask
      if d != 0 then
        buckets := buckets.modify d (addMixed · points[i]!)
    let mut running := zero
    let mut sum := zero
    for k in [0:2 ^ c - 1] do
      let d := 2 ^ c - 1 - k
      running := addJ running buckets[d]!
      sum := addJ sum running
    acc := addJ acc sum
  return acc

theorem msm_rel {points : Array (AF F)} {points' : Array JamCrypto.G1.Aff} (hp : ArrRel ARel points points')
    (scalars : Array Nat) : JRel (msm points scalars) (JamCrypto.G1.msm points' scalars) := by
  unfold msm JamCrypto.G1.msm
  simp (config := {zeta := false}) only [Id.run, bind, pure]
  rw [hp.1]
  extract_lets n c nw mask
  refine forIn_range_rel JRel _ _ _ zero_rel ?_
  intro wi a b hab
  simp (config := {zeta := false}) only [Id.run]
  extract_lets acc w acc2 buckets sum acc3 accR acc2R bucketsR sumR acc3R
  have h2 : JRel acc2 acc2R := by
    refine forIn_range_rel JRel _ _ _ hab ?_
    intro _ x y hxy
    exact dbl_rel hxy
  have hb : ArrRel JRel buckets bucketsR := by
    refine forIn_range_rel (ArrRel JRel) _ _ _ (ArrRel.replicate _ zero_rel) ?_
    intro i x y hxy
    simp only
    split
    · exact hxy.modify _ (fun u v huv => addMixed_rel huv (hp.get! arel_default i))
    · exact hxy
  have hs : JRel sum sumR := by
    refine (forIn_range_rel (fun (s : JF F × JF F) (t : JamCrypto.G1.Jac × JamCrypto.G1.Jac) =>
      JRel s.1 t.1 ∧ JRel s.2 t.2) _ _ _ ?_ ?_).2
    · exact ⟨zero_rel, zero_rel⟩
    rintro k ⟨r1, s1⟩ ⟨r2, s2⟩ ⟨hr, hs⟩
    have hr' := addJ_rel hr (hb.get! jrel_default (2 ^ c - 1 - k))
    exact ⟨hr', addJ_rel hs hr'⟩
  exact addJ_rel h2 hs

/-- `onCurve`. -/
def onCurve (p : AF F) : Bool :=
  p.inf || Field.beq (Field.sq p.y) (Field.add (Field.mul (Field.sq p.x) p.x) (Field.ofNat 4))

theorem onCurve_eq {p : AF F} {p' : JamCrypto.G1.Aff} (h : ARel p p') : onCurve p = JamCrypto.G1.onCurve p' := by
  unfold onCurve JamCrypto.G1.onCurve
  rw [h.2.2, h.2.1.sq.beq ((h.1.sq.mul h.1).add (V.ofNat (by decide)))]

/-- `inSubgroup`. -/
def inSubgroup (p : AF F) : Bool := p.inf || Field.isZero (smul (toJac p) JamCrypto.Fr.R).z

theorem inSubgroup_eq {p : AF F} {p' : JamCrypto.G1.Aff} (h : ARel p p') :
    inSubgroup p = JamCrypto.G1.inSubgroup p' := by
  unfold inSubgroup JamCrypto.G1.inSubgroup
  rw [h.2.2, (smul_rel (toJac_rel h) _).2.2.isZero]

theorem powMod_eq : JamCrypto.Field.powMod = JamCrypto.Modular.powMod := rfl

attribute [local irreducible] powF JamCrypto.Field.powMod JamCrypto.Modular.powMod JamCrypto.Field.ofBE

/-- `decompress`, step for step; the square root is `powF`, as the reference's `powMod`. -/
def decompress (bs : List UInt8) : Option (AF F) := do
  if bs.length != 48 then none
  let b0 := bs.head!
  if b0 &&& 0x80 == 0 then none
  let inf := b0 &&& 0x40 != 0
  let big := b0 &&& 0x20 != 0
  let x := JamCrypto.Field.ofBE ((b0 &&& 0x1f) :: bs.tail)
  if inf then
    if big || x != 0 then none else some ⟨Field.zero, Field.zero, true⟩
  else
  if x ≥ P then none
  let xf : F := Field.ofNat x
  let y2 := Field.add (Field.mul (Field.sq xf) xf) (Field.ofNat 4)
  let y := powF y2 ((P + 1) / 4)
  if !Field.beq (Field.sq y) y2 then none
  let y := if (Field.toNat y > (P - 1) / 2) == big then y else Field.sub Field.zero y
  let p : AF F := ⟨xf, y, false⟩
  if inSubgroup p then some p else none

theorem decompress_rel (bs : List UInt8) :
    OR ARel (decompress (F := F) bs) (JamCrypto.G1.decompress bs) := by
  unfold decompress JamCrypto.G1.decompress
  dsimp only [bind, Option.bind]
  generalize bs.head! = b0
  generalize JamCrypto.Field.ofBE ((b0 &&& 31) :: bs.tail) = X
  refine OR.ite (fun _ => trivial) fun _ => ?_
  refine OR.ite (fun _ => trivial) fun _ => ?_
  refine OR.ite (fun _ => OR.ite (fun _ => trivial) fun _ => ⟨V.zero, V.zero, rfl⟩) fun _ => ?_
  refine OR.ite (fun _ => trivial) fun hx => ?_
  have vx : V (Field.ofNat X : F) X := V.ofNat (Nat.lt_of_not_le hx)
  have vy2 := (vx.sq.mul vx).add (V.ofNat (F := F) (show 4 < P by decide))
  generalize (Field.add (Field.mul (Field.sq (Field.ofNat X)) (Field.ofNat X)) (Field.ofNat 4) : F) = y2 at vy2 ⊢
  generalize JamCrypto.Fq.add (JamCrypto.Fq.mul (JamCrypto.Fq.sq X) X) 4 = y2' at vy2 ⊢
  have vy : V (powF y2 ((P + 1) / 4)) (JamCrypto.Field.powMod y2' ((P + 1) / 4) P) := by
    have := powF_rel' vy2.1 ((P + 1) / 4)
    rw [V.hp (F := F)] at this
    rw [powMod_eq]
    exact this
  generalize powF y2 ((P + 1) / 4) = y at vy ⊢
  generalize JamCrypto.Field.powMod y2' ((P + 1) / 4) P = y' at vy ⊢
  rw [vy.sq.beq vy2]
  refine OR.ite (fun _ => trivial) fun _ => ?_
  rw [vy.toNat]
  have hA : ARel (⟨Field.ofNat X, if (decide (y' > (P - 1) / 2) == (b0 &&& 32 != 0)) = true then y
      else Field.sub Field.zero y, false⟩ : AF F)
      ⟨X, if (decide (y' > (P - 1) / 2) == (b0 &&& 32 != 0)) = true then y' else JamCrypto.Fq.neg y', false⟩ := by
    refine ⟨vx, ?_, rfl⟩
    split
    · exact vy
    · exact vy.neg
  rw [inSubgroup_eq hA]
  exact OR.ite (fun _ => hA) fun _ => trivial

/-- Back to a reference affine point. -/
def toAffNat (a : AF F) : JamCrypto.G1.Aff := ⟨Field.toNat a.x, Field.toNat a.y, a.inf⟩

theorem toAffNat_eq {a : AF F} {b : JamCrypto.G1.Aff} (h : ARel a b) : toAffNat a = b := by
  unfold toAffNat; rw [h.1.toNat, h.2.1.toNat, h.2.2]

/-- A reference affine point with reduced coordinates. -/
def Red (b : JamCrypto.G1.Aff) : Prop := b.x < P ∧ b.y < P

/-- From a reference affine point. -/
def ofAff (b : JamCrypto.G1.Aff) : AF F := ⟨Field.ofNat b.x, Field.ofNat b.y, b.inf⟩

theorem ofAff_rel {b : JamCrypto.G1.Aff} (h : Red b) : ARel (ofAff b : AF F) b :=
  ⟨V.ofNat h.1, V.ofNat h.2, rfl⟩

theorem red_of_rel {a : AF F} {b : JamCrypto.G1.Aff} (h : ARel a b) : Red b := ⟨h.1.2, h.2.1.2⟩

end JamCrypto.Fast.G1F
