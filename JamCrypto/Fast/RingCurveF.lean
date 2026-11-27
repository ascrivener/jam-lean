import JamCrypto.RingCurve
import JamCrypto.RingVerify
import JamCrypto.Fast.EdwardsF

/-!
# The ring's Bandersnatch curve over a fast field, proved to compute what `JamCrypto.Ring.Curve`
computes

Each operation performs the same sequence of field operations as its reference in
`JamCrypto/RingCurve.lean` (unchanged), on a `Fast.Field` whose modulus is the BLS12-381 scalar
field modulus (`IsFr`), instead of `Nat` with `Fr.add`, `Fr.sub`, `Fr.mul`, … `W` relates a fast
element to the reduced value it stands for; `ERel` relates extended points.
-/

namespace JamCrypto.Fast.RingCurveF

open JamCrypto.Fast
open JamCrypto.Fr (R)

set_option linter.unusedSectionVars false

/-- The field's modulus is the BLS12-381 scalar field modulus (the Bandersnatch base field). -/
class IsFr (F : Type) [Field F] : Prop where
  p_eq : Field.p F = JamCrypto.Fr.R

variable {F : Type} [Field F] [LawfulField F] [IsFr F]

/-- `a` stands for the reduced value $x$. -/
def W (a : F) (x : Nat) : Prop := VRel a x ∧ x < R

namespace W

theorem hp : Field.p F = R := IsFr.p_eq

theorem R_pos : 0 < R := by decide

theorem of_mod {a : F} {x : Nat} (h : VRel a x) : W a (x % R) :=
  ⟨by rw [← hp (F := F)]; exact VRel.mod.mpr h, Nat.mod_lt _ R_pos⟩

theorem add_eq {x y : Nat} (hx : x < R) (hy : y < R) : JamCrypto.Fr.add x y = (x + y) % R := by
  unfold JamCrypto.Fr.add
  simp only
  split
  · have : x + y = (x + y - R) + R := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
  · rw [Nat.mod_eq_of_lt (by omega)]

theorem sub_eq {x y : Nat} (hx : x < R) (hy : y < R) :
    JamCrypto.Fr.sub x y = JamCrypto.Modular.subMod x y R := by
  unfold JamCrypto.Fr.sub JamCrypto.Modular.subMod
  rw [Nat.mod_eq_of_lt hy]
  split
  · have : x + R - y = (x - y) + R := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]

theorem add {a b : F} {x y : Nat} (ha : W a x) (hb : W b y) :
    W (Field.add a b) (JamCrypto.Fr.add x y) := by
  rw [add_eq ha.2 hb.2]; exact of_mod (ha.1.add hb.1)

theorem sub {a b : F} {x y : Nat} (ha : W a x) (hb : W b y) :
    W (Field.sub a b) (JamCrypto.Fr.sub x y) := by
  rw [sub_eq ha.2 hb.2]
  have h := ha.1.sub hb.1
  rw [hp (F := F)] at h
  unfold JamCrypto.Modular.subMod at h ⊢
  exact ⟨h, Nat.mod_lt _ R_pos⟩

theorem mul {a b : F} {x y : Nat} (ha : W a x) (hb : W b y) :
    W (Field.mul a b) (JamCrypto.Fr.mul x y) := of_mod (ha.1.mul hb.1)

theorem sq {a : F} {x : Nat} (ha : W a x) : W (Field.sq a) (JamCrypto.Fr.sq x) := of_mod ha.1.sq

theorem mulR {a b : F} {x y : Nat} (ha : VRel a x) (hb : VRel b y) :
    W (Field.mul a b) (JamCrypto.Fr.mul x y) := of_mod (ha.mul hb)

theorem sqR {a : F} {x : Nat} (ha : VRel a x) : W (Field.sq a) (JamCrypto.Fr.sq x) := of_mod ha.sq

theorem neg {a : F} {x : Nat} (ha : W a x) :
    W (Field.sub Field.zero a) (JamCrypto.Fr.neg x) := by
  have h := sub (⟨VRel.zero, R_pos⟩ : W (Field.zero : F) 0) ha
  have e : JamCrypto.Fr.sub 0 x = JamCrypto.Fr.neg x := by
    unfold JamCrypto.Fr.sub JamCrypto.Fr.neg
    by_cases hx : x = 0
    · subst hx; simp
    · have : ¬ (0 ≥ x) := by omega
      rw [if_neg this, show (x == 0) = false by simpa using hx]
      simp
  rwa [e] at h

theorem ofNat {x : Nat} (hx : x < R) : W (Field.ofNat x : F) x := ⟨VRel.ofNat x, hx⟩

theorem zero : W (Field.zero : F) 0 := ⟨VRel.zero, R_pos⟩

theorem one : W (Field.one : F) 1 := ⟨VRel.one, by decide⟩

theorem isZero {a : F} {x : Nat} (ha : W a x) : Field.isZero a = (x == 0) := by
  rw [ha.1.isZero, hp (F := F), Nat.mod_eq_of_lt ha.2]

theorem beq {a b : F} {x y : Nat} (ha : W a x) (hb : W b y) : Field.beq a b = (x == y) := by
  rw [ha.1.beq hb.1, hp (F := F), Nat.mod_eq_of_lt ha.2, Nat.mod_eq_of_lt hb.2]

theorem toNat {a : F} {x : Nat} (ha : W a x) : Field.toNat a = x := by
  rw [ha.1.toNat, hp (F := F), Nat.mod_eq_of_lt ha.2]

end W

open JamCrypto.Ring.Curve (A D)

/-- An extended point (`Curve.Ext`). -/
structure EF (F : Type) where
  x : F
  y : F
  t : F
  z : F

/-- An affine point (`Curve.Aff`). -/
structure AF (F : Type) where
  x : F
  y : F

def ERel (p : EF F) (q : JamCrypto.Ring.Curve.Ext) : Prop := W p.x q.x ∧ W p.y q.y ∧ W p.t q.t ∧ W p.z q.z
def ARel (p : AF F) (q : JamCrypto.Ring.Curve.Aff) : Prop := W p.x q.x ∧ W p.y q.y

instance : Inhabited (EF F) := ⟨⟨Field.zero, Field.zero, Field.zero, Field.zero⟩⟩

theorem erel_default : ERel (default : EF F) (default : JamCrypto.Ring.Curve.Ext) := ⟨W.zero, W.zero, W.zero, W.zero⟩

theorem A_lt : A < R := by decide
theorem D_lt : D < R := by decide

/-- The curve constants $a$ and $d$. -/
def cA : F := Field.ofNat A
def cD : F := Field.ofNat D

theorem cA_rel : W (cA : F) A := W.ofNat A_lt
theorem cD_rel : W (cD : F) D := W.ofNat D_lt

def zero : EF F := ⟨Field.zero, Field.one, Field.zero, Field.one⟩
theorem zero_rel : ERel (zero : EF F) JamCrypto.Ring.Curve.Ext.zero := ⟨W.zero, W.one, W.zero, W.one⟩

def toExt (p : AF F) : EF F := ⟨p.x, p.y, Field.mul p.x p.y, Field.one⟩
theorem toExt_rel {p : AF F} {q : JamCrypto.Ring.Curve.Aff} (h : ARel p q) : ERel (toExt p) q.toExt :=
  ⟨h.1, h.2, h.1.mul h.2, W.one⟩

/-- `onCurve`. -/
def onCurve (p : AF F) : Bool :=
  let x2 := Field.sq p.x
  let y2 := Field.sq p.y
  Field.beq (Field.add (Field.mul cA x2) y2) (Field.add Field.one (Field.mul cD (Field.mul x2 y2)))

theorem onCurve_eq {p : AF F} {q : JamCrypto.Ring.Curve.Aff} (h : ARel p q) :
    onCurve p = JamCrypto.Ring.Curve.onCurve q := by
  unfold onCurve JamCrypto.Ring.Curve.onCurve
  exact ((cA_rel.mul h.1.sq).add h.2.sq).beq (W.one.add (cD_rel.mul (h.1.sq.mul h.2.sq)))

/-- `addE` (add-2008-hwcd), operation for operation. -/
def addE (p q : EF F) : EF F :=
  let a := Field.mul p.x q.x
  let b := Field.mul p.y q.y
  let c := Field.mul cD (Field.mul p.t q.t)
  let d := Field.mul p.z q.z
  let e := Field.sub (Field.sub (Field.mul (Field.add p.x p.y) (Field.add q.x q.y)) a) b
  let f := Field.sub d c
  let g := Field.add d c
  let h := Field.sub b (Field.mul cA a)
  ⟨Field.mul e f, Field.mul g h, Field.mul e h, Field.mul f g⟩

theorem addE_rel {p q : EF F} {p' q' : JamCrypto.Ring.Curve.Ext} (hp : ERel p p') (hq : ERel q q') :
    ERel (addE p q) (JamCrypto.Ring.Curve.addE p' q') := by
  obtain ⟨px, py, pt, pz⟩ := hp
  obtain ⟨qx, qy, qt, qz⟩ := hq
  have a := px.mul qx
  have b := py.mul qy
  have c := cD_rel.mul (pt.mul qt)
  have d := pz.mul qz
  have e := (((px.add py).mul (qx.add qy)).sub a).sub b
  have f := d.sub c
  have g := d.add c
  have h := b.sub (cA_rel.mul a)
  exact ⟨e.mul f, g.mul h, e.mul h, f.mul g⟩

/-- `dblE` (dbl-2008-hwcd), operation for operation. -/
def dblE (p : EF F) : EF F :=
  let a := Field.sq p.x
  let b := Field.sq p.y
  let c := Field.add (Field.sq p.z) (Field.sq p.z)
  let d := Field.mul cA a
  let e := Field.sub (Field.sub (Field.sq (Field.add p.x p.y)) a) b
  let g := Field.add d b
  let f := Field.sub g c
  let h := Field.sub d b
  ⟨Field.mul e f, Field.mul g h, Field.mul e h, Field.mul f g⟩

theorem dblE_rel {p : EF F} {p' : JamCrypto.Ring.Curve.Ext} (hp : ERel p p') :
    ERel (dblE p) (JamCrypto.Ring.Curve.dblE p') := by
  obtain ⟨px, py, -, pz⟩ := hp
  have a := px.sq
  have b := py.sq
  have c := pz.sq.add pz.sq
  have d := cA_rel.mul a
  have e := (((px.add py).sq).sub a).sub b
  have g := d.add b
  have f := g.sub c
  have h := d.sub b
  exact ⟨e.mul f, g.mul h, e.mul h, f.mul g⟩

/-- `Ext.isZero`. -/
def isZero (p : EF F) : Bool := Field.isZero p.x && Field.beq p.y p.z && !Field.isZero p.z

theorem isZero_eq {p : EF F} {p' : JamCrypto.Ring.Curve.Ext} (hp : ERel p p') :
    isZero p = p'.isZero := by
  unfold isZero JamCrypto.Ring.Curve.Ext.isZero
  rw [hp.1.isZero, hp.2.1.beq hp.2.2.2, hp.2.2.2.isZero]
  rfl

/-- `Ext.eq`. -/
def eq (p q : EF F) : Bool :=
  Field.beq (Field.mul p.x q.z) (Field.mul q.x p.z) && Field.beq (Field.mul p.y q.z) (Field.mul q.y p.z)

theorem eq_eq {p q : EF F} {p' q' : JamCrypto.Ring.Curve.Ext} (hp : ERel p p') (hq : ERel q q') :
    eq p q = p'.eq q' := by
  unfold eq JamCrypto.Ring.Curve.Ext.eq
  rw [(hp.1.mul hq.2.2.2).beq (hq.1.mul hp.2.2.2), (hp.2.1.mul hq.2.2.2).beq (hq.2.1.mul hp.2.2.2)]

/-- `Ext.toAff`; the inversion is the reference one on the value. -/
def toAff (p : EF F) : AF F :=
  let zi : F := Field.ofNat (JamCrypto.Fr.inv (Field.toNat p.z))
  ⟨Field.mul p.x zi, Field.mul p.y zi⟩

theorem toAff_rel {p : EF F} {p' : JamCrypto.Ring.Curve.Ext} (hp : ERel p p') :
    ARel (toAff p) p'.toAff := by
  unfold toAff JamCrypto.Ring.Curve.Ext.toAff
  extract_lets zi zi'
  have hz : VRel zi zi' := by
    show VRel (Field.ofNat _) _
    rw [hp.2.2.2.toNat]; exact VRel.ofNat _
  exact ⟨W.mulR hp.1.1 hz, W.mulR hp.2.1.1 hz⟩

/-- `smulW`: the fixed 4-bit window, step for step. -/
def smulW (p : EF F) (k : Nat) : EF F := Id.run do
  let mut tbl : Array (EF F) := #[zero, p]
  for _ in [0:14] do
    tbl := tbl.push (addE tbl.back! p)
  let nd := (k.log2 + 4) / 4
  let mut acc := zero
  for i in [0:nd] do
    acc := dblE (dblE (dblE (dblE acc)))
    let d := (k >>> (4 * (nd - 1 - i))) % 16
    if d != 0 then acc := addE acc tbl[d]!
  return acc

theorem smulW_rel {p : EF F} {p' : JamCrypto.Ring.Curve.Ext} (hp : ERel p p') (k : Nat) :
    ERel (smulW p k) (JamCrypto.Ring.Curve.smulW p' k) := by
  unfold smulW JamCrypto.Ring.Curve.smulW
  simp (config := {zeta := false}) only [Id.run, bind, pure]
  extract_lets t0 t nd a0 acc t0' t' a0' acc'
  have ht : ArrRel ERel t t' := by
    refine forIn_range_rel (ArrRel ERel) _ _ _ ?_ ?_
    · refine ⟨rfl, fun i h1 h2 => ?_⟩
      match i, h1 with
      | 0, _ => exact zero_rel
      | 1, _ => exact hp
    intro _ a b hab
    simp only [Id.run, Array.back!]
    exact hab.push (by rw [hab.1]; exact addE_rel (hab.get! erel_default _) hp)
  refine forIn_range_rel ERel _ _ _ zero_rel ?_
  intro i a b hab
  simp only [Id.run]
  have h4 := dblE_rel (dblE_rel (dblE_rel (dblE_rel hab)))
  split
  · exact addE_rel h4 (ht.get! erel_default _)
  · exact h4

/-- `inSubgroup`. -/
def inSubgroup (p : AF F) : Bool := isZero (smulW (toExt p) JamCrypto.Ring.Curve.N)

theorem inSubgroup_eq {p : AF F} {p' : JamCrypto.Ring.Curve.Aff} (h : ARel p p') :
    inSubgroup p = JamCrypto.Ring.Curve.inSubgroup p' := by
  unfold inSubgroup JamCrypto.Ring.Curve.inSubgroup
  exact isZero_eq (smulW_rel (toExt_rel h) _)

theorem powMod_eq : JamCrypto.Field.powMod = JamCrypto.Modular.powMod := rfl

attribute [local irreducible] powF JamCrypto.Field.powMod JamCrypto.Modular.powMod

theorem pow_rel {a : F} {x : Nat} (h : W a x) (e : Nat) : W (powF a e) (JamCrypto.Fr.pow x e) := by
  have := powF_rel' h.1 e
  rw [W.hp (F := F)] at this
  unfold JamCrypto.Fr.pow
  rw [powMod_eq]
  exact this

/-- `Fr.sqrt?` (Tonelli–Shanks), step for step. -/
def sqrt? (a : F) : Option F := Id.run do
  if Field.isZero a then return some Field.zero
  let w := powF a ((JamCrypto.Fr.T - 1) / 2)
  let mut x := Field.mul a w
  let mut t := Field.mul x w
  let mut m := JamCrypto.Fr.S
  let mut c : F := powF (Field.ofNat JamCrypto.Fr.generator) JamCrypto.Fr.T
  for _ in [0:JamCrypto.Fr.S + 1] do
    if !Field.beq t Field.one then
      let mut i := 0
      let mut tt := t
      for _ in [0:m] do
        if !Field.beq tt Field.one then
          tt := Field.sq tt
          i := i + 1
      if i < m then
        let mut b := c
        for _ in [0:m - i - 1] do
          b := Field.sq b
        m := i
        c := Field.sq b
        t := Field.mul t c
        x := Field.mul x b
  return if Field.beq (Field.sq x) a then some x else none

theorem sqrt?_rel {a : F} {a' : Nat} (h : W a a') :
    OR W (sqrt? a) (JamCrypto.Fr.sqrt? a') := by
  unfold sqrt? JamCrypto.Fr.sqrt?
  simp only [Id.run, bind, pure, bne]
  rw [Nat.mod_eq_of_lt h.2, h.isZero]
  split
  · exact W.zero
  have hw := pow_rel h ((JamCrypto.Fr.T - 1) / 2)
  have hc0 : W (powF (Field.ofNat JamCrypto.Fr.generator) JamCrypto.Fr.T : F) JamCrypto.Fr.rootOfUnity :=
    pow_rel (W.ofNat (by decide)) _
  have h1 : ∀ {u : F} {u'}, W u u' → Field.beq u Field.one = (u' == 1) := fun hu => hu.beq W.one
  have fin : ∀ {X : F × F × Nat × F} {X' : Nat × Nat × Nat × Nat}, W X.1 X'.1 →
      OR W (if Field.beq (Field.sq X.1) a = true then some X.1 else none)
        (if (JamCrypto.Fr.sq X'.1 == a') = true then some X'.1 else none) := by
    intro X X' hx
    rw [hx.sq.beq h]
    split
    · exact hx
    · trivial
  refine fin (forIn_range_rel (fun (s : F × F × Nat × F) (s' : Nat × Nat × Nat × Nat) =>
      W s.1 s'.1 ∧ W s.2.1 s'.2.1 ∧ s.2.2.1 = s'.2.2.1 ∧ W s.2.2.2 s'.2.2.2) _ _ _
    ⟨h.mul hw, (h.mul hw).mul hw, rfl, hc0⟩ ?_).1
  rintro _ ⟨x, t, m, c⟩ ⟨x', t', m', c'⟩ ⟨hx, ht, rfl, hc⟩
  simp only [Id.run]
  rw [h1 ht]
  split
  · have hi := forIn_range_rel (fun (s : Nat × F) (s' : Nat × Nat) => s.1 = s'.1 ∧ W s.2 s'.2) [0:m]
      (fun _ (s : Nat × F) => if (!Field.beq s.snd Field.one) = true then ForInStep.yield (s.fst + 1, Field.sq s.snd)
        else ForInStep.yield (s.fst, s.snd))
      (fun _ (s : Nat × Nat) => if (!(s.snd == 1)) = true then ForInStep.yield (s.fst + 1, JamCrypto.Fr.sq s.snd)
        else ForInStep.yield (s.fst, s.snd))
      (a := (0, t)) (b := (0, t')) ⟨rfl, ht⟩ (fun _ u u' hu => by
          obtain ⟨i, tt⟩ := u; obtain ⟨i', tt'⟩ := u'; obtain ⟨rfl, htt⟩ := hu
          simp only [Id.run]
          rw [h1 htt]
          split
          · exact ⟨rfl, htt.sq⟩
          · exact ⟨rfl, htt⟩)
    simp only [Id.run] at hi
    rw [hi.1]
    split
    · have hb := forIn_range_rel W [0:m - (forIn [0:m] ((0 : Nat), t')
          (fun _ (s : Nat × Nat) => if (!(s.snd == 1)) = true then ForInStep.yield (s.fst + 1, JamCrypto.Fr.sq s.snd)
            else ForInStep.yield (s.fst, s.snd)) : Id _).fst - 1]
        (fun _ (s : F) => ForInStep.yield (Field.sq s)) (fun _ (s : Nat) => ForInStep.yield (JamCrypto.Fr.sq s))
        hc (fun _ u u' hu => by simp only [Id.run]; exact hu.sq)
      simp only [Id.run] at hb
      exact ⟨hx.mul hb, ht.mul hb.sq, rfl, hb.sq⟩
    · exact ⟨hx, ht, rfl, hc⟩
  · exact ⟨hx, ht, rfl, hc⟩

attribute [local irreducible] sqrt? JamCrypto.Fr.sqrt? JamCrypto.Field.invMod JamCrypto.Field.ofLE

/-- `decodeUnchecked`, step for step. -/
def decodeUnchecked (bs : List UInt8) : Option (AF F) := do
  if bs.length != 32 then none
  let v := JamCrypto.Field.ofLE bs
  let neg := v ≥ 2 ^ 255
  let y := v % 2 ^ 255
  if y ≥ R then none
  let yf : F := Field.ofNat y
  let y2 := Field.sq yf
  let den := Field.sub cA (Field.mul cD y2)
  if Field.isZero den then none
  let x2 := Field.mul (Field.sub Field.one y2) (Field.ofNat (JamCrypto.Fr.inv (Field.toNat den)))
  let x ← sqrt? x2
  let (lo, hi) := if Field.toNat x ≤ Field.toNat (Field.sub Field.zero x) then (x, Field.sub Field.zero x)
    else (Field.sub Field.zero x, x)
  some ⟨if neg then hi else lo, yf⟩

theorem decodeUnchecked_rel (bs : List UInt8) :
    OR ARel (decodeUnchecked (F := F) bs) (JamCrypto.Ring.Curve.decodeUnchecked bs) := by
  unfold decodeUnchecked JamCrypto.Ring.Curve.decodeUnchecked
  dsimp only [bind, Option.bind]
  generalize JamCrypto.Field.ofLE bs = v
  refine OR.ite (fun _ => trivial) fun _ => ?_
  refine OR.ite (fun _ => trivial) fun hy => ?_
  have vy : W (Field.ofNat (v % 2 ^ 255) : F) (v % 2 ^ 255) := W.ofNat (Nat.lt_of_not_le hy)
  have vden := cA_rel.sub (cD_rel.mul vy.sq)
  rw [vden.isZero]
  refine OR.ite (fun _ => trivial) fun _ => ?_
  have hi : VRel ((Field.ofNat (JamCrypto.Fr.inv (Field.toNat (Field.sub (cA : F)
      (Field.mul cD (Field.sq (Field.ofNat (v % 2 ^ 255)))))))) : F)
      (JamCrypto.Fr.inv (JamCrypto.Fr.sub A (JamCrypto.Fr.mul D (JamCrypto.Fr.sq (v % 2 ^ 255))))) := by
    rw [vden.toNat]; exact VRel.ofNat _
  have vx2 := W.mulR (W.one.sub vy.sq).1 hi
  have hs := sqrt?_rel vx2
  revert hs
  generalize (sqrt? _ : Option F) = s
  generalize JamCrypto.Fr.sqrt? _ = s'
  intro hs
  cases s <;> cases s' <;> simp only [OR] at hs
  · trivial
  rename_i x x'
  dsimp only
  rw [hs.toNat, hs.neg.toNat]
  by_cases h1 : v ≥ 2 ^ 255 <;> by_cases h2 : x' ≤ JamCrypto.Fr.neg x' <;>
    simp only [h1, h2, if_true, if_false] <;> first | exact ⟨hs, vy⟩ | exact ⟨hs.neg, vy⟩

/-- `decode`: decodes, on the curve, in the prime-order subgroup. -/
def decode (bs : List UInt8) : Option (AF F) := do
  let p ← decodeUnchecked bs
  if onCurve p && inSubgroup p then some p else none

theorem decode_rel (bs : List UInt8) : OR ARel (decode (F := F) bs) (JamCrypto.Ring.Curve.decode bs) := by
  unfold decode JamCrypto.Ring.Curve.decode
  refine OR.bind (decodeUnchecked_rel bs) fun p p' h => ?_
  rw [onCurve_eq h, inSubgroup_eq h]
  exact OR.ite (fun _ => h) fun _ => trivial

/-! ## Hash to curve (`Ring.ell2Map`, `Ring.hashToCurve`) -/

/-- An inversion: the reference `Fr.inv` on the value. -/
def invV (a : F) : F := Field.ofNat (JamCrypto.Fr.inv (Field.toNat a))

theorem invV_rel {a : F} {x : Nat} (h : W a x) : VRel (invV a) (JamCrypto.Fr.inv x) := by
  unfold invV; rw [h.toNat]; exact VRel.ofNat _

/-- `isQR`. -/
def isQR (a : F) : Bool := !Field.isZero a && Field.beq (powF a ((R - 1) / 2)) Field.one

theorem isQR_eq {a : F} {x : Nat} (h : W a x) : isQR a = JamCrypto.Ring.isQR x := by
  unfold isQR JamCrypto.Ring.isQR
  rw [h.isZero, (pow_rel h _).beq W.one, Nat.mod_eq_of_lt h.2]
  rfl

/-- `Ring.ell2Map`, step for step. -/
def ell2Map (e : Nat) : AF F :=
  let k : F := Field.ofNat JamCrypto.Ring.montB
  let jk := Field.mul (Field.ofNat JamCrypto.Ring.montA) (invV (Field.ofNat JamCrypto.Ring.montB))
  let ksqInv := invV (Field.sq (Field.ofNat JamCrypto.Ring.montB))
  let den1 := Field.add Field.one (Field.mul (Field.ofNat JamCrypto.Ring.ell2Z) (Field.sq (Field.ofNat e)))
  let x1 := Field.sub Field.zero (Field.mul jk (invV (if Field.isZero den1 then Field.one else den1)))
  let g (x : F) := Field.add (Field.add (Field.mul (Field.sq x) x) (Field.mul jk (Field.sq x))) (Field.mul x ksqInv)
  let gx1 := g x1
  let x2 := Field.sub (Field.sub Field.zero x1) jk
  let sgn0 := isQR gx1
  let x := if sgn0 then x1 else x2
  let y0 := if sgn0 then (sqrt? gx1).getD Field.zero else (sqrt? (g x2)).getD Field.zero
  let y := if (Field.toNat y0 % 2 == 1) != sgn0 then Field.sub Field.zero y0 else y0
  let s := Field.mul x k
  let t := Field.mul y k
  let tv1 := Field.add s Field.one
  let tv2 := Field.mul tv1 t
  if Field.isZero tv2 then ⟨Field.zero, Field.one⟩ else
  let i := invV tv2
  ⟨Field.mul (Field.mul i tv1) s, Field.mul (Field.mul i t) (Field.sub s Field.one)⟩

theorem getD_rel {o : Option F} {o' : Option Nat} (h : OR W o o') : W (o.getD Field.zero) (o'.getD 0) := by
  cases o <;> cases o' <;> simp only [OR] at h <;> first | exact h | exact W.zero | exact absurd h id

theorem ell2Map_rel (e : Nat) : ARel (ell2Map (F := F) e) (JamCrypto.Ring.ell2Map e) := by
  unfold ell2Map JamCrypto.Ring.ell2Map
  extract_lets k jk ksq den1 x1 g gx1 x2 sgn0 x y0 y s t tv1 tv2 i
    k' jk' ksq' den1' x1' g' gx1' x2' sgn0' x' y0' y' s' t' tv1' tv2' i'
  have vB : W (Field.ofNat JamCrypto.Ring.montB : F) JamCrypto.Ring.montB := W.ofNat (by decide)
  have vk : W k k' := vB
  have vjk : W jk jk' := W.mulR (VRel.ofNat _) (invV_rel vB)
  have vksq : VRel ksq ksq' := invV_rel vB.sq
  have vden1 : W den1 den1' := W.one.add ((W.ofNat (by decide)).mul (W.sqR (VRel.ofNat e)))
  have vsel : W (if Field.isZero den1 = true then Field.one else den1) (if (den1' == 0) = true then 1 else den1') := by
    rw [vden1.isZero]; split
    · exact W.one
    · exact vden1
  have vx1 : W x1 x1' := (W.mulR vjk.1 (invV_rel vsel)).neg
  have hg : ∀ {a : F} {a' : Nat}, W a a' → W (g a) (g' a') := fun ha =>
    ((ha.sq.mul ha).add (vjk.mul ha.sq)).add (W.mulR ha.1 vksq)
  have vgx1 : W gx1 gx1' := hg vx1
  have vx2 : W x2 x2' := vx1.neg.sub vjk
  have hs0 : sgn0 = sgn0' := isQR_eq vgx1
  have vx : W x x' := by
    show W (if sgn0 = true then x1 else x2) (if sgn0' = true then x1' else x2')
    rw [hs0]; split
    · exact vx1
    · exact vx2
  have vy0 : W y0 y0' := by
    show W (if sgn0 = true then (sqrt? gx1).getD Field.zero else (sqrt? (g x2)).getD Field.zero)
      (if sgn0' = true then (JamCrypto.Fr.sqrt? gx1').getD 0 else (JamCrypto.Fr.sqrt? (g' x2')).getD 0)
    rw [hs0]; split
    · exact getD_rel (sqrt?_rel vgx1)
    · exact getD_rel (sqrt?_rel (hg vx2))
  have vy : W y y' := by
    show W (if ((Field.toNat y0 % 2 == 1) != sgn0) = true then Field.sub Field.zero y0 else y0)
      (if ((y0' % 2 == 1) != sgn0') = true then JamCrypto.Fr.neg y0' else y0')
    rw [vy0.toNat, hs0]; split
    · exact vy0.neg
    · exact vy0
  have vs : W s s' := vx.mul vk
  have vt : W t t' := vy.mul vk
  have vtv1 : W tv1 tv1' := vs.add W.one
  have vtv2 : W tv2 tv2' := vtv1.mul vt
  have vi : VRel i i' := invV_rel vtv2
  rw [vtv2.isZero]
  split
  · exact ⟨W.zero, W.one⟩
  · exact ⟨W.mulR (W.mulR vi vtv1.1).1 vs.1, W.mulR (W.mulR vi vt.1).1 (vs.sub W.one).1⟩

/-- `Ring.hashToCurve`. -/
def hashToCurve (data : List UInt8) : AF F :=
  let (u0, u1) := JamCrypto.Ring.hashToField data
  let p := addE (toExt (ell2Map u0)) (toExt (ell2Map u1))
  toAff (dblE (dblE p))

theorem hashToCurve_rel (data : List UInt8) :
    ARel (hashToCurve (F := F) data) (JamCrypto.Ring.hashToCurve data) := by
  unfold hashToCurve JamCrypto.Ring.hashToCurve
  generalize JamCrypto.Ring.hashToField data = uu
  obtain ⟨u0, u1⟩ := uu
  exact toAff_rel (dblE_rel (dblE_rel (addE_rel (toExt_rel (ell2Map_rel u0)) (toExt_rel (ell2Map_rel u1)))))

end JamCrypto.Fast.RingCurveF
