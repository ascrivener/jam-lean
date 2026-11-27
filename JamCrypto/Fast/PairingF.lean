import JamCrypto.Bls12381Pairing
import JamCrypto.Fast.G1F

/-!
# The BLS12-381 pairing over a fast field, proved to compute what `JamCrypto.Pairing` computes

The towers 𝔽_q2, 𝔽_q6 and 𝔽_q12, the Miller loop and the final exponentiation of
`JamCrypto/Bls12381Pairing.lean` (unchanged), each performing the same sequence of field
operations on a `Fast.Field` whose modulus is the BLS12-381 base field modulus (`G1F.IsFq`). The
relations `V2`, `V6`, `V12` relate a fast element to the reference element whose coordinates are
its (reduced) values; every operation preserves them. An 𝔽_q inversion is the reference one,
`Fq.inv`, on the value.
-/

namespace JamCrypto.Fast.PairingF

open JamCrypto.Fast JamCrypto.Fast.G1F
open JamCrypto.Fq (P)

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [LawfulField F] [IsFq F]

/-! ## 𝔽_q2 -/

structure E2 (F : Type) where
  a : F
  b : F

def V2 (x : E2 F) (y : JamCrypto.Pairing.Fq2) : Prop := V x.a y.a ∧ V x.b y.b

namespace E2

def zero : E2 F := ⟨Field.zero, Field.zero⟩
def one : E2 F := ⟨Field.one, Field.zero⟩
@[inline] def add (x y : E2 F) : E2 F := ⟨Field.add x.a y.a, Field.add x.b y.b⟩
@[inline] def sub (x y : E2 F) : E2 F := ⟨Field.sub x.a y.a, Field.sub x.b y.b⟩
@[inline] def neg (x : E2 F) : E2 F := ⟨Field.sub Field.zero x.a, Field.sub Field.zero x.b⟩
@[inline] def mul (x y : E2 F) : E2 F :=
  let t0 := Field.mul x.a y.a
  let t1 := Field.mul x.b y.b
  ⟨Field.sub t0 t1, Field.sub (Field.sub (Field.mul (Field.add x.a x.b) (Field.add y.a y.b)) t0) t1⟩
@[inline] def sq (x : E2 F) : E2 F :=
  ⟨Field.mul (Field.add x.a x.b) (Field.sub x.a x.b), Field.mul (Field.add x.a x.a) x.b⟩
@[inline] def scale (x : E2 F) (k : F) : E2 F := ⟨Field.mul x.a k, Field.mul x.b k⟩
@[inline] def mulXi (x : E2 F) : E2 F := ⟨Field.sub x.a x.b, Field.add x.a x.b⟩
def inv (x : E2 F) : E2 F :=
  let d : F := Field.ofNat (JamCrypto.Fq.inv (Field.toNat (Field.add (Field.sq x.a) (Field.sq x.b))))
  ⟨Field.mul x.a d, Field.sub Field.zero (Field.mul x.b d)⟩
def conj (x : E2 F) : E2 F := ⟨x.a, Field.sub Field.zero x.b⟩
def pow (x : E2 F) (e : Nat) : E2 F := Id.run do
  let mut acc := one
  let n := e.log2 + 1
  for i in [0:n] do
    acc := sq acc
    if (e >>> (n - 1 - i)) % 2 == 1 then acc := mul acc x
  return acc

end E2

namespace V2
open JamCrypto.Pairing (Fq2)

theorem zero : V2 (E2.zero : E2 F) Fq2.zero := ⟨V.zero, V.zero⟩
theorem one : V2 (E2.one : E2 F) Fq2.one := ⟨V.one, V.zero⟩

theorem add {x y : E2 F} {x' y' : Fq2} (hx : V2 x x') (hy : V2 y y') :
    V2 (x.add y) (x'.add y') := ⟨hx.1.add hy.1, hx.2.add hy.2⟩

theorem sub {x y : E2 F} {x' y' : Fq2} (hx : V2 x x') (hy : V2 y y') :
    V2 (x.sub y) (x'.sub y') := ⟨hx.1.sub hy.1, hx.2.sub hy.2⟩

theorem neg {x : E2 F} {x' : Fq2} (hx : V2 x x') : V2 x.neg x'.neg := ⟨hx.1.neg, hx.2.neg⟩

theorem mul {x y : E2 F} {x' y' : Fq2} (hx : V2 x x') (hy : V2 y y') :
    V2 (x.mul y) (x'.mul y') := by
  have t0 := hx.1.mul hy.1
  have t1 := hx.2.mul hy.2
  exact ⟨t0.sub t1, ((((hx.1.add hx.2).mul (hy.1.add hy.2)).sub t0).sub t1)⟩

theorem sq {x : E2 F} {x' : Fq2} (hx : V2 x x') : V2 x.sq x'.sq :=
  ⟨(hx.1.add hx.2).mul (hx.1.sub hx.2), (hx.1.add hx.1).mul hx.2⟩

theorem scale {x : E2 F} {x' : Fq2} {k : F} {k' : Nat} (hx : V2 x x') (hk : V k k') :
    V2 (x.scale k) (x'.scale k') := ⟨hx.1.mul hk, hx.2.mul hk⟩

theorem mulXi {x : E2 F} {x' : Fq2} (hx : V2 x x') : V2 x.mulXi x'.mulXi :=
  ⟨hx.1.sub hx.2, hx.1.add hx.2⟩

theorem inv {x : E2 F} {x' : Fq2} (hx : V2 x x') : V2 x.inv x'.inv := by
  unfold E2.inv Fq2.inv
  extract_lets d d'
  have hd : VRel d d' := by
    show VRel (Field.ofNat _) _
    rw [((hx.1.sq).add (hx.2.sq)).toNat]; exact VRel.ofNat _
  exact ⟨V.mulR hx.1.1 hd, (V.mulR hx.2.1 hd).neg⟩

theorem conj {x : E2 F} {x' : Fq2} (hx : V2 x x') : V2 x.conj x'.conj := ⟨hx.1, hx.2.neg⟩

theorem pow {x : E2 F} {x' : Fq2} (hx : V2 x x') (e : Nat) : V2 (x.pow e) (x'.pow e) := by
  unfold E2.pow Fq2.pow
  simp only [Id.run, bind, pure]
  refine forIn_range_rel V2 _ _ _ one ?_
  intro i a b hab
  simp only [Id.run]
  split
  · exact hab.sq.mul hx
  · exact hab.sq

theorem isZero {x : E2 F} {x' : Fq2} (hx : V2 x x') :
    (Field.isZero x.a && Field.isZero x.b) = x'.isZero := by
  rw [hx.1.isZero, hx.2.isZero]; rfl

end V2

/-! ## 𝔽_q6 -/

structure E6 (F : Type) where
  c0 : E2 F
  c1 : E2 F
  c2 : E2 F

def V6 (x : E6 F) (y : JamCrypto.Pairing.Fq6) : Prop := V2 x.c0 y.c0 ∧ V2 x.c1 y.c1 ∧ V2 x.c2 y.c2

namespace E6

def zero : E6 F := ⟨E2.zero, E2.zero, E2.zero⟩
def one : E6 F := ⟨E2.one, E2.zero, E2.zero⟩
@[inline] def add (x y : E6 F) : E6 F := ⟨x.c0.add y.c0, x.c1.add y.c1, x.c2.add y.c2⟩
@[inline] def sub (x y : E6 F) : E6 F := ⟨x.c0.sub y.c0, x.c1.sub y.c1, x.c2.sub y.c2⟩
@[inline] def neg (x : E6 F) : E6 F := ⟨x.c0.neg, x.c1.neg, x.c2.neg⟩
def mul (x y : E6 F) : E6 F :=
  let t0 := x.c0.mul y.c0
  let t1 := x.c1.mul y.c1
  let t2 := x.c2.mul y.c2
  let c0 := t0.add (((x.c1.add x.c2).mul (y.c1.add y.c2)).sub (t1.add t2)).mulXi
  let c1 := (((x.c0.add x.c1).mul (y.c0.add y.c1)).sub (t0.add t1)).add t2.mulXi
  let c2 := (((x.c0.add x.c2).mul (y.c0.add y.c2)).sub (t0.add t2)).add t1
  ⟨c0, c1, c2⟩
@[inline] def mulV (x : E6 F) : E6 F := ⟨x.c2.mulXi, x.c0, x.c1⟩
@[inline] def scale (x : E6 F) (k : F) : E6 F := ⟨x.c0.scale k, x.c1.scale k, x.c2.scale k⟩
def inv (x : E6 F) : E6 F :=
  let t0 := x.c0.sq.sub (x.c1.mul x.c2).mulXi
  let t1 := x.c2.sq.mulXi.sub (x.c0.mul x.c1)
  let t2 := x.c1.sq.sub (x.c0.mul x.c2)
  let d := (x.c0.mul t0).add ((x.c2.mul t1).add (x.c1.mul t2)).mulXi
  let di := d.inv
  ⟨t0.mul di, t1.mul di, t2.mul di⟩

end E6

namespace V6
open JamCrypto.Pairing (Fq6)

theorem zero : V6 (E6.zero : E6 F) Fq6.zero := ⟨V2.zero, V2.zero, V2.zero⟩
theorem one : V6 (E6.one : E6 F) Fq6.one := ⟨V2.one, V2.zero, V2.zero⟩

theorem add {x y : E6 F} {x' y' : Fq6} (hx : V6 x x') (hy : V6 y y') :
    V6 (x.add y) (x'.add y') := ⟨hx.1.add hy.1, hx.2.1.add hy.2.1, hx.2.2.add hy.2.2⟩

theorem sub {x y : E6 F} {x' y' : Fq6} (hx : V6 x x') (hy : V6 y y') :
    V6 (x.sub y) (x'.sub y') := ⟨hx.1.sub hy.1, hx.2.1.sub hy.2.1, hx.2.2.sub hy.2.2⟩

theorem neg {x : E6 F} {x' : Fq6} (hx : V6 x x') : V6 x.neg x'.neg :=
  ⟨hx.1.neg, hx.2.1.neg, hx.2.2.neg⟩

theorem mul {x y : E6 F} {x' y' : Fq6} (hx : V6 x x') (hy : V6 y y') :
    V6 (x.mul y) (x'.mul y') := by
  obtain ⟨x0, x1, x2⟩ := hx
  obtain ⟨y0, y1, y2⟩ := hy
  have t0 := x0.mul y0
  have t1 := x1.mul y1
  have t2 := x2.mul y2
  exact ⟨t0.add ((((x1.add x2).mul (y1.add y2)).sub (t1.add t2)).mulXi),
    (((x0.add x1).mul (y0.add y1)).sub (t0.add t1)).add t2.mulXi,
    (((x0.add x2).mul (y0.add y2)).sub (t0.add t2)).add t1⟩

theorem mulV {x : E6 F} {x' : Fq6} (hx : V6 x x') : V6 x.mulV x'.mulV :=
  ⟨hx.2.2.mulXi, hx.1, hx.2.1⟩

theorem scale {x : E6 F} {x' : Fq6} {k : F} {k' : Nat} (hx : V6 x x') (hk : V k k') :
    V6 (x.scale k) (x'.scale k') := ⟨hx.1.scale hk, hx.2.1.scale hk, hx.2.2.scale hk⟩

theorem inv {x : E6 F} {x' : Fq6} (hx : V6 x x') : V6 x.inv x'.inv := by
  obtain ⟨x0, x1, x2⟩ := hx
  have t0 := x0.sq.sub (x1.mul x2).mulXi
  have t1 := x2.sq.mulXi.sub (x0.mul x1)
  have t2 := x1.sq.sub (x0.mul x2)
  have d := (x0.mul t0).add ((x2.mul t1).add (x1.mul t2)).mulXi
  have di := d.inv
  exact ⟨t0.mul di, t1.mul di, t2.mul di⟩

end V6

/-! ## 𝔽_q12 -/

structure E12 (F : Type) where
  d0 : E6 F
  d1 : E6 F

def V12 (x : E12 F) (y : JamCrypto.Pairing.Fq12) : Prop := V6 x.d0 y.d0 ∧ V6 x.d1 y.d1

namespace E12

def one : E12 F := ⟨E6.one, E6.zero⟩
def ofFq2 (x : E2 F) : E12 F := ⟨⟨x, E2.zero, E2.zero⟩, E6.zero⟩
@[inline] def add (x y : E12 F) : E12 F := ⟨x.d0.add y.d0, x.d1.add y.d1⟩
def mul (x y : E12 F) : E12 F :=
  let t0 := x.d0.mul y.d0
  let t1 := x.d1.mul y.d1
  ⟨t0.add t1.mulV, ((x.d0.add x.d1).mul (y.d0.add y.d1)).sub (t0.add t1)⟩
def sq (x : E12 F) : E12 F := mul x x
@[inline] def scale (x : E12 F) (k : F) : E12 F := ⟨x.d0.scale k, x.d1.scale k⟩
def conj (x : E12 F) : E12 F := ⟨x.d0, x.d1.neg⟩
def inv (x : E12 F) : E12 F :=
  let d := (x.d0.mul x.d0).sub (x.d1.mul x.d1).mulV
  let di := d.inv
  ⟨x.d0.mul di, (x.d1.mul di).neg⟩
def pow (x : E12 F) (e : Nat) : E12 F := Id.run do
  let mut acc := one
  let n := e.log2 + 1
  for i in [0:n] do
    acc := sq acc
    if (e >>> (n - 1 - i)) % 2 == 1 then acc := mul acc x
  return acc

end E12

namespace V12
open JamCrypto.Pairing (Fq12)

theorem one : V12 (E12.one : E12 F) Fq12.one := ⟨V6.one, V6.zero⟩

theorem ofFq2 {x : E2 F} {x' : JamCrypto.Pairing.Fq2} (hx : V2 x x') :
    V12 (E12.ofFq2 x) (Fq12.ofFq2 x') := ⟨⟨hx, V2.zero, V2.zero⟩, V6.zero⟩

theorem add {x y : E12 F} {x' y' : Fq12} (hx : V12 x x') (hy : V12 y y') :
    V12 (x.add y) (x'.add y') := ⟨hx.1.add hy.1, hx.2.add hy.2⟩

theorem mul {x y : E12 F} {x' y' : Fq12} (hx : V12 x x') (hy : V12 y y') :
    V12 (x.mul y) (x'.mul y') := by
  have t0 := hx.1.mul hy.1
  have t1 := hx.2.mul hy.2
  exact ⟨t0.add t1.mulV, ((hx.1.add hx.2).mul (hy.1.add hy.2)).sub (t0.add t1)⟩

theorem sq {x : E12 F} {x' : Fq12} (hx : V12 x x') : V12 x.sq x'.sq := hx.mul hx

theorem scale {x : E12 F} {x' : Fq12} {k : F} {k' : Nat} (hx : V12 x x') (hk : V k k') :
    V12 (x.scale k) (x'.scale k') := ⟨hx.1.scale hk, hx.2.scale hk⟩

theorem conj {x : E12 F} {x' : Fq12} (hx : V12 x x') : V12 x.conj x'.conj := ⟨hx.1, hx.2.neg⟩

theorem inv {x : E12 F} {x' : Fq12} (hx : V12 x x') : V12 x.inv x'.inv := by
  have d := (hx.1.mul hx.1).sub (hx.2.mul hx.2).mulV
  have di := d.inv
  exact ⟨hx.1.mul di, (hx.2.mul di).neg⟩

theorem pow {x : E12 F} {x' : Fq12} (hx : V12 x x') (e : Nat) : V12 (x.pow e) (x'.pow e) := by
  unfold E12.pow Fq12.pow
  simp only [Id.run, bind, pure]
  refine forIn_range_rel V12 _ _ _ one ?_
  intro i a b hab
  simp only [Id.run]
  split
  · exact hab.sq.mul hx
  · exact hab.sq

end V12

/-! ## The pairing -/

open JamCrypto.Pairing (blsX)

def w : E12 F := ⟨E6.zero, E6.one⟩
def wInv : E12 F := (w : E12 F).inv
def wInv3 : E12 F := (wInv : E12 F).mul ((wInv : E12 F).mul wInv)

theorem w_rel : V12 (w : E12 F) JamCrypto.Pairing.w := ⟨V6.zero, V6.one⟩
theorem wInv_rel : V12 (wInv : E12 F) JamCrypto.Pairing.wInv := w_rel.inv
theorem wInv3_rel : V12 (wInv3 : E12 F) JamCrypto.Pairing.wInv3 := wInv_rel.mul (wInv_rel.mul wInv_rel)

/-- A G2 point (`Pairing.G2`). -/
structure G2F (F : Type) where
  x : E2 F
  y : E2 F
  inf : Bool

def GRel (q : G2F F) (q' : JamCrypto.Pairing.G2) : Prop := V2 q.x q'.x ∧ V2 q.y q'.y ∧ q.inf = q'.inf

/-- A pair of line coefficients. -/
def LRel (a : E12 F × E12 F) (b : JamCrypto.Pairing.Fq12 × JamCrypto.Pairing.Fq12) : Prop :=
  V12 a.1 b.1 ∧ V12 a.2 b.2

instance : Inhabited (E12 F) := ⟨⟨⟨⟨Field.zero, Field.zero⟩, ⟨Field.zero, Field.zero⟩, ⟨Field.zero, Field.zero⟩⟩,
  ⟨⟨Field.zero, Field.zero⟩, ⟨Field.zero, Field.zero⟩, ⟨Field.zero, Field.zero⟩⟩⟩⟩
instance : Inhabited (E2 F) := ⟨⟨Field.zero, Field.zero⟩⟩

theorem v12_default : V12 (default : E12 F) (default : JamCrypto.Pairing.Fq12) :=
  ⟨⟨⟨V.zero, V.zero⟩, ⟨V.zero, V.zero⟩, ⟨V.zero, V.zero⟩⟩, ⟨⟨V.zero, V.zero⟩, ⟨V.zero, V.zero⟩, ⟨V.zero, V.zero⟩⟩⟩

theorem lrel_default : LRel (default : E12 F × E12 F) (default : JamCrypto.Pairing.Fq12 × JamCrypto.Pairing.Fq12) :=
  ⟨v12_default, v12_default⟩

theorem v2_default : V2 (default : E2 F) (default : JamCrypto.Pairing.Fq2) := ⟨V.zero, V.zero⟩

theorem arr_push {α β : Type} {R : α → β → Prop} {a : Array α} {b : Array β} (h : ArrRel R a b)
    {x : α} {y : β} (hxy : R x y) : ArrRel R (a.push x) (b.push y) := by
  refine ⟨by simp [h.1], fun i h1 h2 => ?_⟩
  rw [Array.getElem_push, Array.getElem_push]
  have hs := h.1
  simp only [Array.size_push] at h1 h2
  by_cases hi : i < a.size
  · rw [dif_pos hi, dif_pos (hs ▸ hi)]; exact h.2 i hi (hs ▸ hi)
  · rw [dif_neg hi, dif_neg (hs ▸ hi)]; exact hxy

/-- `lines`, step for step. -/
def lines (q : G2F F) : Array (E12 F × E12 F) := Id.run do
  let mut out : Array (E12 F × E12 F) := #[]
  let mut tx := q.x
  let mut ty := q.y
  let n := blsX.log2
  let coeffs (lam xt yt : E2 F) : E12 F × E12 F :=
    ((E12.ofFq2 lam.neg).mul wInv, (E12.ofFq2 ((lam.mul xt).sub yt)).mul wInv3)
  for i in [0:n] do
    let lam := (tx.sq.scale (Field.ofNat 3)).mul (ty.add ty).inv
    out := out.push (coeffs lam tx ty)
    let x3 := lam.sq.sub (tx.add tx)
    let y3 := (lam.mul (tx.sub x3)).sub ty
    tx := x3; ty := y3
    if (blsX >>> (n - 1 - i)) % 2 == 1 then
      let lam := (q.y.sub ty).mul (q.x.sub tx).inv
      out := out.push (coeffs lam tx ty)
      let x3 := (lam.sq.sub tx).sub q.x
      let y3 := (lam.mul (tx.sub x3)).sub ty
      tx := x3; ty := y3
  return out

theorem lines_rel {q : G2F F} {q' : JamCrypto.Pairing.G2} (hq : GRel q q') :
    ArrRel LRel (lines q) (JamCrypto.Pairing.lines q') := by
  obtain ⟨qx, qy, -⟩ := hq
  unfold lines JamCrypto.Pairing.lines
  simp only [Id.run, bind, pure]
  have hc : ∀ {l l' x x' y y'}, V2 l l' → V2 x x' → V2 y y' →
      LRel (((E12.ofFq2 l.neg).mul wInv, (E12.ofFq2 ((l.mul x).sub y)).mul wInv3) : E12 F × E12 F)
        ((JamCrypto.Pairing.Fq12.ofFq2 l'.neg).mul JamCrypto.Pairing.wInv,
          (JamCrypto.Pairing.Fq12.ofFq2 ((l'.mul x').sub y')).mul JamCrypto.Pairing.wInv3) :=
    fun hl hx hy => ⟨(V12.ofFq2 hl.neg).mul wInv_rel, (V12.ofFq2 ((hl.mul hx).sub hy)).mul wInv3_rel⟩
  refine (forIn_range_rel (fun (s : Array (E12 F × E12 F) × E2 F × E2 F)
      (t : Array (JamCrypto.Pairing.Fq12 × JamCrypto.Pairing.Fq12) × JamCrypto.Pairing.Fq2 × JamCrypto.Pairing.Fq2) =>
      ArrRel LRel s.1 t.1 ∧ V2 s.2.1 t.2.1 ∧ V2 s.2.2 t.2.2) _ _ _ ?_ ?_).1
  · exact ⟨⟨rfl, fun i h1 => absurd h1 (Nat.not_lt_zero _)⟩, qx, qy⟩
  rintro i ⟨out, tx, ty⟩ ⟨out', tx', ty'⟩ ⟨ho, hx, hy⟩
  dsimp only at ho hx hy
  simp only [Id.run]
  have hl := ((hx.sq).scale (V.ofNat (show 3 < P by decide))).mul (hy.add hy).inv
  have ho2 := arr_push ho (hc hl hx hy)
  have hx3 := hl.sq.sub (hx.add hx)
  have hy3 := (hl.mul (hx.sub hx3)).sub hy
  split
  · have hl2 := (qy.sub hy3).mul (qx.sub hx3).inv
    exact ⟨arr_push ho2 (hc hl2 hx3 hy3), (hl2.sq.sub hx3).sub qx, (hl2.mul (hx3.sub ((hl2.sq.sub hx3).sub qx))).sub hy3⟩
  · exact ⟨ho2, hx3, hy3⟩

/-- `miller`, step for step, with the line coefficients `ls` of `q` given (`lines q`, or the same
    array computed once for a fixed `q`). -/
def millerWith (p : AF F) (q : G2F F) (ls : Array (E12 F × E12 F)) : E12 F := Id.run do
  if p.inf || q.inf then return E12.one
  let evalLine (k : Nat) : E12 F :=
    let (a, b) := ls[k]!
    let l := b.add (a.scale p.x)
    { l with d0 := { l.d0 with c0 := l.d0.c0.add ⟨p.y, Field.zero⟩ } }
  let mut f := E12.one
  let mut k := 0
  let n := blsX.log2
  for i in [0:n] do
    f := f.sq.mul (evalLine k)
    k := k + 1
    if (blsX >>> (n - 1 - i)) % 2 == 1 then
      f := f.mul (evalLine k)
      k := k + 1
  return f.conj

theorem millerWith_rel {p : AF F} {p' : JamCrypto.G1.Aff} {q : G2F F} {q' : JamCrypto.Pairing.G2}
    {ls : Array (E12 F × E12 F)} (hp : ARel p p') (hq : GRel q q')
    (hls : ArrRel LRel ls (JamCrypto.Pairing.lines q')) :
    V12 (millerWith p q ls) (JamCrypto.Pairing.miller p' q') := by
  unfold millerWith JamCrypto.Pairing.miller
  simp only [Id.run, bind, pure]
  rw [hp.2.2, hq.2.2]
  split
  · exact V12.one
  have ev : ∀ {x : E12 F × E12 F} {y : JamCrypto.Pairing.Fq12 × JamCrypto.Pairing.Fq12}, LRel x y →
      V12 (⟨⟨(x.2.add (x.1.scale p.x)).d0.c0.add ⟨p.y, Field.zero⟩, (x.2.add (x.1.scale p.x)).d0.c1,
          (x.2.add (x.1.scale p.x)).d0.c2⟩, (x.2.add (x.1.scale p.x)).d1⟩ : E12 F)
        ⟨⟨(y.2.add (y.1.scale p'.x)).d0.c0.add ⟨p'.y, 0⟩, (y.2.add (y.1.scale p'.x)).d0.c1,
          (y.2.add (y.1.scale p'.x)).d0.c2⟩, (y.2.add (y.1.scale p'.x)).d1⟩ := by
    intro x y h
    have hl := h.2.add (h.1.scale hp.1)
    exact ⟨⟨hl.1.1.add ⟨hp.2.1, V.zero⟩, hl.1.2.1, hl.1.2.2⟩, hl.2⟩
  have he := fun k => ev (hls.get! lrel_default k)
  refine V12.conj (forIn_range_rel (fun (s : E12 F × Nat) (t : JamCrypto.Pairing.Fq12 × Nat) =>
      V12 s.1 t.1 ∧ s.2 = t.2) _ _ _ ⟨V12.one, rfl⟩ ?_).1
  rintro i ⟨f, k⟩ ⟨f', k'⟩ ⟨hf, rfl⟩
  simp only [Id.run]
  split
  · exact ⟨(hf.sq.mul (he k)).mul (he (k + 1)), rfl⟩
  · exact ⟨hf.sq.mul (he k), rfl⟩

/-- `miller`. -/
def miller (p : AF F) (q : G2F F) : E12 F := millerWith p q (lines q)

theorem miller_rel {p : AF F} {p' : JamCrypto.G1.Aff} {q : G2F F} {q' : JamCrypto.Pairing.G2}
    (hp : ARel p p') (hq : GRel q q') : V12 (miller p q) (JamCrypto.Pairing.miller p' q') :=
  millerWith_rel hp hq (lines_rel hq)

/-- `frobGamma`. -/
def frobGamma : E2 F := E2.pow ⟨Field.one, Field.one⟩ ((P - 1) / 6)

theorem frobGamma_rel : V2 (frobGamma : E2 F) JamCrypto.Pairing.frobGamma :=
  V2.pow ⟨V.one, V.one⟩ _

/-- `frobGammas`. -/
def frobGammas : Array (E2 F) := Id.run do
  let mut out := #[E2.one]
  for _ in [0:5] do out := out.push (out.back!.mul frobGamma)
  return out

theorem frobGammas_rel : ArrRel V2 (frobGammas : Array (E2 F)) JamCrypto.Pairing.frobGammas := by
  unfold frobGammas JamCrypto.Pairing.frobGammas
  simp only [Id.run, bind, pure]
  refine forIn_range_rel (ArrRel V2) _ _ _ ?_ ?_
  · refine ⟨rfl, fun i h1 h2 => ?_⟩
    have : i = 0 := by simpa using h1
    subst this
    exact V2.one
  intro i a b hab
  simp only [Id.run, Array.back!]
  exact arr_push hab (by rw [hab.1]; exact (hab.get! v2_default _).mul frobGamma_rel)

/-- `frob`. -/
def frob (f : E12 F) : E12 F :=
  let g := frobGammas
  let c (a : E2 F) (i : Nat) := a.conj.mul g[i]!
  ⟨⟨c f.d0.c0 0, c f.d0.c1 2, c f.d0.c2 4⟩, ⟨c f.d1.c0 1, c f.d1.c1 3, c f.d1.c2 5⟩⟩

theorem frob_rel {f : E12 F} {f' : JamCrypto.Pairing.Fq12} (h : V12 f f') :
    V12 (frob f) (JamCrypto.Pairing.frob f') := by
  have c : ∀ {a a'}, V2 a a' → ∀ i, V2 ((a : E2 F).conj.mul (frobGammas : Array (E2 F))[i]!)
      (a'.conj.mul JamCrypto.Pairing.frobGammas[i]!) :=
    fun ha i => ha.conj.mul (frobGammas_rel.get! v2_default i)
  exact ⟨⟨c h.1.1 0, c h.1.2.1 2, c h.1.2.2 4⟩, ⟨c h.2.1 1, c h.2.2.1 3, c h.2.2.2 5⟩⟩

/-- `powX`. -/
def powX (f : E12 F) : E12 F := (f.pow blsX).conj

theorem powX_rel {f : E12 F} {f' : JamCrypto.Pairing.Fq12} (h : V12 f f') :
    V12 (powX f) (JamCrypto.Pairing.powX f') := (h.pow _).conj

/-- `finalExp`, step for step. -/
def finalExp (f : E12 F) : E12 F :=
  let f1 := f.conj.mul f.inv
  let f2 := (frob (frob f1)).mul f1
  let t0 := (powX f2).mul f2.conj
  let t1 := (powX t0).mul t0.conj
  let t2 := (powX t1).mul (frob t1)
  let t3 := ((powX (powX t2)).mul (frob (frob t2))).mul t2.conj
  t3.mul (f2.sq.mul f2)

theorem finalExp_rel {f : E12 F} {f' : JamCrypto.Pairing.Fq12} (h : V12 f f') :
    V12 (finalExp f) (JamCrypto.Pairing.finalExp f') := by
  have f1 := h.conj.mul h.inv
  have f2 := (frob_rel (frob_rel f1)).mul f1
  have t0 := (powX_rel f2).mul f2.conj
  have t1 := (powX_rel t0).mul t0.conj
  have t2 := (powX_rel t1).mul (frob_rel t1)
  have t3 := ((powX_rel (powX_rel t2)).mul (frob_rel (frob_rel t2))).mul t2.conj
  exact t3.mul (f2.sq.mul f2)

/-- Two lists agree elementwise. -/
def ListRel {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: l, b :: l' => R a b ∧ ListRel R l l'
  | _, _ => False

/-- The product of the Miller loops of `pairingCheck`, each pair with its line coefficients. -/
def millerProd (pairs : List (AF F × G2F F × Array (E12 F × E12 F))) : E12 F :=
  pairs.foldl (fun acc (p, q, ls) => acc.mul (millerWith p q ls)) E12.one

/-- The pairs agree, and the line coefficients are those of the reference's `lines`. -/
def PRel (a : AF F × G2F F × Array (E12 F × E12 F)) (b : JamCrypto.G1.Aff × JamCrypto.Pairing.G2) : Prop :=
  ARel a.1 b.1 ∧ GRel a.2.1 b.2 ∧ ArrRel LRel a.2.2 (JamCrypto.Pairing.lines b.2)

theorem millerProd_rel {pairs : List (AF F × G2F F × Array (E12 F × E12 F))}
    {pairs' : List (JamCrypto.G1.Aff × JamCrypto.Pairing.G2)} (h : ListRel PRel pairs pairs') :
    V12 (finalExp (millerProd pairs))
      (JamCrypto.Pairing.finalExp (pairs'.foldl (fun acc (p, q) => acc.mul (JamCrypto.Pairing.miller p q))
        JamCrypto.Pairing.Fq12.one)) := by
  unfold millerProd
  refine finalExp_rel ?_
  suffices ∀ (a : E12 F) a', V12 a a' → V12 (pairs.foldl (fun acc (p, q, ls) => acc.mul (millerWith p q ls)) a)
      (pairs'.foldl (fun acc (p, q) => acc.mul (JamCrypto.Pairing.miller p q)) a') from this _ _ V12.one
  induction pairs generalizing pairs' with
  | nil => cases pairs' <;> simp_all [ListRel]
  | cons x xs ih =>
    cases pairs' with
    | nil => exact absurd h id
    | cons y ys =>
      intro a a' ha
      exact ih h.2 _ _ (ha.mul (millerWith_rel h.1.1 h.1.2.1 h.1.2.2))

end JamCrypto.Fast.PairingF
