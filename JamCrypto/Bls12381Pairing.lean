import JamCrypto.Bls12381G1

/-!
# The BLS12-381 pairing

The tower 𝔽_q2 = 𝔽_q[u]/(u² + 1), 𝔽_q6 = 𝔽_q2[v]/(v³ − ξ) with ξ = 1 + u, 𝔽_q12 = 𝔽_q6[w]/(w² − v),
and the optimal ate pairing e : G1 × G2 → 𝔽_q12 with the BLS parameter x = −0xd201000000010000.

G2 is the twist E' : y² = x³ + 4ξ over 𝔽_q2; (x, y) ∈ E' maps into E(𝔽_q12) as (x/w², y/w³)
(w⁶ = ξ). The Miller loop runs on E' and evaluates each line, untwisted, at the G1 point. The
final exponentiation raises to (q¹² − 1)/r as (q⁶ − 1)·(q² + 1)·((q⁴ − q² + 1)/r).

Only what KZG verification needs is here: `pairingCheck` decides Π e(Pᵢ, Qᵢ) = 1.
-/

namespace JamCrypto.Pairing

open JamCrypto

/-! ## 𝔽_q2 -/

structure Fq2 where
  a : Nat
  b : Nat
  deriving Inhabited, BEq, Repr

namespace Fq2
def zero : Fq2 := ⟨0, 0⟩
def one : Fq2 := ⟨1, 0⟩
@[inline] def add (x y : Fq2) : Fq2 := ⟨Fq.add x.a y.a, Fq.add x.b y.b⟩
@[inline] def sub (x y : Fq2) : Fq2 := ⟨Fq.sub x.a y.a, Fq.sub x.b y.b⟩
@[inline] def neg (x : Fq2) : Fq2 := ⟨Fq.neg x.a, Fq.neg x.b⟩
@[inline] def mul (x y : Fq2) : Fq2 :=
  let t0 := Fq.mul x.a y.a
  let t1 := Fq.mul x.b y.b
  ⟨Fq.sub t0 t1, Fq.sub (Fq.sub (Fq.mul (Fq.add x.a x.b) (Fq.add y.a y.b)) t0) t1⟩
@[inline] def sq (x : Fq2) : Fq2 :=
  ⟨Fq.mul (Fq.add x.a x.b) (Fq.sub x.a x.b), Fq.mul (Fq.add x.a x.a) x.b⟩
@[inline] def scale (x : Fq2) (k : Nat) : Fq2 := ⟨Fq.mul x.a k, Fq.mul x.b k⟩
/-- Multiplication by ξ = 1 + u. -/
@[inline] def mulXi (x : Fq2) : Fq2 := ⟨Fq.sub x.a x.b, Fq.add x.a x.b⟩
def inv (x : Fq2) : Fq2 :=
  let d := Fq.inv (Fq.add (Fq.sq x.a) (Fq.sq x.b))
  ⟨Fq.mul x.a d, Fq.neg (Fq.mul x.b d)⟩
def isZero (x : Fq2) : Bool := x.a == 0 && x.b == 0
/-- The Frobenius x ↦ x^q (conjugation). -/
def conj (x : Fq2) : Fq2 := ⟨x.a, Fq.neg x.b⟩
def pow (x : Fq2) (e : Nat) : Fq2 := Id.run do
  let mut acc := one
  let n := e.log2 + 1
  for i in [0:n] do
    acc := sq acc
    if (e >>> (n - 1 - i)) % 2 == 1 then acc := mul acc x
  return acc
end Fq2

/-! ## 𝔽_q6 -/

structure Fq6 where
  c0 : Fq2
  c1 : Fq2
  c2 : Fq2
  deriving Inhabited, BEq, Repr

namespace Fq6
def zero : Fq6 := ⟨Fq2.zero, Fq2.zero, Fq2.zero⟩
def one : Fq6 := ⟨Fq2.one, Fq2.zero, Fq2.zero⟩
@[inline] def add (x y : Fq6) : Fq6 := ⟨x.c0.add y.c0, x.c1.add y.c1, x.c2.add y.c2⟩
@[inline] def sub (x y : Fq6) : Fq6 := ⟨x.c0.sub y.c0, x.c1.sub y.c1, x.c2.sub y.c2⟩
@[inline] def neg (x : Fq6) : Fq6 := ⟨x.c0.neg, x.c1.neg, x.c2.neg⟩
def mul (x y : Fq6) : Fq6 :=
  let t0 := x.c0.mul y.c0
  let t1 := x.c1.mul y.c1
  let t2 := x.c2.mul y.c2
  -- Karatsuba
  let c0 := t0.add (((x.c1.add x.c2).mul (y.c1.add y.c2)).sub (t1.add t2)).mulXi
  let c1 := (((x.c0.add x.c1).mul (y.c0.add y.c1)).sub (t0.add t1)).add t2.mulXi
  let c2 := (((x.c0.add x.c2).mul (y.c0.add y.c2)).sub (t0.add t2)).add t1
  ⟨c0, c1, c2⟩
/-- Multiplication by v. -/
@[inline] def mulV (x : Fq6) : Fq6 := ⟨x.c2.mulXi, x.c0, x.c1⟩
@[inline] def scale (x : Fq6) (k : Nat) : Fq6 := ⟨x.c0.scale k, x.c1.scale k, x.c2.scale k⟩
def inv (x : Fq6) : Fq6 :=
  let t0 := x.c0.sq.sub (x.c1.mul x.c2).mulXi
  let t1 := x.c2.sq.mulXi.sub (x.c0.mul x.c1)
  let t2 := x.c1.sq.sub (x.c0.mul x.c2)
  let d := (x.c0.mul t0).add ((x.c2.mul t1).add (x.c1.mul t2)).mulXi
  let di := d.inv
  ⟨t0.mul di, t1.mul di, t2.mul di⟩
end Fq6

/-! ## 𝔽_q12 -/

structure Fq12 where
  d0 : Fq6
  d1 : Fq6
  deriving Inhabited, BEq, Repr

namespace Fq12
def one : Fq12 := ⟨Fq6.one, Fq6.zero⟩
def ofFq2 (x : Fq2) : Fq12 := ⟨⟨x, Fq2.zero, Fq2.zero⟩, Fq6.zero⟩
@[inline] def add (x y : Fq12) : Fq12 := ⟨x.d0.add y.d0, x.d1.add y.d1⟩
def mul (x y : Fq12) : Fq12 :=
  let t0 := x.d0.mul y.d0
  let t1 := x.d1.mul y.d1
  ⟨t0.add t1.mulV, ((x.d0.add x.d1).mul (y.d0.add y.d1)).sub (t0.add t1)⟩
def sq (x : Fq12) : Fq12 := mul x x
@[inline] def scale (x : Fq12) (k : Nat) : Fq12 := ⟨x.d0.scale k, x.d1.scale k⟩
def conj (x : Fq12) : Fq12 := ⟨x.d0, x.d1.neg⟩
def inv (x : Fq12) : Fq12 :=
  let d := (x.d0.mul x.d0).sub (x.d1.mul x.d1).mulV
  let di := d.inv
  ⟨x.d0.mul di, (x.d1.mul di).neg⟩
/-- x^e by square-and-multiply. -/
def pow (x : Fq12) (e : Nat) : Fq12 := Id.run do
  let mut acc := one
  let n := e.log2 + 1
  for i in [0:n] do
    acc := sq acc
    if (e >>> (n - 1 - i)) % 2 == 1 then acc := mul acc x
  return acc
end Fq12

/-! ## The pairing -/

/-- |x| for the BLS parameter x = −0xd201000000010000. -/
def blsX : Nat := 0xd201000000010000

/-- The prime-order subgroup's order r (= 𝔽_r's modulus). -/
def r : Nat := Fr.R

def w : Fq12 := ⟨Fq6.zero, Fq6.one⟩
def wInv : Fq12 := w.inv
def wInv3 : Fq12 := wInv.mul (wInv.mul wInv)

/-- A G2 point (affine, on the twist). -/
structure G2 where
  x : Fq2
  y : Fq2
  inf : Bool := false
  deriving Inhabited, BEq, Repr

/-- The uncompressed zcash encoding of a G2 point (192 octets: x.c1, x.c0, y.c1, y.c0). The
    point is checked to be on the twist, not to be in G2. -/
def G2.decode (bs : ByteArray) : Option G2 := Id.run do
  if bs.size != 192 then return none
  let b0 := bs.get! 0
  if b0 &&& 0x80 != 0 then return none
  let num (off : Nat) (mask : Bool) : Nat := Id.run do
    let mut v := 0
    for i in [0:48] do
      let b := bs.get! (off + i)
      v := v * 256 + (if mask && i == 0 then (b &&& 0x1f) else b).toNat
    return v
  let x1 := num 0 true
  let x0 := num 48 false
  let y1 := num 96 false
  let y0 := num 144 false
  if b0 &&& 0x40 != 0 then
    return if x0 == 0 && x1 == 0 && y0 == 0 && y1 == 0 then some ⟨Fq2.zero, Fq2.zero, true⟩ else none
  if x0 ≥ Fq.P || x1 ≥ Fq.P || y0 ≥ Fq.P || y1 ≥ Fq.P then return none
  let x : Fq2 := ⟨x0, x1⟩
  let y : Fq2 := ⟨y0, y1⟩
  let b' : Fq2 := Fq2.mulXi ⟨4, 0⟩
  return if y.sq == (x.sq.mul x).add b' then some ⟨x, y, false⟩ else none

/-- The line coefficients (A, B) of each Miller step, for a fixed Q: the line at P = (xP, yP) is
    yP + A·xP + B. Steps: for each bit of |x| below the top one, a doubling, then an addition
    when the bit is set. -/
def lines (q : G2) : Array (Fq12 × Fq12) := Id.run do
  let mut out : Array (Fq12 × Fq12) := #[]
  let mut tx := q.x
  let mut ty := q.y
  let n := blsX.log2
  let coeffs (lam xt yt : Fq2) : Fq12 × Fq12 :=
    ((Fq12.ofFq2 lam.neg).mul wInv, (Fq12.ofFq2 ((lam.mul xt).sub yt)).mul wInv3)
  for i in [0:n] do
    -- doubling
    let lam := (tx.sq.scale 3).mul (ty.add ty).inv
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

/-- The Miller loop f_{|x|,Q}(P), conjugated for the negative x. -/
def miller (p : G1.Aff) (q : G2) : Fq12 := Id.run do
  if p.inf || q.inf then return Fq12.one
  let ls := lines q
  let evalLine (k : Nat) : Fq12 :=
    let (a, b) := ls[k]!
    let l := b.add (a.scale p.x)
    { l with d0 := { l.d0 with c0 := l.d0.c0.add ⟨p.y, 0⟩ } }
  let mut f := Fq12.one
  let mut k := 0
  let n := blsX.log2
  for i in [0:n] do
    f := f.sq.mul (evalLine k)
    k := k + 1
    if (blsX >>> (n - 1 - i)) % 2 == 1 then
      f := f.mul (evalLine k)
      k := k + 1
  return f.conj

/-- γ = ξ^((q − 1)/6): w^q = γ·w. -/
def frobGamma : Fq2 := Fq2.pow ⟨1, 1⟩ ((Fq.P - 1) / 6)
/-- γ⁰ … γ⁵. -/
def frobGammas : Array Fq2 := Id.run do
  let mut out := #[Fq2.one]
  for _ in [0:5] do out := out.push (out.back!.mul frobGamma)
  return out

/-- The Frobenius f ↦ f^q: with f = Σᵢ aᵢwⁱ (aᵢ ∈ 𝔽_q2, i < 6), f^q = Σᵢ conj(aᵢ)·γⁱ·wⁱ. -/
def frob (f : Fq12) : Fq12 :=
  let g := frobGammas
  let c (a : Fq2) (i : Nat) := a.conj.mul g[i]!
  -- w^(2j) carries d0.cj, w^(2j+1) carries d1.cj
  ⟨⟨c f.d0.c0 0, c f.d0.c1 2, c f.d0.c2 4⟩, ⟨c f.d1.c0 1, c f.d1.c1 3, c f.d1.c2 5⟩⟩

/-- f^x for the (negative) BLS parameter, f in the cyclotomic subgroup (inverse = conjugate). -/
def powX (f : Fq12) : Fq12 := (f.pow blsX).conj

/-- f^((q¹² − 1)/r)³: the easy part (q⁶ − 1)(q² + 1), then 3·(q⁴ − q² + 1)/r
    = (x − 1)²·(x + q)·(x² + q² − 1) + 3 (the BLS12 decomposition). The cube is harmless:
    3 is prime to r, so the result is 1 exactly when f^((q¹² − 1)/r) is. -/
def finalExp (f : Fq12) : Fq12 :=
  let f1 := f.conj.mul f.inv
  let f2 := (frob (frob f1)).mul f1
  let t0 := (powX f2).mul f2.conj            -- f2^(x−1)
  let t1 := (powX t0).mul t0.conj            -- f2^((x−1)²)
  let t2 := (powX t1).mul (frob t1)          -- ·^(x+q)
  let t3 := ((powX (powX t2)).mul (frob (frob t2))).mul t2.conj  -- ·^(x²+q²−1)
  t3.mul (f2.sq.mul f2)

/-- The plain final exponentiation f^((q¹² − 1)/r), for tests. -/
def finalExpSlow (f : Fq12) : Fq12 :=
  let f1 := f.conj.mul f.inv
  let f2 := (f1.pow (Fq.P ^ 2)).mul f1
  f2.pow ((Fq.P ^ 4 - Fq.P ^ 2 + 1) / r)

/-- Π e(Pᵢ, Qᵢ) = 1. -/
def pairingCheck (pairs : List (G1.Aff × G2)) : Bool :=
  finalExp (pairs.foldl (fun acc (p, q) => acc.mul (miller p q)) Fq12.one) == Fq12.one

/-- e(P, Q)³ (see `finalExp`), for tests. -/
def pairing (p : G1.Aff) (q : G2) : Fq12 := finalExp (miller p q)

end JamCrypto.Pairing
