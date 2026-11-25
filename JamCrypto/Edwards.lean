import JamCrypto.Modular

/-!
# Twisted Edwards curves a·x² + y² = 1 + d·x²·y² over 𝔽_p

Points in extended coordinates (X : Y : Z : T) with x = X/Z, y = Y/Z, x·y = T/Z (Hisil–Wong–Carter–
Dawson 2008). Addition uses the unified formula `add-2008-hwcd`, which is the group law wherever its
denominators 1 ± d·x₁x₂y₁y₂ do not vanish. For Ed25519 (a square, d non-square) it is complete. For
Bandersnatch (a and d both non-squares) it is exceptional only when a sum or difference of the
operands is a point at infinity, which needs operands outside the prime-order subgroup; such a step
yields Z = 0, every later step keeps the all-zero `invalid` point, and `valid` reports it, so the
callers reject instead of computing with a wrong point.
-/

namespace JamCrypto

open JamCrypto.Modular

/-- A twisted Edwards curve over 𝔽_p. -/
structure Curve where
  p : Nat
  a : Nat
  d : Nat

/-- A point in extended coordinates. -/
structure Point where
  X : Nat
  Y : Nat
  Z : Nat
  T : Nat
deriving Inhabited

namespace Curve

variable (E : Curve)

/-- The neutral element (0, 1). -/
def zero : Point := ⟨0, 1, 1, 0⟩

/-- The result of an exceptional addition. -/
def invalid : Point := ⟨0, 0, 0, 0⟩

/-- The affine point (x, y). -/
def ofAffine (x y : Nat) : Point := ⟨x % E.p, y % E.p, 1, x * y % E.p⟩

/-- Not the result of an exceptional addition. -/
def valid (P : Point) : Bool := P.Z % E.p != 0

/-- (x, y) is on the curve. -/
def onCurve (x y : Nat) : Bool :=
  let p := E.p
  let x2 := x * x % p
  let y2 := y * y % p
  (E.a * x2 + y2) % p == (1 + E.d * x2 % p * y2) % p

/-- P + Q (`add-2008-hwcd`). -/
def add (P Q : Point) : Point :=
  let p := E.p
  let A := P.X * Q.X % p
  let B := P.Y * Q.Y % p
  let C := E.d * (P.T * Q.T % p) % p
  let D := P.Z * Q.Z % p
  let Ee := subMod ((P.X + P.Y) * (Q.X + Q.Y) % p) ((A + B) % p) p
  let F := subMod D C p
  let G := (D + C) % p
  let H := subMod B (E.a * A % p) p
  let Z3 := F * G % p
  if Z3 == 0 then invalid else ⟨Ee * F % p, G * H % p, Z3, Ee * H % p⟩

/-- −P. -/
def neg (P : Point) : Point := ⟨subMod 0 P.X E.p, P.Y, P.Z, subMod 0 P.T E.p⟩

/-- P − Q. -/
def sub (P Q : Point) : Point := E.add P (E.neg Q)

/-- [k]P, by double-and-add from the most significant bit of k. -/
def smul (k : Nat) (P : Point) : Point := Id.run do
  let mut R := zero
  let n := k.log2 + 1
  for j in [0:n] do
    R := E.add R R
    if k.testBit (n - 1 - j) then R := E.add R P
  return R

/-- P = Q, for valid points. -/
def eq (P Q : Point) : Bool :=
  let p := E.p
  E.valid P && E.valid Q &&
    P.X * Q.Z % p == Q.X * P.Z % p && P.Y * Q.Z % p == Q.Y * P.Z % p

/-- P is the neutral element. -/
def isZero (P : Point) : Bool := E.eq P zero

/-- The affine coordinates (x, y) of a valid point. -/
def toAffine (P : Point) : Nat × Nat :=
  let zi := invMod P.Z E.p
  (P.X * zi % E.p, P.Y * zi % E.p)

end Curve

end JamCrypto
