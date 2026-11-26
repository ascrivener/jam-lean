import JamCrypto.Fast.Fp25519
import JamCrypto.Ed25519

/-!
# Ed25519 verification on fixed-limb field arithmetic

The same function as `JamCrypto.Ed25519.verifyWith` (the reference implementation, which stays as
it is), computed over `Fast.Fp25519` instead of `Nat`, with a joint (Straus) scalar
multiplication.

**Status: tested, not proved.** `FastTest` compares it with the reference on every published
vector and on randomized valid, mutated and garbage inputs, under all three `Rules`.

Why the results agree, in outline: edwards25519's `add-2008-hwcd` formula is complete (a = −1 a
square, d a non-square), so every point either implementation computes is given by the group law,
whatever the order of the additions; decoding follows the reference step for step (square roots
are normalised by parity), and results are compared only through `eq` and `isZero`.
-/

namespace JamCrypto.Fast.Ed25519

open JamCrypto.Fast
open JamCrypto.Modular (leToNat)

abbrev F := Fp25519.Elem

/-- A point in extended coordinates. -/
structure Pt where
  X : F
  Y : F
  Z : F
  T : F
deriving Inhabited

def zero : Pt := ⟨Fp25519.zero, Fp25519.one, Fp25519.one, Fp25519.zero⟩
def invalid : Pt := ⟨Fp25519.zero, Fp25519.zero, Fp25519.zero, Fp25519.zero⟩

def dC : F := Fp25519.ofNat JamCrypto.Ed25519.d
def sqrtM1 : F := Fp25519.ofNat JamCrypto.Ed25519.sqrtM1

@[inline] def valid (P : Pt) : Bool := !P.Z.isZero

def ofAffine (x y : F) : Pt := ⟨x, y, Fp25519.one, x * y⟩

/-- P + Q (`add-2008-hwcd` with a = −1, as `Curve.add`). -/
def add (P Q : Pt) : Pt :=
  let A := P.X * Q.X
  let B := P.Y * Q.Y
  let C := dC * (P.T * Q.T)
  let D := P.Z * Q.Z
  let E := (P.X + P.Y) * (Q.X + Q.Y) - (A + B)
  let F := D - C
  let G := D + C
  let H := B + A
  let Z3 := F * G
  if Z3.isZero then invalid else ⟨E * F, G * H, Z3, E * H⟩

/-- 2P (`dbl-2008-hwcd` with a = −1). -/
def dbl (P : Pt) : Pt :=
  let A := P.X.sq
  let B := P.Y.sq
  let C := Fp25519.dbl P.Z.sq
  let D := Fp25519.neg A
  let E := (P.X + P.Y).sq - A - B
  let G := D + B
  let F := G - C
  let H := D - B
  let Z3 := F * G
  if Z3.isZero then invalid else ⟨E * F, G * H, Z3, E * H⟩

def neg (P : Pt) : Pt := ⟨Fp25519.neg P.X, P.Y, P.Z, Fp25519.neg P.T⟩

def eq (P Q : Pt) : Bool :=
  valid P && valid Q && P.X * Q.Z == Q.X * P.Z && P.Y * Q.Z == Q.Y * P.Z

def isZero (P : Pt) : Bool := eq P zero

/-- The 4-bit digits of k mod 2^256, least significant first. -/
def nibbles (k : Nat) : Array UInt8 := Id.run do
  let mut out : Array UInt8 := Array.mkEmpty 64
  for w in [0:4] do
    let v := (k >>> (64 * w)).toUInt64
    for i in [0:16] do
      out := out.push ((v >>> (4 * i).toUInt64) &&& 15).toUInt8
  return out

def table (P : Pt) : Array Pt := Id.run do
  let mut t : Array Pt := Array.mkEmpty 16
  t := t.push zero
  t := t.push P
  for i in [2:16] do
    t := t.push (if i % 2 == 0 then dbl t[i / 2]! else add t[i - 1]! P)
  return t

def topDigit (ds : Array UInt8) : Nat := Id.run do
  let mut n := 0
  for i in [0:ds.size] do
    if ds[i]! != 0 then n := i + 1
  return n

/-- [k₁]P₁ + [k₂]P₂ for k₁, k₂ < 2^256 (Straus, 4-bit windows). -/
def smul2 (k1 : Nat) (P1 : Pt) (k2 : Nat) (P2 : Pt) : Pt := Id.run do
  let d1 := nibbles k1
  let d2 := nibbles k2
  let t1 := table P1
  let t2 := table P2
  let n := max (topDigit d1) (topDigit d2)
  let mut acc := zero
  for j in [0:n] do
    let i := n - 1 - j
    acc := dbl (dbl (dbl (dbl acc)))
    let a := d1[i]!
    if a != 0 then acc := add acc t1[a.toNat]!
    let b := d2[i]!
    if b != 0 then acc := add acc t2[b.toNat]!
  return acc

/-- (p − 5)/8. -/
def expBits : Array Bool := Fp25519.bitsMsb ((JamCrypto.Ed25519.p - 5) / 8)

/-- Decode a 32-octet point encoding (as `Ed25519.decode`). -/
def decode (rules : JamCrypto.Ed25519.Rules) (bs : List UInt8) : Option Pt := do
  guard (bs.length == 32)
  let n := leToNat bs
  let sign := n / 2 ^ 255
  let yy := n % 2 ^ 255
  if rules.canonicalPoints && yy ≥ JamCrypto.Ed25519.p then none
  let y := Fp25519.ofNat yy
  let y2 := y.sq
  let u := y2 - Fp25519.one
  let v := dC * y2 + Fp25519.one
  -- w = u/v and x0 = w^((p+3)/8) = u·v³·(u·v⁷)^((p−5)/8) (RFC 8032 §5.1.3; v ≠ 0 since −1/d is
  -- not a square), without the inversion
  let v3 := v.sq * v
  let x0 := u * v3 * Fp25519.powBits (u * v3 * v3 * v) expBits
  -- x0² = w ⟺ v·x0² = u, and x0² = −w ⟺ v·x0² = −u
  let vx2 := v * x0.sq
  let x ← if vx2 == u then some x0
    else if vx2 == Fp25519.neg u then some (x0 * sqrtM1)
    else none
  if x.isZero && sign == 1 && rules.canonicalPoints then none
  let x := if (if Fp25519.isOdd x then 1 else 0) != sign then Fp25519.neg x else x
  return ofAffine x y

/-- The base point. -/
def B : Pt := ⟨Fp25519.ofNat JamCrypto.Ed25519.B.X, Fp25519.ofNat JamCrypto.Ed25519.B.Y,
  Fp25519.ofNat JamCrypto.Ed25519.B.Z, Fp25519.ofNat JamCrypto.Ed25519.B.T⟩

/-- `Ed25519.verifyWith rules` with a decoded key (`decode rules key = some A`). -/
def verifyDecoded (rules : JamCrypto.Ed25519.Rules) (A : Pt) (key msg sig : List UInt8) : Bool := Id.run do
  if key.length != 32 || sig.length != 64 then return false
  let Rb := sig.take 32
  let S := leToNat (sig.drop 32)
  if S ≥ JamCrypto.Ed25519.L then return false
  let some R := decode rules Rb | return false
  let k := leToNat (JAM.Sha512.hash (Rb ++ key ++ msg)) % JamCrypto.Ed25519.L
  -- [S]B − [k]A, then − R
  let P := smul2 S B k (neg A)
  if rules.cofactored then
    return isZero (dbl (dbl (dbl (add P (neg R)))))
  else
    return eq P R

/-- The same function as `Ed25519.verifyWith rules`. -/
def verifyWith (rules : JamCrypto.Ed25519.Rules) (key msg sig : List UInt8) : Bool := Id.run do
  if key.length != 32 || sig.length != 64 then return false
  let S := leToNat (sig.drop 32)
  if S ≥ JamCrypto.Ed25519.L then return false
  let some A := decode rules key | return false
  return verifyDecoded rules A key msg sig

/-- The same function as `Ed25519.verify` (ZIP 215). -/
def verify (key msg sig : List UInt8) : Bool := verifyWith JamCrypto.Ed25519.zip215 key msg sig

end JamCrypto.Fast.Ed25519
