import JamCrypto.Fast.Fr
import JamCrypto.Bandersnatch
import JamCrypto.ThinVrf

/-!
# Bandersnatch on fixed-limb field arithmetic: fast IETF and Thin VRF verification

The same functions as `JamCrypto.Bandersnatch.ietfVerify`, `Bandersnatch.vrfOutput`,
`Bandersnatch.Thin.verify` and `Bandersnatch.Thin.vrfOutput` (the reference implementations,
which stay as they are), computed over `Fast.Fr` (𝔽_q on 32-bit limbs) instead of `Nat`, with
windowed and joint (Straus) scalar multiplication.

**Status: tested, not proved.** `FastTest` compares each function here with its reference on
every published vector and on randomized valid, mutated and garbage inputs.

Why the results agree, in outline:
* `add` is the reference's `add-2008-hwcd` formula, step for step, over the same field values, and
  `dbl` the dedicated doubling `dbl-2008-hwcd`, whose Z₃ is −1 times the unified formula's on the
  same point, so both are exceptional (Z₃ = 0, giving the absorbing `invalid` point) exactly when
  the reference is.
* On the prime-order subgroup the formula is never exceptional (Edwards.lean), so there every
  computation is the group law and any order of additions gives the same point, up to the
  projective representative; results are compared only through `eq` and affine encodings.
* Points outside the subgroup occur only in the subgroup check and in hash to curve. The subgroup
  check decides membership whatever the order of additions: a subgroup point never meets an
  exceptional step and [r − 1]P = −P; a point outside either meets one (and is rejected, as by
  the reference) or is computed by the group law, where [r − 1]P ≠ −P. Hash to curve uses the
  reference's operation sequence (one addition, then two doublings, which [4]· by double-and-add
  also is, up to adding to the neutral element).
* Square roots are normalised by every caller (sign or parity), so which root is found does not
  matter.
-/

namespace JamCrypto.Fast.Bandersnatch

open JamCrypto.Fast
open JamCrypto.Modular (leToNat beToNat natToLE slice)

abbrev F := Fr.Elem

/-- A point in extended coordinates over `Fast.Fr`. -/
structure Pt where
  X : F
  Y : F
  Z : F
  T : F
deriving Inhabited

/-- The neutral element. -/
def zero : Pt := ⟨Fr.zero, Fr.one, Fr.one, Fr.zero⟩

/-- The result of an exceptional step (as `Curve.invalid`). -/
def invalid : Pt := ⟨Fr.zero, Fr.zero, Fr.zero, Fr.zero⟩

/-- d. -/
def dC : F := Fr.ofNat JamCrypto.Bandersnatch.curve.d

/-- a·x for a = −5. -/
@[inline] def mulA (x : F) : F := Fr.neg (Fr.add (Fr.dbl (Fr.dbl x)) x)

/-- Not the result of an exceptional step. -/
@[inline] def valid (P : Pt) : Bool := !P.Z.isZero

/-- The affine point (x, y). -/
def ofAffine (x y : F) : Pt := ⟨x, y, Fr.one, x * y⟩

/-- A reference point. -/
def ofPoint (P : JamCrypto.Point) : Pt :=
  ⟨Fr.ofNat P.X, Fr.ofNat P.Y, Fr.ofNat P.Z, Fr.ofNat P.T⟩

/-- P + Q (`add-2008-hwcd`, as `Curve.add`). -/
def add (P Q : Pt) : Pt :=
  let A := P.X * Q.X
  let B := P.Y * Q.Y
  let C := dC * (P.T * Q.T)
  let D := P.Z * Q.Z
  let E := (P.X + P.Y) * (Q.X + Q.Y) - (A + B)
  let F := D - C
  let G := D + C
  let H := B - mulA A
  let Z3 := F * G
  if Z3.isZero then invalid else ⟨E * F, G * H, Z3, E * H⟩

/-- 2P (`dbl-2008-hwcd`). -/
def dbl (P : Pt) : Pt :=
  let A := P.X.sq
  let B := P.Y.sq
  let C := Fr.dbl P.Z.sq
  let D := mulA A
  let E := (P.X + P.Y).sq - A - B
  let G := D + B
  let F := G - C
  let H := D - B
  let Z3 := F * G
  if Z3.isZero then invalid else ⟨E * F, G * H, Z3, E * H⟩

/-- −P. -/
def neg (P : Pt) : Pt := ⟨Fr.neg P.X, P.Y, P.Z, Fr.neg P.T⟩

/-- P = Q, for valid points (as `Curve.eq`). -/
def eq (P Q : Pt) : Bool :=
  valid P && valid Q && P.X * Q.Z == Q.X * P.Z && P.Y * Q.Z == Q.Y * P.Z

/-- P is the neutral element. -/
def isZero (P : Pt) : Bool := eq P zero

/-- The 4-bit digits of k mod 2^256, least significant first. -/
def nibbles (k : Nat) : Array UInt8 := Id.run do
  let mut out : Array UInt8 := Array.mkEmpty 64
  for w in [0:4] do
    let v := (k >>> (64 * w)).toUInt64
    for i in [0:16] do
      out := out.push ((v >>> (4 * i).toUInt64) &&& 15).toUInt8
  return out

/-- 0, P, 2P, …, 15P. -/
def table (P : Pt) : Array Pt := Id.run do
  let mut t : Array Pt := Array.mkEmpty 16
  t := t.push zero
  t := t.push P
  for i in [2:16] do
    t := t.push (if i % 2 == 0 then dbl t[i / 2]! else add t[i - 1]! P)
  return t

/-- The index of the most significant nonzero digit, plus one. -/
def topDigit (ds : Array UInt8) : Nat := Id.run do
  let mut n := 0
  for i in [0:ds.size] do
    if ds[i]! != 0 then n := i + 1
  return n

/-- [k]P for k < 2^256 (fixed 4-bit window). -/
def smul (k : Nat) (P : Pt) : Pt := Id.run do
  let ds := nibbles k
  let tbl := table P
  let n := topDigit ds
  let mut acc := zero
  for j in [0:n] do
    let d := ds[n - 1 - j]!
    acc := dbl (dbl (dbl (dbl acc)))
    if d != 0 then acc := add acc tbl[d.toNat]!
  return acc

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

/-- The affine coordinates of a valid point, as values. -/
def toAffine (P : Pt) : Nat × Nat :=
  if P.Z == Fr.one then (P.X.toNat, P.Y.toNat) else
  let zi := P.Z.inv
  ((P.X * zi).toNat, (P.Y * zi).toNat)

/-- The 32-octet encoding of a valid point (as `Bandersnatch.encode`). -/
def encode (P : Pt) : List UInt8 :=
  let (x, y) := toAffine P
  natToLE 32 (y + (if x > (Bandersnatch.q - 1) / 2 then 2 ^ 255 else 0))

/-! ## Square roots -/

/-- q − 1 = 2^32·t. -/
def tOdd : Nat := 12208678567578594777604504606729831043093128246378069236549469339647

def tMinus1Half : Array Bool := Fr.bitsMsb ((tOdd - 1) / 2)

/-- 7^t, a primitive 2^32-th root of unity. -/
def rootOfUnity : F := Fr.pow (Fr.ofNat 7) tOdd

/-- A square root of a, if a is a square (Tonelli–Shanks, 2-adicity 32). -/
def sqrt (a : F) : Option F := Id.run do
  if a.isZero then return some Fr.zero
  let w := Fr.powBits a tMinus1Half
  let mut x := a * w
  let mut t := x * w
  let mut m := 32
  let mut c := rootOfUnity
  for _ in [0:33] do
    if t != Fr.one then
      let mut i := 0
      let mut tt := t
      for _ in [0:m] do
        if tt != Fr.one then
          tt := tt.sq
          i := i + 1
      if i < m then
        let mut b := c
        for _ in [0:m - i - 1] do
          b := b.sq
        m := i
        c := b.sq
        t := t * c
        x := x * b
  return if x.sq == a then some x else none

/-! ## Decoding -/

/-- The point a 32-octet encoding stands for, on the curve (as `Bandersnatch.decodeOnCurve`). -/
def decodeOnCurve (bs : List UInt8) : Option Pt := do
  guard (bs.length == 32)
  let n := leToNat bs
  let negative := n / 2 ^ 255 == 1
  let yn := n % 2 ^ 255
  guard (yn < Bandersnatch.q)
  let y := Fr.ofNat yn
  let y2 := y.sq
  let den := mulA Fr.one - dC * y2
  guard (!den.isZero)
  let x ← sqrt ((Fr.one - y2) * den.inv)
  let xn := x.toNat
  let mn := (Fr.neg x).toNat
  let small := min xn mn
  let large := max xn mn
  return ofAffine (Fr.ofNat (if negative then large else small)) y

/-- In the prime-order subgroup (as `Bandersnatch.inSubgroup`): [r − 1]P = −P. -/
def inSubgroup (P : Pt) : Bool := eq (smul (Bandersnatch.r - 1) P) (neg P)

/-- string_to_point (as `Bandersnatch.decode`). -/
def decode (bs : List UInt8) : Option Pt := do
  let P ← decodeOnCurve bs
  guard (inSubgroup P)
  return P

/-! ## Hash to curve -/

def montB : F := Fr.ofNat JamCrypto.Bandersnatch.montB
def montAoverB : F := Fr.ofNat JamCrypto.Bandersnatch.montAoverB
def oneOverB2 : F := Fr.ofNat JamCrypto.Bandersnatch.oneOverB2
def five : F := Fr.ofNat 5

/-- The arkworks 0.5 Elligator 2 map (as `Bandersnatch.elligator2`). -/
def elligator2 (u : F) : Option Pt := do
  let k := montB
  let j := montAoverB
  let den1 := Fr.one + five * u.sq
  let x1 := Fr.neg (j * (if den1.isZero then Fr.one else den1).inv)
  let g := fun (x : F) => x.sq * x + j * x.sq + x * oneOverB2
  let gx1 := g x1
  let x2 := Fr.neg x1 - j
  -- the reference takes x1 iff g(x1) is a nonzero square, then a root of g(x); here the root of
  -- g(x1), when there is one, decides
  let r1 := if gx1.isZero then none else sqrt gx1
  let (x, odd, y0) ← match r1 with
    | some y1 => some (x1, true, y1)
    | none => (sqrt (g x2)).map fun y2 => (x2, false, y2)
  let y := if Fr.isOdd y0 != odd then Fr.neg y0 else y0
  let s := x * k
  let t := y * k
  let tv1 := s + Fr.one
  let tv2 := tv1 * t
  if tv2.isZero then return ofAffine Fr.zero Fr.one
  let inv := tv2.inv
  return ofAffine (inv * tv1 * s) (inv * t * (s - Fr.one))

/-- hash_to_curve from the 96 expanded octets (as `Bandersnatch.hashToCurve` and
    `Bandersnatch.Thin.hashToCurve` after `expandMessage`). -/
def hashToCurveOf (u : List UInt8) : Option Pt := do
  let P0 ← elligator2 (Fr.ofNat (beToNat (u.take 48) % Bandersnatch.q))
  let P1 ← elligator2 (Fr.ofNat (beToNat (u.drop 48) % Bandersnatch.q))
  let P := dbl (dbl (add P0 P1))
  guard (valid P)
  return P

/-! ## IETF VRF (GP v0.8.0) -/

/-- The generator. -/
def G : Pt := ofPoint JamCrypto.Bandersnatch.G

/-- The challenge (as `Bandersnatch.challenge`), from encoded points. -/
def ietfChallenge (encs : List (List UInt8)) (ad : List UInt8) : Nat :=
  let h := JAM.Sha512.hash (Bandersnatch.suiteString ++ [2] ++ encs.flatten ++ ad ++ [0])
  beToNat (h.take 32) % Bandersnatch.r

/-- `Bandersnatch.ietfVerify` with a decoded key (`decode key = some Y`). -/
def ietfVerifyWith (Y : Pt) (encY ctx msg sig : List UInt8) : Bool := Id.run do
  if sig.length != 96 then return false
  let s := leToNat (slice sig 64 32)
  if s ≥ Bandersnatch.r then return false
  let c := leToNat (slice sig 32 32) % Bandersnatch.r
  let some O := decode (sig.take 32) | return false
  let some I := hashToCurveOf (Bandersnatch.expandMessage ctx) | return false
  -- U = sG − cY, V = sI − cO
  let U := smul2 s G c (neg Y)
  let V := smul2 s I c (neg O)
  if !(valid U && valid V) then return false
  return ietfChallenge [encY, encode I, encode O, encode U, encode V] msg == c

/-- The same function as `Bandersnatch.ietfVerify`. -/
def ietfVerify (key ctx msg sig : List UInt8) : Bool := Id.run do
  if key.length != 32 || sig.length != 96 then return false
  let s := leToNat (slice sig 64 32)
  if s ≥ Bandersnatch.r then return false
  let some Y := decode key | return false
  return ietfVerifyWith Y (encode Y) ctx msg sig

/-- The same function as `Bandersnatch.vrfOutput`. -/
def vrfOutput (sig : List UInt8) : List UInt8 :=
  match decodeOnCurve (sig.take 32) with
  | some O => (JAM.Sha512.hash (Bandersnatch.suiteString ++ [3] ++ encode O ++ [0])).take 32
  | none => JAM.Sha512.vrfOutput sig

/-! ## Thin VRF (GP v0.8.1) -/

namespace Thin

open JamCrypto.Bandersnatch.Thin (Transcript tagThinVrf tagDelinearize tagChallenge tagPointToHash
  challengeLen enc64 decScalarMod)

/-- The encoding of the generator. -/
def encG : List UInt8 := JamCrypto.Bandersnatch.encode JamCrypto.Bandersnatch.G

/-- `Bandersnatch.Thin.verify` with a decoded key (`decode key = some Y`) and its encoding. -/
def verifyWith (Y : Pt) (encY ctx msg sig : List UInt8) (rd : Reading := .prose) : Bool := Id.run do
  if sig.length != 96 then return false
  let some O := decode (sig.take 32) | return false
  let some R := decode (slice sig 32 32) | return false
  let s := leToNat (slice sig 64 32)
  if s ≥ Bandersnatch.r then return false
  let some I := hashToCurveOf (Bandersnatch.Thin.expandMessage ctx rd) | return false
  if isZero Y || isZero I || isZero O then return false
  -- vrfTranscript
  let ad := msg
  let t := Transcript.new.absorb
    ([tagThinVrf] ++ enc64 2 ++ encG ++ encY ++ encode I ++ encode O ++ enc64 ad.length ++ ad)
  let z := decScalarMod ((t.absorb [tagDelinearize]).squeeze challengeLen)
  let Im := add G (smul z I)
  let Om := add Y (smul z O)
  -- challenge
  let c := decScalarMod ((t.absorb ([tagChallenge] ++ encode R)).squeeze challengeLen)
  -- s·Im = R + c·Om  ⟺  s·Im − c·Om = R (subgroup points: no exceptional steps)
  let lhs := smul2 s Im c (neg Om)
  return valid lhs && eq lhs R

/-- The same function as `Bandersnatch.Thin.verify`. -/
def verify (key ctx msg sig : List UInt8) (rd : Reading := .prose) : Bool := Id.run do
  if key.length != 32 then return false
  let some Y := decode key | return false
  return verifyWith Y (encode Y) ctx msg sig rd

/-- The same function as `Bandersnatch.Thin.vrfOutput`. -/
def vrfOutput (sig : List UInt8) : List UInt8 :=
  match decodeOnCurve (sig.take 32) with
  | some O => (Transcript.new.absorb ([tagPointToHash] ++ encode O)).squeeze 32
  | none => (Transcript.new.absorb ([tagPointToHash] ++ sig.take 32)).squeeze 32

end Thin

end JamCrypto.Fast.Bandersnatch
