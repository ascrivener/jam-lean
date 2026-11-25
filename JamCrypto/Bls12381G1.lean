import JamCrypto.Bls12381Field

/-!
# The group G1 of BLS12-381

G1 is the curve y² = x³ + 4 over 𝔽_q (its prime-order subgroup). Points are affine (`Aff`) or
Jacobian (`Jac`, (X : Y : Z) standing for (X/Z², Y/Z³), Z = 0 the identity).

Octet encodings are the zcash BLS12-381 ones used by arkworks (`ark-bls12-381`): a coordinate is 48
big-endian octets; the three high bits of the first octet are the flags *compressed*, *infinity*
and *y is the lexicographically largest of ±y* (compressed form only).

Multi-scalar multiplication is Pippenger's bucket method (`msm`).
-/

namespace JamCrypto.G1

open JamCrypto.Fq

/-- An affine point; `inf` is the identity (then x, y are 0). -/
structure Aff where
  x : Nat
  y : Nat
  inf : Bool := false
  deriving Inhabited, BEq, Repr

/-- A Jacobian point; z = 0 is the identity. -/
structure Jac where
  x : Nat
  y : Nat
  z : Nat
  deriving Inhabited, Repr

def Jac.zero : Jac := ⟨1, 1, 0⟩

def Aff.toJac (p : Aff) : Jac := if p.inf then Jac.zero else ⟨p.x, p.y, 1⟩

def onCurve (p : Aff) : Bool := p.inf || sq p.y == add (mul (sq p.x) p.x) 4

/-- Doubling (dbl-2009-l, a = 0). -/
def dbl (p : Jac) : Jac :=
  if p.z == 0 || p.y == 0 then Jac.zero else
  let a := sq p.x
  let b := sq p.y
  let c := sq b
  let t := add p.x b
  let d := add (sub (sub (sq t) a) c) (sub (sub (sq t) a) c)
  let e := add (add a a) a
  let f := sq e
  let x3 := sub f (add d d)
  let c8 := add (add (add c c) (add c c)) (add (add c c) (add c c))
  let y3 := sub (mul e (sub d x3)) c8
  let z3 := mul (add p.y p.y) p.z
  ⟨x3, y3, z3⟩

/-- Mixed addition p + q with q affine (madd-2007-bl). -/
def addMixed (p : Jac) (q : Aff) : Jac :=
  if q.inf then p else
  if p.z == 0 then q.toJac else
  let z1z1 := sq p.z
  let u2 := mul q.x z1z1
  let s2 := mul (mul q.y p.z) z1z1
  let h := sub u2 p.x
  let r := add (sub s2 p.y) (sub s2 p.y)
  if h == 0 then (if r == 0 then dbl p else Jac.zero) else
  let hh := sq h
  let i := add (add hh hh) (add hh hh)
  let j := mul h i
  let v := mul p.x i
  let x3 := sub (sub (sq r) j) (add v v)
  let yj := mul p.y j
  let y3 := sub (mul r (sub v x3)) (add yj yj)
  let z3 := sub (sub (sq (add p.z h)) z1z1) hh
  ⟨x3, y3, z3⟩

/-- Addition of Jacobian points (add-2007-bl). -/
def addJ (p q : Jac) : Jac :=
  if p.z == 0 then q else if q.z == 0 then p else
  let z1z1 := sq p.z
  let z2z2 := sq q.z
  let u1 := mul p.x z2z2
  let u2 := mul q.x z1z1
  let s1 := mul (mul p.y q.z) z2z2
  let s2 := mul (mul q.y p.z) z1z1
  let h := sub u2 u1
  let r := add (sub s2 s1) (sub s2 s1)
  if h == 0 then (if r == 0 then dbl p else Jac.zero) else
  let i := sq (add h h)
  let j := mul h i
  let v := mul u1 i
  let x3 := sub (sub (sq r) j) (add v v)
  let sj := mul s1 j
  let y3 := sub (mul r (sub v x3)) (add sj sj)
  let z3 := mul (sub (sub (sq (add p.z q.z)) z1z1) z2z2) h
  ⟨x3, y3, z3⟩

def negJ (p : Jac) : Jac := ⟨p.x, Fq.neg p.y, p.z⟩

def Jac.toAff (p : Jac) : Aff :=
  if p.z == 0 then ⟨0, 0, true⟩ else
  let zi := inv p.z
  let zi2 := sq zi
  ⟨mul p.x zi2, mul p.y (mul zi2 zi), false⟩

/-- Scalar multiplication by double-and-add (most significant bit first). -/
def smul (p : Jac) (k : Nat) : Jac := Id.run do
  let mut acc := Jac.zero
  let n := k.log2 + 1
  for i in [0:n] do
    acc := dbl acc
    if (k >>> (n - 1 - i)) % 2 == 1 then acc := addJ acc p
  return acc

/-- Bits of the scalars in `msm`: scalars are below 2^255 (elements of 𝔽_r). -/
def scalarBits : Nat := 255

/-- The window width minimising ⌈b/c⌉·(n + 2^(c+1)) additions. -/
def window (n : Nat) : Nat := Id.run do
  let mut best := 1
  let mut bestCost := (scalarBits + 0) * (n + 4)
  for c in [2:17] do
    let cost := ((scalarBits + c - 1) / c) * (n + 2 ^ (c + 1))
    if cost < bestCost then best := c; bestCost := cost
  return best

/-- Σ kᵢ·Pᵢ (Pippenger's bucket method). Scalars must be below 2^255; extra points or scalars are
    ignored. -/
def msm (points : Array Aff) (scalars : Array Nat) : Jac := Id.run do
  let n := min points.size scalars.size
  let c := window n
  let nw := (scalarBits + c - 1) / c
  let mask := 2 ^ c - 1
  let mut acc := Jac.zero
  for wi in [0:nw] do
    let w := nw - 1 - wi
    -- shift the accumulator by c bits
    for _ in [0:c] do
      acc := dbl acc
    let mut buckets : Array Jac := Array.replicate (2 ^ c) Jac.zero
    for i in [0:n] do
      let d := (scalars[i]! >>> (w * c)) &&& mask
      if d != 0 then
        buckets := buckets.modify d (addMixed · points[i]!)
    -- Σ d·B_d = Σ_d (B_d + … + B_top), by running sums from the top
    let mut running := Jac.zero
    let mut sum := Jac.zero
    for k in [0:2 ^ c - 1] do
      let d := 2 ^ c - 1 - k
      running := addJ running buckets[d]!
      sum := addJ sum running
    acc := addJ acc sum
  return acc

/-- The compressed 48-octet zcash encoding. -/
def compress (p : Aff) : List UInt8 :=
  if p.inf then 0xc0 :: List.replicate 47 0 else
  let bs := Field.toBE 48 p.x
  let flags : UInt8 := 0x80 ||| (if p.y > (P - 1) / 2 then 0x20 else 0)
  match bs with
  | b :: rest => (b ||| flags) :: rest
  | [] => []

/-- The uncompressed 96-octet zcash encoding at offset `off` of `bs` (no subgroup check; the
    point is checked to be on the curve). -/
def decodeUncompressed (bs : ByteArray) (off : Nat) : Option Aff := Id.run do
  if off + 96 > bs.size then return none
  let b0 := bs.get! off
  if b0 &&& 0x80 != 0 then return none
  let mut x := (b0 &&& 0x1f).toNat
  for i in [1:48] do
    x := x * 256 + (bs.get! (off + i)).toNat
  let mut y := 0
  for i in [48:96] do
    y := y * 256 + (bs.get! (off + i)).toNat
  if b0 &&& 0x40 != 0 then
    return if x == 0 && y == 0 then some ⟨0, 0, true⟩ else none
  if x ≥ P || y ≥ P then return none
  let p : Aff := ⟨x, y, false⟩
  return if onCurve p then some p else none

/-- The uncompressed 96-octet zcash encoding. -/
def encodeUncompressed (p : Aff) : List UInt8 :=
  if p.inf then 0x40 :: List.replicate 95 0 else Field.toBE 48 p.x ++ Field.toBE 48 p.y

/-- In the prime-order subgroup: [r]P is the identity. -/
def inSubgroup (p : Aff) : Bool := p.inf || (smul p.toJac Fr.R).z == 0

/-- The compressed 48-octet zcash encoding, decoded and checked to be in G1 (as arkworks'
    validating deserialization does). -/
def decompress (bs : List UInt8) : Option Aff := do
  if bs.length != 48 then none
  let b0 := bs.head!
  if b0 &&& 0x80 == 0 then none
  let inf := b0 &&& 0x40 != 0
  let big := b0 &&& 0x20 != 0
  let x := Field.ofBE ((b0 &&& 0x1f) :: bs.tail)
  if inf then
    if big || x != 0 then none else some ⟨0, 0, true⟩
  else
  if x ≥ P then none
  let y2 := add (mul (sq x) x) 4
  -- q ≡ 3 (mod 4)
  let y := Field.powMod y2 ((P + 1) / 4) P
  if sq y != y2 then none
  let y := if (y > (P - 1) / 2) == big then y else Fq.neg y
  let p : Aff := ⟨x, y, false⟩
  if inSubgroup p then some p else none

end JamCrypto.G1
