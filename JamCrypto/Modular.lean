/-!
# Prime-field arithmetic on `Nat`, and octet-string conversions

Elements of 𝔽_p are natural numbers below p; every operation reduces modulo p. Exponentiation and
square roots loop a bounded number of times (the bit length of the exponent, the 2-adicity of
p − 1), so every definition is total without `partial`.
-/

namespace JamCrypto.Modular

/-- a^e mod m, by square-and-multiply over the bits of e. -/
def powMod (a e m : Nat) : Nat := Id.run do
  let mut r := 1 % m
  let mut b := a % m
  let mut e := e
  for _ in [0:e.log2 + 1] do
    if e % 2 == 1 then r := r * b % m
    b := b * b % m
    e := e / 2
  return r

/-- The inverse of a in 𝔽_p (p prime) by Fermat: a^(p−2). It is 0 for a ≡ 0. -/
def invMod (a p : Nat) : Nat := powMod a (p - 2) p

/-- Subtraction in 𝔽_p of reduced elements. -/
@[inline] def subMod (a b p : Nat) : Nat := (a + p - b % p) % p

/-- a is a nonzero square in 𝔽_p (Euler's criterion; p an odd prime). -/
def isSquare (a p : Nat) : Bool := powMod a ((p - 1) / 2) p == 1

/-- A square root of n in 𝔽_p by Tonelli–Shanks, where p − 1 = 2^s·t with t odd and z is a
    quadratic non-residue; `none` if n is not a square. -/
def sqrtTS (p s t z n : Nat) : Option Nat := Id.run do
  let n := n % p
  if n == 0 then return some 0
  if !isSquare n p then return none
  let mut m := s
  let mut c := powMod z t p
  let mut u := powMod n t p
  let mut r := powMod n ((t + 1) / 2) p
  for _ in [0:s] do
    if u == 1 then break
    -- least i with u^(2^i) = 1 (0 < i < m)
    let mut i := 0
    let mut u2 := u
    for _ in [0:m] do
      if u2 == 1 then break
      u2 := u2 * u2 % p
      i := i + 1
    let b := powMod c (2 ^ (m - i - 1)) p
    m := i
    c := b * b % p
    u := u * c % p
    r := r * b % p
  if r * r % p == n then return some r else return none

/-- The natural number an octet string encodes little-endian. -/
def leToNat (bs : List UInt8) : Nat := bs.foldr (fun b acc => b.toNat + 256 * acc) 0

/-- The natural number an octet string encodes big-endian. -/
def beToNat (bs : List UInt8) : Nat := bs.foldl (fun acc b => 256 * acc + b.toNat) 0

/-- The n-octet little-endian encoding of x mod 256^n. -/
def natToLE (n x : Nat) : List UInt8 := (List.range n).map fun i => UInt8.ofNat (x / 256 ^ i % 256)

/-- Octets i to i+n−1 of a sequence. -/
@[inline] def slice (bs : List UInt8) (i n : Nat) : List UInt8 := (bs.drop i).take n

end JamCrypto.Modular
