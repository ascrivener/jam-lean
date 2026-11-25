/-!
# Prime fields of BLS12-381

Elements are `Nat`s below the modulus (Lean's `Nat` is GMP-backed). Two fields:

* 𝔽_q, the base field of BLS12-381 (381 bits), over which G1 is defined (`Fq`);
* 𝔽_r, the scalar field of BLS12-381 (255 bits), which is also the base field of the Bandersnatch
  curve (`Fr`). The KZG polynomials of the ring commitment live over 𝔽_r.

Moduli as in the BLS12-381 and Bandersnatch definitions (Bandersnatch paper, eprint 2021/1152).
-/

namespace JamCrypto.Field

/-- a^e mod m, by binary exponentiation over the bits of e (structural on the bit count). -/
def powMod (a e m : Nat) : Nat := Id.run do
  let mut r := 1 % m
  let mut b := a % m
  let mut k := e
  for _ in [0:e.log2 + 1] do
    if k % 2 == 1 then r := r * b % m
    b := b * b % m
    k := k / 2
  return r

/-- Inverse modulo a prime m by the extended Euclidean algorithm (0 for 0). Fuel: the Euclidean
    algorithm on numbers below 2^k ends within 2k+2 steps. -/
def invMod (a m : Nat) : Nat := Id.run do
  let a := a % m
  if a == 0 then return 0
  -- invariant: r0 ≡ s0·a, r1 ≡ s1·a (mod m)
  let mut r0 : Nat := m
  let mut r1 : Nat := a
  let mut s0 : Int := 0
  let mut s1 : Int := 1
  for _ in [0:2 * m.log2 + 4] do
    if r1 != 0 then
      let q := r0 / r1
      let r2 := r0 - q * r1
      let s2 := s0 - (q : Int) * s1
      r0 := r1; r1 := r2; s0 := s1; s1 := s2
  return (s0 % (m : Int)).toNat

/-- Big-endian octets to a number. -/
def ofBE (bs : List UInt8) : Nat := bs.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Little-endian octets to a number. -/
def ofLE (bs : List UInt8) : Nat := ofBE bs.reverse

/-- The n little-endian octets of x mod 256^n. -/
def toLE (n x : Nat) : List UInt8 := Id.run do
  let mut out : Array UInt8 := #[]
  let mut v := x
  for _ in [0:n] do
    out := out.push (UInt8.ofNat (v % 256))
    v := v / 256
  return out.toList

/-- The n big-endian octets of x mod 256^n. -/
def toBE (n x : Nat) : List UInt8 := (toLE n x).reverse

end JamCrypto.Field

namespace JamCrypto.Fq

/-- The BLS12-381 base field modulus. -/
def P : Nat :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

@[inline] def add (a b : Nat) : Nat := let s := a + b; if s ≥ P then s - P else s
@[inline] def sub (a b : Nat) : Nat := if a ≥ b then a - b else a + P - b
@[inline] def mul (a b : Nat) : Nat := a * b % P
@[inline] def sq (a : Nat) : Nat := a * a % P
@[inline] def neg (a : Nat) : Nat := if a == 0 then 0 else P - a
def inv (a : Nat) : Nat := Field.invMod a P

end JamCrypto.Fq

namespace JamCrypto.Fr

/-- The BLS12-381 scalar field modulus, the Bandersnatch base field modulus. -/
def R : Nat := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

@[inline] def add (a b : Nat) : Nat := let s := a + b; if s ≥ R then s - R else s
@[inline] def sub (a b : Nat) : Nat := if a ≥ b then a - b else a + R - b
@[inline] def mul (a b : Nat) : Nat := a * b % R
@[inline] def sq (a : Nat) : Nat := a * a % R
@[inline] def neg (a : Nat) : Nat := if a == 0 then 0 else R - a
def inv (a : Nat) : Nat := Field.invMod a R
def pow (a e : Nat) : Nat := Field.powMod a e R

/-- R − 1 = 2^32 · T with T odd. -/
def S : Nat := 32
def T : Nat := (R - 1) / 2 ^ 32

/-- The multiplicative generator 7 of 𝔽_r^× (as fixed by the BLS12-381 field parameters). -/
def generator : Nat := 7

/-- generator^T, a primitive 2^32-th root of unity. -/
def rootOfUnity : Nat := pow generator T

/-- A square root of a in 𝔽_r, if a is a square (Tonelli–Shanks; 𝔽_r has 2-adicity 32). The root
    returned is not normalised; callers pick the sign they need. -/
def sqrt? (a : Nat) : Option Nat := Id.run do
  let a := a % R
  if a == 0 then return some 0
  -- w = a^((T−1)/2), x = a^((T+1)/2), t = a^T
  let w := pow a ((T - 1) / 2)
  let mut x := mul a w
  let mut t := mul x w
  let mut m := S
  let mut c := rootOfUnity
  for _ in [0:S + 1] do
    if t != 1 then
      -- least i with t^(2^i) = 1 (i = m when a is not a square)
      let mut i := 0
      let mut tt := t
      for _ in [0:m] do
        if tt != 1 then
          tt := sq tt
          i := i + 1
      if i < m then
        let mut b := c
        for _ in [0:m - i - 1] do
          b := sq b
        m := i
        c := sq b
        t := mul t c
        x := mul x b
  return if sq x == a then some x else none

/-- Batch inversion (Montgomery's trick); zero entries map to zero. -/
def batchInv (xs : Array Nat) : Array Nat := Id.run do
  let n := xs.size
  let mut pre : Array Nat := Array.mkEmpty n
  let mut acc := 1
  for x in xs do
    pre := pre.push acc
    if x != 0 then acc := mul acc x
  let mut inv := Fr.inv acc
  let mut out : Array Nat := Array.replicate n 0
  for k in [0:n] do
    let i := n - 1 - k
    let x := xs[i]!
    if x != 0 then
      out := out.set! i (mul inv pre[i]!)
      inv := mul inv x
  return out

end JamCrypto.Fr
