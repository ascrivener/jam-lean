import JamCrypto.Bls12381Field

/-!
# Bandersnatch, as much as the ring needs

The Bandersnatch curve (eprint 2021/1152) in twisted Edwards form a·x² + y² = 1 + d·x²·y² over
𝔽_r (the BLS12-381 scalar field), a = −5; its prime-order subgroup has order `N` and cofactor 4.

* Points are affine (`Aff`) or extended (`Ext`, (X : Y : T : Z) with x = X/Z, y = Y/Z, T = XY/Z).
* `decode`: the compressed 32-octet encoding of the Bandersnatch VRF spec (arkworks): y little
  endian, the top bit of the last octet set when x is the larger of ±x. A key decodes only when it
  is on the curve and in the prime-order subgroup.
* The constants of the ring: the Pedersen blinding base `blindingBase` (H), the ring's
  `accumulatorBase` (seed) and `padding` point, as fixed by the Bandersnatch VRF spec and ark-vrf
  0.1.0 (`suites::bandersnatch`).

This file is private to the ring code; the IETF VRF has its own Bandersnatch module.
-/

namespace JamCrypto.Ring.Curve

open JamCrypto.Fr

/-- a = −5. -/
def A : Nat := R - 5
/-- d. -/
def D : Nat := 45022363124591815672509500913686876175488063829319466900776701791074614335719
/-- The order of the prime-order subgroup. -/
def N : Nat := 13108968793781547619861935127046491459309155893440570251786403306729687672801

structure Aff where
  x : Nat
  y : Nat
  deriving Inhabited, BEq, Repr

structure Ext where
  x : Nat
  y : Nat
  t : Nat
  z : Nat
  deriving Inhabited, Repr

def Ext.zero : Ext := ⟨0, 1, 0, 1⟩
def Aff.zero : Aff := ⟨0, 1⟩
def Aff.toExt (p : Aff) : Ext := ⟨p.x, p.y, mul p.x p.y, 1⟩

def onCurve (p : Aff) : Bool :=
  let x2 := sq p.x
  let y2 := sq p.y
  add (mul A x2) y2 == add 1 (mul D (mul x2 y2))

/-- Addition in extended coordinates (add-2008-hwcd). -/
def addE (p q : Ext) : Ext :=
  let a := mul p.x q.x
  let b := mul p.y q.y
  let c := mul D (mul p.t q.t)
  let d := mul p.z q.z
  let e := sub (sub (mul (add p.x p.y) (add q.x q.y)) a) b
  let f := sub d c
  let g := add d c
  let h := sub b (mul A a)
  ⟨mul e f, mul g h, mul e h, mul f g⟩

/-- Doubling in extended coordinates (dbl-2008-hwcd). -/
def dblE (p : Ext) : Ext :=
  let a := sq p.x
  let b := sq p.y
  let c := add (sq p.z) (sq p.z)
  let d := mul A a
  let e := sub (sub (sq (add p.x p.y)) a) b
  let g := add d b
  let f := sub g c
  let h := sub d b
  ⟨mul e f, mul g h, mul e h, mul f g⟩

def negE (p : Ext) : Ext := ⟨Fr.neg p.x, p.y, Fr.neg p.t, p.z⟩

def Ext.isZero (p : Ext) : Bool := p.x == 0 && p.y == p.z && p.z != 0

def Ext.eq (p q : Ext) : Bool := mul p.x q.z == mul q.x p.z && mul p.y q.z == mul q.y p.z

def Ext.toAff (p : Ext) : Aff :=
  let zi := inv p.z
  ⟨mul p.x zi, mul p.y zi⟩

/-- Scalar multiplication by double-and-add (most significant bit first). -/
def smul (p : Ext) (k : Nat) : Ext := Id.run do
  let mut acc := Ext.zero
  let n := k.log2 + 1
  for i in [0:n] do
    acc := dblE acc
    if (k >>> (n - 1 - i)) % 2 == 1 then acc := addE acc p
  return acc

/-- Affine conversion of many points with one inversion. -/
def normalize (ps : Array Ext) : Array Aff :=
  let zs := batchInv (ps.map (·.z))
  (ps.zip zs).map fun (p, zi) => ⟨mul p.x zi, mul p.y zi⟩

/-- Scalar multiplication with a fixed 4-bit window. -/
def smulW (p : Ext) (k : Nat) : Ext := Id.run do
  let mut tbl : Array Ext := #[Ext.zero, p]
  for _ in [0:14] do
    tbl := tbl.push (addE tbl.back! p)
  let nd := (k.log2 + 4) / 4
  let mut acc := Ext.zero
  for i in [0:nd] do
    acc := dblE (dblE (dblE (dblE acc)))
    let d := (k >>> (4 * (nd - 1 - i))) % 16
    if d != 0 then acc := addE acc tbl[d]!
  return acc

/-- In the prime-order subgroup: [N]P is the identity. -/
def inSubgroup (p : Aff) : Bool := (smulW p.toExt N).isZero

/-- The compressed encoding (32 octets). -/
def encode (p : Aff) : List UInt8 :=
  let neg := p.x > (R - 1) / 2
  Field.toLE 32 (p.y + (if neg then 2 ^ 255 else 0))

/-- The point on the curve with this y and sign flag, if any (no subgroup check). -/
def decodeUnchecked (bs : List UInt8) : Option Aff := do
  if bs.length != 32 then none
  let v := Field.ofLE bs
  let neg := v ≥ 2 ^ 255
  let y := v % 2 ^ 255
  if y ≥ R then none
  let y2 := sq y
  let den := sub A (mul D y2)
  if den == 0 then none
  let x2 := mul (sub 1 y2) (inv den)
  let x ← sqrt? x2
  let (lo, hi) := if x ≤ Fr.neg x then (x, Fr.neg x) else (Fr.neg x, x)
  some ⟨if neg then hi else lo, y⟩

/-- A key: decodes, is on the curve and is in the prime-order subgroup. -/
def decode (bs : List UInt8) : Option Aff := do
  let p ← decodeUnchecked bs
  if onCurve p && inSubgroup p then some p else none

/-- The Pedersen blinding base H. -/
def blindingBase : Aff :=
  ⟨6150229251051246713677296363717454238956877613358614224171740096471278798312,
   28442734166467795856797249030329035618871580593056783094884474814923353898473⟩

/-- The ring accumulator base (the ring proof's seed point). -/
def accumulatorBase : Aff :=
  ⟨37805570861274048643170021838972902516980894313648523898085159469000338764576,
   14738305321141000190236674389841754997202271418876976886494444739226156422510⟩

/-- The ring padding point. -/
def padding : Aff :=
  ⟨26287722405578650394504321825321286533153045350760430979437739593351290020913,
   19058981610000167534379068105702216971787064146691007947119244515951752366738⟩

/-! ### GP v0.8.1: the same points of the VRF spec's Draft 35 (hash_to_curve of "pedersen-blinding",
    "ring-accumulator" and "ring-padding" under suite `Bandersnatch-SHA512-ELL2-v1`, §4 and §5) -/

/-- The Pedersen blinding base B of Draft 35. -/
def blindingBase081 : Aff :=
  ⟨23335687741101763108036518445642207119627658113885888016488710494487028845889,
   5552214580375038693022409684979828600325210968745774080859660443337357929963⟩

/-- The ring accumulator base S of Draft 35. -/
def accumulatorBase081 : Aff :=
  ⟨14056632001415368875257708737821299882600475929746323097150942355715730684350,
   10322661992765989500407719465917595459409463902187386706652408883505670839210⟩

/-- The ring padding point of Draft 35. -/
def padding081 : Aff :=
  ⟨26913883415342152801331916189968962157924271221160514298872262294143390094043,
   30874728313203001508631936119690348239461579770372782660098261717479009115354⟩

end JamCrypto.Ring.Curve
