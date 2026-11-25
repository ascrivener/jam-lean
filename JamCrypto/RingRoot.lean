import JamCrypto.RingSrs
import JamCrypto.RingCurve

/-!
# The ring root O(**k**) (GP v0.8.0 Appendix G)

O(**k**) is the commitment to the ring of Bandersnatch keys **k** of the ring VRF (Bandersnatch VRF
spec, ring proof of eprint 2023/002 as implemented by ark-vrf 0.1.0 / w3f ring-proof 0.0.2): the KZG
commitments, over BLS12-381 G1 with the ring SRS, of the ring's three fixed columns.

Ring layout, for rings of up to n keys (ark-vrf's "ring size"; JAM's is V):
* the PIOP domain has size N = the least power of two ≥ n + 4 + 253 (3 zero-knowledge rows, one
  row the constraints leave free, and 253 = the bit size of a Bandersnatch scalar): 512 for the
  tiny spec (n = 6), 2048 for the full spec (n = 1023);
* the column has N − 3 usable rows, of which the first N − 257 hold the keys (a key with no curve
  point, and every row after the last key, holds the padding point; keys beyond N − 257 are
  dropped), and the next 253 hold
  H, 2H, …, 2^252·H for the Pedersen blinding base H; the remaining 4 rows are 0;
* the selector column is 1 on the key rows and 0 elsewhere.

Each of the columns x(points), y(points) and selector is interpolated over the radix-2 subgroup
⟨ω⟩ of 𝔽_r^× of order N (ω = 7^((r−1)/N); row i is evaluated at ωⁱ) and committed as
Σⱼ cⱼ·[τʲ]G1 for the polynomial's coefficients cⱼ. The root is the concatenation of the three
compressed commitments: 144 octets.
-/

namespace JamCrypto.Ring

open JamCrypto.Fr

/-- The constants a ring depends on, which differ between the Gray Paper versions: the Pedersen
    blinding base H, the padding point, the accumulator seed of the ring proof and the label its
    Fiat–Shamir transcript starts with (the suite id). -/
structure Consts where
  blinding : Curve.Aff
  padding : Curve.Aff
  seed : Curve.Aff
  label : List UInt8

/-- GP v0.8.0 (ark-vrf 0.1.0). -/
def Consts.v080 : Consts :=
  { blinding := Curve.blindingBase, padding := Curve.padding, seed := Curve.accumulatorBase
    label := "Bandersnatch_SHA-512_ELL2".toUTF8.toList }

/-- GP v0.8.1 (VRF spec Draft 35; the transcript label is Draft 35's suite id, as its ring
    vectors require). -/
def Consts.v081 : Consts :=
  { blinding := Curve.blindingBase081, padding := Curve.padding081, seed := Curve.accumulatorBase081
    label := "Bandersnatch-SHA512-ELL2-v1".toUTF8.toList }

/-- Bits of a Bandersnatch scalar. -/
def scalarBits : Nat := 253

/-- The least power of two ≥ m (for m ≥ 1). -/
def nextPow2 (m : Nat) : Nat := Id.run do
  let mut p := 1
  for _ in [0:m.log2 + 2] do
    if p < m then p := 2 * p
  return p

/-- The PIOP domain size for a ring of n keys. -/
def domainSize (n : Nat) : Nat := nextPow2 (n + 4 + scalarBits)

/-- The number of key rows (keys and padding) for domain size N. -/
def keysetSize (dom : Nat) : Nat := dom - 3 - scalarBits - 1

/-- A primitive N-th root of unity in 𝔽_r for N a power of two ≤ 2^32 (arkworks' choice). -/
def omega (dom : Nat) : Nat := pow generator ((R - 1) / dom)

/-- Reverses the low `bits` bits of i. -/
def bitrev (bits i : Nat) : Nat := Id.run do
  let mut r := 0
  let mut v := i
  for _ in [0:bits] do
    r := 2 * r + v % 2
    v := v / 2
  return r

/-- In-place radix-2 NTT over 𝔽_r of a power-of-two-sized array with root w (w of order size). -/
def ntt (a : Array Nat) (w : Nat) : Array Nat := Id.run do
  let n := a.size
  let bits := n.log2
  let mut v := a
  for i in [0:n] do
    let j := bitrev bits i
    if i < j then v := v.swapIfInBounds i j
  let mut len := 2
  for _ in [0:bits] do
    let wl := pow w (n / len)
    let half := len / 2
    -- twiddles wl^k for k < half
    let mut tw : Array Nat := Array.mkEmpty half
    let mut t := 1
    for _ in [0:half] do
      tw := tw.push t
      t := mul t wl
    for s in [0:n / len] do
      let base := s * len
      for k in [0:half] do
        let u := v[base + k]!
        let x := mul v[base + k + half]! tw[k]!
        v := v.set! (base + k) (add u x)
        v := v.set! (base + k + half) (sub u x)
    len := 2 * len
  return v

/-- The coefficients of the polynomial of degree < N taking value evals[i] at ωⁱ. -/
def interpolate (evals : Array Nat) : Array Nat :=
  let n := evals.size
  let ninv := inv n
  (ntt evals (inv (omega n))).map (mul · ninv)

/-- The KZG commitment of the column with these evaluations, compressed (48 octets). -/
def commitColumn (srs : Srs) (evals : Array Nat) : List UInt8 :=
  G1.compress (G1.msm srs.g1 (interpolate evals)).toAff

/-- H, 2H, …, 2^252·H. -/
def blindingMultiples (k : Consts := .v080) : Array Curve.Aff := Id.run do
  let mut ps : Array Curve.Ext := Array.mkEmpty scalarBits
  let mut h := k.blinding.toExt
  for _ in [0:scalarBits] do
    ps := ps.push h
    h := Curve.dblE h
  return Curve.normalize ps

/-- The ring's points column for these keys: keys (padding for undecodable ones), padding up to
    the keyset size, then the blinding multiples. Keys beyond the keyset size are dropped. -/
def pointsColumn (dom : Nat) (keys : List Curve.Aff) (k : Consts := .v080) : Array Curve.Aff :=
  let ks := keys.take (keysetSize dom)
  ks.toArray ++ Array.replicate (keysetSize dom - ks.length) k.padding ++ blindingMultiples k

/-- The selector column for domain size N. -/
def selectorColumn (dom : Nat) : Array Nat :=
  Array.replicate (keysetSize dom) 1 ++ Array.replicate (dom - keysetSize dom) 0

/-- The ring commitment of a sequence of curve points, for domain size N. -/
def commitPoints (srs : Srs) (dom : Nat) (keys : List Curve.Aff) (k : Consts := .v080) : List UInt8 :=
  let pts := pointsColumn dom keys k
  let zeros := Array.replicate (dom - pts.size) 0
  let xs := pts.map (·.x) ++ zeros
  let ys := pts.map (·.y) ++ zeros
  let sel := match srs.selectors.lookup dom with
    | some c => c
    | none => commitColumn srs (selectorColumn dom)
  commitColumn srs xs ++ commitColumn srs ys ++ sel

/-- O(**k**): the 144-octet ring root of a sequence of Bandersnatch keys (GP Appendix G), for
    rings of up to `ringSize` keys: JAM uses the chain's validator count V (6 tiny, 1023 full)
    whatever |**k**| is (jam-test-vectors 0.8.0 `safrole/full/enact-epoch-change-with-set-resize`).
    Keys with no curve point in the prime-order subgroup stand for the padding point. Empty when
    the SRS is too short for the ring (never for JAM's rings). `k` selects the GP version's
    constants (default v0.8.0). -/
def root (srs : Srs) (ringSize : Nat) (keys : List (List UInt8)) (k : Consts := .v080) : List UInt8 :=
  let dom := domainSize ringSize
  if srs.g1.size < dom then [] else
  commitPoints srs dom (keys.map fun key => (Curve.decode key).getD k.padding) k

/-- The SRS with the selector commitments of rings of these sizes precomputed (default: the tiny
    and full specs' 6 and 1023 validators). The selector column does not depend on the keys. -/
def withSelectors (srs : Srs) (ringSizes : List Nat := [6, 1023]) : Srs :=
  let doms := (ringSizes.map domainSize).eraseDups.filter (· ≤ srs.g1.size)
  { srs with selectors := doms.map fun d => (d, commitColumn srs (selectorColumn d)) }

end JamCrypto.Ring
