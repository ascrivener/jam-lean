import JamCrypto.RingSrs
import JamCrypto.RingCurve
import JamCrypto.ThinVrf

/-!
# The ring root $\mathcal{O}(\mathbf{k})$ (GP v0.8.0 Appendix G)

$\mathcal{O}(\mathbf{k})$ is the commitment to the ring of Bandersnatch keys $\mathbf{k}$ of the
ring VRF (Bandersnatch VRF spec, ring proof of eprint 2023/002 as implemented by ark-vrf 0.1.0 / w3f
ring-proof 0.0.2): the KZG commitments, over BLS12-381 G1 with the ring SRS, of the ring's three
fixed columns.

Ring layout, for rings of up to $n$ keys (ark-vrf's "ring size"; JAM's is $\mathsf{V}$):
* the PIOP domain has size $N$ = the least power of two $\ge n + 4 + 253$ (3 zero-knowledge rows,
  one row the constraints leave free, and 253 = the bit size of a Bandersnatch scalar): 512 for the
  tiny spec ($n = 6$), 2048 for the full spec ($n = 1023$);
* the column has $N - 3$ usable rows, of which the first $N - 257$ hold the keys (a key with no
  curve point, and every row after the last key, holds the padding point; keys beyond $N - 257$ are
  dropped), and the next 253 hold $H, 2H, \dots, 2^{252} \cdot H$ for the Pedersen blinding base
  $H$; the remaining 4 rows are 0;
* the selector column is 1 on the key rows and 0 elsewhere.

Each of the columns $x(\text{points})$, $y(\text{points})$ and selector is interpolated over the
radix-2 subgroup $\langle \omega \rangle$ of $\mathbb{F}_r^{\times}$ of order $N$
($\omega = 7^{(r-1)/N}$; row $i$ is evaluated at $\omega^i$) and committed as
$\sum_j c_j \cdot [\tau^j]G_1$ for the polynomial's coefficients $c_j$. The root is the
concatenation of the three compressed commitments: 144 octets.
-/

namespace JamCrypto.Ring

open JamCrypto.Fr

/-- The constants a ring depends on, which differ between the Gray Paper versions: the Pedersen
    blinding base $H$, the padding point, the accumulator seed of the ring proof and the label its
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

/-- GP v0.8.1 under the vectors' reading of the VRF spec's Draft 35: the points are the coordinates
    §4 and §5 print (hash_to_curve of their names with the 48-octet $Z_{\text{pad}}$), and the
    transcript label is Draft 35's suite id, which its ring vectors require. -/
def Consts.v081Vectors : Consts :=
  { blinding := Curve.blindingBase081, padding := Curve.padding081, seed := Curve.accumulatorBase081
    label := "Bandersnatch-SHA512-ELL2-v1".toUTF8.toList }

/-- hash_to_curve of a name under the prose reading of Draft 35 ($Z_{\text{pad}}$ of 128 octets), as
    a point of the ring code's curve type (the same curve, the same affine coordinates). The names
    used here all hash to a point, which cryptotest checks; the identity fallback is never taken. -/
def h2cProse (name : String) : Curve.Aff :=
  let (x, y) := Bandersnatch.curve.toAffine
    ((Bandersnatch.Thin.hashToCurve name.toUTF8.toList .prose).getD JamCrypto.Curve.zero)
  ⟨x, y⟩

/-- The blinding base $B$ of Draft 35 §4 under the prose reading:
    hash_to_curve("pedersen-blinding"). -/
def blindingBase081Prose : Curve.Aff := h2cProse "pedersen-blinding"
/-- The accumulator base $S$ of Draft 35 §5 under the prose reading:
    hash_to_curve("ring-accumulator"). -/
def accumulatorBase081Prose : Curve.Aff := h2cProse "ring-accumulator"
/-- The padding point $\square$ of Draft 35 §5 under the prose reading:
    hash_to_curve("ring-padding"). -/
def padding081Prose : Curve.Aff := h2cProse "ring-padding"

/-- GP v0.8.1 under the prose reading of the VRF spec's Draft 35: the three points derived with the
    prose hash to curve ($Z_{\text{pad}}$ of 128 octets, RFC 9380 §5.3.1), and the transcript label
    "ring-proof" (§5: "Begin with empty transcript and "ring-proof" label"). -/
def Consts.v081Prose : Consts :=
  { blinding := blindingBase081Prose, padding := padding081Prose, seed := accumulatorBase081Prose
    label := "ring-proof".toUTF8.toList }

/-- GP v0.8.1 (VRF spec Draft 35) under the reading `rd` (default `.prose`). -/
def Consts.v081 (rd : Reading := .prose) : Consts :=
  match rd with
  | .prose => Consts.v081Prose
  | .vectors => Consts.v081Vectors

/-- Bits of a Bandersnatch scalar. -/
def scalarBits : Nat := 253

/-- The least power of two $\ge m$ (for $m \ge 1$). -/
def nextPow2 (m : Nat) : Nat := Id.run do
  let mut p := 1
  for _ in [0:m.log2 + 2] do
    if p < m then p := 2 * p
  return p

/-- The PIOP domain size for a ring of $n$ keys. -/
def domainSize (n : Nat) : Nat := nextPow2 (n + 4 + scalarBits)

/-- The number of key rows (keys and padding) for domain size $N$. -/
def keysetSize (dom : Nat) : Nat := dom - 3 - scalarBits - 1

/-- A primitive $N$-th root of unity in $\mathbb{F}_r$ for $N$ a power of two $\le 2^{32}$
    (arkworks' choice). -/
def omega (dom : Nat) : Nat := pow generator ((R - 1) / dom)

/-- Reverses the low `bits` bits of $i$. -/
def bitrev (bits i : Nat) : Nat := Id.run do
  let mut r := 0
  let mut v := i
  for _ in [0:bits] do
    r := 2 * r + v % 2
    v := v / 2
  return r

/-- In-place radix-2 NTT over $\mathbb{F}_r$ of a power-of-two-sized array with root $w$ ($w$ of
    order size). -/
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

/-- The coefficients of the polynomial of degree $< N$ taking value `evals[i]` at $\omega^i$. -/
def interpolate (evals : Array Nat) : Array Nat :=
  let n := evals.size
  let ninv := inv n
  (ntt evals (inv (omega n))).map (mul · ninv)

/-- The KZG commitment of the column with these evaluations, compressed (48 octets). -/
def commitColumn (srs : Srs) (evals : Array Nat) : List UInt8 :=
  G1.compress (G1.msm srs.g1 (interpolate evals)).toAff

/-- $H, 2H, \dots, 2^{252} \cdot H$. -/
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

/-- The selector column for domain size $N$. -/
def selectorColumn (dom : Nat) : Array Nat :=
  Array.replicate (keysetSize dom) 1 ++ Array.replicate (dom - keysetSize dom) 0

/-- The ring commitment of a sequence of curve points, for domain size $N$. -/
def commitPoints (srs : Srs) (dom : Nat) (keys : List Curve.Aff) (k : Consts := .v080) : List UInt8 :=
  let pts := pointsColumn dom keys k
  let zeros := Array.replicate (dom - pts.size) 0
  let xs := pts.map (·.x) ++ zeros
  let ys := pts.map (·.y) ++ zeros
  let sel := match srs.selectors.lookup dom with
    | some c => c
    | none => commitColumn srs (selectorColumn dom)
  commitColumn srs xs ++ commitColumn srs ys ++ sel

/-- $\mathcal{O}(\mathbf{k})$: the 144-octet ring root of a sequence of Bandersnatch keys (GP
    Appendix G), for rings of up to `ringSize` keys: JAM uses the chain's validator count
    $\mathsf{V}$ (6 tiny, 1023 full) whatever $|\mathbf{k}|$ is (jam-test-vectors 0.8.0
    `safrole/full/enact-epoch-change-with-set-resize`). Keys with no curve point in the prime-order
    subgroup stand for the padding point. Empty when the SRS is too short for the ring (never for
    JAM's rings). `k` selects the GP version's constants (default v0.8.0). -/
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
