import JAM.Codec
import JAM.Constants

/-!
# Erasure coding (GP v0.8.1 Appendix H)

Systematic Reed–Solomon over GF(2¹⁶), as the paper defines it (§H.3, "The Generator Polynomial",
as fixed by GP #580): for v validators, d = R(v) message words (eq. `ecoriginalshards`),
d' = 2^⌈log₂ d⌉ and v' = v + d' − d, the polynomial p of degree < d' takes the message words at
0̃, …, (d−1)~ and zero at d̃, …, (d'−1)~. Code words sit at the indices I = ℕ_d ∪ [d', v'), and
the word at index i goes to validator f(i) = i for i < d and i − (d' − d) for i ≥ d'. So validator
j receives p at index g(j) = j for j < d and j + (d' − d) otherwise (`codeIndex`). Words are octet
pairs read by ℰ_2, and both words and indices stand for field elements through the Cantor basis
v₀, …, v₁₅ (§H.2): bit j of the word selects v_j.

(v0.8.0 §H.3 took p of degree < d and gave validator i the word p(ĩ); the vectors already used the
v0.8.1 layout, upstream candidate 28.)

Arithmetic is done in the polynomial basis {1, α, …, α¹⁵} of 𝔽₂[x]/(x¹⁶ + x⁵ + x³ + x² + 1), where
the Cantor basis vectors are given; `toField` and `ofField` convert. The polynomial is primitive
(α has order 2¹⁶ − 1, which `GF.expTable` relies on and the test checks), so products use
logarithm tables.

p is never built: evaluating it at a point is Lagrange interpolation, Σ_s L_s(x)·p(x_s), and the
weights L_s(x) depend only on the points (`lagrange`). The same routine gives ℰ_C (from the d'
points ℕ_{d'} to the v code indices) and ℛ (from the d known code indices and the d' − d zero
points back to the d message points).

Tables and arrays are read with `getD … 0`: every index is a field element below 2¹⁶, an octet
offset or a position inside an array of known size, but its type is ℕ. The proofs package shows the
default is never used (`ErasureProofs.Interp`, "Reads in bounds"), and
`JAM.Theorems.CheckedIndex.Erasure` states each definition equal to its earlier `a[i]!` form.
-/

namespace JAM.Erasure

/-! ## The field -/

namespace GF

/-- x¹⁶ + x⁵ + x³ + x² + 1 (GP §H.2). -/
def poly : Nat := 0x1002D

/-- α^i for i < 2¹⁶ − 1, by repeated multiplication by α. -/
def expTable : Array Nat := Id.run do
  let mut t : Array Nat := Array.mkEmpty 65535
  let mut x := 1
  for _ in [0:65535] do
    t := t.push x
    x := x <<< 1
    if x &&& 0x10000 ≠ 0 then x := x ^^^ poly
  return t

/-- log_α, the inverse of `expTable` on nonzero elements (entry 0 unused). -/
def logTable : Array Nat := Id.run do
  let mut t : Array Nat := Array.replicate 65536 0
  for i in [0:65535] do
    t := t.set! (expTable.getD i 0) i
  return t

/-- Whether α generates the multiplicative group, so `mul` and `inv` are right: given the tables
    `exp := expTable` and `log := logTable`, every nonzero element has a distinct logarithm and no
    power of α is 0. Takes the tables as arguments so that it is a function, not a closed term the
    compiler would evaluate when an executable starts ([`Tests/ErasureTest.lean`](https://github.com/ascrivener/jam-lean/blob/main/Tests/ErasureTest.lean) runs it). -/
def primitive (exp log : Array Nat) : Bool := (log.toList.drop 1).eraseDups.length == 65535 &&
  exp.all (· ≠ 0)

/-- Addition (and subtraction) in characteristic 2. -/
def add (a b : Nat) : Nat := a ^^^ b

/-- Multiplication, by logarithms. -/
def mul (a b : Nat) : Nat :=
  if a = 0 ∨ b = 0 then 0 else expTable.getD ((logTable.getD a 0 + logTable.getD b 0) % 65535) 0

/-- Multiplicative inverse of a nonzero element. -/
def inv (a : Nat) : Nat := expTable.getD ((65535 - logTable.getD a 0) % 65535) 0

/-- The Cantor basis v₀ … v₁₅ (GP §H.2), each as the exponents of α in its standard-basis
    expansion. -/
def cantorExponents : List (List Nat) :=
  [[0],
   [15, 13, 11, 10, 7, 6, 3, 1],
   [13, 12, 11, 10, 3, 2, 1],
   [12, 10, 9, 5, 4, 3, 2, 1],
   [15, 14, 10, 8, 7, 1],
   [15, 14, 13, 11, 10, 8, 5, 3, 2, 1],
   [15, 12, 8, 6, 3, 2],
   [14, 4, 1],
   [14, 13, 11, 10, 7, 4, 3],
   [12, 7, 6, 4, 3],
   [14, 13, 11, 9, 6, 5, 4, 1],
   [15, 13, 12, 11, 8],
   [15, 14, 13, 12, 11, 10, 8, 7, 5, 4, 3],
   [15, 14, 13, 12, 11, 9, 8, 5, 4, 2],
   [15, 14, 13, 12, 11, 10, 9, 8, 5, 4, 3],
   [15, 12, 11, 8, 4, 3, 2, 1]]

/-- v_j in the standard basis. -/
def cantor : Array Nat := (cantorExponents.map fun es => es.foldl (fun acc e => acc ||| (1 <<< e)) 0).toArray

/-- m̃ = Σ_j m_j v_j (GP §H.2), for every 16-bit m. -/
def toFieldTable : Array Nat := (Array.range 65536).map fun m =>
  (List.range 16).foldl (fun acc j => if m.testBit j then acc ^^^ cantor.getD j 0 else acc) 0

/-- The inverse of `toFieldTable` (the Cantor basis is a basis, so it is a bijection). -/
def ofFieldTable : Array Nat := Id.run do
  let mut t : Array Nat := Array.replicate 65536 0
  for m in [0:65536] do
    t := t.set! (toFieldTable.getD m 0) m
  return t

/-- Whether `toFieldTable` is a bijection, i.e. the v_j are linearly independent. -/
def cantorIsBasis : Bool := (List.range 65536).all fun m => ofFieldTable.getD (toFieldTable.getD m 0) 0 == m

end GF

/-- The field element m̃ of a word or validator index m < 2¹⁶ (GP §H.2). -/
def toField (m : Nat) : Nat := GF.toFieldTable.getD (m % 65536) 0

/-- The word whose field element is x. -/
def ofField (x : Nat) : Nat := GF.ofFieldTable.getD (x % 65536) 0

/-! ## Interpolation -/

/-- Lagrange weights: row t, column s is L_s(x_t), the value at x_t of the polynomial of degree
    < |**src**| that is 1 at x_s and 0 at the other source points, with x_i = ĩ. Barycentric form:
    L_s(x) = ℓ(x)·w_s / (x − x_s) with ℓ(x) = Π_s (x − x_s) and w_s = 1 / Π_{r≠s} (x_s − x_r); a
    target that is a source point gets the indicator row. Source indices must be distinct. -/
def lagrange (src tgt : List Nat) : Array (Array Nat) :=
  let xs := (src.map toField).toArray
  let w := xs.mapIdx fun s xsv =>
    GF.inv (xs.foldl (init := (1, 0)) (fun (acc, r) xr =>
      (if r = s then acc else GF.mul acc (GF.add xsv xr), r + 1))).1
  (tgt.map fun t =>
    let x := toField t
    match xs.findIdx? (· == x) with
    | some s => (Array.range xs.size).map fun r => if r = s then 1 else 0
    | none =>
      let l := xs.foldl (fun acc xr => GF.mul acc (GF.add x xr)) 1
      (Array.range xs.size).map fun s => GF.mul l (GF.mul (w.getD s 0) (GF.inv (GF.add x (xs.getD s 0))))).toArray

/-- Apply interpolation weights to words: the words at the target points, given the words at the
    source points. -/
def interpolate (m : Array (Array Nat)) (words : Array Nat) : Array Nat :=
  let ys := words.map toField
  m.map fun row => ofField ((List.range row.size).foldl (fun acc s => GF.add acc (GF.mul (row.getD s 0) (ys.getD s 0))) 0)

/-! ## The erasure code -/

/-- R(v) = max {d ∈ ℕ_{v/3+2} | 𝖶_G mod 2d = 0} (GP eq. `ecoriginalshards`): the number of
    original shards for v validators, with 𝖶_G = 4104 the segment size. d = 0 is excluded, where
    "𝖶_G mod 0" has no meaning. -/
def originalShards (v : Nat) : Nat :=
  ((List.range (v / 3 + 2)).filter fun d => d > 0 ∧ Constants.Csegmentsize % (2 * d) = 0).foldl max 0

/-- The word ℰ_2⁻¹ at octet offset `o`. -/
def word (b : ByteArray) (o : Nat) : Nat := (b.data.getD o 0).toNat + 256 * (b.data.getD (o + 1) 0).toNat

/-- ℰ_2 of a word. -/
def wordOctets (w : Nat) : List UInt8 := [UInt8.ofNat w, UInt8.ofNat (w / 256)]

/-- d' = 2^⌈log₂ d⌉, the least power of two ≥ d (GP v0.8.1 §H.3). -/
def paddedShards (d : Nat) : Nat := Id.run do
  let mut n := 1
  for _ in [0:d] do
    if n < d then n := 2 * n
  return n

/-- g(j), the code index whose word validator j receives: the inverse of f (GP v0.8.1 §H.3),
    j for j < d and j + (d' − d) otherwise. -/
def codeIndex (d j : Nat) : Nat := if j < d then j else j + (paddedShards d - d)

/-- ℰ_C^k (GP eq. `erasurecoding`, §H.3) with d message words per piece and the weights `m` from
    the d' points ℕ_{d'} to the code indices of the validators: the data, of 2k·d octets, is split
    into d chunks of k words; piece p is word p of every chunk, followed by d' − d zero words;
    each piece is coded into one word per validator; chunk i of the result is word i of every
    piece. `none` if the length is not a multiple of 2d. -/
def encodeWith (d : Nat) (m : Array (Array Nat)) (data : ByteArray) : Option (List ByteArray) :=
  if d = 0 ∨ data.size % (2 * d) ≠ 0 then none
  else
    let k := data.size / (2 * d)
    let pieces := (List.range k).map fun p =>
      interpolate m ((Array.range (paddedShards d)).map fun j =>
        if j < d then word data (2 * k * j + 2 * p) else 0)
    some ((List.range m.size).map fun i => ⟨(pieces.flatMap fun c => wordOctets (c.getD i 0)).toArray⟩)

/-- The weights ℰ_C uses for v validators: from ℕ_{d'} to g(0), …, g(v − 1). -/
def encodeWeights (v : Nat) : Array (Array Nat) :=
  let d := originalShards v
  lagrange (List.range (paddedShards d)) ((List.range v).map (codeIndex d))

/-- ℰ_C^k for v validators (GP eq. `erasurecoding`). -/
def encode (v : Nat) (data : ByteArray) : Option (List ByteArray) :=
  encodeWith (originalShards v) (encodeWeights v) data

/-- ℛ^k for v validators (GP eq. `erasurecodinginv`): from d = R(v) chunks of 2k octets with
    distinct validator indices below v, the original 2k·d octets. Piece p's d words, at the code
    indices g(j), together with the zeroes at d, …, d' − 1, are interpolated back to the message
    points 0 … d−1 and joined chunk by chunk. When the indices are exactly 0 … d−1 the weights are
    the identity, which is the paper's first case (the chunks concatenated in index order). `none`
    if the chunks are not d of equal even length with distinct indices below v. -/
def recover (v : Nat) (c : List (ByteArray × Nat)) : Option ByteArray :=
  let d := originalShards v
  let n := paddedShards d
  let idx := c.map (·.2)
  match c with
  | [] => none
  | (x₀, _) :: _ =>
    let len := x₀.size
    if c.length ≠ d ∨ idx.eraseDups.length ≠ d ∨ idx.any (· ≥ v) ∨ len % 2 ≠ 0 ∨
        c.any (·.1.size ≠ len) then none
    else
      let k := len / 2
      let m := lagrange (idx.map (codeIndex d) ++ (List.range (n - d)).map (d + ·)) (List.range d)
      let pieces := (List.range k).map fun p =>
        interpolate m ((c.map fun (x, _) => word x (2 * p)).toArray ++ Array.replicate (n - d) 0)
      -- chunk j of the data is word j of every piece
      some ⟨((List.range d).flatMap fun j => pieces.flatMap fun ws => wordOctets (ws.getD j 0)).toArray⟩

-- Regression tests (GP v0.8.1 #580): d' and the index map f⁻¹.
#guard paddedShards 2 = 2 ∧ paddedShards 3 = 4 ∧ paddedShards 342 = 512 ∧ paddedShards 1 = 1
#guard originalShards 6 = 3 ∧ originalShards 1023 = 342
#guard (List.range 6).map (codeIndex 3) = [0, 1, 2, 4, 5, 6]

end JAM.Erasure
