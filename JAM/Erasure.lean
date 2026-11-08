import JAM.Codec
import JAM.Constants

/-!
# Erasure coding (GP v0.8.0 Appendix H)

Systematic Reed–Solomon over GF(2¹⁶), as the paper defines it: a message of d = R(v) words
(eq. `ecoriginalshards`) is the values at 0̃, …, (d−1)~ of the unique polynomial p of degree < d,
and code word i is p(ĩ) (§H.3, "The Generator Polynomial"). Words are octet pairs read by ℰ_2,
and both words and validator indices stand for field elements through the Cantor basis
v₀, …, v₁₅ (§H.2): bit j of the word selects v_j.

Arithmetic is done in the polynomial basis {1, α, …, α¹⁵} of 𝔽₂[x]/(x¹⁶ + x⁵ + x³ + x² + 1), where
the Cantor basis vectors are given; `toField` and `ofField` convert. The polynomial is primitive
(α has order 2¹⁶ − 1, which `GF.expTable` relies on and the test checks), so products use
logarithm tables.

p is never built: evaluating it at a point is Lagrange interpolation, Σ_s L_s(x)·p(x_s), and the
weights L_s(x) depend only on the points (`lagrange`). The same routine gives ℰ_C (from the d
message points to all v) and ℛ (from any d known points back to the d message points).
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
    t := t.set! expTable[i]! i
  return t

/-- Whether α generates the multiplicative group, so `mul` and `inv` are right. -/
def primitive : Bool := (logTable.toList.drop 1).eraseDups.length == 65535 &&
  expTable.all (· ≠ 0)

/-- Addition (and subtraction) in characteristic 2. -/
def add (a b : Nat) : Nat := a ^^^ b

/-- Multiplication, by logarithms. -/
def mul (a b : Nat) : Nat :=
  if a = 0 ∨ b = 0 then 0 else expTable[(logTable[a]! + logTable[b]!) % 65535]!

/-- Multiplicative inverse of a nonzero element. -/
def inv (a : Nat) : Nat := expTable[(65535 - logTable[a]!) % 65535]!

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
  (List.range 16).foldl (fun acc j => if m.testBit j then acc ^^^ cantor[j]! else acc) 0

/-- The inverse of `toFieldTable` (the Cantor basis is a basis, so it is a bijection). -/
def ofFieldTable : Array Nat := Id.run do
  let mut t : Array Nat := Array.replicate 65536 0
  for m in [0:65536] do
    t := t.set! toFieldTable[m]! m
  return t

/-- Whether `toFieldTable` is a bijection, i.e. the v_j are linearly independent. -/
def cantorIsBasis : Bool := (List.range 65536).all fun m => ofFieldTable[toFieldTable[m]!]! == m

end GF

/-- The field element m̃ of a word or validator index m < 2¹⁶ (GP §H.2). -/
def toField (m : Nat) : Nat := GF.toFieldTable[m % 65536]!

/-- The word whose field element is x. -/
def ofField (x : Nat) : Nat := GF.ofFieldTable[x % 65536]!

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
      (Array.range xs.size).map fun s => GF.mul l (GF.mul w[s]! (GF.inv (GF.add x xs[s]!)))).toArray

/-- Apply interpolation weights to words: the words at the target points, given the words at the
    source points. -/
def interpolate (m : Array (Array Nat)) (words : Array Nat) : Array Nat :=
  let ys := words.map toField
  m.map fun row => ofField ((List.range row.size).foldl (fun acc s => GF.add acc (GF.mul row[s]! ys[s]!)) 0)

/-! ## The erasure code -/

/-- R(v) = max {d ∈ ℕ_{v/3+2} | 𝖶_G mod 2d = 0} (GP eq. `ecoriginalshards`): the number of
    original shards for v validators, with 𝖶_G = 4104 the segment size. d = 0 is excluded, where
    "𝖶_G mod 0" has no meaning. -/
def originalShards (v : Nat) : Nat :=
  ((List.range (v / 3 + 2)).filter fun d => d > 0 ∧ Constants.Csegmentsize % (2 * d) = 0).foldl max 0

/-- The word ℰ_2⁻¹ at octet offset `o`. -/
def word (b : ByteArray) (o : Nat) : Nat := (b.get! o).toNat + 256 * (b.get! (o + 1)).toNat

/-- ℰ_2 of a word. -/
def wordOctets (w : Nat) : List UInt8 := [UInt8.ofNat w, UInt8.ofNat (w / 256)]

/-- ℰ_C^k (GP eq. `erasurecoding`) for v validators, with the weights `m` from the message
    points 0 … d−1 to the validator points 0 … v−1: the data, of 2k·d octets, is split into d
    chunks of k words; piece p is word p of every chunk; each piece is coded into v words; chunk i
    of the result is word i of every piece. `none` if the length is not a multiple of 2d. -/
def encodeWith (d : Nat) (m : Array (Array Nat)) (data : ByteArray) : Option (List ByteArray) :=
  if d = 0 ∨ data.size % (2 * d) ≠ 0 then none
  else
    let k := data.size / (2 * d)
    let pieces := (List.range k).map fun p =>
      interpolate m ((Array.range d).map fun j => word data (2 * k * j + 2 * p))
    some ((List.range m.size).map fun i => ⟨(pieces.flatMap fun c => wordOctets c[i]!).toArray⟩)

/-- The weights ℰ_C uses for v validators. -/
def encodeWeights (v : Nat) : Array (Array Nat) := lagrange (List.range (originalShards v)) (List.range v)

/-- ℰ_C^k for v validators (GP eq. `erasurecoding`). -/
def encode (v : Nat) (data : ByteArray) : Option (List ByteArray) :=
  encodeWith (originalShards v) (encodeWeights v) data

/-- ℛ^k for v validators (GP eq. `erasurecodinginv`): from d = R(v) chunks of 2k octets with
    distinct indices below v, the original 2k·d octets. Piece p's d words are interpolated back to
    the message points 0 … d−1 and joined chunk by chunk. When the indices are exactly 0 … d−1 the
    weights are the identity, which is the paper's first case (the chunks concatenated in index
    order). `none` if the chunks are not d of equal even length with distinct indices below v. -/
def recover (v : Nat) (c : List (ByteArray × Nat)) : Option ByteArray :=
  let d := originalShards v
  let idx := c.map (·.2)
  match c with
  | [] => none
  | (x₀, _) :: _ =>
    let len := x₀.size
    if c.length ≠ d ∨ idx.eraseDups.length ≠ d ∨ idx.any (· ≥ v) ∨ len % 2 ≠ 0 ∨
        c.any (·.1.size ≠ len) then none
    else
      let k := len / 2
      let m := lagrange idx (List.range d)
      let pieces := (List.range k).map fun p =>
        interpolate m ((c.map fun (x, _) => word x (2 * p)).toArray)
      -- chunk j of the data is word j of every piece
      some ⟨((List.range d).flatMap fun j => pieces.flatMap fun ws => wordOctets ws[j]!).toArray⟩

end JAM.Erasure
