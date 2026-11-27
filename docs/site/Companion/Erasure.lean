import VersoManual
import Companion.Source
import Companion.Paper
import Companion.Docstring
import JAM.Erasure

open Verso.Genre Manual
open Companion
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Appendix H: erasure coding" =>
%%%
tag := "erasure"
shortTitle := "H. Erasure coding"
file := "erasure-coding"
%%%

*In the paper:* {gpchapter}`sec:erasurecoding`.

*In brief.* JAM keeps data available without asking every validator to store all of it. Appendix H
defines the erasure code that makes this possible: data is coded into one chunk per validator, and a
fixed number of the chunks, together with their positions, is enough to rebuild it. With 1023
validators any 342 chunks suffice: an exported segment of 4104 octets becomes 1023 chunks of 12
octets each, and any 342 of them give the segment back. Guarantors code a work-package bundle and
its exported segments this way ({ref "work"}[§14], {ref "guaranteeing"}[§15]), validators assure
that they hold their chunks ({ref "assurance"}[§16]), and auditors rebuild a bundle from chunks they
collect ({ref "auditing"}[§17]). The code is a Reed–Solomon code over a field of 2¹⁶ elements,
working on two-octet words.

*Key terms:*

* $`\fnecoriginalshards(v)`, the number of chunks needed to rebuild data coded for $`v` validators.
* $`\fnerasurecode{v}{k}`, the encoding, and $`\fnecrecover{v}{k}`, the recovery, where the data is
  split into $`k` pieces of $`\fnecoriginalshards(v)` two-octet words.

Appendix H of GP v0.8.1 defines the erasure code behind JAM's data availability: a systematic
Reed–Solomon code over $`\mathrm{GF}(2^{16})`. Data is cut into words of two octets and coded so that each of
the $`v` validators holds one chunk, and any $`\mathcal{D}(v)` of the chunks, together with their indices, give the
data back. The appendix defines the rate (§H), how a blob is split, coded and recovered (§H.1), how
words are read as field elements (§H.2), and the polynomial that does the coding (§H.3).

In the model the whole appendix is `JAM/Erasure.lean`. Its two main functions are
{api}`JAM.Erasure.encode` and {api}`JAM.Erasure.recover`. That recovery gives back the encoded
data is proved, with Mathlib, in a separate package of proofs; see {ref "erasure-proofs"}[below].

# The rate (§H)
%%%
tag := "erasure-rate"
%%%

{gpeq "H.1"}

$`\mathcal{D}(v)` is the number of chunks needed to recover the data, so the code's rate is $`\mathcal{D}(v):v`. With
$`\mathsf{W}_G = 4104` octets, $`\mathcal{D}(1023) = 342` and $`\mathcal{D}(6) = 3`.

{leanSource JAM.Erasure.originalShards}

The model's name for $`\mathcal{D}` is `originalShards`. $`\mathcal{D}` is defined on $`v \in \mathbb{V}`, the possible validator counts:
$`\mathbb{V} = \{3c \mid c \in \mathbb{N}_{2\dots\mathsf{C}+1}\}` (eq. {eq}`6.8`), multiples of 3 from 6 to $`3\mathsf{C} = 1023`.

# Blob encoding and recovery (§H.1)
%%%
tag := "erasure-blob"
%%%

A blob of $`2k \cdot \mathcal{D}(v)` octets is split into $`\mathcal{D}(v)` runs of $`k` words (a word is an octet pair). Piece $`p`, as the
paper uses the word, is word $`p` of every run: there are $`k` pieces of $`\mathcal{D}(v)` words. Each piece is coded with $`\mathcal{C}^v`
into $`v` words, and validator $`i`'s chunk is word $`i` of every coded piece, $`k` words in all. The paper writes this with a
split, a join and a transposition:

{gpeq "H.2"}

{gpeq "H.3"}

{gpeq "H.4"}

{gpeq "H.5"}

The model indexes the words directly instead of building the intermediate sequences: word $`j` of
piece $`p` is at octet $`2k \cdot j + 2p`, and chunk $`i` of the result is word $`i` of every coded piece.
{api}`JAM.Erasure.encodeWith` takes the interpolation weights as an argument, and
{api}`JAM.Erasure.encode` supplies the ones for $`v` validators:

{leanSource JAM.Erasure.encodeWith}

{leanSource JAM.Erasure.encodeWeights}

{leanSource JAM.Erasure.encode}

Recovery takes $`\mathcal{D}(v)` chunks with distinct indices. If they are the first $`\mathcal{D}(v)` chunks, the data is their
concatenation in index order; in general each piece is recovered with $`\mathcal{R}^v` and the results are joined:

{gpeq "H.6"}

{leanSource JAM.Erasure.recover}

Outside their domain both functions return `none`. {api}`JAM.Erasure.encode` does so when the data's size is
not a multiple of $`2\mathcal{D}(v)` (exactly then, by `encode_isSome_iff` below). {api}`JAM.Erasure.recover` does so for an empty
list, a number of chunks other than $`\mathcal{D}(v)`, repeated indices, an index $`\geq v`, or chunks of odd or unequal
lengths.

The model has one path for both cases. When the indices are exactly $`0, \dots, \mathcal{D}(v) - 1`, every target point is a
source point, the interpolation weights are rows of the identity, and the result is the chunks in
index order, as the first case says.

# Words as field elements (§H.2)
%%%
tag := "erasure-field"
%%%

The field is built from the polynomial $`x^{16} + x^5 + x^3 + x^2 + 1` (eq. {eq}`H.7`):

{gpeq "H.8"}

and $`\alpha` is a root of it. A word is not read in the standard basis $`\{1, \alpha, \dots, \alpha^{15}\}`, but in the following Cantor
basis: bit $`j` of the word (least significant first, eq. {eq}`H.9`) selects $`v_j`, so word $`m_i` stands for
$`\tilde{m}_i = \sum_{j=0}^{15} m_{i,j} v_j`.

$$`\begin{array}{ll} v_{0} & 1 \\ v_{1} & \alpha^{15} + \alpha^{13} + \alpha^{11} + \alpha^{10} + \alpha^7 + \alpha^6 + \alpha^3 + \alpha \\ v_{2} & \alpha^{13} + \alpha^{12} + \alpha^{11} + \alpha^{10} + \alpha^3 + \alpha^2 + \alpha \\ v_{3} & \alpha^{12} + \alpha^{10} + \alpha^9 + \alpha^5 + \alpha^4 + \alpha^3 + \alpha^2 + \alpha \\ v_{4} & \alpha^{15} + \alpha^{14} + \alpha^{10} + \alpha^8 + \alpha^7 + \alpha \\ v_{5} & \alpha^{15} + \alpha^{14} + \alpha^{13} + \alpha^{11} + \alpha^{10} + \alpha^8 + \alpha^5 + \alpha^3 + \alpha^2 + \alpha \\ v_{6} & \alpha^{15} + \alpha^{12} + \alpha^8 + \alpha^6 + \alpha^3 + \alpha^2 \\ v_{7} & \alpha^{14} + \alpha^4 + \alpha \\ v_{8} & \alpha^{14} + \alpha^{13} + \alpha^{11} + \alpha^{10} + \alpha^7 + \alpha^4 + \alpha^3 \\ v_{9} & \alpha^{12} + \alpha^7 + \alpha^6 + \alpha^4 + \alpha^3 \\ v_{10} & \alpha^{14} + \alpha^{13} + \alpha^{11} + \alpha^9 + \alpha^6 + \alpha^5 + \alpha^4 + \alpha \\ v_{11} & \alpha^{15} + \alpha^{13} + \alpha^{12} + \alpha^{11} + \alpha^8 \\ v_{12} & \alpha^{15} + \alpha^{14} + \alpha^{13} + \alpha^{12} + \alpha^{11} + \alpha^{10} + \alpha^8 + \alpha^7 + \alpha^5 + \alpha^4 + \alpha^3 \\ v_{13} & \alpha^{15} + \alpha^{14} + \alpha^{13} + \alpha^{12} + \alpha^{11} + \alpha^9 + \alpha^8 + \alpha^5 + \alpha^4 + \alpha^2 \\ v_{14} & \alpha^{15} + \alpha^{14} + \alpha^{13} + \alpha^{12} + \alpha^{11} + \alpha^{10} + \alpha^9 + \alpha^8 + \alpha^5 + \alpha^4 + \alpha^3 \\ v_{15} & \alpha^{15} + \alpha^{12} + \alpha^{11} + \alpha^8 + \alpha^4 + \alpha^3 + \alpha^2 + \alpha \end{array}`

The model stores each $`v_j` as the exponents of $`\alpha` in this table:

{leanSource JAM.Erasure.GF.cantorExponents}

It computes in the standard basis: field elements are 16-bit numbers whose bit $`j` is the coefficient
of $`\alpha^j`, addition is exclusive or, and multiplication and inversion use tables of powers and
logarithms of $`\alpha`. {api}`JAM.Erasure.toField` and {api}`JAM.Erasure.ofField` convert between a word
and its field element through the Cantor basis:

{leanSource JAM.Erasure.ofField}

{leanSource JAM.Erasure.GF.mul}

{leanSource JAM.Erasure.GF.toFieldTable}

{leanSource JAM.Erasure.toField}

Logarithm tables are correct only if $`\alpha` generates the multiplicative group, and the conversion is a
bijection only if the $`v_j` are linearly independent. The model has Boolean checks of both,
{api}`JAM.Erasure.GF.primitive` and {api}`JAM.Erasure.GF.cantorIsBasis`, which the erasure test runs;
the proofs package proves both facts ({ref "erasure-proofs"}[below]).

# The generator polynomial (§H.3)
%%%
tag := "erasure-polynomial"
%%%

Let $`d = \mathcal{D}(v)`, $`d' = 2^{\lceil \log_2 d \rceil}` and $`v' = v + d' - d`. The code words are indexed by $`I`, and the word at
index $`i` goes to validator $`f(i)`:

{gpeq "H.10, H.11"}

Each index $`i` stands for the field element $`\tilde{\imath} = \sum_{j=0}^{15} i_j v_j` (eq. {eq}`H.12`), where $`i_{15} \dots i_0` are the bits of $`i`. The
message words are interpolated by the polynomial $`p` of degree at most $`d' - 1` with

{gpeq "H.13"}

and the code word at index $`i \in I` is $`p(\tilde{\imath})`. The code is systematic: for $`i < d` the code word is the message
word.

{leanSource JAM.Erasure.paddedShards}

{leanSource JAM.Erasure.codeIndex}

{api}`JAM.Erasure.codeIndex` is the inverse of $`f`: it gives the index whose word validator $`j` receives.
The model never builds $`p`. Evaluating $`p` at a point is Lagrange interpolation through the $`d'` points of
eq. {eq}`H.13`, and the weights depend only on the points, so {api}`JAM.Erasure.lagrange` computes them
once for all pieces, and {api}`JAM.Erasure.interpolate` applies them:

{leanSource JAM.Erasure.lagrange}

{leanSource JAM.Erasure.interpolate}

Encoding interpolates from the points $`\tilde{0}, \dots, \widetilde{d'-1}` (message words, then zeros) to the code indices of the $`v` validators.
Recovery interpolates from the code indices of the $`d` chunks it is given, together with the $`d' - d` points where
$`p` is zero, back to $`\tilde{0}, \dots, \widetilde{d-1}`.

# What is proved
%%%
tag := "erasure-proofs"
%%%

The proofs about the erasure code use Mathlib's field theory and polynomials, so they are in a
separate Lean package, `proofs/` in the repository, which nothing in the model imports (the model
itself uses only Lean's core library and Std). These theorems are not in the API reference, and the
book's build does not check them; CI builds the package on every run on `main`. The statements below are copied from
[`proofs/ErasureProofs/Recovery.lean`](https://github.com/ascrivener/jam-lean/blob/1f8496f83ca22f3b8b8121f875906313402aab56/proofs/ErasureProofs/Recovery.lean),
in the namespace `JAM.Erasure.Proofs`, at commit `1f8496f`.

The package defines the field as `AdjoinRoot` of $`x^{16} + x^5 + x^3 + x^2 + 1` over `ZMod 2`, and proves that
$`\alpha` has order $`2^{16} - 1` (so the quotient is a field), that the model's `GF.add`, `GF.mul` and `GF.inv` are
the field's operations, that `toField` and `ofField` are inverse bijections on 16-bit numbers, and
that `interpolate (lagrange src tgt)` evaluates Lagrange interpolation through the source points.

On that basis it proves that every coded word is an evaluation of the polynomial of eq. {eq}`H.13`
([`encode_word`](https://github.com/ascrivener/jam-lean/blob/1f8496f83ca22f3b8b8121f875906313402aab56/proofs/ErasureProofs/Recovery.lean#L248-L254)).
For $`v \le 2^{15}`, $`p < k` and $`i < v`, word $`i` of coded piece $`p` is a 16-bit number (`W`), and it is the value at $`\widetilde{g(i)}` (with $`g` = `codeIndex`) of the
polynomial of degree less than $`d'` that takes the piece's message words at $`\tilde{0}, \dots, \widetilde{d-1}` and zero at
$`\tilde{d}, \dots, \widetilde{d'-1}`. The theorem is stated about the package's own definitions of the coded pieces
(`encPieces`) and of that polynomial (`msgPoly`). Two further theorems connect it to the model's chunks:
`encode_eq` (the chunks `encode` returns are built from `encPieces`) and `chunk_word` (word $`p` of chunk $`i` is
word $`i` of coded piece $`p`).

```
theorem encode_word (v : ℕ) (data : ByteArray) (k : ℕ) (hv : v ≤ 32768) {p i : ℕ} (hp : p < k)
    (hi : i < v) :
    W ((encPieces v data k)[p]!)[i]! ∧
    X ((encPieces v data k)[p]!)[i]! = eval (X (codeIndex (originalShards v) i))
      (msgPoly v data k p)
```

[`recover_encode`](https://github.com/ascrivener/jam-lean/blob/1f8496f83ca22f3b8b8121f875906313402aab56/proofs/ErasureProofs/Recovery.lean#L289-L295):
for at most $`2^{15}` validators, if `encode v data` gives `chunks`, then any $`\mathcal{D}(v)` distinct validator
indices below $`v`, in any order, with their chunks, give back `data`:

```
theorem recover_encode {v : ℕ} (hv : v ≤ 32768) {data : ByteArray} {chunks : List ByteArray}
    (henc : encode v data = some chunks) {J : List ℕ} (hJ : J.Nodup)
    (hlen : J.length = originalShards v) (hJv : ∀ j ∈ J, j < v) :
    recover v (J.map fun j => (chunks[j]!, j)) = some data
```

[`encode_isSome_iff`](https://github.com/ascrivener/jam-lean/blob/1f8496f83ca22f3b8b8121f875906313402aab56/proofs/ErasureProofs/Recovery.lean#L491-L494):
encoding succeeds exactly on data whose size is a multiple of $`2\mathcal{D}(v)`:

```
theorem encode_isSome_iff (v : ℕ) (data : ByteArray) :
    (encode v data).isSome ↔ data.size % (2 * originalShards v) = 0
```

[`erasure_recovery`](https://github.com/ascrivener/jam-lean/blob/1f8496f83ca22f3b8b8121f875906313402aab56/proofs/ErasureProofs/Recovery.lean#L511-L518)
puts the two together: such data encodes to $`v` chunks, and any $`\mathcal{D}(v)` of them recover it:

```
theorem erasure_recovery {v : ℕ} (hv : v ≤ 32768) (data : ByteArray)
    (hsize : data.size % (2 * originalShards v) = 0) :
    ∃ chunks, encode v data = some chunks ∧ chunks.length = v ∧
      ∀ J : List ℕ, J.Nodup → J.length = originalShards v → (∀ j ∈ J, j < v) →
        recover v (J.map fun j => (chunks[j]!, j)) = some data
```

The two chain sizes of the test vectors, as corollaries:
[`recover_encode_full`](https://github.com/ascrivener/jam-lean/blob/1f8496f83ca22f3b8b8121f875906313402aab56/proofs/ErasureProofs/Recovery.lean#L522-L526)
(1023 validators, any 342 chunks) and
[`recover_encode_tiny`](https://github.com/ascrivener/jam-lean/blob/1f8496f83ca22f3b8b8121f875906313402aab56/proofs/ErasureProofs/Recovery.lean#L528-L532)
(6 validators, any 3 chunks):

```
theorem recover_encode_full {data : ByteArray} {chunks : List ByteArray}
    (henc : encode 1023 data = some chunks) {J : List ℕ} (hJ : J.Nodup) (hlen : J.length = 342)
    (hJv : ∀ j ∈ J, j < 1023) : recover 1023 (J.map fun j => (chunks[j]!, j)) = some data

theorem recover_encode_tiny {data : ByteArray} {chunks : List ByteArray}
    (henc : encode 6 data = some chunks) {J : List ℕ} (hJ : J.Nodup) (hlen : J.length = 3)
    (hJv : ∀ j ∈ J, j < 6) : recover 6 (J.map fun j => (chunks[j]!, j)) = some data
```

The bound $`v \le 2^{15}` keeps every code index (below $`v + d' - d`) under $`2^{16}`, so distinct indices are distinct field
elements. It covers every $`v \in \mathbb{V}`, the largest of which is 1023. Separately, the erasure test (`Tests/ErasureTest.lean`) checks {api}`JAM.Erasure.encode` and
{api}`JAM.Erasure.recover` against the GP v0.8.0 erasure-coding vectors.

# Readings chosen
%%%
tag := "erasure-readings"
%%%

* *$`\mathcal{D}(v)` excludes $`d = 0`.* The set in eq. {eq}`H.1` ranges over $`d \in \mathbb{N}_{v/3+2}`, which includes 0, where
  $`\mathsf{W}_G \mathbin{\%} 2d` has no meaning. The model takes the largest positive $`d`.
* *$`v/3` is exact on $`\mathbb{V}`.* $`\mathcal{D}` is typed on $`v \in \mathbb{V}`, and every $`v \in \mathbb{V}` is a multiple of 3 (eq. {eq}`6.8`), so $`v/3` in
  $`\mathbb{N}_{v/3+2}` is a whole number. `originalShards` uses integer division, which agrees with it on $`\mathbb{V}` (and rounds
  down for other $`v`).
* *The layout of §H.3.* The erasure vectors of GP v0.8.0 already used the layout that GP v0.8.1
  §H.3 defines ($`p` of degree less than $`d'`, parity words at the indices from $`d'` on), while v0.8.0's §H.3 did
  not. This was note 28 of the model's
  [notes on the paper and the vectors](https://github.com/ascrivener/jam-lean/blob/main/docs/upstream-candidates.md#paper-and-vectors),
  resolved by v0.8.1.
