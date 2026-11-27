import VersoManual
import Companion.Source
import Companion.Paper
import Companion.Docstring
import JAM.Merkle
import JAM.Segments
import JAM.History
import JAM.State

open Verso.Genre Manual
open Companion
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Appendix E: general Merklization" =>
%%%
tag := "merkle"
shortTitle := "E. General Merklization"
file := "general-merklization"
%%%

*In the paper:* {gpchapter}`sec:merklization`.

Appendix E of GP v0.8.1 defines the Merkle structures the protocol uses outside the state trie:
binary Merkle trees, well-balanced (§E.1.1) and of constant depth (§E.1.2), with the functions
that cut a constant-depth tree into pages and give the path to a page; and Merkle mountain ranges
and belts (§E.2). Section 14 then uses the constant-depth tree to commit to a work package's
exported segments, and the page functions to build the *paged proofs* that justify each segment.

In the model the node function and the well-balanced tree are in `JAM/Merkle.lean`, the
constant-depth tree, its pages and the paged proofs in `JAM/Segments.lean`, and the mountain
ranges in `JAM/History.lean`. Every function except the super-peak takes the hash function $`H` as an argument, as the
paper's do; the paper's default is Blake2b. The super-peak $`\mathcal{M}_R` is fixed to Keccak in the paper, and
{api}`JAM.MMR.superPeak` takes no $`H`.

# The node function and the trace (§E.1)
%%%
tag := "merkle-node"
%%%

$`N` hashes a sequence of items pairwise into a single root, splitting it at $`\lceil |\mathbf{v}|/2 \rceil` and
prefixing each inner node with $`\$\text{node}`:

{gpeq "E.1"}

{leanSource JAM.Merkle.node}

The recursion is bounded by `fuel`, because Lean needs every function to terminate; the callers
pass the length of the sequence. The following theorem shows that the fuel does not change the result
once it is at least that length:

{mathdoc JAM.Segments.node_fuel}

The trace $`T` lists the sibling of each node on the way from the root to item $`i`, top first. These
siblings are what a proof of inclusion is made of:

$$`T\colon \left\{\begin{aligned} (\llbracket\mathbb{B}_n\rrbracket, \mathbb{N}_{|\mathbf{v}|}, \mathbb{B} \to \mathbb{H}) &\to \llbracket\mathbb{B}_n \cup \mathbb{H}\rrbracket \\ (\mathbf{v}, i, H) &\mapsto \begin{cases} [N(P^\bot(\mathbf{v}, i), H)] \frown T(P^\top(\mathbf{v}, i), i - P_I(\mathbf{v}, i), H) & \text{if } |\mathbf{v}| > 1 \\ [\,] & \text{otherwise} \end{cases} \end{aligned}\right.`

$$`\text{where } P^s(\mathbf{v}, i) \equiv \begin{cases} \mathbf{v}_{\dots\lceil |\mathbf{v}|/2 \rceil} & \text{if } (i < \lceil |\mathbf{v}|/2 \rceil) = s \\ \mathbf{v}_{\lceil |\mathbf{v}|/2 \rceil\dots} & \text{otherwise} \end{cases}`

{transcribed "E.2" "afa0fbbc72"}

$$`\text{and } P_I(\mathbf{v}, i) \equiv \begin{cases} 0 & \text{if } i < \lceil |\mathbf{v}|/2 \rceil \\ \lceil |\mathbf{v}|/2 \rceil & \text{otherwise} \end{cases} \qquad \text{(E.2)}`

{leanSource JAM.Segments.trace}

The two branches of `if i < h` are the two values of the condition $`i < \lceil |\mathbf{v}|/2 \rceil`, which $`P^s` compares
with $`s`: in each, the sibling `o` is $`P^\bot`, and the recursive call goes into $`P^\top` at index $`i - P_I`.

# The well-balanced tree (§E.1.1)
%%%
tag := "merkle-wb"
%%%

{gpeq "E.3"}

{leanSource JAM.Merkle.root}

# The constant-depth tree and its pages (§E.1.2)
%%%
tag := "merkle-cd"
%%%

The constant-depth tree first applies the constancy preprocessor $`C`, which hashes each item with the
prefix $`\$\text{leaf}` and pads the sequence with zero hashes to a power of two, so that every leaf is at the
same depth:

{gpeq "E.7"}

{leanSource JAM.Segments.constancy}

{leanSource JAM.Segments.ceilLog2}

{leanSource JAM.Segments.length_constancy}

$`\mathcal{M}` is the root of the padded tree. $`\mathcal{J}_x` gives the path from the root down to the page of $`2^x` leaves with
index $`i`: the first $`\lceil \log_2(\max(1, |\mathbf{v}|)) \rceil - x` siblings of the trace to its first leaf. $`\mathcal{L}_x` gives the page itself,
as leaf hashes:

{gpeq "E.4"}

{gpeq "E.5"}

{gpeq "E.6"}

{leanSource JAM.Segments.cdRoot}

{leanSource JAM.Segments.justify}

{leanSource JAM.Segments.page}

`ceilLog2 v.length - x` is natural-number subtraction, which is never below 0, so it is the paper's
$`\max(0, \cdot)`.

# Checking a justification
%%%
tag := "merkle-verify"
%%%

The paper defines how justifications are made, but not how they are checked. {ref "work"}[§14.2] says only that
justifications are "generated, stored, included alongside the fetched data and verified", and {ref "auditing"}[§17.2]
that a justification "allows verification that each segment's hash is included in the referencing
Merkle root". The model defines the check as the inverse of $`T`. {api}`JAM.Segments.foldPath`
rebuilds a root from the value at the bottom of a path and the path, top first, as $`T` gives it:

{leanSource JAM.Segments.foldPath}

{api}`JAM.Segments.verifySegment` checks one item against a root with its $`\mathcal{J}_0` justification, and
{api}`JAM.Segments.verifyPage` checks a page from $`\mathcal{L}_x` with its $`\mathcal{J}_x` path:

{leanSource JAM.Segments.verifySegment}

{leanSource JAM.Segments.verifyPage}

The model proves that these checks accept what the paper's functions produce: every item verifies
against $`\mathcal{M}` with its $`\mathcal{J}_0` justification, and every page verifies with its $`\mathcal{J}_x` path:

{mathdoc JAM.Segments.verifySegment_justify}

{mathdoc JAM.Segments.verifyPage_page_justify}

These theorems are about acceptance only. They do not say that the check rejects a wrong segment;
that would rest on the hash function, which here is an arbitrary parameter.

# Paged proofs (§14.3, §14.4)
%%%
tag := "merkle-paged"
%%%

A work package's exported segments $`\mathbf{s}` are committed to by $`\mathcal{M}(\mathbf{s})`, the segment root. So that each segment can
be justified later, the paged proofs $`P(\mathbf{s})` are erasure-coded and distributed with them: for each page of 64
segments, the page's leaf hashes and its path, encoded and zero-padded to one segment of $`\mathsf{W}_G` octets:

{gpeq "14.13"}

{gpeq "14.20"}

{leanSource JAM.Segments.pagedProofs}

{leanSource JAM.Segments.zeroPad}

{leanSource JAM.Segments.encodeProof}

The paper says there are exactly $`\lceil |\mathbf{s}|/64 \rceil` paged-proof segments. The model proves this, and that each
one is the padded encoding of a page and a path that verify against the segment root:

{mathdoc JAM.Segments.length_pagedProofs}

{mathdoc JAM.Segments.pagedProofs_verify}

{ref "work"}[§14.4] also notes that each segment's justification "can be derived through a single paged-proof".
The model proves it: the $`\mathcal{J}_0` justification of segment $`n` is the path of its page followed by the
trace of $`n \bmod 2^x` within the page's leaves:

{mathdoc JAM.Segments.justify_zero_eq_page}

# Merkle mountain ranges and belts (§E.2)
%%%
tag := "merkle-mmr"
%%%

A Merkle mountain range is a sequence of optional peaks $`\llbracket\mathbb{H}^?\rrbracket`; peak $`i`, when present, is the root of a tree of
$`2^i` items. The model's type is {api}`JAM.MMR`. Appending an item carries it up through the occupied
peaks, as a binary counter carries a bit:

$$`\mathcal{A}\colon \left\{\begin{aligned} (\llbracket\mathbb{H}^?\rrbracket, \mathbb{H}, \mathbb{B} \to \mathbb{H}) &\to \llbracket\mathbb{H}^?\rrbracket \\ (\mathbf{r}, l, H) &\mapsto P(\mathbf{r}, l, 0, H) \end{aligned}\right.`

where

$$`P\colon \left\{\begin{aligned} (\llbracket\mathbb{H}^?\rrbracket, \mathbb{H}, \mathbb{N}, \mathbb{B} \to \mathbb{H}) &\to \llbracket\mathbb{H}^?\rrbracket \\ (\mathbf{r}, l, n, H) &\mapsto \begin{cases} \mathbf{r} \mathbin{+\!\!+} l & \text{if } n \ge |\mathbf{r}| \\ R(\mathbf{r}, n, l) & \text{if } n < |\mathbf{r}| \wedge \mathbf{r}_n = \emptyset \\ P(R(\mathbf{r}, n, \emptyset), H(\mathbf{r}_n \frown l), n + 1, H) & \text{otherwise} \end{cases} \end{aligned}\right.`

and

{transcribed "E.8" "b84c8c049c"}

$$`R\colon \left\{\begin{aligned} (\llbracket T\rrbracket, \mathbb{N}, T) &\to \llbracket T\rrbracket \\ (\mathbf{s}, i, v) &\mapsto \mathbf{s}' \ \text{where } \mathbf{s}' = \mathbf{s} \text{ except } \mathbf{s}'_i = v \end{aligned}\right. \qquad \text{(E.8)}`

{leanSource JAM.MMR.place}

{leanSource JAM.MMR.append}

$`R` is `List.set`. Each recursive call moves $`n` one peak up, and Lean is given that measure
(`termination_by r.length - n`).

The range is encoded as its optional peaks with a length, and committed to by its *super-peak*, which
folds the present peaks together with Keccak and the prefix $`\$\text{peak}`:

{gpeq "E.9"}

$$`\mathcal{M}_R\colon \left\{\begin{aligned} \llbracket\mathbb{H}^?\rrbracket &\to \mathbb{H} \\ \mathbf{b} &\mapsto \begin{cases} \mathbb{H}_0 & \text{if } |\mathbf{h}| = 0 \\ \mathbf{h}_0 & \text{if } |\mathbf{h}| = 1 \\ \mathcal{H}_K\left(\$\text{peak} \frown \mathcal{M}_R(\mathbf{h}_{\dots|\mathbf{h}|-1}) \frown \mathbf{h}_{|\mathbf{h}|-1}\right) & \text{otherwise} \end{cases} \end{aligned}\right.`

{transcribed "E.10" "192dcbf5f4"}

$$`\text{where } \mathbf{h} = \left[h \;\middle|\; h \mathrel{<\mkern-7mu-} \mathbf{b}, h \ne \emptyset\right] \qquad \text{(E.10)}`

$`\mathcal{E}_M` is the second half of the $`C(3)` row of the state serialization, `varSeq (opt id) r.belt` in
{api}`JAM.Serialize.recent` ({ref "statemerkle"}[Appendix D]). $`\mathcal{M}_R` takes the last present peak off at each
step, so the model works on the present peaks in reverse order:

{leanSource JAM.Serialize.recent}

{leanSource JAM.MMR.superPeakRev}

{leanSource JAM.MMR.superPeak}

# Readings chosen
%%%
tag := "merkle-readings"
%%%

These are recorded in the model's
[notes on the paper](https://github.com/ascrivener/jam-lean/blob/main/docs/upstream-candidates.md#gray-paper-issues):

* *Note v0.8.1-A13, checking a justification.* The paper defines how justifications are made but not
  how they are checked. The model's check ({api}`JAM.Segments.verifySegment`,
  {api}`JAM.Segments.verifyPage`) is the inverse of $`T` on the perfect trees $`C` produces. The depth of
  the tree is read from the length of the path, the index must be below $`2^{|\text{path}|}`, and a page may hold
  at most $`2^x` leaves. A page's
  subtree root pads the page with $`\mathbb{H}_0` to $`2^x` leaves when its path is non-empty, and to
  $`2^{\lceil \log_2 |\text{page}| \rceil}` leaves when the page is the whole tree ({api}`JAM.Segments.pageRoot`).
* *Note v0.8.1-A14, the page index.* $`\mathcal{J}_x` and $`\mathcal{L}_x` type their index as $`i \in \mathbb{N}_{|\mathbf{v}|}`, but it is a page index: only
  $`i < \lceil |\mathbf{v}|/2^x \rceil` names a page, and $`P` uses only those. For a larger $`i`, $`\mathcal{J}_x`'s trace leads to padding while
  $`2^x \cdot i < |C(\mathbf{v})|`, and indexes past the end of $`C(\mathbf{v})` once $`2^x \cdot i \geq |C(\mathbf{v})|`. The model accepts any $`i` and states its theorems for page indices.
* *Note v0.8.1-A15, the pages of $`P`.* {ref "work"}[§14.4] describes each paged proof as "a page of 64 hashes of
  segments". By the equation, the page is $`\mathcal{L}_6`, the hashes $`H(\$\text{leaf} \frown \mathbf{s}_i)` of the segments rather than
  $`\mathcal{H}(\mathbf{s}_i)`, and the last page holds only $`|\mathbf{s}| \bmod 64` of them when 64 does not divide $`|\mathbf{s}|`. The model follows the equation.

{api}`JAM.Segments.pageRoot`, which note v0.8.1-A13 above refers to:

{leanSource JAM.Segments.pageRoot}
