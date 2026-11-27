import VersoManual
import Companion.Source
import Companion.Paper
import Companion.Docstring
import JAM.Shuffle
import JAM.Theorems.Auditing

open Verso.Genre Manual
open Companion
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Appendix F: shuffling" =>
%%%
tag := "shuffle"
shortTitle := "F. Shuffling"
file := "shuffle"
%%%

*In the paper:* {gpchapter}`sec:shuffle`.

The paper uses a Fisher–Yates shuffle $`\mathcal{F}` wherever it needs a random order: for the
guarantor assignments of §11.3 ({ref "reports-assignments"}[chapter]) it shuffles the core indices $`[\lfloor i/3 \rfloor \mid i \mathrel{\mathrlap{<}{-}} \mathbb{N}_v]`, one per validator, and
for the selection of reports to audit in {ref "auditing"}[§17] it shuffles reports. §3.7.5 introduces it: it takes a sequence and some entropy, and returns
the same elements in an order fixed by the entropy. Appendix F of GP v0.8.1 defines it, first for
entropy given as a sequence of naturals, then for entropy given as a hash.

The module is `JAM/Shuffle.lean`; its full API is on the
[doc-gen4 page](https://ascrivener.github.io/jam-lean/api/JAM/Shuffle.html).

# The shuffle (eq. F.1)
%%%
tag := "shuffle-seq"
%%%

{transcribed "F.1" "0a1e35509f"}

$$`\forall T, l \in \mathbb{N} : \mathcal{F} \colon \begin{cases} \left\lgroup \llbracket T \rrbracket_l, \llbracket \mathbb{N} \rrbracket_{l:} \right\rgroup \to \llbracket T \rrbracket_l \\ (\mathbf{s}, \mathbf{r}) \mapsto \begin{cases} [\mathbf{s}_{\mathbf{r}_0 \bmod l}] \frown \mathcal{F}(\mathbf{s}'_{\dots l-1}, \mathbf{r}_{1\dots}) & \text{if } \mathbf{s} \ne [] \\ [] & \text{otherwise} \end{cases} \\ \qquad \text{where } \mathbf{s}' = \mathbf{s} \text{ except } \mathbf{s}'_{\mathbf{r}_0 \bmod l} = \mathbf{s}_{l-1} \end{cases} \qquad \text{(F.1)}`

(The paper writes the "where" clause inside the first case, on the same line.) Each step takes the element at $`\mathbf{r}_0 \bmod l`, moves the last element into its place, drops the last
position, and continues with the rest of $`\mathbf{r}`. The model's {api}`JAM.Shuffle.shuffle` does
exactly this. Lean accepts its recursion because $`\mathbf{s}` gets one element shorter at each step:

{leanSource JAM.Shuffle.shuffle}

# The shuffle from a hash (eqs. F.2, F.3)
%%%
tag := "shuffle-hash"
%%%

$`\mathcal{Q}_l` stretches a 32-octet hash into $`l` naturals below $`2^{32}`: entry $`i` is the little-endian decoding of
four octets of $`\mathcal{H}(h \frown \mathcal{E}_4(\lfloor i/8 \rfloor))`, so each hash gives eight entries. $`\mathcal{F}` given a hash shuffles with
$`\mathcal{Q}_l` of it:

{gpeq "F.2"}

{gpeq "F.3"}

{leanSource JAM.Shuffle.seqFromHash}

{leanSource JAM.Shuffle.shuffleHash}

$`\mathcal{H}` is Blake2b-256 ({ref "primitives"}[§3.8]), and $`\mathcal{E}_4` and $`\mathcal{E}^{-1}_4` are the four-octet little-endian encoding and its
inverse ({ref "codec"}[Appendix C]), here `PVM.Num.encodeLE 4` and `PVM.Num.decodeLE`.

# What the model proves
%%%
tag := "shuffle-theorems"
%%%

§3.7.5 describes $`\mathcal{F}` as returning "a sequence of the same length with the same elements". The model
proves that, for any entropy sequence, even one shorter than $`\mathbf{s}`:

{mathdoc JAM.Auditing.shuffle_perm}

It also proves that the positions $`\mathcal{F}` picks do not depend on the elements, so shuffling the indices
$`0, 1, \dots` and then looking the elements up gives the same result as shuffling the elements:

{mathdoc JAM.Auditing.shuffle_map}

The shuffle is also run against the shuffle test vectors (`shuffle/shuffle_tests.json`, GP
v0.8.0), which apply the hash form to $`[0, 1, \dots, n-1]`.

# Readings chosen
%%%
tag := "shuffle-readings"
%%%

* *Note v0.8.1-A52, a short entropy sequence.* (F.1) types $`\mathbf{r}` as having at least $`l` entries, so $`\mathbf{r}_0` always exists. The
  model's {api}`JAM.Shuffle.shuffle` accepts any $`\mathbf{r}`, and reads a missing entry as 0, to stay total.
  The paper's uses never reach that case: (F.3) passes $`\mathcal{Q}_l(h)`, which has exactly $`l` entries. This is
  recorded in the model's
  [notes on the paper](https://github.com/ascrivener/jam-lean/blob/main/docs/upstream-candidates.md#gray-paper-issues).
