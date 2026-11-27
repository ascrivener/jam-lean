import VersoManual
import Companion.Source
import Companion.Paper
import Companion.Docstring
import JAM.History
import JAM.Accumulation

open Verso.Genre Manual
open Companion
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "§7 Recent history" =>
%%%
tag := "history"
shortTitle := "§7 Recent history"
file := "history"
%%%

*In the paper:* {gpchapter}`sec:recenthistory`.

*In brief.* the chain keeps a short memory of its last eight blocks, so that later checks can
refer to them. When a guarantee arrives ({ref "reports"}[§11]), its work-report names a recent
block, the *anchor*, as the context the work was done in; the anchor must be found here with a
matching state root, output-log commitment and timeslot, and a work-package already reported in one of these
blocks is rejected as a duplicate. The same component holds the Accumulation Output Log, a running
commitment, built with Keccak, to the outputs that services yield in accumulation
({ref "accumulation"}[§12]); its latest value is what validators sign for third-party systems in
{ref "beefy"}[§18]. One detail: a block's own state root is not known until the next block, so each
new entry records a zero placeholder, which the next block corrects.

*Key terms:*

* $`\recenthistory`, the recent blocks, at most $`\Crecenthistorylen = 8`;
* $`\accoutbelt`, the Accumulation Output Log, a Merkle mountain belt ({ref "merkle"}[Appendix E]);
* $`\lastaccout`, the outputs of the latest accumulation, from which the log grows.

The state keeps a short record of the most recent $`\mathsf{H}` blocks ($`\mathsf{H} = 8`). Guarantees use it ({ref "reports"}[§11]) to reject work
reports that are duplicates or whose context is out of date. It also holds the Accumulation Output
Log, a Merkle mountain belt that commits to the outputs of every block's accumulation. In the model,
the whole transition of GP v0.8.1 §7 is one function, {api}`JAM.recentHistory`, in
`JAM/History.lean` ([API page](https://ascrivener.github.io/jam-lean/api/JAM/History.html)).

# The state
%%%
tag := "history-state"
%%%

{gpeq "7.1"}

{gpeq "7.2"}

{gpeq "7.3, 7.4"}

Each entry of $`\beta_H` holds a block's header hash $`h`, its state root $`s`, the super-peak $`b` of the
Accumulation Output Log after that block, its timeslot $`t`, and the work packages reported in it:
$`\mathbf{p}` maps each package hash to its segment root. $`\beta_B` is the log itself, a sequence of optional peaks.
$`\langle\!|\, K \to V \,|\!\rangle` is the paper's notation for dictionaries from $`K` to $`V` (§3.5; the paper draws the angle brackets
with a bar). $`\theta` is the sequence of accumulation outputs, (service, hash) pairs; it is produced by accumulation
({ref "accumulation"}[§12]) and kept in the state as a separate component.

The model keeps the five fields of an entry in {api}`JAM.RecentBlock` (the field `accRoot` is $`b`) and
$`\beta` in {api}`JAM.Recent`:

{leanSource JAM.RecentBlock}

{leanSource JAM.Recent}

Mountain ranges and belts, $`\llbracket \mathbb{H}\boldsymbol{?} \rrbracket`, are {api}`JAM.MMR`. Hashes are octet lists whose length the types
do not fix.

{leanSource JAM.MMR}

# Correcting the parent's state root
%%%
tag := "history-dagger"
%%%

A block's entry is added before its posterior state root is known, so it is first recorded with
the zero hash $`\mathbb{H}_0`. The next block's header carries that root as $`\mathbf{H}_R`, and the transition puts it in place:

{gpeq "7.5"}

{leanSource JAM.Recent.withParentRoot}

$`\beta^\dagger_H` is also used by {ref "reports"}[§11]'s check that each report's anchor block is recent (eq. {eq}`11.36`), and it appears
as its own node, eq. {eq}`4.6`, of the {ref "overview"}[dependency graph].

# The Accumulation Output Log
%%%
tag := "history-belt"
%%%

The block's accumulation outputs $`\theta'` are encoded, Merklized with Keccak, and the root is appended to
the log:

{gpeq "7.6"}

{gpeq "7.7"}

In the model, accumulation computes the root $`\mathcal{M}_B(\mathbf{s}, \mathcal{H}_K)` (it is `AccResult.root`, returned by
{api}`JAM.accumulate`) and passes it to {api}`JAM.recentHistory` as `HistoryInput.accRoot`. Everything
the transition reads from the block and from accumulation is in {api}`JAM.HistoryInput`:

{leanSource JAM.HistoryInput}

The append function $`\mathcal{A}` and the super-peak function $`\mathcal{M}_R` are defined in {ref "merkle"}[Appendix E.2]:

{transcribed "E.8" "b84c8c049c"}

$$`\begin{aligned} \mathcal{A}(\mathbf{r}, l, H) &\equiv P(\mathbf{r}, l, 0, H) \qquad \text{(E.8)} \\ \text{where } P(\mathbf{r}, l, n, H) &= \begin{cases} \mathbf{r} \mathbin{+\!\!+} l & \text{if } n \geq |\mathbf{r}| \\ R(\mathbf{r}, n, l) & \text{if } n < |\mathbf{r}| \wedge \mathbf{r}_n = \emptyset \\ P\left(R(\mathbf{r}, n, \emptyset), H(\mathbf{r}_n \frown l), n + 1, H\right) & \text{otherwise} \end{cases} \end{aligned}`

Here $`R(\mathbf{s}, i, v)` is $`\mathbf{s}` with entry $`i` replaced by $`v`, which is Lean's `List.set`.

{leanSource JAM.MMR.place}

{leanSource JAM.MMR.append}

{transcribed "E.10" "192dcbf5f4"}

$$`\begin{aligned} \mathcal{M}_R(\mathbf{b}) &= \begin{cases} \mathbb{H}_0 & \text{if } |\mathbf{h}| = 0 \\ \mathbf{h}_0 & \text{if } |\mathbf{h}| = 1 \\ \mathcal{H}_K\left(\texttt{\$peak} \frown \mathcal{M}_R(\mathbf{h}_{\dots|\mathbf{h}|-1}) \frown \mathbf{h}_{|\mathbf{h}|-1}\right) & \text{otherwise} \end{cases} \qquad \text{(E.10)} \\ \text{where } \mathbf{h} &= \left[\, h \;\middle|\; h \mathrel{\mathrlap{<}{-}} \mathbf{b}, h \neq \emptyset \,\right] \end{aligned}`

The model drops the empty peaks once and recurses on the list of present peaks, reversed, so that
removing the last peak is taking the tail of the list:

{leanSource JAM.MMR.superPeakRev}

{leanSource JAM.MMR.superPeak}

# The new entry
%%%
tag := "history-entry"
%%%

The posterior $`\beta_H` appends an entry for the new block and keeps the last $`\mathsf{H}`:

{gpeq "7.8"}

$`\overleftarrow{\mathbf{s}}^n` is the last $`n` elements of $`\mathbf{s}` (§3.7), and $`\mathbf{p}` maps the package hash of each guaranteed report's
availability specification to its segment root. The new state root is $`\mathbb{H}_0`. The paper notes that this is
"inaccurate but safe": $`\beta'` is only used to form the next block's $`\beta^\dagger`, which corrects it by {eq}`7.5`.

{leanSource JAM.recentHistory}

The model's `h.drop (h.length - params.recentHistoryLen)` keeps the last $`\mathsf{H}` entries. Natural-number
subtraction stops at 0, so a shorter sequence is kept whole.

# What is checked

No theorems about §7 are proved yet. The transition is run against the v0.8.0 test vectors
`stf/history` (tiny and full), which give the accumulation root directly, and compared with their
posterior $`\beta_H` and $`\beta_B` ([`Tests/HistoryTest.lean`](https://github.com/ascrivener/jam-lean/blob/main/Tests/HistoryTest.lean)).

# Readings chosen
%%%
tag := "history-readings"
%%%

The notes named below are in the model's [notes on the paper](https://github.com/ascrivener/jam-lean/blob/main/docs/upstream-candidates.md#gray-paper-issues).

* *An empty history (note v0.8.1-A26).* Eq. {eq}`7.5` indexes the last entry, $`\beta_H[|\beta_H| - 1]`, which does not exist when $`\beta_H` is empty
  (as at genesis). The model then leaves $`\beta^\dagger_H` empty ({api}`JAM.Recent.withParentRoot`).
* *The package map (note v0.8.1-A27).* $`\mathbf{p}` is written as a set of pairs $`k \mapsto v`, which makes it a dictionary. If two guarantees
  had the same package hash, the model would keep the later one (`Std.ExtTreeMap.ofList`). The
  guarantee checks of {ref "reports"}[§11] reject duplicate packages before this point (eq. {eq}`11.35`), so the case does not arise in
  a valid block.
