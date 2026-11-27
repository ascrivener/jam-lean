import VersoManual
import Companion.Source
import Companion.Paper
import Companion.Docstring
import JAM.Auditing
import JAM.Guarantee
import JAM.Theorems.Auditing
import JAM.BestChain

open Verso.Genre Manual
open Companion
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "§17 Auditing and judging" =>
%%%
tag := "auditing"
shortTitle := "§17 Auditing"
file := "auditing"
%%%

*In the paper:* {gpchapter}`sec:auditing`.

Once a work-report becomes available, validators audit it: each one refines the work-package again
and publishes a judgment on whether the report is correct. §17 of GP v0.8.1 says which reports a
validator must audit, in tranches that grow when announced auditors do not deliver, what it signs,
and when it considers a report, and a block, audited.

This is off-chain logic, and the paper takes the view of one validator $`v` looking at one block
$`\mathbf{B}`: $`\rho` is that block's prior availability assignments, $`\kappa` its prior validator set, $`\mathbf{H}` its header. The
model's `JAM/Auditing.lean` computes the deterministic parts from that view. What a validator has
learnt from the others (their announcements and judgments) is an input, and so is the outcome of
its own re-refinement. Signatures are checked through the model's crypto parameter. The API page is
[JAM.Auditing](https://ascrivener.github.io/jam-lean/api/JAM/Auditing.html), and the theorems are in
[JAM.Theorems.Auditing](https://ascrivener.github.io/jam-lean/api/JAM/Theorems/Auditing.html).

§17.2, "Data Fetching", describes the checks on a bundle rebuilt from erasure-coded chunks. The
model implements them in `JAM/Guarantee.lean`, next to its §14 code; see {ref "work-checks"}[Checking a bundle].

# The reports to audit (§17.3)
%%%
tag := "auditing-q"
%%%

$`\mathbf{q}` maps each active core to the report that just became available on it, or to $`\emptyset`:

$$`\mathbf{q} \in \llbracket \mathbb{R}\boldsymbol{?} \rrbracket_{|\kappa|/3} \qquad \text{(17.1)}`

$$`\mathbf{q} \equiv \left[ \begin{rcases} (\rho[c]_\mathbf{g})_\mathbf{r} & \text{if } (\rho[c]_\mathbf{g})_\mathbf{r} \in \mathbf{R} \\ \emptyset & \text{otherwise} \end{rcases} \;\middle|\; c \mathrel{\mathrlap{<}{-}} \mathbb{N}_{|\kappa|/3} \right] \qquad \text{(17.2)}`

$`\mathbf{R}` is the set of reports that became available in the block (§11). The model compares reports by
their encoding:

{leanSource JAM.Auditing.auditReports}

# Tranche 0 (§17.3)
%%%
tag := "auditing-tranche0"
%%%

The first tranche is drawn with $`s_0`, a VRF signature under the validator's Bandersnatch key $`\kappa[v]_b` with
an empty message and a context made from the block's entropy source $`\mathcal{Y}(\mathbf{H}_V)`:

$$`s_0 \in \overset{\backsim}{\mathbb{V}}{}^{[]}_{\kappa[v]_b}\left\langle \mathsf{X}_U \frown \mathcal{Y}(\mathbf{H}_V) \right\rangle \qquad \text{(17.3)} \qquad\qquad \mathsf{X}_U = \texttt{\$jam\_audit} \qquad \text{(17.4)}`

{leanSource JAM.Auditing.initialSeedValid}

The validator audits the non-empty reports among the first ten entries of $`\mathbf{q}` shuffled with
$`\mathcal{Y}(s_0)` ($`\mathcal{F}` is the shuffle of Appendix F):

$$`\mathbf{a}_0 = \left\{ \mathbf{r} \;\middle|\; \mathbf{r} \in \mathcal{F}\left(\mathbf{q}, \mathcal{Y}(s_0)\right)_{\dots+10},\ \mathbf{r} \ne \emptyset \right\} \qquad \text{(17.5)}`

{leanSource JAM.Auditing.tranche0}

The paper writes $`\mathbf{a}_0` as a set; the model keeps it as a sequence in shuffle order. A second form,
{api}`JAM.Auditing.tranche0Indexed`, makes the same draw over $`\mathbf{q}` paired with core indices. What the model
proves about $`\mathbf{a}_0`:

{mathdoc JAM.Auditing.tranche0_length_le}

{mathdoc JAM.Auditing.tranche0Indexed_nodup_cores}

{mathdoc JAM.Auditing.tranche0Indexed_mem}

{mathdoc JAM.Auditing.tranche0_eq_map_snd}

# The current tranche (§17.3)
%%%
tag := "auditing-n"
%%%

A new tranche starts every $`\mathsf{A} = 8` seconds after the start of the block's timeslot:

$$`\text{let } n = \left\lfloor \frac{\mathcal{T} - \mathsf{P}\cdot\mathbf{H}_T}{\mathsf{A}} \right\rfloor \qquad \text{(17.6)}`

{leanSource JAM.Auditing.currentTranche}

# Announcements (§17.3)
%%%
tag := "auditing-announce"
%%%

Before auditing, a validator announces which reports it will audit in tranche $`n`, signing with its
Ed25519 key $`\kappa[v]_e`:

$$`S \equiv \bar{\mathbb{V}}_{\kappa[v]_e}\left\langle \mathsf{X}_I \mathbin{+\!\!+} n \frown \mathbf{x}_n \frown \mathcal{H}(\mathbf{H}) \right\rangle \qquad \text{(17.7)}`

$$`\text{where } \mathbf{x}_n = \mathcal{E}\left(\left\{ \mathcal{E}_2(\mathbf{r}_c) \frown \mathcal{H}(\mathbf{r}) \;\middle|\; \mathbf{r} \in \mathbf{a}_n \right\}\right) \qquad \text{(17.8)}`

$$`\mathsf{X}_I = \texttt{\$jam\_announce} \qquad \text{(17.9)}`

{leanSource JAM.Auditing.announcementItems}

{leanSource JAM.Auditing.announcementMessage}

{leanSource JAM.Auditing.announcementValid}

# What the validator knows (§17.3)
%%%
tag := "auditing-view"
%%%

$`A_n(\mathbf{r})` is the validator's perception of which validators must audit $`\mathbf{r}` in tranche $`n`, from their
announcements; $`J_\top(\mathbf{r})` and $`J_\bot(\mathbf{r})` are the validators it knows to have judged $`\mathbf{r}` valid and invalid, in
any tranche:

$$`A_n\colon \mathbb{R} \to \left\{\!\left[\, \mathbb{N}_{|\kappa|} \,\right]\!\right\} \qquad \text{(17.10)} \qquad\qquad J_{\{\bot, \top\}}\colon \mathbb{R} \to \left\{\!\left[\, \mathbb{N}_{|\kappa|} \,\right]\!\right\} \qquad \text{(17.12)}`

(The paper's (17.11) numbers an empty line: the line after (17.10), which would put the validator
itself in $`A_0` for its own tranche-0 reports, is commented out in the paper's source.)

These are inputs to the model, gathered in a {api}`JAM.Auditing.View`. Reports are named by
$`\mathcal{H}(\mathbf{r})`, as announcements and judgments name them, and a set of validators is a
{api}`JAM.Auditing.VSet`, of which only the indices below $`|\kappa|` are read:

{leanSource JAM.Auditing.View}

# Later tranches (§17.3)
%%%
tag := "auditing-later"
%%%

In a later tranche, a validator may have to audit a report because some validators announced for
it in the previous tranche and have not been seen to judge it valid (the *no-shows*, $`A_{n-1}(\mathbf{r}) \setminus J_\top(\mathbf{r})`). A fresh VRF output
for each report decides, with probability growing with the number of no-shows:

$$`\begin{aligned} &\forall n > 0: \\ &\quad s_n(\mathbf{r}) \in \overset{\backsim}{\mathbb{V}}{}^{[]}_{\kappa[v]_b}\left\langle \mathsf{X}_U \frown \mathcal{Y}(\mathbf{H}_V) \frown \mathcal{H}(\mathbf{r}) \mathbin{+\!\!+} n \right\rangle && \text{(17.13)} \\ &\quad a_n(\mathbf{r}) \equiv \tfrac{|\kappa|}{65536\mathsf{F}}\, \mathcal{E}_2^{-1}\left(\mathcal{Y}(s_n(\mathbf{r}))_{0\dots+2}\right) < \left|A_{n-1}(\mathbf{r}) \setminus J_\top(\mathbf{r})\right| && \text{(17.14)} \\ &\quad \mathbf{a}_n \equiv \left\{ \mathbf{r} \;\middle|\; \mathbf{r} \in \mathbf{q},\ \mathbf{r} \ne \emptyset,\ a_n(\mathbf{r}) \right\} && \text{(17.15)} \end{aligned}`

The bias factor is $`\mathsf{F} = 2`, the expected number of validators drawn for one no-show. The model
decides $`a_n(\mathbf{r})` in whole numbers, as $`|\kappa| \cdot \mathcal{E}_2^{-1}(\dots) < 65536 \cdot \mathsf{F} \cdot m` with $`m` the number of no-shows, which is
the same inequality multiplied out:

{leanSource JAM.Auditing.laterSeedValid}

{leanSource JAM.Auditing.noShows}

{leanSource JAM.Auditing.laterSelected}

{leanSource JAM.Auditing.laterTranche}

The prose also says a validator must always judge a report on which it has seen a negative
judgment; that rule is not in (17.15). The model keeps (17.15) as {api}`JAM.Auditing.laterTranche` and adds
the prose rule in a second function, {api}`JAM.Auditing.laterTrancheWithNegatives` (see
{ref "auditing-readings"}[Readings chosen]). {api}`JAM.Auditing.tranche` gives $`\mathbf{a}_n` for any $`n`. What the model proves:

{mathdoc JAM.Auditing.laterSelected_zero}

{mathdoc JAM.Auditing.laterSelected_mono}

{mathdoc JAM.Auditing.laterTranche_eq_nil}

{mathdoc JAM.Auditing.laterTranche_sublist}

{mathdoc JAM.Auditing.laterTranche_subset_withNegatives}

# Evaluation and judgments (§17.3)
%%%
tag := "auditing-judgments"
%%%

For each report it must audit, the validator rebuilds a candidate bundle $`C(\mathbf{r})` and evaluates the
report by computing it again with $`\Xi` (§14):

$$`\begin{aligned} &\forall \mathbf{r} \in \mathbf{a}_n: \\ &e_n(\mathbf{r}) \Leftrightarrow \begin{cases} M(\mathbf{r}, \mathbf{p}) & \text{if } \exists \mathbf{p} \in \mathbb{P}: B(\mathbf{p}, \mathbf{r}_\mathbf{l}) = C(\mathbf{r}) \\ \bot & \text{otherwise} \end{cases} \\ &\text{where } M(\mathbf{r}, \mathbf{p}) \equiv \mathbf{r} = \Xi(\mathbf{p}, \mathbf{r}_c, \mathbf{r}_\mathbf{l}, (\mathbf{r}_\mathbf{s})_v) \end{aligned} \qquad \text{(17.16)}`

The model does not define $`e_n` as one function: the evaluation is an input to the judgment below. Its
parts are in `JAM/Guarantee.lean`: decoding and checking the bundle
({api}`JAM.Guarantee.verifyBundle`) and $`\Xi` ({api}`JAM.Guarantee.computeReport`), described in the
{ref "work"}[§14 chapter].

The validator then signs a judgment on each report:

$$`\mathbf{j}_n = \left\{ \bar{\mathcal{S}}_{\kappa[v]_e}\left(\mathsf{X}_{e_n(\mathbf{r})} \frown \mathcal{H}(\mathbf{r})\right) \;\middle|\; \mathbf{r} \in \mathbf{a}_n \right\} \qquad \text{(17.17)}`

$`\mathsf{X}_\top` is `$jam_valid` and $`\mathsf{X}_\bot` is `$jam_invalid`:

{leanSource JAM.Auditing.judgmentMessage}

{leanSource JAM.Auditing.judgmentValid}

By inspection, this is the message §10 checks for a vote in a verdict: `checkVerdict`
(`JAM/Disputes.lean`) verifies each vote against `Xvalidif j.valid ++ r`, the same message. No
theorem connects the two definitions yet.

# The audited conditions (§17.3)
%%%
tag := "auditing-u"
%%%

A report is audited when it has no negative judgment and, in some tranche, every validator required
to audit it has judged it valid; or when more than two thirds of the validators have judged it
valid:

$$`U(\mathbf{r}) \Leftrightarrow \bigvee \left\{ \begin{aligned} &J_\bot(\mathbf{r}) = \emptyset \wedge \exists n : A_n(\mathbf{r}) \subseteq J_\top(\mathbf{r}) \\ &|J_\top(\mathbf{r})| > \tfrac{2}{3}|\kappa| \end{aligned} \right. \qquad \text{(17.18)}`

The model bounds $`n` in $`\exists n` by the current tranche (see {ref "auditing-readings"}[Readings chosen]).
`h` is $`\mathcal{H}(\mathbf{r})` and `current` the current tranche:

{leanSource JAM.Auditing.Audited}

{leanSource JAM.Auditing.audited}

{mathdoc JAM.Auditing.audited_iff}

A block is audited when every report that became available in it is:

$$`\mathbf{U} \Leftrightarrow \forall \mathbf{r} \in \mathbf{R} : U(\mathbf{r}) \qquad \text{(17.19)}`

{leanSource JAM.Auditing.blockAudited}

{mathdoc JAM.Auditing.blockAudited_iff}

What the model proves about $`U`. More positive judgments, or a later tranche, never make a report
unaudited, but one negative judgment does, below the two-thirds count:

{mathdoc JAM.Auditing.audited_mono_positive}

{mathdoc JAM.Auditing.audited_mono_current}

{mathdoc JAM.Auditing.audited_false_of_negative}

The two theorems behind the reading of $`\exists n`: read literally, once some tranche has no announcements for $`\mathbf{r}`, the first
clause of $`U` collapses to $`J_\bot(\mathbf{r}) = \emptyset`; and even bounded, a tranche in which nobody announced for $`\mathbf{r}` satisfies it.

{leanSource JAM.Auditing.AuditedLiteral}

{mathdoc JAM.Auditing.auditedLiteral_degenerate}

{mathdoc JAM.Auditing.audited_of_empty_tranche}

# Disregarded chains and verdicts (§17.3)
%%%
tag := "auditing-verdicts"
%%%

"Furthermore, we pointedly disregard chains which include the accumulation of a report which we know at least
$`\tfrac{1}{3}` of validators judge as being invalid." The model's test for one report is:

{leanSource JAM.Auditing.disregarded}

§19's best-chain rule takes a disregarded flag for each block, which
{api}`JAM.BestChain.disregardedBlock` computes from this test over the reports the block accumulates
({ref "bestchain"}[§19 chapter]).

A block author that has seen enough judgments on a report, at least one of them negative, may put a
verdict on it in the disputes extrinsic (§10). The paper does not say which verdict to form when
several are possible. {api}`JAM.Auditing.formVerdict` tries good, then bad, then wonky. The theorems
show that what it returns has the count, order and outcome that §10 checks, with every vote backed
by a judgment the author has seen (the signatures are supplied by the caller and are not checked
here), and that it finds a good verdict whenever enough positive judgments are known. The
supermajority clause of $`U` is exactly the count a good verdict needs.

{mathdoc JAM.Auditing.formVerdict_sound}

{mathdoc JAM.Auditing.formVerdict_good_complete}

{mathdoc JAM.Auditing.supermajority_iff_verdictGood}

# Readings chosen
%%%
tag := "auditing-readings"
%%%

Where the paper leaves a point open, the model picks one meaning. The notes cited are in the
model's [notes on the paper](https://github.com/ascrivener/jam-lean/blob/main/docs/upstream-candidates.md#gray-paper-issues).

* *$`\exists n` in $`U` is bounded by the current tranche (note v0.8.1-A8).* Read literally, $`\exists n : A_n(\mathbf{r}) \subseteq J_\top(\mathbf{r})`
  holds as soon as any tranche has $`A_n(\mathbf{r}) = \emptyset`. By (17.14), every tranche after one with no no-shows
  has $`A_n(\mathbf{r}) = \emptyset`, and tranches not yet reached are perceived as empty too, so the first clause of $`U`
  would reduce to "no negative judgment": a report nobody judged would count as audited
  ({api}`JAM.Auditing.auditedLiteral_degenerate`). The paper notes that $`A_n` "cannot be correctly evaluated until
  $`n` is current", and the model reads $`n` as ranging over the tranches up to the current one
  ({api}`JAM.Auditing.audited`). Even so, a tranche up to the current one in which nobody announced for
  $`\mathbf{r}` still satisfies the clause ({api}`JAM.Auditing.audited_of_empty_tranche`).
* *How $`n` is appended (note v0.8.1-A9).* $`\mathsf{X}_I \mathbin{+\!\!+} n` and $`\mathcal{H}(\mathbf{r}) \mathbin{+\!\!+} n` append a natural number to an octet
  sequence without saying how it is encoded. The model uses the general natural encoding $`\mathcal{E}(n)`,
  one octet for $`n < 128`.
* *The order of $`\mathbf{x}_n` (note v0.8.1-A9).* The encoding of a set lists its elements in order. The elements of
  $`\mathbf{x}_n` are octet strings $`\mathcal{E}_2(\mathbf{r}_c) \frown \mathcal{H}(\mathbf{r})`, and the model orders them lexicographically. Since $`\mathcal{E}_2` is
  little-endian, this is not core order.
* *Hashes of items (note v0.8.1-A9).* $`\mathcal{H}(\mathbf{r})` and $`\mathcal{H}(\mathbf{H})` are read as $`\mathcal{H}(\mathcal{E}(\mathbf{r}))` and $`\mathcal{H}(\mathcal{E}(\mathbf{H}))`.
* *Negative judgments in later tranches (note v0.8.1-A10).* The prose says a validator that has seen a
  negative judgment must always judge the report, but (17.15) has only the no-show condition. The
  model gives both: {api}`JAM.Auditing.laterTranche` is the equation, and
  {api}`JAM.Auditing.laterTrancheWithNegatives` adds the prose rule.
* *The validator's own tranche-0 audits (note v0.8.1-A10).* The line that would put the validator in
  $`A_0(\mathbf{r})` for its own tranche-0 reports is commented out in the paper's source. In the model $`A_n` is an
  input, which a validator fills from the verified announcements, its own included.
* *One third (note v0.8.1-A11).* The overview ban-lists a block when *more than* $`\tfrac{1}{3}` of the
  validators judge a report invalid; the best-block paragraph disregards chains with a report *at
  least* $`\tfrac{1}{3}` judge invalid. {api}`JAM.Auditing.disregarded` follows the latter: $`3 \cdot |J_\bot(\mathbf{r})| \ge |\kappa|`.
* *Active cores (note v0.8.1-A12).* $`\mathbf{q}` has $`|\kappa|/3` entries while $`\rho` has $`\mathsf{C}`. The two are equal for the
  full and tiny chains; the model reads $`\rho` at the indices below $`|\kappa|/3`, missing entries as $`\emptyset`.
* *A wall clock before the slot (note v0.8.1-A12).* $`\mathcal{T} - \mathsf{P}\cdot\mathbf{H}_T` is negative before the slot starts; the model
  subtracts in natural numbers, so that time counts as tranche 0.
* *The choice of verdict (note v0.8.1-A12).* When several verdicts are possible the paper does not say
  which to form; {api}`JAM.Auditing.formVerdict` tries good, then bad, then wonky.
