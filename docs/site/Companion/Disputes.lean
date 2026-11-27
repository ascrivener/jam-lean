import VersoManual
import Companion.Source
import Companion.Paper
import Companion.Docstring
import JAM.Disputes
import JAM.Theorems.Auditing

open Verso.Genre Manual
open Companion
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "§10 Disputes, verdicts and judgments" =>
%%%
tag := "disputes"
shortTitle := "§10 Disputes"
file := "disputes"
%%%

*In the paper:* {gpchapter}`sec:disputes`.

The disputes system records *verdicts*, collections of judgments by validators on whether a
work-report is valid, and *offences*: guarantees or judgments that contradict an established
verdict. A verdict that is not positive also removes the report from the pipeline before it is
accumulated. In the model, the whole of §10 of GP v0.8.1 is one function,
{api}`JAM.disputesTransition`. It checks the disputes extrinsic against the prior state and
returns the posterior disputes state $`\psi'`, the cleared availability assignments $`\rho^\dagger`
and the offenders marker $`\mathbf{H}_O`.

The module is `JAM/Disputes.lean`; its full API is on the
[doc-gen4 page](https://ascrivener.github.io/jam-lean/api/JAM/Disputes.html).

Below, $`[x \in \mathbf{s} \wr\wr k]` stands for the paper's "$`\mathbf{s}`, ordered by $`k` and without duplicates"
(§3.7), and $`\mathbf{a} \mathbin{\downharpoonleft} \mathbf{b}` for "disjoint from" (the paper's sign, `\downspoon`, has no KaTeX
equivalent). As in the paper, $`\left\lgroup\dots\right\rgroup` encloses the members of a tuple type and $`(\dots)` a tuple of values.

# The state (§10.1)
%%%
tag := "disputes-state"
%%%

$$`\psi \equiv (\psi_G, \psi_B, \psi_W, \psi_O) \qquad \text{(10.1)}`

The good-set $`\psi_G`, the bad-set $`\psi_B` and the wonky-set $`\psi_W` hold the hashes of
work-reports judged correct, incorrect, or impossible to judge. The punish-set $`\psi_O` holds the
Ed25519 keys of validators found to have misjudged a report.

{leanSource JAM.DisputesState}

# The extrinsic (§10.2)
%%%
tag := "disputes-extrinsic"
%%%

The disputes extrinsic has three parts: verdicts $`\mathbf{E}_V`, culprits $`\mathbf{E}_C` (guarantors of a report
found invalid) and faults $`\mathbf{E}_F` (judges who contradicted a verdict):

$$`\begin{aligned} \mathbf{E}_D &\equiv \left\lgroup \mathbf{E}_V, \mathbf{E}_C, \mathbf{E}_F \right\rgroup \\ \text{where } \mathbf{E}_V &\in \llbracket\left\lgroup\mathbb{H}, \left\lfloor\frac{\tau}{\mathsf{E}}\right\rfloor - \mathbb{N}_2, \llbracket\left\lgroup\{\top, \bot\}, \mathbb{N}, \bar{\mathbb{V}}\right\rgroup\rrbracket\right\rgroup\rrbracket_{:\mathsf{N}_V} \\ \text{and } \mathbf{E}_C &\in \llbracket\left\lgroup\mathbb{H}, \bar{\mathbb{H}}, \bar{\mathbb{V}}\right\rgroup\rrbracket_{:\mathsf{N}_O} \\ \text{and } \mathbf{E}_F &\in \llbracket\left\lgroup\mathbb{H}, \{\top, \bot\}, \bar{\mathbb{H}}, \bar{\mathbb{V}}\right\rgroup\rrbracket_{:\mathsf{N}_O} \end{aligned} \qquad \text{(10.2)}`

The model's types are {api}`JAM.Disputes`, {api}`JAM.Verdict` (with its judgments,
{api}`JAM.Judgment`), {api}`JAM.Culprit` and {api}`JAM.Fault`. {api}`JAM.disputesTransition` checks
the length bounds first ($`\mathsf{N}_V = \mathsf{N}_O = 16`, `Constants.Cmaxextrinsicverdicts` and
`Constants.Cmaxextrinsicoffenses`); see the readings below for the errors it uses.

## Verdicts

Each verdict names the epoch whose validator set judged it: the current one ($`\kappa`) or the
previous one ($`\lambda`). It must carry exactly $`\lfloor 2/3 |\mathbf{k}| \rfloor + 1` judgments, each signed by the
judge it names:

$$`K(a) \equiv \begin{cases} \kappa & \text{if } a = \left\lfloor \dfrac{\tau}{\mathsf{E}} \right\rfloor \\ \lambda & \text{otherwise} \end{cases} \qquad \text{(10.3)}`

$$`\forall (r, a, \mathbf{j}) \in \mathbf{E}_V : \bigwedge \begin{cases} |\mathbf{j}| = \lfloor 2/3 |\mathbf{k}| \rfloor + 1 \,, \\ \forall (v, i, s) \in \mathbf{j} : \\ \quad i < |\mathbf{k}| \wedge s \in \bar{\mathbb{V}}_{\mathbf{k}[i]_e}\langle \mathsf{X}_v \frown r \rangle \end{cases} \quad \text{where } \mathbf{k} = K(a) \qquad \text{(10.4)}`

$$`\mathsf{X}_\top \equiv \texttt{\$jam\_valid} \,,\ \mathsf{X}_\bot \equiv \texttt{\$jam\_invalid} \qquad \text{(10.5)}`

Verdicts are ordered by report hash, judgments by validator index, without duplicates, and no
verdict may be about a report already judged:

$$`\mathbf{E}_V = [(r, a, \mathbf{j}) \in \mathbf{E}_V \wr\wr r] \qquad \text{(10.8)}`

$$`\{ r \mid (r, a, \mathbf{j}) \in \mathbf{E}_V \} \mathbin{\downharpoonleft} \psi_G \cup \psi_B \cup \psi_W \qquad \text{(10.10)}`

$$`\forall (r, a, \mathbf{j}) \in \mathbf{E}_V : \mathbf{j} = [(v, i, s) \in \mathbf{j} \wr\wr i] \qquad \text{(10.11)}`

In the model, $`K` is {api}`JAM.judgeKeys`, with $`\kappa` and $`\lambda` entering only through their Ed25519
keys. The type $`\lfloor \tau/\mathsf{E} \rfloor - \mathbb{N}_2` of $`a` becomes the condition $`a = e \vee a + 1 = e`. The other conditions of
(10.4), (10.10) and (10.11) for one verdict are {api}`JAM.checkVerdict`, which also returns the
verdict's outcome:

{leanSource JAM.judgeKeys}

{leanSource JAM.checkVerdict}

{api}`JAM.Xvalidif` gives $`\mathsf{X}_v`. The order of (10.8) is checked first in
{api}`JAM.disputesTransition`, by {api}`JAM.orderedUniqBy`.

## The verdict sequence v (eq. 10.12)
%%%
tag := "disputes-verdicts"
%%%

Each verdict's outcome is fixed by its number of positive judgments $`t`: exactly two-thirds plus one
is good, zero is bad, and one third is wonky. No other count is allowed:

$$`\begin{aligned} \mathbf{v} &\in \llbracket (\mathbb{H}, \{\top, \bot, \emptyset\}) \rrbracket \\ \mathbf{v} &\equiv [(r, V(a, \mathbf{j})) \mid (r, a, \mathbf{j}) \mathrel{<\!\!\!-} \mathbf{E}_V] \\ V(a, \mathbf{j}) &\equiv \begin{cases} \top & \text{if } t = \lfloor 2/3 |\mathbf{k}| \rfloor + 1 \\ \bot & \text{if } t = 0 \\ \emptyset & \text{if } t = \lfloor 1/3 |\mathbf{k}| \rfloor \end{cases} \\ \text{where } t &= \sum_{(v, i, s) \in \mathbf{j}} v \\ \text{and } \mathbf{k} &= K(a) \end{aligned} \qquad \text{(10.12)}`

$`V` is {api}`JAM.verdictOutcome`. It returns `none` where the paper's $`V` is undefined, and
{api}`JAM.checkVerdict` rejects such a verdict:

{leanSource JAM.verdictOutcome}

The good-verdict count is the supermajority that §17's auditing uses: of `V` validators, `t` positive
judgments are more than two thirds ($`3t > 2V`) exactly when there are at least $`\lfloor 2V/3 \rfloor + 1` of them.
In the theorem `V` is the validator count and `t` the number of positive judgments; `V` is not the
function $`V` of (10.12).

{mathdoc JAM.Auditing.supermajority_iff_verdictGood}

# Culprits and faults
%%%
tag := "disputes-offences"
%%%

A culprit is a guarantor of a report now in the bad-set; a fault is a judgment whose validity
contradicts the verdict. Neither may name a key already punished:

$$`\forall (r, f, s) \in \mathbf{E}_C : \bigwedge \begin{cases} r \in \psi'_B \,, \\ f \in \mathbf{k} \,, \\ s \in \bar{\mathbb{V}}_f\langle \mathsf{X}_G \frown r \rangle \end{cases} \qquad \text{(10.6)}`

$$`\forall (r, v, f, s) \in \mathbf{E}_F : \bigwedge \begin{cases} r \in \psi'_B \Leftrightarrow r \notin \psi'_G \Leftrightarrow v \,, \\ f \in \mathbf{k} \,, \\ s \in \bar{\mathbb{V}}_f\langle \mathsf{X}_v \frown r \rangle \end{cases} \qquad \text{(10.7)}`

$$`\text{where } \mathbf{k} = \{ i_e \mid i \in \lambda \cup \kappa \} \setminus \psi_O`

$$`\mathbf{E}_C = [(r, f, s) \in \mathbf{E}_C \wr\wr f] \,,\ \mathbf{E}_F = [(r, v, f, s) \in \mathbf{E}_F \wr\wr f] \qquad \text{(10.9)}`

Every good verdict must come with at least one fault for its report:

$$`\forall (r, \top) \in \mathbf{v} : \exists (r, \dots) \in \mathbf{E}_F \qquad \text{(10.13)}`

These checks are the culprit, fault and good-verdict loops of {api}`JAM.disputesTransition`,
shown in full {ref "disputes-transition"}[below]. $`\mathsf{X}_G` (`$jam_guarantee`, eq. (11.28)) is
{api}`JAM.Xguarantee`.

# Clearing the availability assignments (eq. 10.14)
%%%
tag := "disputes-clear"
%%%

A core whose pending report has a bad or wonky verdict is cleared, so the report is not
accumulated:

$$`\forall c \in \mathbb{N}_{\mathsf{C}} : \rho^\dagger[c] = \begin{cases} \emptyset & \text{if } \left(\mathcal{H}\left((\rho[c]_{\mathbf{g}})_{\mathbf{r}}\right), v\right) \in \mathbf{v}, v \in \{\bot, \emptyset\} \\ \rho[c] & \text{otherwise} \end{cases} \qquad \text{(10.14)}`

The report is hashed through its encoding, as $`\mathcal{H}` applies to the codec's output (§3.8):

{leanSource JAM.clearNonPositive}

# The posterior state (eqs. 10.15–10.18)
%%%
tag := "disputes-posterior"
%%%

$$`\begin{aligned} \psi'_G &\equiv \psi_G \cup \{ r \mid (r, \top) \in \mathbf{v} \} & \text{(10.15)} \\ \psi'_B &\equiv \psi_B \cup \{ r \mid (r, \bot) \in \mathbf{v} \} & \text{(10.16)} \\ \psi'_W &\equiv \psi_W \cup \{ r \mid (r, \emptyset) \in \mathbf{v} \} & \text{(10.17)} \\ \psi'_O &\equiv \psi_O \cup \{ f \mid (f, \dots) \in \mathbf{E}_C \} \cup \{ f \mid (f, \dots) \in \mathbf{E}_F \} & \text{(10.18)} \end{aligned}`

The first three are {api}`JAM.assimilate`:

{leanSource JAM.assimilate}

$`\psi'_O` is built at the end of {api}`JAM.disputesTransition`, from the same keys as the marker below.

# The offenders marker (§10.3)
%%%
tag := "disputes-header"
%%%

$$`\mathbf{H}_O \equiv [f \mid (f, \dots) \mathrel{<\!\!\!-} \mathbf{E}_C] \frown [f \mid (f, \dots) \mathrel{<\!\!\!-} \mathbf{E}_F] \qquad \text{(10.19)}`

This is `mark` in {api}`JAM.disputesTransition`, returned as `offendersMark`
({api}`JAM.DisputesOutput`).

# The transition
%%%
tag := "disputes-transition"
%%%

{leanSource JAM.disputesTransition}

No theorems about the disputes transition itself are proved yet. It is run against the GP v0.8.0
disputes test vectors. Ed25519 verification is a parameter of the model; in those runs it is
replaced by an oracle that rejects every signature exactly when a vector expects a bad signature,
so the vectors check where the model looks for one, not the signatures themselves.

# Readings chosen
%%%
tag := "disputes-readings"
%%%

The first two points are note 29, and the others the notes they name, in the model's
[notes on the paper](https://github.com/ascrivener/jam-lean/blob/main/docs/upstream-candidates.md#gray-paper-issues):

* *The fault condition.* $`r \in \psi'_B \Leftrightarrow r \notin \psi'_G \Leftrightarrow v` can be read as a chain of two
  equivalences or as $`((r \in \psi'_B \Leftrightarrow r \notin \psi'_G) \Leftrightarrow v)`. The second reading would accept a fault
  with $`v = \top` on a report with a good verdict. The model reads a chain.
* *Errors and their order.* The paper names no errors for an invalid disputes extrinsic and gives
  no order between its conditions. The model uses the test vectors' error names
  ({api}`JAM.DisputesError`). It checks the length bounds of (10.2) first, then each part's order
  before the conditions on its elements: the order of the verdicts (10.8); then, for each verdict, its epoch index (the type
  $`\lfloor \tau/\mathsf{E} \rfloor - \mathbb{N}_2` of (10.2)), the order of its judgments (10.11), their number and
  each judge's index and signature (10.4), that its report is not already judged (10.10), and that
  $`V` is defined (10.12); then the order of the culprits (10.9) and, for each culprit, the
  conditions of (10.6); then the order of the faults (10.9) and, for each fault, the conditions of
  (10.7); and last (10.13). A key outside $`\mathbf{k}` is reported as already an offender when it is
  in $`\psi_O`, and as an unknown guarantor or auditor otherwise.
* *Note v0.8.1-A54, the length bounds.* No error is named for a disputes extrinsic longer than
  (10.2) allows, and no test vector has one. The model uses its own names: `tooManyVerdicts`,
  `tooManyCulprits` and `tooManyFaults` ({api}`JAM.DisputesError`).
* *Note v0.8.1-A50, overlapping cases of V.* When $`|\mathbf{k}| < 3`, $`\lfloor 1/3 |\mathbf{k}| \rfloor = 0`, so the cases $`\bot` and
  $`\emptyset` of (10.12) both apply at $`t = 0`. {api}`JAM.verdictOutcome` takes $`\bot`. The full and tiny
  chains have $`|\mathbf{k}| = 1023` and $`6`, and every validator count in the paper is a multiple of 3 of at least 6
  (eq. (6.8)), so the cases never overlap there.
* *Note v0.8.1-A7, context strings.* The paper's wording leaves open whether the `$` of
  `$jam_valid`, `$jam_invalid` and `$jam_guarantee` is an octet of the signed message. The note
  records that every signature in the v0.8.0 test vectors verifies only without it. That was
  checked outside the disputes test runs, which replace signature checks by an oracle (see
  {ref "disputes-transition"}[above]). The model drops the `$` ({api}`JAM.contextString`).
