import VersoManual
import Companion.Source
import Companion.Paper
import Companion.Docstring
import JAM.Reports

open Verso.Genre Manual
open Companion
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "§11 Reporting and Assurance" =>
%%%
tag := "reports"
shortTitle := "§11 Reports"
file := "reports"
%%%

*In the paper:* {gpchapter}`sec:reporting`.

A work-report enters the chain in a *guarantee*, signed by two or three validators assigned to its
core. It waits on that core, as the core's *availability assignment*, until more than two thirds of
the validators *assure* that its data is available, or until it times out. Within a block the paper
processes assurances first and guarantees second, so §11 of GP v0.8.1 gives two transitions on the
assignments $`\rho`:

* assurances (§11.2) take $`\rho^\dagger`, left by the disputes of {ref "disputes"}[§10], to $`\rho^\ddagger`, and give the newly
  available reports $`\mathbf{R}`. In the model this is {api}`JAM.assurances`;
* guarantees (§11.3–§11.5) take $`\rho^\ddagger` to $`\rho'`, and give the reporters set $`\mathbf{G}`. In the model
  this is {api}`JAM.guarantees`.

The modules are `JAM/Assurances.lean` and `JAM/Reports.lean`; their full API is on the doc-gen4
pages for [Assurances](https://ascrivener.github.io/jam-lean/api/JAM/Assurances.html) and
[Reports](https://ascrivener.github.io/jam-lean/api/JAM/Reports.html).

As in the {ref "disputes"}[§10 chapter], $`[x \in \mathbf{s} \wr\wr k]` stands for the paper's "$`\mathbf{s}`, ordered by
$`k` and without duplicates" (§3.7).

# The state (§11.1)
%%%
tag := "reports-state"
%%%

$$`\rho \in \llbracket \left\lgroup \mathbf{g} \in \mathbb{G}, t \in \mathbb{N}_T \right\rgroup? \rrbracket_{\mathsf{C}} \qquad \text{(11.1)}`

An entry is a guarantee and the timeslot at which it was reported. The model's entry is
{api}`JAM.AvailAssignment`, and $`\rho` is {api}`JAM.AvailAssignments`.

{leanSource JAM.AvailAssignment}

{leanSource JAM.AvailAssignments}

§11.1 goes on to define the work-report and its parts: the report $`\mathbb{R}` (eq. (11.2)), the
refinement context $`\mathbb{C}` (eq. (11.4)), the availability specification $`\mathbb{Y}` (eq. (11.5)), the
work-digest $`\mathbb{D}` (eq. (11.6)) and the work errors $`\mathbb{E}` (eq. (11.7)). The model's types are
{api}`JAM.WorkReport`, {api}`JAM.RefineContext`, {api}`JAM.AvailabilitySpec`,
{api}`JAM.WorkDigest` and {api}`JAM.WorkError`. It also bounds a report's dependencies and size:

{leanSource JAM.WorkReport}

{leanSource JAM.RefineContext}

{leanSource JAM.AvailabilitySpec}

{leanSource JAM.WorkDigest}

$$`\forall \mathbf{r} \in \mathbb{R} : |\mathbf{r}_\mathbf{l}| + |(\mathbf{r}_\mathbf{c})_\mathbf{p}| \le \mathsf{J} \qquad \text{(11.3)}`

$$`\forall \mathbf{r} \in \mathbb{R} : |\mathbf{r}_\mathbf{t}| + \sum_{i=0}^{i<|\mathbf{r}_\mathbf{d}|} L(\mathbf{r}_\mathbf{d}[i]_\mathbf{l}) \le \mathsf{W}_R \qquad \text{(11.8)}`

$$`L(\mathbf{l} \in \mathbb{B} \cup \mathbb{E}) \equiv \begin{cases} |\mathbf{l}| & \text{if } \mathbf{l} \in \mathbb{B} \\ 0 & \text{otherwise} \end{cases} \qquad \text{(11.9)} \qquad \mathsf{W}_R \equiv 48 \cdot 2^{10} \qquad \text{(11.10)}`

With the bound $`1 \le |\mathbf{r}_\mathbf{d}| \le \mathsf{I}` from the type $`\mathbf{d} \in \llbracket \mathbb{D} \rrbracket_{1:\mathsf{I}}` in (11.2), these are
{api}`JAM.checkReportShape`, which {api}`JAM.guarantees` applies to each incoming report:

{leanSource JAM.checkReportShape}

{leanSource JAM.resultSize}

# Assurances (§11.2)
%%%
tag := "reports-assurances"
%%%

## The assurances extrinsic

Each assurance is a bitstring with one bit per core, the assuring validator's index and its
signature. Assurances are ordered by validator index, without duplicates:

$$`\mathbf{E}_A \in \llbracket \left\lgroup f \in \text{𝕓}_{\mathsf{C}},\, v \in \mathbb{N}_{|\kappa|},\, s \in \bar{\mathbb{V}} \right\rgroup \rrbracket \qquad \text{(11.11)}`

$$`\mathbf{E}_A = [a \in \mathbf{E}_A \wr\wr a_v] \qquad \text{(11.12)}`

The signature covers the parent header hash and the bitstring, and a bit may be set only on a core
with an assignment:

$$`\forall a \in \mathbf{E}_A : a_s \in \bar{\mathbb{V}}_{\kappa[a_v]_e}\langle \mathsf{X}_A \frown \mathcal{H}(\mathcal{E}(\mathbf{H}_P, a_f)) \rangle \qquad \text{(11.13)}`

$$`\mathsf{X}_A \equiv \texttt{\$jam\_available} \qquad \text{(11.14)}`

$$`\forall a \in \mathbf{E}_A, c \in \mathbb{N}_{\mathsf{C}} : \quad a_f[c] \Rightarrow \rho^\dagger[c] \ne \emptyset \qquad \text{(11.15)}`

The model's assurance is {api}`JAM.Assurance`. {api}`JAM.checkAssurance` checks one assurance
against the index of the one before it:

{leanSource JAM.Assurance}

{leanSource JAM.assuranceMessage}

{leanSource JAM.checkAssurance}

## Available reports and ρ‡

A report becomes available when more than two thirds of the validators set its core's bit.
$`\rho^\ddagger` is $`\rho^\dagger` with the cores of available reports cleared, together with those that timed out, and all
of them when the size of the validator set changes:

$$`\mathbf{R} \equiv \left[ (\rho^\dagger[c]_\mathbf{g})_\mathbf{r} \;\middle|\; c \mathrel{<\!\!\!-} \mathbb{N}_{\mathsf{C}},\; \sum_{a \in \mathbf{E}_A} a_f[c] > \tfrac{2}{3} |\kappa| \right] \qquad \text{(11.16)}`

$$`\forall c \in \mathbb{N}_{\mathsf{C}} : \rho^\ddagger[c] \equiv \begin{cases} \emptyset & \text{if } p = \emptyset \vee (p_\mathbf{g})_\mathbf{r} \in \mathbf{R} \vee {} \\ & \phantom{\text{if }} \mathbf{H}_T \ge p_t + \mathsf{U} \vee |\kappa| \ne |\kappa'| \\ p & \text{otherwise} \end{cases} \quad \text{where } p = \rho^\dagger[c] \qquad \text{(11.17)}`

Both are in {api}`JAM.assurances`: `available` is the threshold of (11.16), written
$`3 \cdot \text{count} > 2|\kappa|`, and `ρ'` is $`\rho^\ddagger`:

{leanSource JAM.assurances}

# Guarantor assignments (§11.3)
%%%
tag := "reports-assignments"
%%%

Of the $`\mathsf{C} = 341` cores, only the first $`|\kappa'|/3` are active, and each active core has three validators
assigned to it. $`\mathbf{M}` gives each validator's core and key:

$$`\mathbf{M} \in \left\lgroup \llbracket \mathbb{N}_{\mathsf{C}} \rrbracket_{|\kappa'|}, \llbracket \mathbb{K} \rrbracket_{|\kappa'|} \right\rgroup \qquad \text{(11.18)}`

The cores come from a shuffle with the epochal entropy $`\eta'_2`, rotated every $`\mathsf{R}` slots:

$$`R(\mathbf{c}, n) \equiv \left[ (x + n) \bmod \frac{|\mathbf{c}|}{3} \;\middle|\; x \mathrel{<\!\!\!-} \mathbf{c} \right] \qquad \text{(11.19)}`

$$`P(v, e, t) \equiv R\left( \mathcal{F}\left( \left[ \left\lfloor \frac{i}{3} \right\rfloor \;\middle|\; i \mathrel{<\!\!\!-} \mathbb{N}_v \right], e \right), \left\lfloor \frac{t \bmod \mathsf{E}}{\mathsf{R}} \right\rfloor \right) \qquad \text{(11.20)}`

$$`\mathbf{M} \equiv \left( P(|\kappa'|, \eta'_2, \tau'), \Phi(\kappa') \right) \qquad \text{(11.21)}`

$`\mathcal{F}` is the shuffle of Appendix F ({ref "shuffle"}[chapter]). $`\Phi` (eq. (6.16)) replaces
the key of each validator in the punish-set $`\psi'_O` by the null key $`\mathbb{K}_0` (eq. (6.14)), whose
Ed25519 part is $`[2, 0, 0, \dots]`. In the model, which reads only the Ed25519 keys here, $`\Phi` is
{api}`JAM.blacklist` and the null Ed25519 key is {api}`JAM.nullEdKey`:

{leanSource JAM.rotate}

{leanSource JAM.permute}

{leanSource JAM.blacklist}

{leanSource JAM.assignments}

$`\mathbf{M}^*` is $`\mathbf{M}` as it was under the previous rotation, with the previous epoch's keys and entropy if
that rotation was in the previous epoch:

$$`\begin{aligned} \text{let } (\mathbf{k}, e) &= \begin{cases} (\kappa', \eta'_2) & \text{if } \left\lfloor \dfrac{\tau' - \mathsf{R}}{\mathsf{E}} \right\rfloor = \left\lfloor \dfrac{\tau'}{\mathsf{E}} \right\rfloor \\ (\lambda', \eta'_3) & \text{otherwise} \end{cases} \\ \mathbf{M}^* &\equiv \left( P(|\mathbf{k}|, e, \tau' - \mathsf{R}), \Phi(\mathbf{k}) \right) \end{aligned} \qquad \text{(11.22)}`

{leanSource JAM.priorAssignments}

# Guarantees (§11.4)
%%%
tag := "reports-guarantees"
%%%

A guarantee is a work-report, the timeslot at which it was guaranteed and a credential of two or
three signatures. The extrinsic holds at most one guarantee per core, in core order:

$$`\mathbb{G} \equiv \left\lgroup \mathbf{r} \in \mathbb{R}, t \in \mathbb{N}_T, a \in \llbracket \left\lgroup \mathbb{N}, \bar{\mathbb{V}} \right\rgroup \rrbracket_{2:3} \right\rgroup \qquad \text{(11.23)}`

$$`\mathbf{E}_G \in \llbracket \mathbb{G} \rrbracket_{:\mathsf{C}} \qquad \text{(11.24)} \qquad \mathbf{E}_G = [\mathbf{g} \in \mathbf{E}_G \wr\wr (\mathbf{g}_\mathbf{r})_c] \qquad \text{(11.25)}`

$$`\forall g \in \mathbf{E}_G : g_a = [(v, s) \in g_a \wr\wr v] \qquad \text{(11.26)}`

Each signer must be assigned to the report's core, under $`\mathbf{M}` if $`t` is in the current rotation and under
$`\mathbf{M}^*` if it is in the previous one, and the core must be active now. The signers' Ed25519 keys form
the reporters set $`\mathbf{G}`, which the validator statistics of {ref "statistics"}[§13] read:

$$`\begin{aligned} &\forall (\mathbf{r}, t, a) \in \mathbf{E}_G, \forall (v, s) \in a : \begin{cases} v < |\mathbf{k}| \wedge \mathbf{c}_v = \mathbf{r}_c < \dfrac{|\kappa'|}{3} \\ s \in \bar{\mathbb{V}}_{(\mathbf{k}_v)_e}\langle \mathsf{X}_G \frown \mathcal{H}(\mathbf{r}) \rangle \\ \mathsf{R}(\lfloor \tau'/\mathsf{R} \rfloor - 1) \le t \le \tau' \end{cases} \\ &k \in \mathbf{G} \Leftrightarrow \exists (\mathbf{r}, t, a) \in \mathbf{E}_G, \exists (v, s) \in a : k = (\mathbf{k}_v)_e \\ &\quad \text{where } (\mathbf{c}, \mathbf{k}) = \begin{cases} \mathbf{M} & \text{if } \left\lfloor \dfrac{\tau'}{\mathsf{R}} \right\rfloor = \left\lfloor \dfrac{t}{\mathsf{R}} \right\rfloor \\ \mathbf{M}^* & \text{otherwise} \end{cases} \end{aligned} \qquad \text{(11.27)}`

$$`\mathsf{X}_G \equiv \texttt{\$jam\_guarantee} \qquad \text{(11.28)}`

{api}`JAM.checkGuarantee` checks one guarantee and returns its signers' keys, from which
{api}`JAM.guarantees` builds $`\mathbf{G}`. A signer whose key $`\Phi` replaced by the null key is rejected before its
signature is checked, since no signature is valid under that key:

{leanSource JAM.checkGuarantee}

The incoming reports $`\mathbf{I}` must give the right number of erasure-coded chunks, land on a core with no
assignment in $`\rho^\ddagger`, be authorized by the core's pool $`\alpha`, and respect the gas limits:

$$`\text{let } \mathbf{I} = \{ \mathbf{g}_\mathbf{r} \mid \mathbf{g} \in \mathbf{E}_G \} \qquad \text{(11.29)}`

$$`\forall \mathbf{r} \in \mathbf{I} : (\mathbf{r}_\mathbf{s})_v = |\kappa'| \qquad \text{(11.30)}`

$$`\forall \mathbf{r} \in \mathbf{I} : \rho^\ddagger[\mathbf{r}_c] = \emptyset \wedge \mathbf{r}_a \in \alpha[\mathbf{r}_c] \qquad \text{(11.31)}`

$$`\forall \mathbf{r} \in \mathbf{I} : \sum_{\mathbf{d} \in \mathbf{r}_\mathbf{d}} (\mathbf{d}_g) \le \mathsf{G}_A \ \wedge\ \forall \mathbf{d} \in \mathbf{r}_\mathbf{d} : \mathbf{d}_g \ge \delta[\mathbf{d}_s]_g \qquad \text{(11.32)}`

Each report must also stay within the limits applied to every work-package. v0.8.1 adds these
conditions (GP #563):

$$`\forall \mathbf{r} \in \mathbf{I} : \bigwedge \begin{cases} \sum_{\mathbf{d} \in \mathbf{r}_\mathbf{d}} (\mathbf{d}_u) \le \mathsf{G}_R \\ \sum_{\mathbf{d} \in \mathbf{r}_\mathbf{d}} (\mathbf{d}_i) \le \mathsf{W}_M \\ (\mathbf{r}_\mathbf{s})_n = \sum_{\mathbf{d} \in \mathbf{r}_\mathbf{d}} (\mathbf{d}_e) \le \mathsf{W}_X \\ \sum_{\mathbf{d} \in \mathbf{r}_\mathbf{d}} (\mathbf{d}_x) \le \mathsf{T} \\ \sum_{\mathbf{d} \in \mathbf{r}_\mathbf{d}} (\mathbf{d}_z + \mathbf{d}_i \cdot \mathsf{W}_F) \le \mathsf{W}_I \\ (\mathbf{r}_\mathbf{s})_l \le \mathsf{W}_B \\ \mathbf{r}_g \le \mathsf{G}_I \end{cases} \qquad \text{(11.33)}`

{leanSource JAM.checkReportLoad}

## Contextual validity (§11.4.1)
%%%
tag := "reports-context"
%%%

$`\mathbf{x}` and $`\mathbf{p}` are the contexts and the work-package hashes of the incoming reports. No package may be
reported twice:

$$`\text{let } \mathbf{x} \equiv \{ \mathbf{r}_\mathbf{c} \mid \mathbf{r} \in \mathbf{I} \} ,\quad \mathbf{p} \equiv \{ (\mathbf{r}_\mathbf{s})_p \mid \mathbf{r} \in \mathbf{I} \} \qquad \text{(11.34)} \qquad |\mathbf{p}| = |\mathbf{I}| \qquad \text{(11.35)}`

Each anchor must be a recent block, with matching details; each lookup-anchor must be at most $`\mathsf{L}`
slots old and in the ancestor set $`\mathbf{A}` of the last $`\mathsf{L}` headers:

$$`\forall x \in \mathbf{x} : \exists y \in \beta^\dagger_H : x_a = y_h \wedge x_s = y_s \wedge x_b = y_b \wedge x_n = y_t \qquad \text{(11.36)}`

$$`\forall x \in \mathbf{x} :\ x_t \ge \mathbf{H}_T - \mathsf{L} \qquad \text{(11.37)}`

$$`\forall x \in \mathbf{x} : \exists h, h' \in \mathbf{A} : \bigwedge \begin{cases} h_T = x_t \\ \mathcal{H}(h) = x_l \\ h'_P = \mathcal{H}(h) \\ h'_R = x_r \end{cases} \qquad \text{(11.38)}`

{leanSource JAM.checkAnchor}

The ancestor set is not part of the state, so the model takes the condition of (11.38) as an input,
`lookupAnchorKnown` of {api}`JAM.ReportsInput`.

A package already in the pipeline may not be reported again: not one reported in recent history
$`\beta_H`, accumulated in $`\xi`, waiting in the ready queue $`\omega`, or assigned in $`\rho`:

$$`\text{let } \mathbf{q} = \{ (\mathbf{r}_\mathbf{s})_p \mid (\mathbf{r}, \mathbf{d}) \in \overgroup{\omega} \} \qquad \text{(11.39)}`

$$`\text{let } \mathbf{a} = \{ (((\mathbf{a}_\mathbf{g})_\mathbf{r})_\mathbf{s})_p \mid \mathbf{a} \in \rho, \mathbf{a} \ne \emptyset \} \qquad \text{(11.40)}`

$$`\forall p \in \mathbf{p}, p \notin \bigcup_{x \in \beta_H} \mathcal{K}(x_\mathbf{p}) \cup \bigcup_{x \in \xi} x \cup \mathbf{q} \cup \mathbf{a} \qquad \text{(11.41)}`

These sets are also not in the state {api}`JAM.guarantees` reads. Their union is computed by
{api}`JAM.knownPackages` and passed in as `known`:

{leanSource JAM.knownPackages}

Prerequisites and segment-root lookups must name packages in the extrinsic or in recent history,
with the right segment roots:

$$`\begin{aligned} &\forall \mathbf{r} \in \mathbf{I}, \forall p \in (\mathbf{r}_\mathbf{c})_\mathbf{p} \cup \mathcal{K}(\mathbf{r}_\mathbf{l}) : \\ &\quad p \in \mathbf{p} \cup \{ x \mid x \in \mathcal{K}(b_\mathbf{p}),\, b \in \beta_H \} \end{aligned} \qquad \text{(11.42)}`

$$`\text{let } \mathbf{p} = \{ (((g_\mathbf{r})_\mathbf{s})_p \mapsto ((g_\mathbf{r})_\mathbf{s})_e) \mid g \in \mathbf{E}_G \} \qquad \text{(11.43)}`

$$`\forall \mathbf{r} \in \mathbf{I} : \mathbf{r}_\mathbf{l} \subseteq \mathbf{p} \cup \bigcup_{b \in \beta_H} b_\mathbf{p} \qquad \text{(11.44)}`

Finally, each digest must name its service's current code hash:

$$`\forall \mathbf{r} \in \mathbf{I}, \forall \mathbf{d} \in \mathbf{r}_\mathbf{d} : \mathbf{d}_c = \delta[\mathbf{d}_s]_c \qquad \text{(11.45)}`

# The posterior assignments (§11.5)
%%%
tag := "reports-posterior"
%%%

Each core with a new guarantee takes it, stamped with the current time; the others keep their
entry in $`\rho^\ddagger`:

$$`\forall c \in \mathbb{N}_{\mathsf{C}} : \rho'[c] \equiv \begin{cases} (\mathbf{g},\, t \mathrel{\substack{\scriptscriptstyle\blacktriangleright \\ \scriptscriptstyle\blacktriangleright}} \tau') & \text{if } \exists \mathbf{g} \in \mathbf{E}_G, (\mathbf{g}_\mathbf{r})_c = c \\ \rho^\ddagger[c] & \text{otherwise} \end{cases} \qquad \text{(11.46)}`

This is the `ρ'` binding at the end of {api}`JAM.guarantees`, which also carries out every check
of §11.4, in the order given in its docstring:

{leanSource JAM.guarantees}

# Theorems

No theorems about the assurances or guarantees transitions are proved yet. The functions are run
against test vectors:

* the assurances vectors of davxy/jam-test-vectors v0.8.0. v0.8.1 drops the assurance's anchor
  (GP #562), so the one vector whose only fault is its anchor is listed as an expected deviation:
  the model accepts it (its name is given below);
* the reports vectors of davxy/jam-test-vectors master at commit 5e8d2a2, later than v0.8.0, which
  adds vectors for (11.33). They carry no ancestor set, so the runs take `lookupAnchorKnown` to hold
  for every context, and the ancestry condition of (11.38) is not exercised.

The assurances vector listed as an expected deviation is
`assurance_with_bad_attestation_parent`.

Ed25519 verification is a parameter of the model; in those runs it is
replaced by an oracle that rejects every signature exactly when a vector expects a bad signature,
so the vectors check where the model looks for one, not the signatures themselves.

# Readings chosen
%%%
tag := "reports-readings"
%%%

These points are recorded, under the note numbers given, in the model's
[notes on the paper](https://github.com/ascrivener/jam-lean/blob/main/docs/upstream-candidates.md#gray-paper-issues):

* *Note 30, errors and order for assurances.* No errors are named for an invalid $`\mathbf{E}_A`, and no
  order is given between its conditions. The model uses the test vectors' names
  ({api}`JAM.AssurancesError`) and checks each assurance in turn: the index range, the order,
  the signature, then the bits.
* *Note 32, division by 3.* $`R` divides by 3 ($`|\mathbf{c}|/3`), and the active-core bound in (11.27) is
  $`|\kappa'|/3`. In the paper the division is exact: every validator key sequence has a length in
  $`\mathbb{V} \equiv \{ 3c \mid c \in \mathbb{N}_{2\dots\mathsf{C}+1} \}` (eqs. (6.7), (6.8)). The model's types do not enforce
  $`|\kappa'| \in \mathbb{V}`; its integer division ({api}`JAM.rotate`, {api}`JAM.checkGuarantee`) gives the floor
  $`\lfloor |\kappa'|/3 \rfloor`, which is the exact quotient whenever $`|\kappa'| \in \mathbb{V}`.
* *Note 32, the previous rotation.* $`\mathbf{M}^*` uses $`\tau' - \mathsf{R}`, which is negative when $`\tau' < \mathsf{R}`, and
  the model's natural subtraction truncates it at 0 ({api}`JAM.priorAssignments`). This is never reached:
  $`\mathbf{M}^*` is used only for a timeslot $`t \le \tau'` in an earlier rotation than $`\tau'`, which needs
  $`\tau' \ge \mathsf{R}`.
* *Note 32, errors and order for guarantees.* No errors are named for an invalid $`\mathbf{E}_G`, and no
  order is given between its conditions. The model uses the test vectors' names
  ({api}`JAM.ReportsError`) and the order given at {api}`JAM.guarantees`. A segment-root lookup
  key that is neither in the extrinsic nor in recent history fails both (11.42) and (11.44); the
  model checks (11.44) first, so it reports an invalid lookup. An anchor found by its header hash
  with another field wrong is reported by the first field that differs ({api}`JAM.checkAnchor`).
* *Note v0.8.1-A2, the work-package limits.* (11.33) names no errors and gives no order between its
  rows or against the other conditions. The model uses the test vectors' later error names
  (`refineLoadTooHigh`, `badExportsCount`, `bundleTooBig`, `authGasTooHigh`) and checks the rows in
  the paper's order ({api}`JAM.checkReportLoad`).
* *Note v0.8.1-A51, report equality in (11.17).* $`(p_\mathbf{g})_\mathbf{r} \in \mathbf{R}` compares work-reports without
  saying how. The model compares their encodings ({api}`JAM.assurances`).
* *Note v0.8.1-A53, a digest for a service that does not exist.* (11.32) and (11.45) read
  $`\delta[\mathbf{d}_s]`, which is undefined when $`\mathbf{d}_s \notin \mathcal{K}(\delta)`. The model rejects such a report
  (`badServiceId`, the test vectors' name), before the minimum-gas condition ({api}`JAM.guarantees`).
