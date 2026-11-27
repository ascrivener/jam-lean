import VersoManual
import Companion.Source
import Companion.Paper
import Companion.Docstring
import JAM.Accumulation
import JAM.Preimages
import JAM.Theorems.Confinement

open Verso.Genre Manual
open Companion
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option maxHeartbeats 1000000

#doc (Manual) "§12 Accumulation and preimages" =>
%%%
tag := "accumulation"
shortTitle := "§12 Accumulation"
file := "accumulation"
%%%

*In the paper:* {gpchapter}`sec:accumulation`.

Accumulation runs the on-chain _Accumulate_ code of the services that have work to do in this
block: those with digests in the newly available reports or in queued reports whose dependencies
are now met, the always-accumulate services with their free gas, and the recipients of deferred
transfers. It folds the results into the state. GP v0.8.1 §12 defines,
in this order: the queue of reports waiting for their dependencies (§12.1); the execution in rounds,
with the outer function $`\Delta_+`, the parallel function $`\Delta_*` and the single-service function
$`\Delta_1` (§12.2); the posterior state (§12.3); and the integration of the preimages extrinsic
(§12.4). This chapter follows that order.

In the model, §12.1–§12.3 are `JAM/Accumulation.lean` (the transition is {api}`JAM.accumulate`) and
§12.4 is `JAM/Preimages.lean` ({api}`JAM.preimages`). The accumulate invocation $`\Psi_A` and its host
functions, which $`\Delta_1` calls, belong to {ref "invocations"}[Appendix B] and are in `JAM/Accumulate.lean`. API pages:
[Accumulation](https://ascrivener.github.io/jam-lean/api/JAM/Accumulation.html),
[Preimages](https://ascrivener.github.io/jam-lean/api/JAM/Preimages.html),
[Accumulate](https://ascrivener.github.io/jam-lean/api/JAM/Accumulate.html).

The notation follows the paper: $`\mathbf{R}` is the sequence of newly available reports,
$`\delta` the accounts, $`\chi` the privileges, $`\iota` the staging keys, $`\phi` the
authorizer queue, $`\tau` and $`\tau'` the prior and posterior timeslots. $`x \mathrel{\mathrlap{<}{-}} \mathbf{x}`
draws $`x` from the sequence $`\mathbf{x}` in order.

# History and queuing (§12.1)
%%%
tag := "accumulation-queue"
%%%

## The state: ξ and ω

$`\xi` holds, for each of the last $`\mathsf{E}` blocks, the set of work-package hashes accumulated in it.
$`\omega` holds, per slot of the epoch, the reports that are ready but wait on dependencies, each with
its set of unaccumulated dependencies:

{gpeq "12.1, 12.2"}

{gpeq "12.3"}

The model keeps them in {api}`JAM.AccState`, as `accumulated` and `ready`. A ready entry is a
report with a set of hashes:

{leanSource JAM.ReadyEntry}

{leanSource JAM.AccState}

## Splitting the new reports

Reports with no prerequisites and an empty segment-root lookup, $`\mathbf{R}^!`, are accumulated
at once. The others, $`\mathbf{R}^Q`, are queued with their dependencies, minus those already
accumulated:

{gpeq "12.4"}

{gpeq "12.5"}

{gpeq "12.6"}

{leanSource JAM.deps}

In {api}`JAM.accumulate`, these are the bindings `rBang` and `rQ`.

## E, Q and P

$`E` removes the entries whose package is in $`\mathbf{x}`, and removes $`\mathbf{x}` from the
remaining dependencies. $`Q` repeatedly takes the entries with no dependencies left. $`P` gives the
package hashes of a set of reports:

{transcribed "12.7" "88b75dde25"}

$$`E \colon \left\{ \begin{aligned} &\left(\llbracket (\mathbb{R}, \{\![\,\mathbb{H}\,]\!\}) \rrbracket, \{\![\,\mathbb{H}\,]\!\}\right) \to \llbracket (\mathbb{R}, \{\![\,\mathbb{H}\,]\!\}) \rrbracket \\ &(\mathbf{r}, \mathbf{x}) \mapsto \left[ (r, \mathbf{d} \setminus \mathbf{x}) \;\middle|\; (r, \mathbf{d}) \mathrel{\mathrlap{<}{-}} \mathbf{r},\ (r_\mathbf{s})_p \notin \mathbf{x} \right] \end{aligned} \right. \qquad \text{(12.7)}`

{leanSource JAM.editQueue}

{gpeq "12.8"}

{leanSource JAM.readyOrder}

{gpeq "12.9"}

{leanSource JAM.pkgs}

$`Q` is recursive on a sequence that need not shrink in form, so the model gives it fuel. Each
round that continues removes at least the entries in $`\mathbf{g}`, so $`|\mathbf{r}| + 1` rounds
are enough; {api}`JAM.accumulate` passes that. This argument is in the docstring of
{api}`JAM.readyOrder` and is not stated as a theorem.

## The accumulatable reports R\*

The queue is read starting at the current slot of the epoch, wrapping round, followed by the new
queued reports, with the packages of $`\mathbf{R}^!` removed:

{gpeq "12.10, 12.11"}

{gpeq "12.12"}

Here $`\overgroup{\mathbf{x}}` concatenates the sequences in $`\mathbf{x}`. In
{api}`JAM.accumulate` these are the bindings `m`, `q` and `rStar`, with `slot` for $`\mathbf{H}_T`.

# Execution (§12.2)
%%%
tag := "accumulation-execution"
%%%

## Inputs and the partial state

$`\Psi_A` receives operand tuples, built from a report and one of its digests, and deferred
transfers. A transfer carries its sender $`s`, receiver $`d`, whether it credits the receiver's
supervisor balance ($`u = \top`) or its regular balance ($`u = \bot`), the amount $`a`, a memo $`m`
of $`\mathsf{W}_T = 128` octets and a gas limit $`g`:

{gpeq "12.13"}

{gpeq "12.14"}

{leanSource JAM.OperandTuple}

{leanSource JAM.DeferredTransfer}

{leanSource JAM.AccumulateInput}

The partial state $`\mathbb{S}` holds the parts of the state that accumulation reads and changes:
the accounts, the staging keys, the authorizer queue and the privileges. $`B` and $`U` are the
types of the accumulation outputs and of the gas used:

{gpeq "12.15"}

{transcribed "12.16" "1577c8ac61"}

$$`B \equiv \{\![\,(\mathbb{N}_S, \mathbb{H})\,]\!\} \qquad U \equiv \llbracket (\mathbb{N}_S, \mathbb{N}_G) \rrbracket \qquad \text{(12.16)}`

{leanSource JAM.PartialState}

The model flattens the privileges $`\mathbf{x} = (m, v, r, \mathbf{a}, \mathbf{z})` (eq. (9.9), see
{ref "accounts-privileges"}[§9.4]) into the fields `manager`, `delegator`, `registrar`, `assigners`
and `alwaysAcc`.

## Supervisors and deferred transfers

A service's account can be changed both by its own _Accumulate_ code and by its supervisor's in the
same round. The paper lets both run, and if both modify the service, discards all results of the
service's own run, except the preimages it provided. Ejection counts as a modification. A transfer
cannot be discarded without losing funds, so transfers to a service are never accumulated in the
same round as its supervisor's code. $`T` splits the transfers into those that may run in this
round, $`\mathbf{t}^!`, and those that must wait, $`\mathbf{t}^Q`:

{transcribed "12.17" "62c5927b59"}

$$`T(\mathbf{t}, \mathbf{s}, \mathbf{d}) \equiv T^*(\mathbf{t}, \mathbf{s}, \emptyset, \mathbf{d}) \qquad \text{(12.17)}`

$$`T^* \colon \left\{ \begin{aligned} &\left( \llbracket \text{𝕥} \rrbracket, \{\![\,\mathbb{N}_S\,]\!\}, \{\![\,\mathbb{N}_S\,]\!\}, \langle \mathbb{N}_S \to \mathbb{A} \rangle \right) \to \left( \llbracket \text{𝕥} \rrbracket, \llbracket \text{𝕥} \rrbracket \right) \\ &([], \mathbf{s}, \mathbf{i}, \mathbf{d}) \mapsto ([], []) \\ &([t] \frown \mathbf{t}, \mathbf{s}, \mathbf{i}, \mathbf{d}) \mapsto \begin{cases} (\mathbf{t}^!, [t] \frown \mathbf{t}^Q) & \text{if } q = \top \\ ([t] \frown \mathbf{t}^!, \mathbf{t}^Q) & \text{otherwise} \end{cases} \end{aligned} \right.`

$$`\begin{aligned} \text{where } q &= \left(t_d \in \mathcal{K}(\mathbf{d}) \wedge \mathbf{d}[t_d]_e \in (\mathbf{s} \cup \mathbf{i}) \setminus \{t_d\}\right) \vee \exists s \in \mathbf{i} \setminus \{t_d\} : \mathbf{d}[s]_e = t_d \\ \text{and } \mathbf{i}' &= \begin{cases} \mathbf{i} & \text{if } q = \top \vee t_d \notin \mathcal{K}(\mathbf{d}) \\ \mathbf{i} \cup \{t_d\} & \text{otherwise} \end{cases} \\ \text{and } (\mathbf{t}^!, \mathbf{t}^Q) &= T^*(\mathbf{t}, \mathbf{s}, \mathbf{i}', \mathbf{d}) \end{aligned}`

{leanSource JAM.partitionXfers}

$`\mathbf{d}[s]_e` is the effective supervisor of eq. (9.11), {api}`JAM.effectiveSupervisor`.
The model's `T` is the paper's $`T^*`, called with `[]` for $`\emptyset`; the sets $`\mathbf{s}` and
$`\mathbf{i}` are lists, used only through membership. A transfer may still be lost: if its
destination has been ejected by the time it is accumulated, $`\Psi_A` discards it (eq. (B.9)).

## Δ₊, the outer accumulation function

$`\Delta_+` takes the longest prefix of the reports whose gas limits, with the gas of the
transfers and of the free accumulations, fit in $`g`. It runs that round with $`\Delta_*`, then
recurses on the rest, with the transfers that waited and those the round produced, and the gas that
was left plus the gas of the new transfers:

{transcribed "12.18" "8ebeaa8137"}

$$`\Delta_+ \colon \left\{ \begin{aligned} &\left( \mathbb{N}_G, \llbracket \text{𝕥} \rrbracket, \llbracket \mathbb{R} \rrbracket, \mathbb{S}, \langle \mathbb{N}_S \to \mathbb{N}_G \rangle \right) \to \left( \mathbb{N}, \mathbb{S}, B, U, \llbracket \text{𝕥} \rrbracket \right) \\ &(g, \mathbf{t}, \mathbf{r}, \mathbf{e}, \mathbf{f}) \mapsto \begin{cases} (0, \mathbf{e}, \{\}, [], []) & \text{if } n = 0 \\ (i + j, \mathbf{e}', \mathbf{b}^* \cup \mathbf{b}, \mathbf{u}^* \frown \mathbf{u}, \mathbf{t}^! \frown \mathbf{t}^\dagger) & \text{o/w} \end{cases} \end{aligned} \right. \qquad \text{(12.18)}`

$$`\begin{aligned} \text{where } i &= \max(\mathbb{N}_{|\mathbf{r}|+1}) : \sum_{r \in \mathbf{r}_{\dots i},\, d \in r_\mathbf{d}} (d_g) + \sum_{t \in \mathbf{t}} (t_g) + \sum_{x \in \mathcal{V}(\mathbf{f})} (x) \le g \\ \text{and } \mathbf{s} &= \left\{ d_s \;\middle|\; r \in \mathbf{r}_{\dots i},\, d \in r_\mathbf{d} \right\} \cup \mathcal{K}(\mathbf{f}) \\ \text{and } (\mathbf{t}^!, \mathbf{t}^Q) &= T(\mathbf{t}, \mathbf{s}, \mathbf{e}_\mathbf{d}) \\ \text{and } n &= i + |\mathbf{t}^!| + |\mathbf{f}| \\ \text{and } (\mathbf{e}^*, \mathbf{t}^*, \mathbf{b}^*, \mathbf{u}^*) &= \Delta_*(\mathbf{e}, \mathbf{t}^!, \mathbf{r}_{\dots i}, \mathbf{f}) \\ \text{and } (j, \mathbf{e}', \mathbf{b}, \mathbf{u}, \mathbf{t}^\dagger) &= \Delta_+(g^*, \mathbf{t}^Q \frown \mathbf{t}^*, \mathbf{r}_{i \dots}, \mathbf{e}^*, \{\}) \\ \text{and } g^* &= g + \sum_{t \in \mathbf{t}^*} (t_g) - \sum_{(s, u) \in \mathbf{u}^*} (u) \end{aligned}`

{leanSource JAM.accSeq}

The model computes $`i` as the last $`k \le |\mathbf{r}|` whose prefix fits (the prefix sums only
grow with $`k`, so this is the paper's maximum). Gas is an integer there so that $`g^*` is computed
as written. The paper does not say why the recursion ends; the model bounds the number of rounds
with fuel (see {ref "accumulation-readings"}[the readings]).

## Δ\*, the parallel accumulation function

$`\Delta_*` runs $`\Delta_1` once for each service with work, free gas or incoming transfers, and
merges the results. $`N` and $`\Delta(s)` implement the discarding described above; $`M(s)` takes an
existing account from the service's own run if that run modified it, and otherwise from the run of
its effective supervisor; $`\mathbf{n}` collects the new accounts; the privileges go through $`R`,
which takes the manager's change if there is one and otherwise the holder's own:

{transcribed "12.19" "da351e2b0d"}

$$`\Delta_* \colon \left\{ \begin{aligned} &\left( \mathbb{S}, \llbracket \text{𝕥} \rrbracket, \llbracket \mathbb{R} \rrbracket, \langle \mathbb{N}_S \to \mathbb{N}_G \rangle \right) \to \left( \mathbb{S}, \llbracket \text{𝕥} \rrbracket, B, U \right) \\ &(\mathbf{e}, \mathbf{t}, \mathbf{r}, \mathbf{f}) \mapsto \left( (\mathbf{d}', \mathbf{i}', \mathbf{q}', \mathbf{x}'), \overgroup{\mathbf{t}'}, \mathbf{b}, \mathbf{u} \right) \end{aligned} \right. \qquad \text{(12.19)}`

$$`\begin{aligned} \text{where: let } &(\mathbf{d}, \mathbf{i}, \mathbf{q}, \mathbf{x} : (m, v, r, \mathbf{a}, \mathbf{z})) = \mathbf{e} \\ \mathbf{s} &= \left\{ d_s \;\middle|\; r \in \mathbf{r}, d \in r_\mathbf{d} \right\} \cup \mathcal{K}(\mathbf{f}) \cup \left\{ t_d \;\middle|\; t \in \mathbf{t} \right\} \\ N(\mathbf{o}) \in \mathbb{O} &\equiv (\mathbf{e},\ \mathbf{w} : \{\},\ \mathbf{t} : [],\ y : \emptyset,\ u : \mathbf{o}_u,\ \mathbf{p} : \mathbf{o}_\mathbf{p}) \\ \Delta(s) &\equiv \begin{cases} N(\mathbf{o}) & \text{if } s \in \mathbf{o}_\mathbf{w} \wedge s \in \mathbf{y}_\mathbf{w} \setminus \{\mathbf{d}[s]_e\} \\ \mathbf{o} & \text{otherwise} \end{cases} \\ &\quad \text{where } \mathbf{o} = \Delta_1(\mathbf{e}, \mathbf{t}, \mathbf{r}, \mathbf{f}, s) \\ &\quad \text{and } \mathbf{y} = \Delta_1(\mathbf{e}, \mathbf{t}, \mathbf{r}, \mathbf{f}, \mathbf{d}[s]_e) \end{aligned}`

$$`\begin{aligned} \mathbf{u} &= \left[ (s, \Delta(s)_u) \;\middle|\; s \mathrel{\mathrlap{<}{-}} \mathbf{s} \right] \\ \mathbf{b} &= \left\{ (s, b) \;\middle|\; s \in \mathbf{s},\, b = \Delta(s)_y,\, b \ne \emptyset \right\} \\ \mathbf{t}' &= \left[ \Delta(s)_\mathbf{t} \;\middle|\; s \mathrel{\mathrlap{<}{-}} \mathbf{s} \right] \\ \mathbf{d}' &= I\Big(\mathbf{m} \cup \mathbf{n}, \bigcup_{s \in \mathbf{s}} \Delta(s)_\mathbf{p}\Big) \end{aligned}`

$$`\begin{aligned} X(s) &\equiv (\Delta(s)_\mathbf{e})_\mathbf{x} \\ \mathbf{x}'_{(m, \mathbf{z})} &= X(m)_{(m, \mathbf{z})} \\ \mathbf{x}'_v &= R(v, X(m)_v, X(v)_v) \\ \mathbf{x}'_r &= R(r, X(m)_r, X(r)_r) \\ \forall c \in \mathbb{N}_\mathsf{C} : \mathbf{x}'_\mathbf{a}[c] &= R(\mathbf{a}_c, (X(m)_\mathbf{a})_c, (X(\mathbf{a}_c)_\mathbf{a})_c) \\ \mathbf{i}' &= (\Delta(v)_\mathbf{e})_\mathbf{i} \\ \forall c \in \mathbb{N}_\mathsf{C} : \mathbf{q}'_c &= ((\Delta(\mathbf{a}_c)_\mathbf{e})_\mathbf{q})_c \end{aligned}`

$$`\begin{aligned} M(s) &\equiv \begin{cases} (\Delta(s)_\mathbf{e})_\mathbf{d}[s] & \text{if } s \in \Delta(s)_\mathbf{w} \\ (\Delta(\mathbf{d}[s]_e)_\mathbf{e})_\mathbf{d}[s] & \text{otherwise} \end{cases} \\ \mathbf{m} &= \left\{ (s \mapsto M(s)) \;\middle|\; s \in \mathcal{K}(\mathbf{d}),\, M(s) \ne \emptyset \right\} \\ \mathbf{n} &= \bigcup_{s \in \mathbf{s}} \left( (\Delta(s)_\mathbf{e})_\mathbf{d} \setminus \mathcal{K}(\mathbf{d}) \right) \end{aligned}`

{gpeq "12.20"}

Note that the post-state field of $`N(\mathbf{o})` is written without a value: every other field of
$`N(\mathbf{o})` is given one. The model's choice is explained under
{ref "accumulation-readings"}[the readings]. Here is the model's $`N`, its $`\Delta_*` and $`R`:

{leanSource JAM.discardIfBoth}

{leanSource JAM.accPar}

{leanSource JAM.pick}

How the code maps to the equation:

* `ss` is $`\mathbf{s}`, sorted (a set in the paper, so any order is allowed; $`\mathbf{u}` and
  $`\mathbf{t}'` are built in ascending order of service).
* `acc s` is $`\Delta(s)`. The paper evaluates $`\Delta` at every service in $`\mathbf{s}`, at every
  account in $`\mathcal{K}(\mathbf{d})` (through $`M`) and at $`m`, $`v`, $`r` and $`\mathbf{a}_c`,
  and each $`\Delta(x)` evaluates $`\Delta_1` at $`x` and at its effective supervisor. The model runs
  $`\Delta_1` only for the services in `needed` and reuses the result. Any other
  service gets the unchanged outcome (input state, nothing modified, no gas) without running
  $`\Psi_A`; that this equals $`\Delta_1` for a service with no inputs and no gas is argued in the
  docstring of {api}`JAM.accPar`, not proved.
* `M`, `m`, `n` and `merged` are $`M(s)`, $`\mathbf{m}`, $`\mathbf{n}` and $`\mathbf{m} \cup \mathbf{n}`;
  `accounts` is $`\mathbf{d}'`. The function returns an `Except`, for the conflict described below.
* `eStar` is $`\Delta(m)_\mathbf{e}`, so `eStar.manager` and `eStar.alwaysAcc` are
  $`X(m)_{(m, \mathbf{z})}`.

The paper adds, after the definitions of $`I` and $`Y`, that different services may not contribute
the same index for a new service to $`\mathbf{n}`, and that a block where this happens must be
considered invalid. The model collects $`\mathbf{n}` with {api}`JAM.collectNew`, which returns an
error on such a conflict. {api}`JAM.accPar`, {api}`JAM.accSeq` and {api}`JAM.accumulate` pass the error on,
and block import rejects the block (`BlockError.accumulation`):

{leanSource JAM.AccumulationError}

{leanSource JAM.collectNew}

## I and Y, preimage integration

Preimages that services provide during accumulation, and later those of the preimages extrinsic,
are integrated by $`I`. A provision counts only if the service still exists and its request for
that hash and length is still $`[]`:

{gpeq "12.21"}

{gpeq "12.22"}

{leanSource JAM.integrateProvisions}

{leanSource JAM.providable}

{api}`JAM.integrateProvisions` applies the provisions one at a time and tests $`Y` against the
accounts as updated so far, while the paper tests every provision against the input $`\mathbf{d}`.
The two agree (an argument, not a theorem of the model): a provision changes only the request $`(\mathcal{H}(\mathbf{i}), |\mathbf{i}|)` of its own
service, from $`[]` to $`[\tau']`, and a second provision of the same service and data is the same
element of the set $`\mathbf{p}`. (Two different blobs with the same hash and length would
interact, which the paper's hash assumption excludes.) Requests are read and written with the
accessors of {ref "accounts-entries"}[§9].

## Δ₁, the single-service accumulation function

$`\Delta_1` gathers the transfers to $`s` and the digests for $`s` from the reports, adds up their
gas with $`s`'s free gas, and runs $`\Psi_A`:

{gpeq "12.23"}

{leanSource JAM.AccOut}

{transcribed "12.24" "7b85d9e8e5"}

$$`\Delta_1 \colon \left\{ \begin{aligned} &\left( \mathbb{S}, \llbracket \text{𝕥} \rrbracket, \llbracket \mathbb{R} \rrbracket, \langle \mathbb{N}_S \to \mathbb{N}_G \rangle, \mathbb{N}_S \right) \to \mathbb{O} \\ &(\mathbf{e}, \mathbf{t}, \mathbf{r}, \mathbf{f}, s) \mapsto \Psi_A(\mathbf{e}, \tau', s, g, \mathbf{i}^T \frown \mathbf{i}^U) \end{aligned} \right. \qquad \text{(12.24)}`

$$`\begin{aligned} \text{where: } g &= \mathcal{U}(\mathbf{f}_s, 0) + \sum_{t \in \mathbf{t},\, t_d = s} (t_g) + \sum_{r \in \mathbf{r},\, d \in r_\mathbf{d},\, d_s = s} (d_g) \\ \mathbf{i}^T &= \left[ t \;\middle|\; t \mathrel{\mathrlap{<}{-}} \mathbf{t},\, t_d = s \right] \\ \mathbf{i}^U &= \left[ \left( \begin{aligned} &\mathbf{l} : d_\mathbf{l},\ g : d_g,\ y : d_y,\ \mathbf{t} : r_\mathbf{t}, \\ &e : (r_\mathbf{s})_e,\ p : (r_\mathbf{s})_p,\ a : r_a \end{aligned} \right) \;\middle|\; r \mathrel{\mathrlap{<}{-}} \mathbf{r},\ d \mathrel{\mathrlap{<}{-}} r_\mathbf{d},\ d_s = s \right] \end{aligned}`

{leanSource JAM.accOne}

$`\mathcal{U}(\mathbf{f}_s, 0)` is $`\mathbf{f}_s` if present and 0 otherwise, `f.getD s 0`. `slot`
is $`\tau'`. {api}`JAM.psiA` is $`\Psi_A` (eq. (B.9)): it credits the incoming transfers, marks
$`s` modified if any came in, and runs $`s`'s code.

# Final state integration (§12.3)
%%%
tag := "accumulation-final"
%%%

$`\Delta_+` is called once per block, with the block's gas, no transfers, the reports
$`\mathbf{R}^*`, the partial state made from $`\delta`, $`\iota`, $`\phi`, $`\chi`, and the
always-accumulate services $`\chi_\mathbf{z}` as free gas:

$$`\begin{aligned} \text{let } g &= \max\left(\mathsf{G}_T, \mathsf{G}_A \cdot \mathsf{C} + \textstyle\sum_{x \in \mathcal{V}(\chi_\mathbf{z})} (x)\right) \\ \text{and } \mathbf{e} &= (\mathbf{d} : \delta, \mathbf{i} : \iota, \mathbf{q} : \phi, \mathbf{x} : \chi) \end{aligned}`

{gpeq "12.25"}

{gpeq "12.26"}

{transcribed "12.27" "c59b0af023"}

$$`(\mathbf{d} : \delta^\dagger, \mathbf{i} : \iota', \mathbf{q} : \phi', \mathbf{x} : \chi') \equiv \mathbf{e}' \qquad \text{(12.27)}`

The accumulation statistics count, for each service, the digests accumulated, the transfers
processed and the gas used, and keep the services where any of these is non-zero:

{transcribed "12.28" "e96c3780e4"}

$$`\mathbf{S} \in \langle \mathbb{N}_S \to (\mathbb{N}, \mathbb{N}, \mathbb{N}_G) \rangle \qquad \text{(12.28)}`

$$`\begin{aligned} \mathbf{S} &\equiv \left\{ (s \mapsto S(s)) \;\middle|\; S(s) \ne (0, 0, 0) \right\} \qquad \text{(12.29)} \\ \text{where } S(s) &\equiv (N(s), X(s), G(s)) \\ \text{and } N(s) &\equiv \left| \left[ d \;\middle|\; r \mathrel{\mathrlap{<}{-}} \mathbf{R}^*_{\dots n},\, d \mathrel{\mathrlap{<}{-}} r_\mathbf{d},\, d_s = s \right] \right| \\ \text{and } X(s) &\equiv \left| \left[ t \;\middle|\; t \mathrel{\mathrlap{<}{-}} \mathbf{t},\, t_d = s \right] \right| \\ \text{and } G(s) &\equiv \sum_{(s, u) \in \mathbf{u}} (u) \end{aligned}`

Every accumulated service has its last-accumulation slot set:

{gpeq "12.30, 12.31"}

Finally the history and the ready queue move on by one block: the packages accumulated now enter
$`\xi`, the oldest entry leaves, and the queue drops what was accumulated and the slots that passed:

{gpeq "12.32, 12.33"}

{gpeq "12.34"}

All of §12.1–§12.3 is one function in the model, returning the posterior state, the output root and
the statistics, or the error that makes the block invalid:

{leanSource JAM.AccResult}

{leanSource JAM.accumulate}

How the code maps to the equations:

* `g` and the call to {api}`JAM.accSeq` are (12.25); `params.blockAccGas`, `params.reportAccGas` and
  `params.coreCount` are $`\mathsf{G}_T`, $`\mathsf{G}_A` and $`\mathsf{C}`. The partial state is
  `pre.pstate`, and its `alwaysAcc` is $`\chi_\mathbf{z}`. `rounds` is the fuel for $`\Delta_+`.
* `stats` is $`\mathbf{S}`, with `N`, `T`, `G` for $`N(s)`, $`X(s)`, $`G(s)`; `accounted` is
  $`\mathbf{R}^*_{\dots n}`.
* `accounts` is $`\delta^\ddagger` (12.30, 12.31).
* `newAcc` and `accumulated` are (12.32, 12.33). In `ready`, entry `idx` is
  $`{\omega'}^{\circlearrowleft}_{m-i}` with $`i = (m - \mathit{idx}) \bmod \mathsf{E}`, and the three branches
  are the cases of (12.34).
* `theta` is $`\theta'`, and `root` is $`\mathcal{M}_B(\mathbf{s}, \mathcal{H}_K)`, the Keccak Merkle root over
  $`\mathbf{s} = [\mathcal{E}_4(s) \frown \mathcal{E}(h) \mid (s, h) \mathrel{\mathrlap{<}{-}} \theta']` that {ref "history"}[§7] appends to the
  accumulation-output log (eqs. (7.6, 7.7)); $`\mathcal{E}(h)` of a hash is the hash itself.

# Preimage integration (§12.4)
%%%
tag := "accumulation-preimages"
%%%

After accumulation, the preimages extrinsic $`\mathbf{E}_P` is integrated. It has at most
$`\mathsf{N}_P` pairs, is ordered and without duplicates, provides only data that was requested
and not yet provided in the _prior_ state $`\delta`, and holds at most $`\mathsf{N}_D` octets of data:

{gpeq "12.35, 12.36"}

{gpeq "12.37, 12.38"}

Preimages no longer useful after accumulation (their request was changed or the service ejected)
are disregarded, by $`I`:

{gpeq "12.39"}

{leanSource JAM.PreimageError}

{leanSource JAM.preimageLt}

{leanSource JAM.preimagesOrdered}

{leanSource JAM.preimages}

`prior` is $`\delta` and `postAcc` is $`\delta^\ddagger`. The extrinsic is passed to
{api}`JAM.integrateProvisions` as a set, which it is by (12.36).

# What is checked
%%%
tag := "accumulation-checked"
%%%

*Theorems.* No theorem is yet stated about $`\Delta_+`, $`\Delta_*`, $`T`, $`Q` or $`I`
themselves. One theorem bounds what a single run of $`\Psi_A`, and so of $`\Delta_1`, can change.
Let $`s` be a service with an account whose code is present and contains none of the host calls `bless`, `assign`, `designate`,
`new`, `eject` and `provide` (the list `reachingIds`), and suppose no other service has $`s` as
its effective supervisor (`NoSupervisee`). Then $`\Psi_A` for $`s` leaves every other account, the
staging keys, the authorizer queue and the privileges as they were in $`\mathbf{e}` (`Outside`), and
provides no preimages:

{leanSource JAM.psiA_confined}

The requirement on supervisees is needed because, since v0.8.1, a service may change any service
it effectively supervises.

*Checks on examples.* The test file
[`Tests/HostGeneralTest.lean`](https://github.com/ascrivener/jam-lean/blob/main/Tests/HostGeneralTest.lean)
builds small services by hand (each a short PVM program) and runs them through $`\Psi_A`,
$`\Delta_*`, $`\Delta_+` and {api}`JAM.accumulate`. Each expected result is a `#guard`, evaluated when
the file is compiled, which CI does on every run. These are checks of particular cases, not
theorems. Among them:

* *$`\theta'` is a set, in order.* A service that yields a different hash in each of three rounds
  of one block gives three entries in $`\theta'`, ordered by hash rather than by round, and the
  root is the Merkle root of their encodings $`\mathcal{E}_4(s) \frown h`. A service that yields the
  same hash in two rounds appears once.
* *Discarding, $`N`.* A service and its effective supervisor both write the service's storage key
  in one round. The service's own run is discarded: its storage holds the supervisor's value, and
  its yield is gone, but its gas use is counted and the preimage it provided for its own request
  is integrated (the request becomes $`[\tau']`). If the supervisor does nothing, the service's own
  write and yield stand.
* *$`T` across rounds.* A service sends a transfer to a service and then one to that service's
  effective supervisor. The second waits a round (the second disjunct of $`q`), so $`\mathbf{u}`
  lists the supervised service before its supervisor; both are credited, each is counted with one
  transfer in $`\mathbf{S}`, and both have their last-accumulation slot set.
* *Transfers to the supervisor balance.* In $`\Psi_A`, a transfer with $`u = \top` credits the
  destination's supervisor balance $`x` rather than $`b`, marks the destination modified, and, for a
  service without code, uses no gas.
* *$`R`.* The manager and the delegator both change the delegator in the same round; the manager's
  choice is kept. When the manager does nothing, the delegator's own choice is kept.
* *Self-transfers* (`transfer`, {ref "invocations"}[Appendix B]). An immediate transfer from a service to itself counts
  the credit when the balance is checked against the threshold, and a deferred one does not.
* *The bounds of $`\mathbf{E}_P`.* One pair too many, or one octet too many, is rejected.
* *New-index conflicts.* {api}`JAM.collectNew` collects distinct new indices from two services'
  post-states, ignores indices already in $`\mathbf{d}`, and returns the conflict error when two
  services create the same index, even with identical accounts. (These run on hand-built account
  maps, not through $`\Psi_A`.)

The published accumulate test vectors are for GP v0.8.0; running them against this v0.8.1 model is
suspended until v0.8.1 vectors exist.

# Readings chosen
%%%
tag := "accumulation-readings"
%%%

Each is a note in the model's
[notes on the paper](https://github.com/ascrivener/jam-lean/blob/main/docs/upstream-candidates.md#gray-paper-issues):

* *Note v0.8.1-A1, the post-state of $`N(\mathbf{o})`.* In (12.19), $`N(\mathbf{o})` gives every
  field a value except the post-state. The model takes the round's input state $`\mathbf{e}`
  ({api}`JAM.discardIfBoth`), following the prose: "discard all results of the service's execution",
  with only provided preimages excepted. Taking $`\mathbf{o}`'s post-state instead would keep a
  discarded run's new services and its changes to the privileges, staging keys and queue, while
  $`M(s)` drops its change to its own account. One consequence of the model's reading: if the
  supervisor's own run is also discarded (its own supervisor modified it too), both changes to the
  service are lost. This is filed as
  [graypaper#592](https://github.com/gavofyork/graypaper/issues/592).
* *Note v0.8.1-A46, $`\theta'` as an ordered set.* $`\mathbf{b}` is a set of pairs, so (12.26) lists each pair once.
  The model orders them by service and then by hash ({api}`JAM.accumulate`, `theta`), the order in
  which sets are serialized.
* *Note v0.8.1-A45, the effective supervisor of a service with no account.* $`\mathbf{d}[s]_e` is defined only for
  $`s \in \mathcal{K}(\mathbf{d})`, but $`\mathbf{s}` can contain a service with no account (a digest or
  transfer for it). The model takes $`s` itself ({api}`JAM.effectiveSupervisor`), so
  $`\Delta(s) = \Delta_1(\ldots, s)`, which for a missing account changes nothing.
* *Note v0.8.1-A47, termination of $`\Delta_+` and $`Q`.* The paper gives no argument that the recursions end. The model
  gives each a bound on the number of rounds: $`|\mathbf{q}| + 1` for $`Q`, and
  $`|\mathbf{R}^*| + \lfloor g / \mathsf{M}_T \rfloor + 2` for $`\Delta_+`, where $`\mathsf{M}_T`
  is the base gas of the `transfer` host call (Appendix B). If a bound were reached, the model would
  stop accumulating (and $`Q` would return the reports found so far). No theorem yet shows that
  these bounds are never reached.
* *Note 25 and v0.8.1-A3, the preimages extrinsic.* The paper names no errors for an invalid
  $`\mathbf{E}_P` and orders none of its conditions. The model checks the two bounds, then the order,
  then $`Y`, with the error names of {api}`JAM.PreimageError` (the test vectors' names where they
  exist). The order on pairs, which (12.36) needs, is by service and then by the data octets
  lexicographically ({api}`JAM.preimageLt`).
