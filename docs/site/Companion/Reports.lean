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

{gpeq "11.1"}

An entry is a guarantee and the timeslot at which it was reported. The model's entry is
{api}`JAM.AvailAssignment`, and $`\rho` is {api}`JAM.AvailAssignments`.

§11.1 goes on to define the work-report and its parts: the report $`\mathbb{R}` (eq. {eq}`11.2`), the
refinement context $`\mathbb{C}` (eq. {eq}`11.4`), the availability specification $`\mathbb{Y}` (eq. {eq}`11.5`), the
work-digest $`\mathbb{D}` (eq. {eq}`11.6`) and the work errors $`\mathbb{E}` (eq. {eq}`11.7`). The model's types are
{api}`JAM.WorkReport`, {api}`JAM.RefineContext`, {api}`JAM.AvailabilitySpec`,
{api}`JAM.WorkDigest` and {api}`JAM.WorkError`. It also bounds a report's dependencies and size:

{gpeq "11.3"}

{gpeq "11.8"}

{gpeq "11.9, 11.10"}

With the bound $`1 \le |\mathbf{r}_\mathbf{d}| \le \mathsf{I}` from the type $`\mathbf{d} \in \llbracket \mathbb{D} \rrbracket_{1:\mathsf{I}}` in {eq}`11.2`, these are
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

{gpeq "11.11"}

{gpeq "11.12"}

The signature covers the parent header hash and the bitstring, and a bit may be set only on a core
with an assignment:

{gpeq "11.13"}

{gpeq "11.14"}

{gpeq "11.15"}

The model's assurance is {api}`JAM.Assurance`. {api}`JAM.checkAssurance` checks one assurance
against the index of the one before it:

{leanSource JAM.assuranceMessage}

{leanSource JAM.checkAssurance}

## Available reports and ρ‡

A report becomes available when more than two thirds of the validators set its core's bit.
$`\rho^\ddagger` is $`\rho^\dagger` with the cores of available reports cleared, together with those that timed out, and all
of them when the size of the validator set changes:

{gpeq "11.16"}

{gpeq "11.17"}

Both are in {api}`JAM.assurances`: `available` is the threshold of {eq}`11.16`, written
$`3 \cdot \text{count} > 2|\kappa|`, and `ρ'` is $`\rho^\ddagger`:

{leanSource JAM.assurances}

# Guarantor assignments (§11.3)
%%%
tag := "reports-assignments"
%%%

Of the $`\mathsf{C} = 341` cores, only the first $`|\kappa'|/3` are active, and each active core has three validators
assigned to it. $`\mathbf{M}` gives each validator's core and key:

{gpeq "11.18"}

The cores come from a shuffle with the epochal entropy $`\eta'_2`, rotated every $`\mathsf{R}` slots:

{gpeq "11.19"}

{gpeq "11.20"}

{gpeq "11.21"}

$`\mathcal{F}` is the shuffle of Appendix F ({ref "shuffle"}[chapter]). $`\Phi` (eq. {eq}`6.16`) replaces
the key of each validator in the punish-set $`\psi'_O` by the null key $`\mathbb{K}_0` (eq. {eq}`6.14`), whose
Ed25519 part is $`[2, 0, 0, \dots]`. In the model, which reads only the Ed25519 keys here, $`\Phi` is
{api}`JAM.blacklist` and the null Ed25519 key is {api}`JAM.nullEdKey`:

{leanSource JAM.rotate}

{leanSource JAM.permute}

{leanSource JAM.blacklist}

{leanSource JAM.assignments}

$`\mathbf{M}^*` is $`\mathbf{M}` as it was under the previous rotation, with the previous epoch's keys and entropy if
that rotation was in the previous epoch:

{gpeq "11.22"}

{leanSource JAM.priorAssignments}

# Guarantees (§11.4)
%%%
tag := "reports-guarantees"
%%%

A guarantee is a work-report, the timeslot at which it was guaranteed and a credential of two or
three signatures. The extrinsic holds at most one guarantee per core, in core order:

{gpeq "11.23"}

{gpeq "11.24, 11.25"}

{gpeq "11.26"}

Each signer must be assigned to the report's core, under $`\mathbf{M}` if $`t` is in the current rotation and under
$`\mathbf{M}^*` if it is in the previous one, and the core must be active now. The signers' Ed25519 keys form
the reporters set $`\mathbf{G}`, which the validator statistics of {ref "statistics"}[§13] read:

{gpeq "11.27"}

{gpeq "11.28"}

{api}`JAM.checkGuarantee` checks one guarantee and returns its signers' keys, from which
{api}`JAM.guarantees` builds $`\mathbf{G}`. A signer whose key $`\Phi` replaced by the null key is rejected before its
signature is checked, since no signature is valid under that key:

{leanSource JAM.checkGuarantee}

The incoming reports $`\mathbf{I}` must give the right number of erasure-coded chunks, land on a core with no
assignment in $`\rho^\ddagger`, be authorized by the core's pool $`\alpha`, and respect the gas limits:

{gpeq "11.29"}

{gpeq "11.30"}

{gpeq "11.31"}

{gpeq "11.32"}

Each report must also stay within the limits applied to every work-package. v0.8.1 adds these
conditions (GP #563):

{gpeq "11.33"}

{leanSource JAM.checkReportLoad}

## Contextual validity (§11.4.1)
%%%
tag := "reports-context"
%%%

$`\mathbf{x}` and $`\mathbf{p}` are the contexts and the work-package hashes of the incoming reports. No package may be
reported twice:

{gpeq "11.34, 11.35"}

Each anchor must be a recent block, with matching details; each lookup-anchor must be at most $`\mathsf{L}`
slots old and in the ancestor set $`\mathbf{A}` of the last $`\mathsf{L}` headers:

{gpeq "11.36"}

{gpeq "11.37"}

{gpeq "11.38"}

{leanSource JAM.checkAnchor}

The ancestor set is not part of the state, so the model takes the condition of {eq}`11.38` as an input,
`lookupAnchorKnown` of {api}`JAM.ReportsInput`.

A package already in the pipeline may not be reported again: not one reported in recent history
$`\beta_H`, accumulated in $`\xi`, waiting in the ready queue $`\omega`, or assigned in $`\rho`:

{gpeq "11.39"}

{gpeq "11.40"}

{gpeq "11.41"}

These sets are also not in the state {api}`JAM.guarantees` reads. Their union is computed by
{api}`JAM.knownPackages` and passed in as `known`:

{leanSource JAM.knownPackages}

Prerequisites and segment-root lookups must name packages in the extrinsic or in recent history,
with the right segment roots:

{gpeq "11.42"}

{gpeq "11.43"}

{gpeq "11.44"}

Finally, each digest must name its service's current code hash:

{gpeq "11.45"}

# The posterior assignments (§11.5)
%%%
tag := "reports-posterior"
%%%

Each core with a new guarantee takes it, stamped with the current time; the others keep their
entry in $`\rho^\ddagger`:

{gpeq "11.46"}

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
  adds vectors for {eq}`11.33`. They carry no ancestor set, so the runs take `lookupAnchorKnown` to hold
  for every context, and the ancestry condition of {eq}`11.38` is not exercised.

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
* *Note 32, division by 3.* $`R` divides by 3 ($`|\mathbf{c}|/3`), and the active-core bound in {eq}`11.27` is
  $`|\kappa'|/3`. In the paper the division is exact: every validator key sequence has a length in
  $`\mathbb{V} \equiv \{ 3c \mid c \in \mathbb{N}_{2\dots\mathsf{C}+1} \}` (eqs. {eq}`6.7`, {eq}`6.8`). The model's types do not enforce
  $`|\kappa'| \in \mathbb{V}`; its integer division ({api}`JAM.rotate`, {api}`JAM.checkGuarantee`) gives the floor
  $`\lfloor |\kappa'|/3 \rfloor`, which is the exact quotient whenever $`|\kappa'| \in \mathbb{V}`.
* *Note 32, the previous rotation.* $`\mathbf{M}^*` uses $`\tau' - \mathsf{R}`, which is negative when $`\tau' < \mathsf{R}`, and
  the model's natural subtraction truncates it at 0 ({api}`JAM.priorAssignments`). This is never reached:
  $`\mathbf{M}^*` is used only for a timeslot $`t \le \tau'` in an earlier rotation than $`\tau'`, which needs
  $`\tau' \ge \mathsf{R}`.
* *Note 32, errors and order for guarantees.* No errors are named for an invalid $`\mathbf{E}_G`, and no
  order is given between its conditions. The model uses the test vectors' names
  ({api}`JAM.ReportsError`) and the order given at {api}`JAM.guarantees`. A segment-root lookup
  key that is neither in the extrinsic nor in recent history fails both {eq}`11.42` and {eq}`11.44`; the
  model checks {eq}`11.44` first, so it reports an invalid lookup. An anchor found by its header hash
  with another field wrong is reported by the first field that differs ({api}`JAM.checkAnchor`).
* *Note v0.8.1-A2, the work-package limits.* {eq}`11.33` names no errors and gives no order between its
  rows or against the other conditions. The model uses the test vectors' later error names
  (`refineLoadTooHigh`, `badExportsCount`, `bundleTooBig`, `authGasTooHigh`) and checks the rows in
  the paper's order ({api}`JAM.checkReportLoad`).
* *Note v0.8.1-A51, report equality in {eq}`11.17`.* $`(p_\mathbf{g})_\mathbf{r} \in \mathbf{R}` compares work-reports without
  saying how. The model compares their encodings ({api}`JAM.assurances`).
* *Note v0.8.1-A53, a digest for a service that does not exist.* {eq}`11.32` and {eq}`11.45` read
  $`\delta[\mathbf{d}_s]`, which is undefined when $`\mathbf{d}_s \notin \mathcal{K}(\delta)`. The model rejects such a report
  (`badServiceId`, the test vectors' name), before the minimum-gas condition ({api}`JAM.guarantees`).
