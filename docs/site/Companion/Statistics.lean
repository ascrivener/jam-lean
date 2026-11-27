import VersoManual
import Companion.Source
import Companion.Paper
import Companion.Docstring
import JAM.Statistics
import JAM.Reports

open Verso.Genre Manual
open Companion
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "§13 Statistics" =>
%%%
tag := "statistics"
shortTitle := "§13 Statistics"
file := "statistics"
%%%

*In the paper:* {gpchapter}`sec:bookkeeping`.

The chain does not pay rewards itself, but it records what each validator did, so that a staking
system built on top can act on it. §13 of GP v0.8.1 keeps four records in $`\pi`: per-validator
counts for the current epoch and the last one, and per-core and per-service figures for the
current block. In the model they are three functions: {api}`JAM.validatorStats` for the validator
records (§13.1), and {api}`JAM.coreStats` and {api}`JAM.serviceStats` for the core and service
records (§13.2).

The module is `JAM/Statistics.lean`; its full API is on the
[doc-gen4 page](https://ascrivener.github.io/jam-lean/api/JAM/Statistics.html).

# Validator activity (§13.1)
%%%
tag := "statistics-validators"
%%%

$`\pi_V` accumulates the current epoch's records and $`\pi_L` holds the last completed epoch's:

{gpeq "13.1"}

{gpeq "13.2"}

{gpeq "13.3"}

The six counts are the blocks $`b` the validator produced, the tickets $`t` and preimages $`p` it
introduced, the total octets $`d` of those preimages, the reports $`g` it guaranteed and the
assurances $`a` it made. The model's record is {api}`JAM.ValidatorRecord`:

{leanSource JAM.ValidatorRecord}

The update has three stages. Assurances are credited first, over the prior validator set. At an
epoch change the accumulator is moved to $`\pi_L` and a fresh one started. Then the block's author is
credited its block, tickets and preimages, and every validator whose Ed25519 key is in the reporters
set $`\mathbf{G}` (eq. (11.27), {ref "reports-guarantees"}[§11 chapter]) a guarantee:

{gpeq "13.4"}

{gpeq "13.5"}

{gpeq "13.6"}

A Boolean in a sum counts as 1 when true and 0 when false. In {api}`JAM.validatorStats`, `dagger`
is $`\pi^\dagger_V`, `ddagger` and `last'` are $`\pi^\ddagger_V` and $`\pi'_L`, and `curr'` is $`\pi'_V`. The block's
inputs (author index, ticket count, preimages, assurer indices, posterior keys and $`\mathbf{G}`) come in
{api}`JAM.ValidatorStatsInput`:

{leanSource JAM.validatorStats}

# Cores and services (§13.2)
%%%
tag := "statistics-cores"
%%%

The core and service records are kept for the current block only:

{gpeq "13.7"}

{gpeq "13.8"}

The model's records are {api}`JAM.CoreRecord` and {api}`JAM.ServiceRecord`.

## Cores

A core's record sums the load of the reports guaranteed on it in this block ($`\mathbf{I}`, eq. (11.29)), the
data-availability load of the reports that became available on it ($`\mathbf{R}`, eq. (11.16)), and the
number of assurances that set its bit:

{transcribed "13.9" "a7ecea4217"}

$$`\forall c \in \mathbb{N}_{\mathsf{C}} : \pi'_C[c] \equiv \begin{pmatrix} i \mathrel{\substack{\scriptscriptstyle\blacktriangleright \\ \scriptscriptstyle\blacktriangleright}} R(c)_i \,,\ x \mathrel{\substack{\scriptscriptstyle\blacktriangleright \\ \scriptscriptstyle\blacktriangleright}} R(c)_x \,,\ z \mathrel{\substack{\scriptscriptstyle\blacktriangleright \\ \scriptscriptstyle\blacktriangleright}} R(c)_z \,, \\ e \mathrel{\substack{\scriptscriptstyle\blacktriangleright \\ \scriptscriptstyle\blacktriangleright}} R(c)_e \,,\ u \mathrel{\substack{\scriptscriptstyle\blacktriangleright \\ \scriptscriptstyle\blacktriangleright}} R(c)_u \,,\ l \mathrel{\substack{\scriptscriptstyle\blacktriangleright \\ \scriptscriptstyle\blacktriangleright}} L(c) \,, \\ d \mathrel{\substack{\scriptscriptstyle\blacktriangleright \\ \scriptscriptstyle\blacktriangleright}} D(c) \,,\ p \mathrel{\substack{\scriptscriptstyle\blacktriangleright \\ \scriptscriptstyle\blacktriangleright}} \sum_{a \in \mathbf{E}_A} a_f[c] \end{pmatrix} \qquad \text{(13.9)}`

{gpeq "13.10"}

{gpeq "13.11"}

{gpeq "13.12"}

In {api}`JAM.coreStats`, the ceiling $`\lceil n \cdot 65/64 \rceil` is computed as `(n * 65 + 63) / 64`:

{leanSource JAM.coreStats}

## Services

A record is made for every service that had a work-digest reported, a preimage provided, or an
accumulation in this block:

{transcribed "13.13" "56ac02e164"}

$$`\forall s \in \mathbf{s} : \pi'_S[s] \equiv \begin{pmatrix} i \mathrel{\substack{\scriptscriptstyle\blacktriangleright \\ \scriptscriptstyle\blacktriangleright}} R(s)_i \,,\ x \mathrel{\substack{\scriptscriptstyle\blacktriangleright \\ \scriptscriptstyle\blacktriangleright}} R(s)_x \,,\ z \mathrel{\substack{\scriptscriptstyle\blacktriangleright \\ \scriptscriptstyle\blacktriangleright}} R(s)_z \,, \\ e \mathrel{\substack{\scriptscriptstyle\blacktriangleright \\ \scriptscriptstyle\blacktriangleright}} R(s)_e \,,\ r \mathrel{\substack{\scriptscriptstyle\blacktriangleright \\ \scriptscriptstyle\blacktriangleright}} (R(s)_n, R(s)_u) \,, \\ p \mathrel{\substack{\scriptscriptstyle\blacktriangleright \\ \scriptscriptstyle\blacktriangleright}} \sum_{\mathbf{p} \in \mathbf{E}_P, \mathbf{p}_s = s} (1, |\mathbf{p}_\mathbf{d}|) \,, \\ a \mathrel{\substack{\scriptscriptstyle\blacktriangleright \\ \scriptscriptstyle\blacktriangleright}} \mathcal{U}(\mathbf{S}[s], (0, 0, 0)) \end{pmatrix} \qquad \text{(13.13)}`

{gpeq "13.14"}

{gpeq "13.15"}

{gpeq "13.16"}

{gpeq "13.17"}

$`\mathbf{S}` is the accumulation statistics of {ref "accumulation"}[§12] (eq. (12.29)), and $`\mathcal{U}(x, y)` is $`x` unless $`x` is $`\emptyset`, in which case it
is $`y`. v0.8.1 states the provision sum's filter $`\mathbf{p}_s = s` explicitly (GP #567). In {api}`JAM.serviceStats`,
`active` is $`\mathbf{s}`, and `(acc.lookup s).getD (0, 0, 0)` is $`\mathcal{U}(\mathbf{S}[s], (0, 0, 0))`:

{leanSource JAM.serviceStats}

# Theorems

No theorems about the statistics are proved yet. The functions are run against test
vectors: the statistics vectors check the validator records, the preimages vectors the service
records' provision counts, and the reports vectors the core and service figures of the incoming
reports. The statistics and preimages vectors are those of davxy/jam-test-vectors v0.8.0; the
reports vectors are its master at commit 5e8d2a2, later than v0.8.0. The reports vectors have no
newly available reports and no assurances.

# Readings chosen
%%%
tag := "statistics-readings"
%%%

* *Note 23, the length of a fresh accumulator.* At an epoch change, (13.5) starts $`\pi^\ddagger_V` as
  $`[(0, \dots), \dots]`, with no stated length. $`|\pi'_V| = |\kappa'|` (13.3) implies it, and the model uses $`|\kappa'|`
  ({api}`JAM.validatorStats`). This is recorded in the model's
  [notes on the paper](https://github.com/ascrivener/jam-lean/blob/main/docs/upstream-candidates.md#gray-paper-issues).
* *The reporters set as an input.* $`\mathbf{G}` is defined in {ref "reports"}[§11.4] from the guarantor assignments, where the
  signatures are checked. The model computes it there ({api}`JAM.guarantees`) and passes it to
  {api}`JAM.validatorStats`.
