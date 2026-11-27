import VersoManual
import Companion.Source
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

$$`\pi \equiv (\pi_V, \pi_L, \pi_C, \pi_S) \qquad \text{(13.1)}`

$$`(\pi_V, \pi_L) \in \llbracket \left( b \in \mathbb{N}, t \in \mathbb{N}, p \in \mathbb{N}, d \in \mathbb{N}, g \in \mathbb{N}, a \in \mathbb{N} \right) \rrbracket^2 \qquad \text{(13.2)}`

$$`|\pi_V| = |\kappa| \ , \qquad |\pi_L| = |\lambda| \qquad \text{(13.3)}`

The six counts are the blocks $`b` the validator produced, the tickets $`t` and preimages $`p` it
introduced, the total octets $`d` of those preimages, the reports $`g` it guaranteed and the
assurances $`a` it made. The model's record is {api}`JAM.ValidatorRecord`:

{leanSource JAM.ValidatorRecord}

The update has three stages. Assurances are credited first, over the prior validator set. At an
epoch change the accumulator is moved to $`\pi_L` and a fresh one started. Then the block's author is
credited its block, tickets and preimages, and every validator whose Ed25519 key is in the reporters
set $`\mathbf{G}` (eq. (11.27), {ref "reports-guarantees"}[§11 chapter]) a guarantee:

$$`\begin{aligned} \pi^\dagger_V &\equiv \pi_V \text{ except } \forall v \in \mathbb{N}_{|\kappa|} : \\ \pi^\dagger_V[v]_a &= \pi_V[v]_a + (\exists a \in \mathbf{E}_A : a_v = v) \end{aligned} \qquad \text{(13.4)}`

$$`\begin{aligned} &\left( \pi^\ddagger_V, \pi'_L \right) \equiv \begin{cases} \left( \pi^\dagger_V, \pi_L \right) & \text{if } e' = e \\ \left( [(0, \dots), \dots], \pi^\dagger_V \right) & \text{otherwise} \end{cases} \\ &\text{where } e = \left\lfloor \frac{\tau}{\mathsf{E}} \right\rfloor ,\quad e' = \left\lfloor \frac{\tau'}{\mathsf{E}} \right\rfloor \end{aligned} \qquad \text{(13.5)}`

$$`\begin{aligned} \pi'_V &\equiv \pi^\ddagger_V \text{ except } \forall v \in \mathbb{N}_{|\kappa'|} : \\ \pi'_V[v]_b &= \pi^\ddagger_V[v]_b + (v = \mathbf{H}_I) \\ \pi'_V[v]_t &= \pi^\ddagger_V[v]_t + \begin{cases} |\mathbf{E}_T| & \text{if } v = \mathbf{H}_I \\ 0 & \text{otherwise} \end{cases} \\ \pi'_V[v]_p &= \pi^\ddagger_V[v]_p + \begin{cases} |\mathbf{E}_P| & \text{if } v = \mathbf{H}_I \\ 0 & \text{otherwise} \end{cases} \\ \pi'_V[v]_d &= \pi^\ddagger_V[v]_d + \begin{cases} \sum_{\mathbf{p} \in \mathbf{E}_P} |\mathbf{p}_\mathbf{d}| & \text{if } v = \mathbf{H}_I \\ 0 & \text{otherwise} \end{cases} \\ \pi'_V[v]_g &= \pi^\ddagger_V[v]_g + (\kappa'[v]_e \in \mathbf{G}) \end{aligned} \qquad \text{(13.6)}`

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

$$`\pi_C \in \llbracket \begin{pmatrix} d \in \mathbb{N}, p \in \mathbb{N}, i \in \mathbb{N}, x \in \mathbb{N}, \\ z \in \mathbb{N}, e \in \mathbb{N}, l \in \mathbb{N}, u \in \mathbb{N}_G \end{pmatrix} \rrbracket_{\mathsf{C}} \qquad \text{(13.7)}`

$$`\pi_S \in \left\langle \mathbb{N}_S \to \begin{pmatrix} p \in (\mathbb{N}, \mathbb{N}), \quad r \in (\mathbb{N}, \mathbb{N}_G), \\ i \in \mathbb{N}, x \in \mathbb{N}, z \in \mathbb{N}, e \in \mathbb{N}, \\ a \in (\mathbb{N}, \mathbb{N}, \mathbb{N}_G) \end{pmatrix} \right\rangle \qquad \text{(13.8)}`

The model's records are {api}`JAM.CoreRecord` and {api}`JAM.ServiceRecord`.

## Cores

A core's record sums the load of the reports guaranteed on it in this block ($`\mathbf{I}`, eq. (11.29)), the
data-availability load of the reports that became available on it ($`\mathbf{R}`, eq. (11.16)), and the
number of assurances that set its bit:

$$`\forall c \in \mathbb{N}_{\mathsf{C}} : \pi'_C[c] \equiv \begin{pmatrix} i : R(c)_i \,,\ x : R(c)_x \,,\ z : R(c)_z \,, \\ e : R(c)_e \,,\ u : R(c)_u \,,\ l : L(c) \,, \\ d : D(c) \,,\ p : \sum_{a \in \mathbf{E}_A} a_f[c] \end{pmatrix} \qquad \text{(13.9)}`

$$`\text{where } R(c \in \mathbb{N}_{\mathsf{C}}) \equiv \sum_{\mathbf{d} \in \mathbf{r}_\mathbf{d}, \mathbf{r} \in \mathbf{I}, \mathbf{r}_c = c} (\mathbf{d}_i, \mathbf{d}_x, \mathbf{d}_z, \mathbf{d}_e, \mathbf{d}_u,) \qquad \text{(13.10)}`

$$`\text{and } L(c \in \mathbb{N}_{\mathsf{C}}) \equiv \sum_{\mathbf{r} \in \mathbf{I}, \mathbf{r}_c = c} (\mathbf{r}_\mathbf{s})_l \qquad \text{(13.11)}`

$$`\text{and } D(c \in \mathbb{N}_{\mathsf{C}}) \equiv \sum_{\mathbf{r} \in \mathbf{R}, \mathbf{r}_c = c} (\mathbf{r}_\mathbf{s})_l + \mathsf{W}_G \lceil (\mathbf{r}_\mathbf{s})_n \, {}^{65}\!/\!_{64} \rceil \qquad \text{(13.12)}`

In {api}`JAM.coreStats`, the ceiling $`\lceil n \cdot 65/64 \rceil` is computed as `(n * 65 + 63) / 64`:

{leanSource JAM.coreStats}

## Services

A record is made for every service that had a work-digest reported, a preimage provided, or an
accumulation in this block:

$$`\forall s \in \mathbf{s} : \pi'_S[s] \equiv \begin{pmatrix} i : R(s)_i \,,\ x : R(s)_x \,,\ z : R(s)_z \,, \\ e : R(s)_e \,,\ r : (R(s)_n, R(s)_u) \,, \\ p : \sum_{\mathbf{p} \in \mathbf{E}_P, \mathbf{p}_s = s} (1, |\mathbf{p}_\mathbf{d}|) \,, \\ a : \mathcal{U}(\mathbf{S}[s], (0, 0, 0)) \end{pmatrix} \qquad \text{(13.13)}`

$$`\text{where } \mathbf{s} = \mathbf{s}^R \cup \mathbf{s}^P \cup \mathcal{K}(\mathbf{S}) \qquad \text{(13.14)}`

$$`\text{and } \mathbf{s}^R = \{ \mathbf{d}_s \mid \mathbf{d} \in \mathbf{r}_\mathbf{d}, \mathbf{r} \in \mathbf{I} \} \qquad \text{(13.15)}`

$$`\text{and } \mathbf{s}^P = \{ s \mid \exists x : (s, x) \in \mathbf{E}_P \} \qquad \text{(13.16)}`

$$`\text{and } R(s \in \mathbb{N}_S) \equiv \sum_{\mathbf{d} \in \mathbf{r}_\mathbf{d}, \mathbf{r} \in \mathbf{I}, \mathbf{d}_s = s} (n : 1, \mathbf{d}_u, \mathbf{d}_i, \mathbf{d}_x, \mathbf{d}_z, \mathbf{d}_e) \qquad \text{(13.17)}`

$`\mathbf{S}` is the accumulation statistics of §12 (eq. (12.29)), and $`\mathcal{U}(x, y)` is $`x` unless $`x` is $`\emptyset`, in which case it
is $`y`. v0.8.1 states the provision sum's filter $`\mathbf{p}_s = s` explicitly (GP #567). In {api}`JAM.serviceStats`,
`active` is $`\mathbf{s}`, and `(acc.lookup s).getD (0, 0, 0)` is $`\mathcal{U}(\mathbf{S}[s], (0, 0, 0))`:

{leanSource JAM.serviceStats}

# Theorems

No theorems about the statistics are proved yet. The functions are run against GP v0.8.0 test
vectors: the statistics vectors check the validator records, the preimages vectors the service
records' provision counts, and the reports vectors the core and service figures of the incoming
reports (those vectors have no newly available reports and no assurances).

# Readings chosen
%%%
tag := "statistics-readings"
%%%

* *Note 23, the length of a fresh accumulator.* At an epoch change, (13.5) starts $`\pi^\ddagger_V` as
  $`[(0, \dots), \dots]`, with no stated length. $`|\pi'_V| = |\kappa'|` (13.3) implies it, and the model uses $`|\kappa'|`
  ({api}`JAM.validatorStats`). This is recorded in the model's
  [notes on the paper](https://github.com/ascrivener/jam-lean/blob/main/docs/upstream-candidates.md#gray-paper-issues).
* *The reporters set as an input.* $`\mathbf{G}` is defined in §11.4 from the guarantor assignments, where the
  signatures are checked. The model computes it there ({api}`JAM.guarantees`) and passes it to
  {api}`JAM.validatorStats`.
