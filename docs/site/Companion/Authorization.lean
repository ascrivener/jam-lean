import VersoManual
import Companion.Source
import Companion.Docstring
import JAM.Authorization
import JAM.BlockImport

open Verso.Genre Manual
open Companion
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "§8 Authorization" =>
%%%
tag := "authorization"
shortTitle := "§8 Authorization"
file := "authorization"
%%%

A work package may use a core only if one of the core's current *authorizers* allows it. An
authorizer is identified by a hash: the hash of its PVM code hash concatenated with its
configuration blob. Running an authorizer happens in-core, in the Is-Authorized invocation (§14.3), which is separate
from Refine. On chain,
the state only has to say which authorizers each core accepts, and keep that set up to date. That
is §8 of GP v0.8.1, and in the model it is `JAM/Authorization.lean`
([API page](https://ascrivener.github.io/jam-lean/api/JAM/Authorization.html)).

# Pool and queue
%%%
tag := "authorization-state"
%%%

Each core $`c` has an *authorizer pool* $`\alpha[c]`, the authorizers it accepts now, and an *authorizer queue* $`\phi[c]`,
from which the pool is refilled:

$$`\alpha \in \llbracket \llbracket \mathbb{H} \rrbracket_{:\mathsf{O}} \rrbracket_{\mathsf{C}}, \qquad \phi \in \llbracket \llbracket \mathbb{H} \rrbracket_{\mathsf{Q}} \rrbracket_{\mathsf{C}} \qquad \text{(8.1)}`

So each of the $`\mathsf{C} = 341` pools holds at most $`\mathsf{O} = 8` hashes, and each queue exactly $`\mathsf{Q} = 80`. Only accumulation changes
$`\phi`, through a call from a privileged service (§12). In the model's state these are the fields
`authPools` and `authQueue` of {api}`JAM.State`, each a list of lists of hashes. The lengths are not
fixed by the types; if either list has fewer than $`\mathsf{C}` entries, a missing core's pool or queue is read as
empty (`getD`).

# The transition
%%%
tag := "authorization-transition"
%%%

Each block, every core drops the authorizer that a guarantee on that core used, if there is one,
and takes the next authorizer from its posterior queue. The queue is indexed by the block's
timeslot, cyclically:

$$`\forall c \in \mathbb{N}_{\mathsf{C}} : \alpha'[c] \equiv \overleftarrow{F(c) \mathbin{+\!\!+} \phi'[c][\mathbf{H}_T]^{\circlearrowleft}}^{\mathsf{O}} \qquad \text{(8.2)}`

$$`F(c) \equiv \begin{cases} \alpha[c] \ominus \{(g_\mathbf{r})_a\} & \text{if } \exists g \in \mathbf{E}_G : (g_\mathbf{r})_c = c \\ \alpha[c] & \text{otherwise} \end{cases} \qquad \text{(8.3)}`

The notation is from §3.7: $`\mathbf{s}[i]^{\circlearrowleft}` is $`\mathbf{s}[i \bmod |\mathbf{s}|]`; $`\overleftarrow{\mathbf{s}}^n` is the last $`n` elements of $`\mathbf{s}`; $`x \mathbin{+\!\!+} i` appends one element; and
$`\mathbf{s} \ominus \{v\}` is $`\mathbf{s}` without its left-most element equal to $`v`. (The paper draws this operator with its
own symbol, a spoon, which KaTeX cannot draw; it is shown here as $`\ominus`.) $`(g_\mathbf{r})_a` is the authorizer hash of
the work report in guarantee $`g`, and $`(g_\mathbf{r})_c` is its core.

Since $`\alpha'` uses $`\phi'`, it is computed after accumulation (eq. (4.19) of the
{ref "overview"}[dependency graph]).

Sequence subtraction:

{leanSource JAM.seqMinusLeft}

$`F(c)`, given the (core, authorizer) pair of every guarantee in $`\mathbf{E}_G`:

{leanSource JAM.poolUsed}

$`\alpha'[c]`:

{leanSource JAM.poolNext}

And the transition for all cores:

{leanSource JAM.authorizations}

In {api}`JAM.importBlock` the pairs come from the guarantees extrinsic,
`(g.report.core, g.report.authorizerHash)`, and the queue is the one accumulation returns.

# What is checked

No theorems about §8 are proved yet. The transition is run against the v0.8.0 test vectors
`stf/authorizations` (tiny and full), which give each guarantee's core and authorizer in place of
$`\mathbf{E}_G`. No accumulation runs in these vectors, so the test passes the prior queues as $`\phi'` and checks that
the vectors' posterior queues equal their prior ones; it compares the computed $`\alpha'` with the vectors' posterior pools
([`Tests/AuthorizationsTest.lean`](https://github.com/ascrivener/jam-lean/blob/main/Tests/AuthorizationsTest.lean)).

# Readings chosen
%%%
tag := "authorization-readings"
%%%

Notes 21, v0.8.1-A28 and v0.8.1-A29 are in the model's
[notes on the paper](https://github.com/ascrivener/jam-lean/blob/main/docs/upstream-candidates.md#gray-paper-issues).

* *Which guarantee's authorizer (note 21).* In (8.3), $`g` is bound only inside the condition
  $`\exists g \in \mathbf{E}_G : (g_\mathbf{r})_c = c`, but $`(g_\mathbf{r})_a` is used in the result. The model reads $`g` as the guarantee on core $`c`
  ({api}`JAM.poolUsed`).
* *More than one guarantee on a core (note v0.8.1-A28).* A valid $`\mathbf{E}_G` has at most one guarantee per core (§11). The
  model does not rely on that here: if there were several, it would remove each one's authorizer
  in turn.
* *An empty queue (note v0.8.1-A29).* By (8.1) every queue has exactly $`\mathsf{Q}` entries, so $`\phi'[c][\mathbf{H}_T]^{\circlearrowleft}` always exists. The model's
  queues are lists of any length; for an empty queue, where $`i \bmod 0` names no element, it appends
  nothing ({api}`JAM.poolNext`).
