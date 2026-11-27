import VersoManual
import Companion.Source
import Companion.Docstring
import JAM.BestChain
import JAM.Theorems.BestChain

open Verso.Genre Manual
open Companion
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "§19 Grandpa and the best chain" =>
%%%
tag := "bestchain"
shortTitle := "§19 Best chain"
file := "best-chain"
%%%

Nodes finalize blocks with the Grandpa protocol, and between finalizations each node must decide
which block to build on and vote for: the best block $`\mathbf{B}^\flat`. §19 of GP v0.8.1 gives the rule. A block
is *acceptable* when it extends the latest finalized block $`\mathbf{B}^\natural`, is audited, and has no
unfinalized ancestor at a timeslot where two valid blocks were seen; among the acceptable blocks, the
best is one with the most ticket-sealed ancestors.

The model implements this rule in `JAM/BestChain.lean`. Grandpa itself is not modelled: the latest
finalized block $`\mathbf{B}^\natural` is an input, and it must be in the node's store: a block is acceptable only if
$`\mathbf{B}^\natural` is among its ancestors found in the store, so if $`\mathbf{B}^\natural` is missing, no block is acceptable. Nor is the data voted on in Grandpa (the best block's header with its
posterior state root). Like auditing, this is off-chain logic, not part of the state transition. The
API page is [JAM.BestChain](https://ascrivener.github.io/jam-lean/api/JAM/BestChain.html), and the
theorems are in [JAM.Theorems.BestChain](https://ascrivener.github.io/jam-lean/api/JAM/Theorems/BestChain.html).

# What a node knows about a block
%%%
tag := "bestchain-blocks"
%%%

The rule depends on data that is local to the node: which blocks it has seen, and its own view of
whether each is audited (§17). The model makes this data explicit. A node knows a block through a
{api}`JAM.BestChain.BlockInfo`, and a *store*, a list of them, is the set of valid blocks it has seen:

{leanSource JAM.BestChain.BlockInfo}

$`\mathbf{T}` records whether the block was sealed with a ticket: it is 1 when the posterior slot-sealer
sequence $`\gamma'_S` is a sequence of tickets and 0 when it is fallback keys (eqs. (6.17) and (6.18)):

{leanSource JAM.BestChain.ticketedOf}

The audited flag is the node's $`\mathbf{U}` (eq. (17.19)), which {api}`JAM.Auditing.blockAudited` computes, and the
disregarded flag comes from §17.3's rule ({api}`JAM.BestChain.disregardedBlock`, see below).
{api}`JAM.BestChain.BlockInfo.ofHeader` builds a `BlockInfo` from a model header.

# Ancestors (§5)
%%%
tag := "bestchain-ancestors"
%%%

$`P` maps a header to its parent's header, and the ancestors of $`\mathbf{H}` are $`\mathbf{H}` and, recursively, their
parents:

$$`h \in \mathbf{A} \Leftrightarrow h = \mathbf{H} \vee \left(\exists i \in \mathbf{A} : h = P(i)\right) \qquad \text{(5.3)}`

A valid block's timeslot is strictly greater than its parent's, and not in the future:

$$`\mathbf{H}_T \in \mathbb{N}_T, \quad P(\mathbf{H})_T < \mathbf{H}_T \ \wedge\ \mathbf{H}_T \cdot \mathsf{P} \le \mathcal{T} \qquad \text{(5.8)}`

In the model, $`P` looks the parent up in the store, and $`\mathbf{A}` follows parent links while the parent is
known and has a smaller timeslot. The result lists $`\mathbf{H}` first, then its ancestors, youngest first. The
timeslot condition is what makes the recursion terminate (the measure is the timeslot):

{leanSource JAM.BestChain.lookup}

{leanSource JAM.BestChain.ancestry}

{leanSource JAM.BestChain.slotTimely}

{api}`JAM.BestChain.slotTimely` states (5.8)'s rule for the caller. The best-chain functions use only its
first conjunct, $`P(\mathbf{H})_T < \mathbf{H}_T`, and only to stop following parents ({api}`JAM.BestChain.ancestry`). They do not
check the wall-clock bound $`\mathbf{H}_T \cdot \mathsf{P} \le \mathcal{T}`, since the store is taken to hold only valid blocks.

# Acceptable blocks (§19)
%%%
tag := "bestchain-acceptable"
%%%

$$`\mathbf{A}(\mathbf{H}^\flat) \ni \mathbf{H}^\natural \qquad \text{(19.1)}`

$$`\mathbf{U}^\flat \equiv \top \qquad \text{(19.2)}`

$$`\not\exists \mathbf{H}^A, \mathbf{H}^B : \bigwedge \left\{ \begin{aligned} \mathbf{H}^A &\ne \mathbf{H}^B \\ \mathbf{H}^A_T &= \mathbf{H}^B_T \\ \mathbf{H}^A &\in \mathbf{A}(\mathbf{H}^\flat) \\ \mathbf{H}^A &\not\in \mathbf{A}(\mathbf{H}^\natural) \end{aligned} \right. \qquad \text{(19.3)}`

(19.1): the best block has the finalized block as an ancestor. (19.2): it is audited. (19.3): none
of its unfinalized ancestors shares its timeslot with another block the node has seen (an
equivocation).

§17.3 adds one more condition, outside §19's formulas: "we pointedly disregard chains which include
the accumulation of a report which we know at least $`\tfrac{1}{3}` of validators judge as being invalid. Any
chains including such a block are not eligible for authoring on." The model adds it to acceptability:

{leanSource JAM.BestChain.disregardedBlock}

{leanSource JAM.BestChain.equivocates}

{leanSource JAM.BestChain.finalizedAncestors}

{leanSource JAM.BestChain.AuditReading}

{leanSource JAM.BestChain.acceptable}

The model offers two readings of (19.2), explained under {ref "bestchain-readings"}[Readings chosen].
The `chain` reading is the stricter one:

{leanSource JAM.BestChain.acceptable_head_of_chain}

# The best block (§19)
%%%
tag := "bestchain-best"
%%%

Of the acceptable blocks, the best is the one whose chain has the most ticket-sealed blocks:

$$`m = \sum_{\mathbf{H}^A \in \mathbf{A}^\flat} \mathbf{T}^A \qquad \text{(19.4)}`

{leanSource JAM.BestChain.metric}

{mathdoc JAM.BestChain.metric_child}

The paper does not say what to do when several acceptable blocks have the same $`m`. The model
returns all of them, in store order:

{leanSource JAM.BestChain.maxMetric}

{leanSource JAM.BestChain.bestHeads}

{leanSource JAM.BestChain.bestHead?}

What the model proves. The best heads are exactly the known acceptable blocks with the largest $`m`;
with unique hashes, the set of best heads does not depend on the order of the store (the single head
{api}`JAM.BestChain.bestHead?` picks does); and when the finalized
block is known, audited, and has no disregarded ancestor, a best head exists:

{mathdoc JAM.BestChain.mem_bestHeads_iff}

{mathdoc JAM.BestChain.mem_bestHeads_perm}

{mathdoc JAM.BestChain.finalized_acceptable}

{mathdoc JAM.BestChain.bestHeads_ne_nil}

For the single head {api}`JAM.BestChain.bestHead?` picks, {api}`JAM.BestChain.bestHead?_acceptable`,
{api}`JAM.BestChain.bestHead?_extends_finalized` and {api}`JAM.BestChain.bestHead?_maximal` state that it is
acceptable, satisfies (19.1), and maximises $`m`.

# Readings chosen
%%%
tag := "bestchain-readings"
%%%

Where the paper leaves a point open, the model picks one meaning. The notes cited are in the
model's [notes on the paper](https://github.com/ascrivener/jam-lean/blob/main/docs/upstream-candidates.md#gray-paper-issues).

* *Audited: the head, or the chain (note v0.8.1-A21).* (19.2) asks only that the best block itself
  be audited, while the list above it says the best block "is considered audited" and §17.3 asks a
  block to be audited before voting to finalize it. A chain whose head is audited can contain an unaudited
  unfinalized block. The model offers both readings: `AuditReading.head` is the formula, and
  `AuditReading.chain` also asks every unfinalized ancestor to be audited.
* *The disregard rule (note v0.8.1-A22).* §17.3's rule is not among §19's formulas, and §4 words it
  differently. The model adds §17.3's rule to acceptability as a flag per block, checked over all
  ancestors, finalized ones included, so a disregarded finalized block leaves no block acceptable.
* *Equivocations (note v0.8.1-A23).* "Two valid blocks at the same timeslot": only $`\mathbf{H}^A` must be
  unfinalized, and $`\mathbf{H}^B` can be any block seen, on any fork. The model reads (19.3) literally, with
  $`\mathbf{H}^B` ranging over the whole store.
* *Ties (note v0.8.1-A24).* No tie-break is given among acceptable blocks of equal $`m`, and every
  acceptable block is a candidate, not only the leaves: a child sealed with a fallback key ties with
  its parent. The model returns every maximiser ({api}`JAM.BestChain.bestHeads`); {api}`JAM.BestChain.bestHead?`
  takes the first in store order.
* *How far back $`m` counts (note v0.8.1-A25).* $`m` sums $`\mathbf{T}` over all ancestors back to genesis, while §5
  lets nodes keep only the headers of the last 24 hours. The model counts the ancestors in the store.
  Every acceptable block extends $`\mathbf{H}^\natural`, so the ancestors from $`\mathbf{H}^\natural` back add the same amount to every
  candidate, as long as the store holds $`\mathbf{H}^\natural`'s ancestors consistently.
* *Following parents.* The model follows a parent link only when the parent is in the store and
  has a smaller timeslot. A valid block always satisfies the timeslot condition (5.8), and it makes
  the recursion well founded.
