import VersoManual
import Companion.Source
import Companion.Paper
import Companion.Reader
import JAM.BlockImport
import JAM.Model

open Verso.Genre Manual
open Companion

set_option pp.rawOnError true

#doc (Manual) "JAM in plain English" =>
%%%
tag := "plain-english"
shortTitle := "JAM in plain English"
file := "plain-english"
%%%

This chapter is for readers who know how blockchains work but have not read the Gray Paper. It
says what JAM is for, then follows one block through the state transition, step by step, in the
order the model applies them, with a link to the chapter that has the details. It ends with the
work that happens outside blocks. The symbols are kept to a minimum; the {ref "glossary"}[glossary]
lists every symbol the book uses, with its plain meaning and the model's name for it.

# What JAM is for
%%%
tag := "plain-english-purpose"
%%%

JAM is a blockchain for running other people's programs at scale. On most chains every node runs
every transaction. JAM splits the work into two kinds and runs each where it is cheapest:

* *Refine* is the heavy part. It runs _in-core_ (off-chain), on one *core*: a small group of validators
  assigned to that core (its *guarantors*) does the computation, and only a compact result goes on
  chain. There are $`\Ccorecount` cores (341), so many workloads run side by side. Refine cannot
  change the chain's state; it reads the data it was given and can look up older on-chain data.
* *Accumulate* is the light part. It runs _on-chain_: every validator runs it when it imports a
  block. It takes the compact results and changes the state: storage, balances, new services.

The programs are *services*. A service is like a smart contract: an account with code, storage and
a balance ({ref "accounts"}[§9]). Its code has two entry points, one for refine and one for accumulate.

A *work package* is a request for a core's time: one or more *work items*, each naming a service
and carrying a payload for it, plus an authorization. Core time is scarce, so each core keeps a
pool of *authorizers* ({ref "authorization"}[§8]); a package names one of them, and that
authorizer's code must accept the package before any refining happens. Privileged services decide
which authorizers each core's pool is refilled from.

Refining a package produces a *work report* ({ref "work"}[§14]): for each item, the output (or the
error), with hashes that let anyone check the work later. The report is what goes on chain, in
three stages: it is *reported* (guaranteed in a block), it becomes *available* (enough validators
confirm they hold its data), and then it is *accumulated* (the services' accumulate code runs on
it). Meanwhile validators chosen at random re-run the refinement to *audit* it.

Time is divided into *timeslots* of $`\Cslotseconds` seconds, with at most one block per slot, and
*epochs* of $`\Cepochlen` slots (one hour). The set of validators can change at each epoch.

{figure "lifeOfWork"}

# Following one block
%%%
tag := "plain-english-block"
%%%

A block is a *header* and an *extrinsic*. The header names the parent block, commits to the state
and to the extrinsic, and is signed (sealed) by the block's author. The extrinsic carries the
outside data the block brings in, in five parts: lottery tickets, disputes, preimages,
availability assurances and guarantees ({ref "overview"}[§4–§5]).

Importing a block means computing the next state from the current one and the block. The paper
calls this function $`\transitionstate`; in the model it is {api}`JAM.importBlock`. The block is
valid only if every step below accepts it; if any step rejects it, the block is invalid and the
state does not change. The steps run in this order.

1. *Check the header against the chain.* The header must name its parent's hash, carry the
   Merkle root of the current state, and commit to exactly this extrinsic. Its timeslot becomes
   the new current time. The newest entry of the recent-history log, the parent block, gets its
   state root filled in now that it is known. ({ref "overview"}[§4–§5], {ref "history"}[§7])

2. *Disputes.* The disputes part of the extrinsic carries verdicts on work reports, each backed
   by judgments from more than two-thirds of a validator set, and the validators shown to have
   misbehaved. The judgments state records them; a report judged bad, or whose validity cannot be
   known, is removed from its core, which cancels its accumulation. The header must list the
   offending validators. ({ref "disputes"}[§10])

3. *Block production (Safrole).* The author's VRF signature in the header is mixed into the
   chain's entropy. At the first block of an epoch the validator sets move along: the staged keys
   become the next epoch's (with offenders' keys nulled), the next epoch's become active, and the
   active become the previous set; the header then carries an epoch marker. Anonymous lottery
   tickets in the extrinsic are collected, and the best of them decide who seals each slot of the
   next epoch (if too few arrive, a fallback rule picks the sealers). Finally the header's author index
   and seal are checked: the author must hold this slot's ticket or fallback key.
   ({ref "safrole"}[§6])

4. *Assurances.* Each assurance is one validator's signed statement of which cores' pending
   reports it holds its share of data for. A report assured by more than two-thirds of the
   validators becomes *available*, and is collected for accumulation; a report still not
   available after $`\Cassurancetimeoutperiod` slots is dropped, freeing its core.
   ({ref "reports"}[§11])

5. *Guarantees.* Each guarantee is a new work report signed by two or three of the guarantors
   assigned to its core. It is checked against the state: the core must be free, the report's
   authorizer must be in the core's pool, the chain state it was refined against must be recent
   and on this chain, the same package must not already be reported or accumulated, and its sizes
   and gas must be within limits. An accepted report occupies its core until it becomes available
   or times out. ({ref "reports"}[§11], {ref "work"}[§14])

6. *Accumulation.* The newly available reports, together with earlier ones that were waiting for
   a package they depend on, are accumulated: the services they name run their accumulate code
   in the PVM, the virtual machine ({ref "pvm"}[Appendix A], {ref "invocations"}[Appendix B]),
   within a gas budget for the block. Accumulation can change service accounts, move balance
   between services, create services and, for privileged services, change the authorizer queues,
   the next validator keys and the privileges themselves. Reports whose dependencies are still
   missing wait in a queue; the packages accumulated are recorded so they cannot be accumulated
   twice. ({ref "accumulation"}[§12])

7. *Recent history.* The root of this block's accumulation outputs is appended to a Merkle
   mountain range, a compact commitment to the accumulation outputs of every block so far. An
   entry for this block is added to the recent-history log: its header hash, its timeslot, the
   packages reported in it, and the new root of that commitment. ({ref "history"}[§7])

8. *Preimages.* The preimages part of the extrinsic supplies data that services asked for by
   hash. Each blob must have been requested and not yet supplied; it is then stored in the
   requesting service's account. ({ref "accumulation"}[§12])

9. *Authorization.* For each core, the authorizer a guarantee in this block used leaves the
   core's pool, and the next authorizer from the core's queue is added, so that the pool holds at
   most $`\Cauthpoolsize` entries. ({ref "authorization"}[§8])

10. *Statistics.* Counters are updated: blocks, tickets, preimages, guarantees and assurances per
    validator, and the load on each core and service. They are bookkeeping; no other step reads
    them. ({ref "statistics"}[§13])

The result is the new state. Its Merkle root ({ref "statemerkle"}[Appendix D]), over the state
encoded as the paper specifies ({ref "codec"}[Appendix C]), is what the next block's header must
carry. Signatures and VRFs are checked through a cryptography parameter
({ref "bandersnatch"}[Appendix G]); hashing and the other primitives are in {ref "primitives"}[§3].

# Work outside blocks
%%%
tag := "plain-english-offchain"
%%%

The steps above are what every node does when it imports a block. The data in the extrinsic comes
from work that validators do between blocks. The paper describes it too, and the model implements
its deterministic parts, except Beefy's BLS signatures.

* *Guaranteeing* ({ref "guaranteeing"}[§15]). A core's guarantors receive a work package, run its
  authorizer and then each item's refine code ({ref "work"}[§14]), and build the work report. They
  erasure-code the package's data and its exported segments ({ref "erasure"}[Appendix H]) and send
  each validator its share. With two or three signatures the report becomes a guarantee, which the
  next block author can include.

* *Availability assurance* ({ref "assurance"}[§16]). Each validator keeps the shares it received,
  and signs a bitfield saying which cores' reports it holds data for. These are the assurances a
  block includes; more than two-thirds make a report available.

* *Auditing* ({ref "auditing"}[§17]). Once a report is available, validators chosen at random,
  in tranches every few seconds, fetch its data, re-run the refinement and announce their
  judgment; more auditors are drawn when some fail to show up. A negative judgment starts a
  dispute, and its verdict reaches the chain through the disputes extrinsic (step 2). A block
  counts as audited once each report it made available has a positive judgment from every auditor
  announced for it (and no negative one), or from more than two-thirds of all validators.

* *The best chain and finality* ({ref "bestchain"}[§19]). When there are forks, a node builds on
  the best chain: among the chains that extend the latest finalized block, are audited, and have
  no slot with two competing blocks, the one with the most ticket-sealed blocks. Grandpa, a
  separate voting protocol, finalizes blocks. A further protocol, Beefy ({ref "beefy"}[§18]), lets
  other chains follow JAM's accumulation outputs.

The rest of the book follows the paper's sections in order, from {ref "primitives"}[§3].
