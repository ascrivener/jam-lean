import VersoManual
import Companion.Source
import Companion.Paper
import JAM.Reports
import JAM.Guarantee
import JAM.Disputes

open Verso.Genre Manual
open Companion

set_option pp.rawOnError true

#doc (Manual) "§15 Guaranteeing" =>
%%%
tag := "guaranteeing"
shortTitle := "§15 Guaranteeing"
file := "guaranteeing"
%%%

*In the paper:* {gpchapter}`sec:guaranteeing`.

*In brief.* Guaranteeing is the step in which validators vouch for a work-report before it can go on
chain. Each active core has three validators assigned to it, its guarantors, and the assignment is
shuffled every epoch and rotated every ten timeslots ({ref "reports-assignments"}[§11],
{ref "shuffle"}[Appendix F]). A guarantor that receives a work-package computes its work-report as
{ref "work"}[§14] defines, erasure-codes the package's data and distributes the chunks to the
validators, and signs the report. A report signed by two or three of the core's guarantors can be
put in a block's guarantees extrinsic, which {ref "reports"}[§11] checks. Signing is a commitment:
the paper presumes that in a public system a validator that signs a report which does not faithfully
follow from the work-package is punished severely, and auditing ({ref "auditing"}[§17]) and disputes
({ref "disputes"}[§10]) are how such reports are caught.

§15 of GP v0.8.1 describes what a guarantor does with a work-package it receives: it checks the
package's authorization against the authorization pool of the most recent chain state, refines
each work-item, erasure-codes the bundle and the exported data, assembles and signs a work-report,
and distributes the chunks across the validator set. With two guarantor signatures, the report can
go to the next block author, who puts it in the guarantees extrinsic $`\xtguarantees`.

This chapter is a short map. The section's deterministic parts are all defined elsewhere in the
paper, and the model implements them in the chapters linked below. The rest of §15 is node
behaviour, which the model does not cover (see {ref "guaranteeing-not-modelled"}[Not modelled]).

# The report and its signature (§15)
%%%
tag := "guaranteeing-equations"
%%%

For a work-package $`\mathbf{p}`, the work-report, if there is one, is

{gpeq "15.1"}

The guarantor chooses the core index $`c`, the segment-root dictionary $`\mathbf{l}` and the number of assuring
validators $`v`. In the paper's words, "typically $`c` should be the core currently assigned to the
guarantor, $`v` should be the size of the active validator set, and $`\mathbf{l}` should be derived from previously
guaranteed work-reports".

The guarantor then distributes $`(s, i)`: its validator index $`i` and $`s`, an Ed25519 signature with its registered
key on

{gpeq "15.2"}

This is the message that eq. {eq}`11.27` checks for each signer of a guarantee, with $`\Xguarantee = \token{\$jam\_guarantee}`
(eq. {eq}`11.28`); there it is written $`\Xguarantee \concat \blake{\mathbf{r}}`, without the explicit encoding $`\mathcal{E}`.

# Where the model implements it
%%%
tag := "guaranteeing-map"
%%%

* *$`\Xi`, eq. {eq}`15.1`.* The work-report computation of §14.4 is {api}`JAM.Guarantee.computeReport`, described
  in the {ref "work-xi"}[§14 chapter]. It takes two inputs the paper leaves implicit: the account state
  that $`\Psi_I` and $`\Psi_R` read, and the data of every item (extrinsics, imported segments and their
  justifications). The bundle and the availability specifier it builds, including the erasure coding of
  the bundle and of the exports, are in {ref "work-bundle"}[Bundle assembly] and
  {ref "work-avspec"}[The availability specifier]; the erasure code itself is {ref "erasure"}[Appendix H].
* *The choice of $`c`.* The core a validator is assigned to is given by the guarantor assignments
  $`\guarantorassignments` and, for the previous rotation, $`\mathbf{M}^*` (eqs. {eq}`11.18`–{eq}`11.22`): {api}`JAM.assignments` and
  {api}`JAM.priorAssignments`, in the {ref "reports-assignments"}[§11 chapter].
* *The choice of $`v` and $`\mathbf{l}`.* What makes a report includable on-chain is checked by
  {api}`JAM.guarantees` (§11.4, {ref "reports-guarantees"}[Guarantees] and
  {ref "reports-context"}[Contextual validity]): among other conditions, $`(\mathbf{r}_\mathbf{s})_v = |\kappa'|` (eq. {eq}`11.30`), and the
  authorizer must be in the core's pool, $`\mathbf{r}_a \in \alpha[\mathbf{r}_c]` (eq. {eq}`11.31`). The package hashes and segment roots of
  recently guaranteed reports, from which $`\mathbf{l}` is derived, are the $`\mathbf{p}` of each recent-history entry
  (eq. {eq}`7.8`, {ref "history-entry"}[§7 chapter]).
* *The signature, eq. {eq}`15.2`.* {api}`JAM.checkGuarantee` verifies each signer's signature on
  `Xguarantee ++ h`, where `h` is the Blake2b hash of the report's encoding; the context string is
  {api}`JAM.Xguarantee`. The model checks guarantor signatures; it does not produce them, since it holds no
  secret keys.

# Not modelled
%%%
tag := "guaranteeing-not-modelled"
%%%

The model covers the state transition and the deterministic functions it depends on, not how a node
behaves. So it does not model:

* how a guarantor receives a work-package, or sends it to the other guarantors on its core to form
  consensus over the core;
* the distribution of chunks to validators, or serving the bundle and exported data on request;
* which chain state a guarantor evaluates against ("advanced nodes may … attempt to predict the
  state of the chain"), and the order in which it makes its checks;
* the assembly of a guarantee extrinsic by guarantors and block authors;
* timing and anti-spam advice, such as signing "an average of no more than two work-reports per
  timeslot".
