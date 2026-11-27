import VersoManual
import Companion.Source
import Companion.Docstring
import JAM.State
import JAM.Block
import JAM.BlockImport

open Verso.Genre Manual
open Companion
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "§4–§5 The state, the block and the block transition" =>
%%%
tag := "overview"
shortTitle := "§4–§5 State and block"
file := "overview"
%%%

This chapter is the book's map. GP v0.8.1 §4 defines a blockchain by its state $`\sigma`, its blocks $`\mathbf{B}` and
one function, the block-level state transition $`\Upsilon`. It splits $`\sigma` into components and $`\Upsilon` into
section-level transitions, and orders them in a dependency graph. §5 defines the header and the
conditions a valid header meets. This chapter sets out those definitions, the model's
`JAM.State`, `JAM.Block` and `JAM.importBlock` that implement them, and where each component is
covered in this book.

# The block transition
%%%
tag := "overview-upsilon"
%%%

$$`\sigma' \equiv \Upsilon(\sigma, \mathbf{B}) \qquad \text{(4.1)}`

The paper defines JAM by $`\Upsilon` together with a genesis state $`\sigma^0`. In the model, $`\Upsilon` is
{api}`JAM.importBlock`. It returns the posterior state or the reason the block is invalid; its source
is quoted {ref "overview-graph"}[below].

Besides $`\sigma` and $`\mathbf{B}`, it takes three arguments the paper leaves implicit:

* the chain's constants, a {api}`JAM.Params` (see {ref "primitives-constants"}[§3, constants]);
* the cryptography, a {api}`JAM.Crypto`: signature and VRF verification, and the ring root. The
  model keeps these as a parameter and never implements them itself;
* the ancestor headers the importer has kept, a {api}`JAM.Chain`. The paper's ancestor set
  $`\mathcal{A}` (eq. (5.3)) is not part of $`\sigma`, and guarantees (§11) need it.

# The block
%%%
tag := "overview-block"
%%%

$$`\mathbf{B} \equiv (\mathbf{H}, \mathbf{E}) \qquad \text{(4.2)} \qquad\qquad \mathbf{E} \equiv (\mathbf{E}_T, \mathbf{E}_P, \mathbf{E}_G, \mathbf{E}_A, \mathbf{E}_D) \qquad \text{(4.3)}`

The extrinsic $`\mathbf{E}` has five parts: tickets $`\mathbf{E}_T` (§6), preimages $`\mathbf{E}_P` (§12), guarantees of work reports
$`\mathbf{E}_G` (§11), availability assurances $`\mathbf{E}_A` (§11) and disputes $`\mathbf{E}_D` (§10).

{leanSource JAM.Block}

{leanSource JAM.Extrinsic}

# The state
%%%
tag := "overview-state"
%%%

$$`\sigma \equiv (\alpha, \beta, \theta, \gamma, \delta, \eta, \iota, \kappa, \lambda, \rho, \tau, \varphi, \chi, \psi, \pi, \omega, \xi) \qquad \text{(4.4)}`

The model's {api}`JAM.State` has one field per component. It flattens the components that are
tuples: $`\gamma = (\gamma_P, \gamma_Z, \gamma_S, \gamma_A)`, the privileges $`\chi` and the statistics $`\pi` each become several
fields. Each component, with the section that covers it, and its fields:

* $`\alpha` ({ref "authorization"}[§8]): authorizer pools. Fields: `authPools`.
* $`\beta` ({ref "history"}[§7]): recent blocks and the accumulation output log. Fields: `recent`.
* $`\theta` (§7, §12): the most recent accumulation outputs. Fields: `lastAccOut`.
* $`\gamma` ({ref "safrole"}[§6]): Safrole's state. Fields: `pending`, `ringRoot`, `sealKeys`, `accumulator`.
* $`\delta` (§9): service accounts. Fields: `accounts`.
* $`\eta` ({ref "safrole"}[§6]): entropy. Fields: `eta`.
* $`\iota`, $`\kappa`, $`\lambda` ({ref "safrole"}[§6]): staging, active and previous validator keys. Fields: `staging`, `active`, `prev`.
* $`\rho` (§11): work reports awaiting availability, per core. Fields: `avail`.
* $`\tau` ({ref "safrole"}[§6]): the most recent block's timeslot. Fields: `tau`.
* $`\varphi` ({ref "authorization"}[§8]): authorizer queues. Fields: `authQueue`.
* $`\chi` (§9, §12): privileged services. Fields: `manager`, `assigners`, `delegator`, `registrar`, `alwaysAcc`.
* $`\psi` (§10): judgments. Fields: `disputes`.
* $`\pi` (§13): validator, core and service statistics. Fields: `valStats`, `valStatsLast`, `coreStats`, `serviceStats`.
* $`\omega` (§12): reports ready for accumulation. Fields: `ready`.
* $`\xi` (§12): recently accumulated packages. Fields: `accumulated`.

{leanSource JAM.State}

Timeslots are naturals below $`2^{32}` (eq. (4.28), $`\mathbb{N}_T \equiv \mathbb{N}_{2^{32}}`). The model stores them as `Nat` and keeps the
bound where an encoding needs it ($`\mathcal{E}_4`).

# The dependency graph
%%%
tag := "overview-graph"
%%%

The paper specifies $`\Upsilon` by saying what each part of the posterior state depends on. The symbol $`\prec`
reads "depends on":

$$`\begin{aligned} \tau' &\prec \mathbf{H} & \text{(4.5)} \\ \beta^\dagger_H &\prec (\mathbf{H}, \beta_H) & \text{(4.6)} \\ \gamma' &\prec (\mathbf{H}, \tau, \mathbf{E}_T, \gamma, \iota, \eta', \kappa', \psi') & \text{(4.7)} \\ \eta' &\prec (\mathbf{H}, \tau, \eta) & \text{(4.8)} \\ \kappa' &\prec (\mathbf{H}, \tau, \kappa, \gamma) & \text{(4.9)} \\ \lambda' &\prec (\mathbf{H}, \tau, \lambda, \kappa) & \text{(4.10)} \\ \psi' &\prec (\mathbf{E}_D, \psi) & \text{(4.11)} \\ \rho^\dagger &\prec (\mathbf{E}_D, \rho) & \text{(4.12)} \\ \rho^\ddagger &\prec (\mathbf{E}_A, \rho^\dagger) & \text{(4.13)} \\ \rho' &\prec (\mathbf{E}_G, \rho^\ddagger, \kappa, \tau') & \text{(4.14)} \\ \mathbf{R}^* &\prec (\mathbf{E}_A, \rho^\dagger) & \text{(4.15)} \\ (\omega', \xi', \delta^\ddagger, \chi', \iota', \varphi', \theta', \mathbf{S}) &\prec (\mathbf{R}^*, \omega, \xi, \delta, \chi, \iota, \varphi, \tau, \tau') & \text{(4.16)} \\ \beta'_H &\prec (\mathbf{H}, \mathbf{E}_G, \beta^\dagger_H, \theta') & \text{(4.17)} \\ \delta' &\prec (\mathbf{E}_P, \delta^\ddagger, \tau') & \text{(4.18)} \\ \alpha' &\prec (\mathbf{H}, \mathbf{E}_G, \varphi', \alpha) & \text{(4.19)} \\ \pi' &\prec (\mathbf{E}_G, \mathbf{E}_P, \mathbf{E}_A, \mathbf{E}_T, \tau, \kappa', \pi, \mathbf{H}, \mathbf{S}) & \text{(4.20)} \end{aligned}`

The daggered terms are intermediate values: $`\beta^\dagger_H` is recent history with the parent's state root
corrected, $`\rho^\dagger` and $`\rho^\ddagger` are the availability assignments after disputes and after assurances, $`\mathbf{R}^*`
the reports that have just become available, $`\delta^\ddagger` the accounts after accumulation, and $`\mathbf{S}` the
accumulation statistics.

{api}`JAM.importBlock` computes the parts in an order consistent with this graph. Each step is
marked in its source with the section it implements. Each step's binding or function, what it
computes, and the equations and section:

* header checks, `slot`: $`\tau' = \mathbf{H}_T`; (4.5), (5.2), (5.4), (5.9) ({ref "overview-header"}[§5]).
* `recentDagger`: $`\beta^\dagger_H`; (4.6) ({ref "history"}[§7]).
* `disputesTransition`: $`\psi'`, $`\rho^\dagger`; (4.11), (4.12) (§10).
* `safrole`: $`\gamma'`, $`\eta'`, $`\kappa'`, $`\lambda'`; (4.7)–(4.10) ({ref "safrole"}[§6]).
* `assurances`: $`\rho^\ddagger`, $`\mathbf{R}^*`; (4.13), (4.15) (§11).
* `guarantees`: $`\rho'`; (4.14) (§11).
* `accumulate`: $`\omega'`, $`\xi'`, $`\delta^\ddagger`, $`\chi'`, $`\iota'`, $`\varphi'`, $`\theta'`, $`\mathbf{S}`; (4.16) (§12).
* `recentHistory`: $`\beta'`; (4.17) ({ref "history"}[§7]).
* `preimages`: $`\delta'`; (4.18) (§12).
* `authorizations`: $`\alpha'`; (4.19) ({ref "authorization"}[§8]).
* `validatorStats`, `coreStats`, `serviceStats`: $`\pi'`; (4.20) (§13).

The graph lists dependencies, not every input each section reads. The model passes each
section-level function what that section's own equations use. Where that differs from the graph:

* *Guarantees.* (4.14) lists $`\kappa`. The equations of §11 use the posterior keys $`\kappa'` and $`\lambda'`, the posterior
  entropy $`\eta'`, the offenders in $`\psi'` (through the key filter $`\Phi`), and $`\beta^\dagger_H`, $`\alpha` and $`\delta`. The model's guarantee
  step reads those.
* *Preimages.* The model checks $`\mathbf{E}_P` against the prior accounts $`\delta` as well as $`\delta^\ddagger`, as §12.4 does: the
  data must have been solicited but not yet provided in the prior state.
* *The timeslot.* The model sets $`\tau' = \mathbf{H}_T` directly. The check that $`\mathbf{H}_T` is after $`\tau` is made by
  {api}`JAM.safrole` (its `badSlot` error).

{leanSource JAM.importBlock}

# The header (§5)
%%%
tag := "overview-header"
%%%

$$`\mathbf{H} \equiv (\mathbf{H}_P, \mathbf{H}_R, \mathbf{H}_X, \mathbf{H}_T, \mathbf{H}_E, \mathbf{H}_W, \mathbf{H}_O, \mathbf{H}_I, \mathbf{H}_V, \mathbf{H}_S) \qquad \text{(5.1)}`

The parent hash, the prior state root, the extrinsic hash, the timeslot, the epoch, winning-tickets
and offenders markers, the author's index, the entropy-yielding VRF signature and the seal:

{leanSource JAM.Header}

The markers' types:

$$`\mathbf{H}_E \in \left\lgroup \mathbb{H}, \mathbb{H}, \llbracket \left\lgroup \tilde{\mathbb{H}}, \bar{\mathbb{H}} \right\rgroup \rrbracket_{\mathsf{V}} \right\rgroup?, \qquad \mathbf{H}_W \in \llbracket \mathbb{T} \rrbracket_{\mathsf{E}}?, \qquad \mathbf{H}_O \in \llbracket \bar{\mathbb{H}} \rrbracket \qquad \text{(5.11)}`

$`\tilde{\mathbb{H}}` and $`\bar{\mathbb{H}}` are Bandersnatch and Ed25519 keys (§3.8.2). The model's {api}`JAM.EpochMark` and the option
types hold them; the lengths $`\mathsf{V}` and $`\mathsf{E}` are fixed by the decoder ({api}`JAM.Header.decode`), not by the types.

## The header's conditions

$$`\mathbf{H}_P \in \mathbb{H}, \quad \mathbf{H}_P \equiv \mathcal{H}(\mathcal{E}(P(\mathbf{H}))) \qquad \text{(5.2)}`

$$`h \in \mathcal{A} \Leftrightarrow h = \mathbf{H} \vee (\exists i \in \mathcal{A} : h = P(i)) \qquad \text{(5.3)}`

$$`\mathbf{H}_T \in \mathbb{N}_T, \quad P(\mathbf{H})_T < \mathbf{H}_T \wedge \mathbf{H}_T \cdot \mathsf{P} \leq \mathcal{T} \qquad \text{(5.8)}`

$$`\mathbf{H}_R \in \mathbb{H}, \quad \mathbf{H}_R \equiv \mathcal{M}_\sigma(\sigma) \qquad \text{(5.9)}`

$$`\mathbf{H}_I \in \mathbb{N}_{|\kappa'|}, \quad \mathbf{H}_A \equiv \kappa'[\mathbf{H}_I]_b \qquad \text{(5.10)}`

$`P(\mathbf{H})` is the parent header and $`\mathcal{T}` the wall clock. A header's hash is $`\mathcal{H}(\mathcal{E}(\mathbf{H}))`, {api}`JAM.Header.hash`:

{leanSource JAM.Header.hash}

{api}`JAM.importBlock` checks these conditions as follows:

* (5.2): $`\mathbf{H}_P` is the hash of the last header in the {api}`JAM.Chain` it is given.
* (5.3): the ancestor set is the chain's headers together with $`\mathbf{H}` itself. It is used only by the
  lookup-anchor check of §11 ({api}`JAM.lookupAnchorKnown`).
* (5.8): $`P(\mathbf{H})_T < \mathbf{H}_T` is checked as $`\tau < \mathbf{H}_T`, since $`\tau` is the parent's timeslot (Safrole's `badSlot`).
  $`\mathbf{H}_T \cdot \mathsf{P} \leq \mathcal{T}` is not checked: $`\Upsilon` has no clock.
* (5.9): $`\mathbf{H}_R` equals {api}`JAM.State.root`, the state Merklization $`\mathcal{M}_\sigma` of Appendix D.
* (5.10): $`\mathbf{H}_I < |\kappa'|`. $`\mathbf{H}_A` is the author key used to check the seal and the entropy source (§6.4,
  {api}`JAM.sealValid`).
* The markers $`\mathbf{H}_E` and $`\mathbf{H}_W` must equal the ones Safrole produces (§6.6), and $`\mathbf{H}_O` the one disputes
  produce (§10).

## The extrinsic hash

$$`\begin{aligned} \mathbf{H}_X &\in \mathbb{H}, \quad \mathbf{H}_X \equiv \mathcal{H}(\mathcal{E}(\mathcal{H}^\#(\mathbf{a}))) & \text{(5.4)} \\ \text{where } \mathbf{a} &= \left[\mathcal{E}_T(\mathbf{E}_T), \mathbf{p}, \mathbf{g}, \mathcal{E}_A(\mathbf{E}_A), \mathcal{E}_D(\mathbf{E}_D)\right] & \text{(5.5)} \\ \text{and } \mathbf{p} &= \mathcal{E}\left(\updownarrow\left[\left(\mathcal{E}_4(s), \mathcal{H}(\mathbf{d})\right) \;\middle|\; (s, \mathbf{d}) \mathrel{\mathrlap{<}{-}} \mathbf{E}_P\right]\right) & \text{(5.6)} \\ \text{and } \mathbf{g} &= \mathcal{E}\left(\updownarrow\left[\left(\mathcal{H}(r), \mathcal{E}_4(t), \mathcal{E}_C(a)\right) \;\middle|\; (r, t, a) \mathrel{\mathrlap{<}{-}} \mathbf{E}_G\right]\right) & \text{(5.7)} \end{aligned}`

$`\mathcal{H}^\#` applies $`\mathcal{H}` to each element. Preimages and work reports enter by their hashes, so that each can be shown to be
included without the whole extrinsic. $`\mathcal{E}_C` is the credential encoding of Appendix C; the model's
{api}`JAM.encodeCredential`.

{leanSource JAM.Extrinsic.hashParts}

{leanSource JAM.Extrinsic.hash}

$`\mathcal{E}(\mathcal{H}^\#(\mathbf{a}))` is the concatenation of the five hashes: a sequence of fixed-length hashes is encoded without
a length prefix. The model's `flatMap hashL` is that concatenation.

# Readings chosen
%%%
tag := "overview-readings"
%%%

The notes named below are in the model's [notes on the paper](https://github.com/ascrivener/jam-lean/blob/main/docs/upstream-candidates.md#gray-paper-issues).

* *No clock (note v0.8.1-A30).* The paper's $`\Upsilon` assumes a universally known clock $`\mathcal{T}`. The model's {api}`JAM.importBlock` has none, so
  it does not check $`\mathbf{H}_T \cdot \mathsf{P} \leq \mathcal{T}`; a caller that has a clock checks it separately.
* *The ancestors (note v0.8.1-A31).* $`\mathcal{A}` is defined from $`\mathbf{H}` by following parents back to genesis; the paper only requires
  nodes to keep the headers of the last $`\mathsf{L}` = 24 hours. The model takes the kept headers as an argument
  ({api}`JAM.Chain`). When the list is empty (no parent header kept), the $`\mathbf{H}_P` check is skipped.
* *Errors (note v0.8.1-A32).* The paper names no errors for an invalid block. The model reports the first section
  whose check fails, in the order of {api}`JAM.importBlock` ({api}`JAM.BlockError`).
