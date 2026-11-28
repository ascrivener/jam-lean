import VersoManual
import Companion.Source
import Companion.Paper
import Companion.Docstring
import JAM.State
import JAM.Block
import JAM.BlockImport
import JAM.Model

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

*In the paper:* {gpchapter}`sec:overview` and {gpchapter}`sec:header`.

*In brief.* JAM, like any blockchain, is a state and a rule for updating it. The state is
everything the chain remembers (the services and their balances, the validators, the work waiting
on each core), and each block is a bundle of inputs, a header plus the *extrinsic* data (tickets,
preimages, guarantees, assurances and disputes), from which the rule computes the next state. The
paper splits the state into named components and the rule into steps, each defined in its own
section, so most chapters of this book cover one step: who may author a block ({ref "safrole"}[§6]), the record
of recent blocks ({ref "history"}[§7]), and the pipeline that takes work from the cores into the
services' accounts ({ref "reports"}[§11], {ref "accumulation"}[§12]). This chapter is the map: it
shows the whole state, the block, the order in which the steps run and what each depends on, and
the header (§5), which names the parent block by its hash, gives the block's timeslot and its
author's index, and carries the author's seal.

*Key terms:*

* $`\thestate`, the state, and $`\thestate'`, the state after the block;
* $`\block`, the block: the header $`\header` and the extrinsic $`\extrinsic`;
* $`\transitionstate`, the block transition, which computes $`\thestate'` from $`\thestate` and $`\block`.

This chapter is the book's map. GP v0.8.1 §4 defines a blockchain by its state $`\sigma`, its blocks $`\mathbf{B}` and
one function, the block-level state transition $`\Upsilon`. It splits $`\sigma` into components and $`\Upsilon` into
section-level transitions, and orders them in a dependency graph. §5 defines the header and the
conditions a valid header meets. This chapter sets out those definitions, the model's
`JAM.State`, `JAM.Block`, `JAM.importBlock` and `JAM.importBlockWith` that implement them, and where each component is
covered in this book.

# The block transition
%%%
tag := "overview-upsilon"
%%%

{gpeq "4.1"}

The paper defines JAM by $`\Upsilon` together with a genesis state $`\sigma^0`. In the model, $`\Upsilon` is
{api}`JAM.importBlock`, the closed model: the parametric core {api}`JAM.importBlockWith` with the
cryptography fixed to JamCrypto's GP v0.8.1 primitives ({ref "bandersnatch-closed"}[Appendix G]).
It is the function a conformance proof targets; proofs are stated over the core.

{leanSource JAM.importBlock}

{api}`JAM.importBlockWith` returns the posterior state together with an {api}`JAM.ImportTrace` (the newly
available reports and the accumulation root), or the reason the block is invalid; its source is
quoted {ref "overview-graph"}[below].

Besides $`\sigma` and $`\mathbf{B}`, it takes three arguments the paper leaves implicit:

* the chain's constants, a {api}`JAM.Params` (see {ref "primitives-constants"}[§3, constants]);
* the cryptography, a {api}`JAM.Crypto`: signature and VRF verification, and the ring root. The
  core keeps these as a parameter; the paper-shaped modules never implement them. `JamCrypto`
  implements them, and {api}`JAM.importBlock` fixes them (only `JAM/Model.lean` imports `JamCrypto`),
  leaving the ring VRF's public setup as its one cryptographic input;
* the ancestor headers the importer has kept, a {api}`JAM.Chain`. The paper's ancestor set
  $`\mathbf{A}` (eq. {eq}`5.3`) is not part of $`\sigma`, and guarantees ({ref "reports"}[§11]) need it.

# The block
%%%
tag := "overview-block"
%%%

{gpeq "4.2, 4.3"}

The extrinsic $`\mathbf{E}` has five parts: tickets $`\mathbf{E}_T` ({ref "safrole"}[§6]), preimages $`\mathbf{E}_P` ({ref "accumulation"}[§12]), guarantees of work reports
$`\mathbf{E}_G` ({ref "reports"}[§11]), availability assurances $`\mathbf{E}_A` ({ref "reports"}[§11]) and disputes $`\mathbf{E}_D` ({ref "disputes"}[§10]).

{leanSource JAM.Block}

{leanSource JAM.Extrinsic}

# The state
%%%
tag := "overview-state"
%%%

{gpeq "4.4"}

The model's {api}`JAM.State` has one field per component. It flattens the components that are
tuples: $`\gamma = (\gamma_P, \gamma_Z, \gamma_S, \gamma_A)`, the privileges $`\chi` and the statistics $`\pi` each become several
fields. Each component, with the section that covers it, and its fields:

* $`\alpha` ({ref "authorization"}[§8]): authorizer pools. Fields: `authPools`.
* $`\beta` ({ref "history"}[§7]): recent blocks and the accumulation output log. Fields: `recent`.
* $`\theta` ({ref "history"}[§7], {ref "accumulation"}[§12]): the most recent accumulation outputs. Fields: `lastAccOut`.
* $`\gamma` ({ref "safrole"}[§6]): Safrole's state. Fields: `pending`, `ringRoot`, `sealKeys`, `accumulator`.
* $`\delta` ({ref "accounts"}[§9]): service accounts. Fields: `accounts`.
* $`\eta` ({ref "safrole"}[§6]): entropy. Fields: `eta`.
* $`\iota`, $`\kappa`, $`\lambda` ({ref "safrole"}[§6]): staging, active and previous validator keys. Fields: `staging`, `active`, `prev`.
* $`\rho` ({ref "reports"}[§11]): work reports awaiting availability, per core. Fields: `avail`.
* $`\tau` ({ref "safrole"}[§6]): the most recent block's timeslot. Fields: `tau`.
* $`\phi` ({ref "authorization"}[§8]): authorizer queues. Fields: `authQueue`.
* $`\chi` ({ref "accounts"}[§9], {ref "accumulation"}[§12]): privileged services. Fields: `manager`, `assigners`, `delegator`, `registrar`, `alwaysAcc`.
* $`\psi` ({ref "disputes"}[§10]): judgments. Fields: `disputes`.
* $`\pi` ({ref "statistics"}[§13]): validator, core and service statistics. Fields: `valStats`, `valStatsLast`, `coreStats`, `serviceStats`.
* $`\omega` ({ref "accumulation"}[§12]): reports ready for accumulation. Fields: `ready`.
* $`\xi` ({ref "accumulation"}[§12]): recently accumulated packages. Fields: `accumulated`.

{leanSource JAM.State}

Timeslots are naturals below $`2^{32}` (eq. {eq}`4.28`, $`\mathbb{N}_T \equiv \mathbb{N}_{2^{32}}`). The model stores them as `Nat`. {api}`JAM.importBlockWith` does not check
$`\mathbf{H}_T < 2^{32}`, and the four-octet encoding $`\mathcal{E}_4` the model uses (`Codec.fixed 4`) keeps only the low 32 bits
of a larger value.

# The dependency graph
%%%
tag := "overview-graph"
%%%

The paper specifies $`\Upsilon` by saying what each part of the posterior state depends on. The symbol $`\prec`
reads "depends on":

{gpeq "4.5, 4.6, 4.7, 4.8, 4.9, 4.10, 4.11, 4.12, 4.13, 4.14, 4.15, 4.16, 4.17, 4.18, 4.19, 4.20"}

The daggered terms are intermediate values: $`\beta^\dagger_H` is recent history with the parent's state root
corrected, $`\rho^\dagger` and $`\rho^\ddagger` are the availability assignments after disputes and after assurances, $`\mathbf{R}^*`
the reports that have just become available, $`\delta^\ddagger` the accounts after accumulation, and $`\mathbf{S}` the
accumulation statistics.

{api}`JAM.importBlockWith` computes the parts in an order consistent with this graph. Each step is
marked in its source with the section (and sometimes the equation) it implements. Each step's
binding or function, what it computes, and the equations and section:

* header checks, `slot`: $`\tau' = \mathbf{H}_T`; {eq}`4.5`, {eq}`5.2`, {eq}`5.4`, {eq}`5.9` ({ref "overview-header"}[§5]).
* `recentDagger`: $`\beta^\dagger_H`; {eq}`4.6` ({ref "history"}[§7]).
* `disputesTransition`: $`\psi'`, $`\rho^\dagger`; {eq}`4.11`, {eq}`4.12` ({ref "disputes"}[§10]).
* `safrole`: $`\gamma'`, $`\eta'`, $`\kappa'`, $`\lambda'`; {eq}`4.7`–{eq}`4.10` ({ref "safrole"}[§6]).
* `assurances`: $`\rho^\ddagger`, $`\mathbf{R}^*`; {eq}`4.13`, {eq}`4.15` ({ref "reports"}[§11]).
* `guarantees`: $`\rho'`; {eq}`4.14` ({ref "reports"}[§11]).
* `accumulate`: $`\omega'`, $`\xi'`, $`\delta^\ddagger`, $`\chi'`, $`\iota'`, $`\phi'`, $`\theta'`, $`\mathbf{S}`; {eq}`4.16` ({ref "accumulation"}[§12]).
* `accOutRoot`: $`\mathcal{M}_B(\mathbf{s}, \mathcal{H}_K)`, the root of $`\theta'`; {eq}`7.6` ({ref "history"}[§7]).
* `recentHistoryOf`: $`\beta'` from $`\beta^\dagger_H` (both $`\beta'_H`, eq. {eq}`4.17`, and $`\beta'_B`, eq. {eq}`7.7`) ({ref "history"}[§7]).
* `preimages`: $`\delta'`; {eq}`4.18` ({ref "accumulation"}[§12]).
* `authorizations`: $`\alpha'`; {eq}`4.19` ({ref "authorization"}[§8]).
* `validatorStats`, `coreStats`, `serviceStats`: $`\pi'`; {eq}`4.20` ({ref "statistics"}[§13]).

The graph lists dependencies, not every input each section reads. The model passes each
section-level function what that section's own equations use, and several steps read more than
their line of the graph lists:

* *Guarantees.* {eq}`4.14` lists $`\kappa`. The equations of {ref "reports"}[§11] use the posterior keys $`\kappa'` and $`\lambda'`, the posterior
  entropy $`\eta'`, the offenders in $`\psi'` (through the key filter $`\Phi`), and $`\beta^\dagger_H`, $`\alpha` and $`\delta`. The model's guarantee
  step reads those.
* *Preimages.* The model checks $`\mathbf{E}_P` against the prior accounts $`\delta` as well as $`\delta^\ddagger`, as {ref "accumulation"}[§12.4] does: the
  data must have been solicited but not yet provided in the prior state.
* *Other steps.* Disputes read $`\kappa`, $`\lambda` and $`\tau`. Assurances read $`\kappa`, $`|\kappa'|`, $`\mathbf{H}_P` and $`\mathbf{H}_T`. The guarantee
  step also reads the prior $`\beta_H`, $`\xi`, $`\omega` and $`\rho` (to find packages already known) and the ancestor set $`\mathbf{A}`.
  Accumulation reads $`\eta'_0` and $`\mathbf{H}_T`. The core statistics read the newly available reports $`\mathbf{R}`, and the validator statistics read
  the reporters $`\mathbf{G}` of the guarantees, which come from the assignments $`M` and $`M^*` (so from $`\lambda'`, $`\eta'_2`, $`\eta'_3` and $`\psi'_O`).
* *The timeslot.* The model sets $`\tau' = \mathbf{H}_T` directly. The check that $`\mathbf{H}_T` is after $`\tau` is made by
  {api}`JAM.safrole` (its `badSlot` error).

{leanSource JAM.importBlockWith}

# The header (§5)
%%%
tag := "overview-header"
%%%

{gpeq "5.1"}

The parent hash, the prior state root, the extrinsic hash, the timeslot, the epoch, winning-tickets
and offenders markers, the author's index, the entropy-yielding VRF signature and the seal:

{leanSource JAM.Header}

The markers' types:

{gpeq "5.11"}

$`\bskey` and $`\edkey` are Bandersnatch and Ed25519 keys (§3.8.2). The model's {api}`JAM.EpochMark` and the option
types hold them, and the types do not fix their lengths. The decoder ({api}`JAM.Header.decode`) fixes the
winning-tickets marker's $`\mathsf{E}`. The epoch marker's key list is length-prefixed (its encoding is $`\updownarrow\mathbf{k}`); its
length is enforced at import, because $`\mathbf{H}_E` must match the marker Safrole produces.

{leanSource JAM.EpochMark}

{leanSource JAM.Header.decode}

## The header's conditions

{gpeq "5.2"}

{gpeq "5.3"}

{gpeq "5.8"}

{gpeq "5.9"}

{gpeq "5.10"}

$`P(\mathbf{H})` is the parent header and $`\mathcal{T}` the wall clock. A header's hash is $`\mathcal{H}(\mathcal{E}(\mathbf{H}))`, {api}`JAM.Header.hash`:

{leanSource JAM.Header.hash}

{api}`JAM.importBlockWith` checks these conditions as follows:

* {eq}`5.2`: $`\mathbf{H}_P` is the hash of the last header in the {api}`JAM.Chain` it is given.
* {eq}`5.3`: the ancestor set is the chain's headers together with $`\mathbf{H}` itself. It is used only by the
  lookup-anchor check of {ref "reports"}[§11] ({api}`JAM.lookupAnchorKnown`). The retained headers are supplied by the
  caller: only the last is checked against $`\mathbf{H}_P`, and the model assumes, without checking, that they form a
  parent chain.
* {eq}`5.8`: $`P(\mathbf{H})_T < \mathbf{H}_T` is checked as $`\tau < \mathbf{H}_T`, since $`\tau` is the parent's timeslot (Safrole's `badSlot`).
  $`\mathbf{H}_T \cdot \mathsf{P} \leq \mathcal{T}` is not checked: $`\Upsilon` has no clock.
* {eq}`5.9`: $`\mathbf{H}_R` equals {api}`JAM.State.root`, the state Merklization $`\mathcal{M}_\sigma` of {ref "statemerkle"}[Appendix D].
* {eq}`5.10`: $`\mathbf{H}_I < |\kappa'|`. $`\mathbf{H}_A` is the author key used to check the seal and the entropy source ({ref "safrole"}[§6.4],
  {api}`JAM.sealValid`).
* The markers $`\mathbf{H}_E` and $`\mathbf{H}_W` must equal the ones Safrole produces ({ref "safrole"}[§6.6]), and $`\mathbf{H}_O` the one disputes
  produce ({ref "disputes"}[§10]).

{leanSource JAM.lookupAnchorKnown}

{leanSource JAM.sealValid}

## The extrinsic hash

{gpeq "5.4, 5.5, 5.6, 5.7"}

$`\mathcal{H}^\#` applies $`\mathcal{H}` to each element. Preimages and work reports enter by their hashes, so that each can be shown to be
included without the whole extrinsic. $`\mathcal{E}_C` is the credential encoding of {ref "codec"}[Appendix C]; the model's
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

* *No clock (note v0.8.1-A30).* The paper's $`\Upsilon` assumes a universally known clock $`\mathcal{T}`. The model's {api}`JAM.importBlockWith` has none, so
  it does not check $`\mathbf{H}_T \cdot \mathsf{P} \leq \mathcal{T}`; a caller must check it separately (the model has no such caller).
* *The ancestors (note v0.8.1-A31).* $`\mathbf{A}` is defined from $`\mathbf{H}` by following parents back to genesis; the paper only requires
  nodes to keep the headers of the last $`\mathsf{L}` = 24 hours. The model takes the kept headers as an argument
  ({api}`JAM.Chain`). When the list is empty (no parent header kept), the $`\mathbf{H}_P` check is skipped.
* *Errors (note v0.8.1-A32).* The paper names no errors for an invalid block. The model reports the first section
  whose check fails, in the order of {api}`JAM.importBlockWith` ({api}`JAM.BlockError`).
