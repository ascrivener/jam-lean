import VersoManual
import Companion.Source
import Companion.Paper
import Companion.Docstring
import JAM.Safrole
import JAM.Theorems.Safrole

open Verso.Genre Manual
open Companion
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "§6 Safrole: block production and chain growth" =>
%%%
tag := "safrole"
shortTitle := "§6 Safrole"
file := "safrole"
%%%

*In the paper:* {gpchapter}`sec:blockproduction`.

*In brief.* Safrole decides who may author each block. Time is cut into six-second timeslots,
grouped into epochs of 600, and each slot has exactly one key that may seal a block in it; this
keeps the rate of blocks steady and makes forks, competing blocks with the same number of ancestors, rare.
Normally the slots are assigned by anonymous *tickets*: in the first 500 slots of an epoch, the
validators of the next epoch submit tickets that each prove the sender is one of them without saying
which one, and the best-scoring tickets become the next epoch's slots, so only a slot's owner
knows in advance that it is theirs and an attacker cannot tell whom to target. If too few tickets
arrive, a fallback assigns the slots to keys chosen with on-chain randomness, which keeps the chain
going but is not anonymous.

Safrole also keeps that randomness, the entropy pool, which guarantor
assignments ({ref "reports"}[§11]) and services use, and at each epoch change it rotates the
validator key sets, replacing an incoming key that belongs to an offender found by the disputes
system ({ref "disputes"}[§10]) with a null key. The header fields it relies on are in
{ref "overview"}[§5], and the ring signatures behind the tickets in {ref "bandersnatch"}[Appendix G].

*Key terms:*

* $`\thetime`, the most recent block's timeslot;
* $`\entropy`, the entropy pool;
* $`\sealtickets`, the current epoch's slot-sealer sequence, and $`\ticketaccumulator`, the tickets
  collected so far for the next epoch;
* $`\activeset`, the active validators; $`\previousset`, the previous epoch's; $`\pendingset`, the
  next epoch's; $`\stagingset`, the keys queued behind them.

Safrole fixes which validator may seal each timeslot of an epoch. Validators submit anonymous
tickets during an epoch, and the best tickets become the next epoch's slot sealers. If there are
not enough tickets, a fallback sequence of keys drawn with on-chain entropy is used instead. In
the model, the whole transition of GP v0.8.1 §6 is one function, {api}`JAM.safrole`; the seal and entropy-source
conditions on the header (eqs. {eq}`6.17`–{eq}`6.19`) are checked separately, by {api}`JAM.sealValid`. This chapter
goes through it in the paper's order: the entropy accumulator (§6.4), the slot-sealer sequence with
$`Z` and $`F` (§6.5), and the ticket accumulator (§6.7).

The whole module, `JAM/Safrole.lean`, opens with a docstring listing the paper's equations it
covers. Its full API is on the [doc-gen4 page](https://ascrivener.github.io/jam-lean/api/JAM/Safrole.html).

# The state

The paper's Safrole state is $`\gamma = (\gamma_P, \gamma_Z, \gamma_S, \gamma_A)` {eq}`6.3`, together
with $`\tau`, $`\eta` and the key sets $`\kappa`, $`\lambda` and $`\iota`. The model keeps them in one structure:

{mathdoc JAM.SafroleState}

# The entropy accumulator (§6.4)
%%%
tag := "safrole-entropy"
%%%

$`\eta \in \llbracket\mathbb{H}\rrbracket_4` {eq}`6.23`. Every block folds the VRF output of its entropy source into
$`\eta_0`, and an epoch change rotates $`\eta_0, \eta_1, \eta_2` into $`\eta_1, \eta_2, \eta_3`:

{gpeq "6.24, 6.25"}

One reading appears in the model:

* $`\mathcal{Y}(\mathbf{H}_V)`, the VRF output of the header's entropy-source signature, is an input to the transition
  (`SafroleInput.entropy`). The header condition it comes from, {eq}`6.19`, is checked
  separately by {api}`JAM.sealValid`.

$`\mathcal{H}` is Blake2b-256, the paper's hash function ({ref "primitives"}[§3.8]), here {api}`JAM.blake`.
In {api}`JAM.safrole` these are the lines under `-- Entropy (§6.4)`: `eta0'` and the triple
`(eta1', eta2', eta3')`.

{leanSource JAM.blake}

# The slot-sealer sequence (§6.5)
%%%
tag := "safrole-sealers"
%%%

The posterior sealer sequence $`\gamma'_S` {eq}`6.26` is the outside-in ordering $`Z(\gamma_A)` of the
ticket accumulator when the block opens the next epoch, the previous block was in the closing
period ($`m \geq \mathsf{Y}`) and $`\gamma_A` is full. Within an epoch it is unchanged. Otherwise it is the fallback keys:

{gpeq "6.26"}

In the model this is the `sealKeys'` binding of {api}`JAM.safrole`, with the three cases in the
paper's order.

## Z, the outside-in sequencer

{transcribed "6.27" "562b74cb04"}

$$`Z \colon \mathbf{s} \mapsto \left[\mathbf{s}_0, \mathbf{s}_{|\mathbf{s}|-1}, \mathbf{s}_1, \mathbf{s}_{|\mathbf{s}|-2}, \dots\right] \qquad \text{(6.27)}`

{leanSource JAM.outsideIn}

The paper gives $`Z` only by its first four entries. The model takes entry $`i` from index $`i/2` when $`i` is
even and from index $`|\mathbf{s}| - 1 - \lfloor i/2 \rfloor` when $`i` is odd. The paper's typing $`\llbracket \mathbb{T}\rrbracket_{\mathsf{E}} \to \llbracket \mathbb{T}\rrbracket_{\mathsf{E}}` needs only
that the length is preserved; the theorems below show that, and also that this reading is a permutation:

{mathdoc JAM.outsideIn_perm}

{mathdoc JAM.length_outsideIn}

## F, the fallback key sequence

{transcribed "6.28" "23e8046198"}

$$`F \colon (r, \mathbf{k}) \mapsto \left[\, \left(\mathbf{k}^{\circlearrowleft}_{\mathcal{E}_4^{-1}\left(\mathcal{H}(r \frown \mathcal{E}_4(i))_{\dots 4}\right)}\right)_b \;\middle|\; i \in \mathbb{N}_{\mathsf{E}} \right] \qquad \text{(6.28)}`

{leanSource JAM.fallbackKeys}

The cyclic index $`\mathbf{k}^{\circlearrowleft}` is `j % k.length`. `getD … ValidatorKey.null` keeps the function total when
$`\mathbf{k}` is empty. The paper never calls $`F` with an empty $`\mathbf{k}`, because $`|\kappa'| = \mathsf{V}`.

{mathdoc JAM.safrole_sealKeys_length}

# The tickets extrinsic and the ticket accumulator (§6.7)
%%%
tag := "safrole-tickets"
%%%

A ticket carries an entry index below $`n` and a Ring VRF proof over the context
$`\mathsf{X}_T \frown \eta'_2 \mathbin{+\!\!+} e` {eq}`6.31` ($`\mathsf{X}_T` is `$jam_ticket_seal`). The extrinsic is bounded by $`\mathsf{K}` before the
epoch's tail and by 0 within it {eq}`6.32`:

{gpeq "6.31, 6.32"}

{leanSource JAM.maxAttempts}

{mathdoc JAM.maxAttempts_spec}

{leanSource JAM.ticketContext}

The new accumulator keeps the $`\mathsf{E}` lowest identifiers of the union of the new tickets $`\mathbf{n}` with the old
accumulator, or with nothing at an epoch change. Every submitted ticket must survive:

{gpeq "6.36, 6.37"}

In {api}`JAM.safrole` this is the `acc'` binding: a merge sort by identifier, then `take E`, and
the `uselessTicket` check for $`\mathbf{n} \subseteq \gamma'_A`. The order on identifiers is {api}`JAM.octetLt`:

{leanSource JAM.octetLt}

What the model proves about the accumulator:

{mathdoc JAM.safrole_accumulator_length}

{mathdoc JAM.safrole_accumulator_sorted}

The winning-tickets marker $`\mathbf{H}_W` (eq. {eq}`6.30`) is $`Z(\gamma_A)` in the first block after the submission period
when the accumulator is full, and $`\emptyset` otherwise:

{mathdoc JAM.safrole_ticketsMark_length}

# Readings chosen
%%%
tag := "safrole-readings"
%%%

The paper leaves several points of §6.7 open, and the model decides each one. They are recorded as
note 31 of the model's
[notes on the paper](https://github.com/ascrivener/jam-lean/blob/main/docs/upstream-candidates.md#gray-paper-issues):

* *The order on identifiers.* Tickets are ordered by their identifier $`y \in \mathbb{H}`, but no order on $`\mathbb{H}` is
  defined. The model compares octet sequences lexicographically ({api}`JAM.octetLt`), the evident
  reading and the one the test vectors use.
* *The entry index in the context.* $`\mathsf{X}_T \frown \eta'_2 \mathbin{+\!\!+} e` appends a natural number to an
  octet sequence without saying how it is encoded. The model appends one octet ({api}`JAM.ticketContext`), and
  proves that one octet holds every allowed $`e` when $`2\mathsf{E} \le 256 \cdot |\gamma'_P|`. That holds for the full and tiny
  chains whenever there are at least 6 pending validators ($`|\gamma'_P| \ge 6`), as the second theorem assumes:

{mathdoc JAM.safrole_attempt_fits}

{mathdoc JAM.attempt_fits_of_six}

* *Errors and their order.* No errors are named for an invalid $`\mathbf{E}_T`, and no order is given between
  its conditions. The model uses the test vectors' error names (`SafroleError`), in the order given
  in the module docstring.

# The transition

For reference, here is the whole transition. Each block of it is marked with the paper section it
implements:

{leanSource JAM.safrole}

Here is the transition on two epoch changes from the test vectors. In the first the ticket accumulator
is full, so tickets seal the new epoch; in the second no tickets were submitted, so the fallback keys do:

{example "safrole-epoch-change"}

{example "safrole-epoch-change-fallback"}
