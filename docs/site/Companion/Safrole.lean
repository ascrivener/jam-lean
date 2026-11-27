import VersoManual
import Companion.Source
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

Safrole fixes which validator may seal each timeslot of an epoch. Validators submit anonymous
tickets during an epoch, and the best tickets become the next epoch's slot sealers. If there are
not enough tickets, a fallback sequence of keys drawn with on-chain entropy is used instead. In
the model, the whole transition of GP v0.8.1 §6 is one function, {api}`JAM.safrole`. This chapter
goes through it in the paper's order: the entropy accumulator (§6.4), the slot-sealer sequence with
$`Z` and $`F` (§6.5), and the ticket accumulator (§6.7).

The whole module, `JAM/Safrole.lean`, opens with a docstring listing the paper's equations it
covers. Its full API is on the [doc-gen4 page](https://ascrivener.github.io/jam-lean/api/JAM/Safrole.html).

# The state

The paper's Safrole state is $`\gamma = (\gamma_P, \gamma_Z, \gamma_S, \gamma_A)` (eq. (6.3), `consensusstatecomposition`), together
with $`\tau`, $`\eta` and the key sets $`\kappa`, $`\lambda` and $`\iota`. The model keeps them in one structure:

{mathdoc JAM.SafroleState}

# The entropy accumulator (§6.4)
%%%
tag := "safrole-entropy"
%%%

$`\eta \in \llbracket\mathbb{H}\rrbracket_4` (eq. (6.23), `entropycomposition`). Every block folds the VRF output of its entropy source into
$`\eta_0`, and an epoch change rotates $`\eta_0, \eta_1, \eta_2` into $`\eta_1, \eta_2, \eta_3`:

$$`\eta'_0 \equiv \mathcal{H}\left(\eta_0 \frown \mathcal{Y}(\mathbf{H}_V)\right) \qquad \left(\eta'_1, \eta'_2, \eta'_3\right) \equiv \begin{cases} (\eta_0, \eta_1, \eta_2) & \text{if }e' > e \\ (\eta_1, \eta_2, \eta_3) & \text{otherwise} \end{cases} \qquad \text{(6.24, 6.25)}`

One reading appears in the model:

* $`\mathcal{Y}(\mathbf{H}_V)`, the VRF output of the header's entropy-source signature, is an input to the transition
  (`SafroleInput.entropy`). The header condition it comes from, eq. (6.19), `vrfsigcheck`, is checked
  separately by {api}`JAM.sealValid`.

$`\mathcal{H}` is Blake2b-256, the paper's hash function (§3.8), here {api}`JAM.blake`.
In {api}`JAM.safrole` these are the lines under `-- Entropy (§6.4)`: `eta0'` and the triple
`(eta1', eta2', eta3')`.

{leanSource JAM.blake}

# The slot-sealer sequence (§6.5)
%%%
tag := "safrole-sealers"
%%%

The posterior sealer sequence $`\gamma'_S` (eq. (6.26), `slotkeysequence`) is the outside-in ordering of the ticket
accumulator when that accumulator is full at the end of the previous epoch. Otherwise it is the
fallback keys:

$$`\gamma'_S \equiv \begin{cases} Z(\gamma_A) & \text{if }e' = e + 1 \wedge m \geq \mathsf{Y} \wedge |\gamma_A| = \mathsf{E} \\ \gamma_S & \text{if }e' = e \\ F(\eta'_2, \kappa') & \text{otherwise} \end{cases} \qquad \text{(6.26)}`

In the model this is the `sealKeys'` binding of {api}`JAM.safrole`, with the three cases in the
paper's order.

## Z, the outside-in sequencer

$$`Z \colon \mathbf{s} \mapsto \left[\mathbf{s}_0, \mathbf{s}_{|\mathbf{s}|-1}, \mathbf{s}_1, \mathbf{s}_{|\mathbf{s}|-2}, \dots\right] \qquad \text{(6.27)}`

{leanSource JAM.outsideIn}

The paper gives $`Z` only by its first four entries. The model takes entry $`i` from index $`i/2` when $`i` is
even and from index $`|\mathbf{s}| - 1 - \lfloor i/2 \rfloor` when $`i` is odd. The theorems below show that this reading is a
permutation, as the paper's typing $`\llbracket T\rrbracket_{\mathsf{E}} \to \llbracket T\rrbracket_{\mathsf{E}}` requires:

{mathdoc JAM.outsideIn_perm}

{mathdoc JAM.length_outsideIn}

## F, the fallback key sequence

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
$`\mathsf{X}_T \frown \eta'_2 \mathbin{+\!\!+} e` (eq. (6.31), `ticketsextrinsic`; $`\mathsf{X}_T` is `$jam_ticket_seal`). The extrinsic is bounded by $`\mathsf{K}` before the
epoch's tail and by 0 within it (eq. (6.32), `enforceticketlimit`):

$$`\mathbf{E}_T \in \left\lbrack\left(e \in \mathbb{N}_n,\; p \in \mathring{\mathbb{V}}^{[]}_{\gamma'_Z}\langle X_T \frown \eta'_2 \mathbin{+\!\!+} e \rangle\right)\right\rbrack \quad \text{where } n = \left\lceil \frac{2\mathsf{E}}{|\gamma'_P|} \right\rceil \qquad |\mathbf{E}_T| \le \begin{cases} \mathsf{K} & \text{if }m' < \mathsf{Y} \\ 0 & \text{otherwise} \end{cases} \qquad \text{(6.31, 6.32)}`

{leanSource JAM.maxAttempts}

{mathdoc JAM.maxAttempts_spec}

{leanSource JAM.ticketContext}

The new accumulator keeps the $`\mathsf{E}` lowest identifiers of the union of the new tickets $`\mathbf{n}` with the old
accumulator, or with nothing at an epoch change. Every submitted ticket must survive:

$$`\gamma'_A \equiv \overrightarrow{\left[x \in \mathbf{n} \cup \begin{cases} \emptyset & \text{if }e' > e \\ \gamma_A & \text{otherwise} \end{cases} \;\wr\; x_y \right]}^{\mathsf{E}} \qquad \mathbf{n} \subseteq \gamma'_A \qquad \text{(6.36, 6.37)}`

In {api}`JAM.safrole` this is the `acc'` binding: a merge sort by identifier, then `take E`, and
the `uselessTicket` check for $`\mathbf{n} \subseteq \gamma'_A`. The order on identifiers is {api}`JAM.octetLt`:

{leanSource JAM.octetLt}

What the model proves about the accumulator:

{mathdoc JAM.safrole_accumulator_length}

{mathdoc JAM.safrole_accumulator_sorted}

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
  proves that one octet holds every allowed $`e` for the full and tiny chains:

{mathdoc JAM.safrole_attempt_fits}

{mathdoc JAM.attempt_fits_of_six}

* *Errors and their order.* No errors are named for an invalid $`\mathbf{E}_T`, and no order is given between
  its conditions. The model uses the test vectors' error names (`SafroleError`), in the order given
  in the module docstring.

# The transition

For reference, here is the whole transition. Each block of it is marked with the paper section it
implements:

{leanSource JAM.safrole}
