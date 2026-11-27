import VersoManual
import Companion.Source
import JAM.Safrole
import JAM.Theorems.Safrole

open Verso.Genre Manual
open Companion

set_option pp.rawOnError true

#doc (Manual) "§6 Safrole: block production and chain growth" =>
%%%
tag := "safrole"
shortTitle := "§6 Safrole"
%%%

Safrole fixes which validator may seal each timeslot of an epoch. Validators submit anonymous
tickets during an epoch, and the best tickets become the next epoch's slot sealers. If there are
not enough tickets, a fallback sequence of keys drawn with on-chain entropy is used instead. In
the model, the whole transition of GP v0.8.1 §6 is one function, {name}`JAM.safrole`. This chapter
goes through it in the paper's order: the entropy accumulator (§6.4), the slot-sealer sequence with
Z and F (§6.5), and the ticket accumulator (§6.7).

The whole module, `JAM/Safrole.lean`, opens with a docstring listing the paper's equations it
covers. Its full API is on the [doc-gen4 page](/jam-lean/api/JAM/Safrole.html).

# The state

The paper's Safrole state is γ = (γ_P, γ_Z, γ_S, γ_A) (eq. `consensusstatecomposition`), together
with τ, η and the key sets κ, λ and ι. The model keeps them in one structure:

{docstring JAM.SafroleState}

# The entropy accumulator (§6.4)
%%%
tag := "safrole-entropy"
%%%

η ∈ ⟦ℍ⟧₄ (eq. `entropycomposition`). Every block folds the VRF output of its entropy source into
η₀, and an epoch change rotates η₀, η₁, η₂ into η₁, η₂, η₃:

$$`\eta'_0 \equiv \mathcal{H}\left(\eta_0 \frown \mathcal{Y}(\mathbf{H}_V)\right) \qquad \left(\eta'_1, \eta'_2, \eta'_3\right) \equiv \begin{cases} (\eta_0, \eta_1, \eta_2) & \text{when } e' > e \\ (\eta_1, \eta_2, \eta_3) & \text{otherwise} \end{cases}`

Two readings appear in the model:

* 𝒴(𝐇_V), the VRF output of the header's entropy-source signature, is an input to the transition
  (`SafroleInput.entropy`). The header condition it comes from, eq. `vrfsigcheck`, is checked
  separately by {name}`JAM.sealValid`.
* ℋ is Blake2b-256 ({name}`JAM.blake`).

In {name}`JAM.safrole` these are the lines under `-- Entropy (§6.4)`: `eta0'` and the triple
`(eta1', eta2', eta3')`.

{leanSource JAM.blake}

# The slot-sealer sequence (§6.5)
%%%
tag := "safrole-sealers"
%%%

The posterior sealer sequence γ_S′ (eq. `slotkeysequence`) is the outside-in ordering of the ticket
accumulator when that accumulator is full at the end of the previous epoch. Otherwise it is the
fallback keys:

$$`\gamma'_S \equiv \begin{cases} Z(\gamma_A) & \text{when } e' = e + 1 \wedge m \geq \mathsf{Y} \wedge |\gamma_A| = \mathsf{E} \\ \gamma_S & \text{when } e' = e \\ F(\eta'_2, \kappa') & \text{otherwise} \end{cases}`

In the model this is the `sealKeys'` binding of {name}`JAM.safrole`, with the three cases in the
paper's order.

## Z, the outside-in sequencer

$$`Z \colon \mathbf{s} \mapsto \left[\mathbf{s}_0, \mathbf{s}_{|\mathbf{s}|-1}, \mathbf{s}_1, \mathbf{s}_{|\mathbf{s}|-2}, \dots\right]`

{leanSource JAM.outsideIn}

The paper gives Z only by its first four entries. The model takes entry i from index i/2 when i is
even and from index |s| − 1 − ⌊i/2⌋ when i is odd. The theorems below show that this reading is a
permutation, as the paper's typing ⟦T⟧_𝖤 → ⟦T⟧_𝖤 requires:

{docstring JAM.outsideIn_perm}

{docstring JAM.length_outsideIn}

## F, the fallback key sequence

$$`F \colon (r, \mathbf{k}) \mapsto \left[\, \left(\mathbf{k}^{\circlearrowleft}_{\mathcal{E}_4^{-1}\left(\mathcal{H}(r \frown \mathcal{E}_4(i))_{\dots 4}\right)}\right)_b \;\middle|\; i \in \mathbb{N}_{\mathsf{E}} \right]`

{leanSource JAM.fallbackKeys}

The cyclic index 𝐤^↻ is `j % k.length`. `getD … ValidatorKey.null` keeps the function total when
𝐤 is empty. The paper never calls F with an empty 𝐤, because |κ′| = 𝖵.

{docstring JAM.safrole_sealKeys_length}

# The tickets extrinsic and the ticket accumulator (§6.7)
%%%
tag := "safrole-tickets"
%%%

A ticket carries an entry index below n and a Ring VRF proof over the context
`$jam_ticket_seal` ⌢ η₂′ ⌢ e (eq. `ticketsextrinsic`). The extrinsic is bounded by 𝖪 before the
epoch's tail and by 0 within it (eq. `enforceticketlimit`):

$$`\mathbf{E}_T \in \left\lbrack\left(e \in \mathbb{N}_n,\; p \in \bar{\mathbb{V}}^{\gamma'_Z}_{X_T \frown \eta'_2 \frown e}\langle[]\rangle\right)\right\rbrack \quad \text{where } n = \left\lceil \frac{2\mathsf{E}}{|\gamma'_P|} \right\rceil \qquad |\mathbf{E}_T| \le \begin{cases} \mathsf{K} & \text{when } m' < \mathsf{Y} \\ 0 & \text{otherwise} \end{cases}`

{leanSource JAM.maxAttempts}

{docstring JAM.maxAttempts_spec}

{leanSource JAM.ticketContext}

The new accumulator keeps the 𝖤 lowest identifiers of the union of the new tickets 𝐧 with the old
accumulator, or with nothing at an epoch change. Every submitted ticket must survive:

$$`\gamma'_A \equiv \overrightarrow{\left[x \in \mathbf{n} \cup \begin{cases} [] & \text{when } e' > e \\ \gamma_A & \text{otherwise} \end{cases} \;\middle\|\; x_y \right]}^{\mathsf{E}} \qquad \mathbf{n} \subseteq \gamma'_A`

In {name}`JAM.safrole` this is the `acc'` binding: a merge sort by identifier, then `take E`, and
the `uselessTicket` check for 𝐧 ⊆ γ_A′. The order on identifiers is {name}`JAM.octetLt`:

{leanSource JAM.octetLt}

What the model proves about the accumulator:

{docstring JAM.safrole_accumulator_length}

{docstring JAM.safrole_accumulator_sorted}

{docstring JAM.safrole_ticketsMark_length}

# Readings chosen
%%%
tag := "safrole-readings"
%%%

The paper leaves several points of §6.7 open, and the model decides each one. They are recorded as
note 31 of the model's
[upstream candidates](https://github.com/ascrivener/jam-lean/blob/main/docs/upstream-candidates.md):

* *The order on identifiers.* Tickets are ordered by their identifier y ∈ ℍ, but no order on ℍ is
  defined. The model compares octet sequences lexicographically ({name}`JAM.octetLt`), the evident
  reading and the one the test vectors use.
* *The entry index in the context.* `$jam_ticket_seal` ⌢ η₂′ ⌢ e appends a natural number to an
  octet sequence without saying how. The model appends one octet ({name}`JAM.ticketContext`), and
  proves that one octet holds every allowed e for the full and tiny chains:

{docstring JAM.safrole_attempt_fits}

{docstring JAM.attempt_fits_of_six}

* *Errors and their order.* No errors are named for an invalid 𝐄_T, and no order is given between
  its conditions. The model uses the test vectors' error names (`SafroleError`), in the order given
  in the module docstring.

# The transition

For reference, here is the whole transition. Each block of it is marked with the paper section it
implements:

{leanSource JAM.safrole}
