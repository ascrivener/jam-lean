import VersoManual
import Companion.Source
import Companion.Paper
import Companion.Docstring
import JAM.Account
import JAM.Accumulate
import JAM.State
import JAM.Theorems.Confinement

open Verso.Genre Manual
open Companion
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "§9 Service accounts" =>
%%%
tag := "accounts"
shortTitle := "§9 Service accounts"
file := "accounts"
%%%

*In the paper:* {gpchapter}`sec:accounts`.

A service in JAM has code, storage and a balance, much like a smart contract. GP v0.8.1 §9 defines
the account record, the preimage lookups that make data available to in-core code, the deposit an
account must hold for what it stores, the privileged services and, new in v0.8.1, supervisors. This
chapter follows the paper's order: the account (§9), code and gas (§9.1), preimage lookups (§9.2),
the footprint and threshold balance (§9.3), privileges (§9.4) and supervisors (§9.5).

The model's account is in `JAM/Account.lean`; its full API is on the
[doc-gen4 page](https://ascrivener.github.io/jam-lean/api/JAM/Account.html).

# The account
%%%
tag := "accounts-account"
%%%

Service accounts are a partial mapping from service identifiers to account records:

{gpeq "9.1, 9.2"}

{leanSource JAM.Accounts}

An account is the storage dictionary $`\mathbf{s}`, the preimage dictionaries $`\mathbf{p}` and
$`\mathbf{l}`, the gratis storage offset $`f`, the code hash $`c`, the balance $`b`, the supervisor
$`u` with its creation slot $`d` and the supervisor balance $`x`, the gas limits $`g` and $`m`, the
creation slot $`r`, the slot of the most recent accumulation $`a`, and the parent service $`p`:

{gpeq "9.3"}

The model's record, {api}`JAM.ServiceAccount`, keeps the same fields, with two differences of form:
$`\mathbf{s}` and $`\mathbf{l}` share one dictionary, `entries`, and the footprint terms $`a_i` and
$`a_o` of §9.3 are stored fields, `items` and `octets`. Why, and what that costs, is explained
{ref "accounts-entries"}[below]. The field types are also wider than the paper's: the numeric fields
are unbounded natural numbers rather than $`\mathbb{N}_B`, $`\mathbb{N}_S`, $`\mathbb{N}_T` or
$`\mathbb{N}_G`, and the code hash is an octet list of any length rather than $`\mathbb{H}` (see
{ref "accounts-readings"}[the readings]).

{leanSource JAM.ServiceAccount}

# Code and gas (§9.1)
%%%
tag := "accounts-code"
%%%

An account's code is the preimage of its code hash:

{gpeq "9.4"}

{leanSource JAM.ServiceAccount.code}

`none` stands for a code hash with no preimage. The gas limits $`g` (per work item) and $`m` (per
deferred transfer) are the fields `minAccGas` and `minMemoGas`.

# Preimage lookups (§9.2)
%%%
tag := "accounts-lookups"
%%%

$`\mathbf{p}` maps a hash to its preimage, and $`\mathbf{l}` records, for a hash and a length, the
history of the preimage's availability. The paper's invariant ties the two together:

{gpeq "9.6"}

The model does not carry {eq}`9.6` as a property of {api}`JAM.ServiceAccount`, and no theorem yet
states that the transitions which change $`\mathbf{p}` and $`\mathbf{l}` preserve it.

A history of length 0 means the preimage is requested but not supplied; 1, available since
$`h_0`; 2, unavailable since $`h_1` after being available from $`h_0`; 3, available again since
$`h_2`. The historical lookup $`\Lambda` returns the preimage if it was available at time $`t`:

{transcribed "9.7" "76c008da78"}

$$`\Lambda(\mathbf{a}, t, h) \equiv \begin{cases} \mathbf{a}_\mathbf{p}[h] & \text{if } h \in \mathcal{K}(\mathbf{a}_\mathbf{p}) \wedge I(\mathbf{a}_\mathbf{l}[h, |\mathbf{a}_\mathbf{p}[h]|], t) \\ \emptyset & \text{otherwise} \end{cases} \qquad \text{(9.7)}`

$$`\text{where } I(\mathbf{l}, t) = \begin{cases} \bot & \text{if } [] = \mathbf{l} \\ x \le t & \text{if } [x] = \mathbf{l} \\ x \le t < y & \text{if } [x, y] = \mathbf{l} \\ x \le t < y \vee z \le t & \text{if } [x, y, z] = \mathbf{l} \end{cases}`

{leanSource JAM.ServiceAccount.availableAt}

{leanSource JAM.ServiceAccount.historicalLookup}

The paper first types $`\Lambda` with $`t` restricted to the last $`\mathsf{D}` slots,
$`\mathbb{N}_{(\mathbf{H}_T - \mathsf{D}) \dots \mathbf{H}_T}` (eq. {eq}`9.5`), and then defines it for
any $`t \in \mathbb{N}_T` in {eq}`9.7`. The model follows {eq}`9.7`: {api}`JAM.ServiceAccount.historicalLookup`
takes any $`t`; keeping $`t` in that range is left to its callers.

# Storage and requests in the model
%%%
tag := "accounts-entries"
%%%

{ref "statemerkle"}[Appendix D] (eq. {eq}`D.2`) serializes each storage item under the state key
$`C(s, \mathcal{E}_4(2^{32}-1) \frown \mathbf{k})` and each request under
$`C(s, \mathcal{E}_4(z) \frown h)`, where $`C(s, h)` (eq. {eq}`D.1`) interleaves $`\mathcal{E}_4(s)` with the
first 27 octets of $`\mathcal{H}(h)`. The paper adds that storage keys cannot be inspected or enumerated, so "implementations
are free to use this fact in order to avoid storing the keys themselves" (§D.1). The model does
this: it keys $`\mathbf{s}` and $`\mathbf{l}` by those 27 octets, in one dictionary, exactly as
$`T(\sigma)` holds them.

{leanSource JAM.ServiceAccount.stateKeyHash}

{leanSource JAM.ServiceAccount.storageKey}

{leanSource JAM.ServiceAccount.requestKey}

A request history is held in its serialized form, $`\mathcal{E}(\updownarrow[\mathcal{E}_4(x) \mid x \mathrel{\mathrlap{<}{-}} \mathbf{t}])`.
Every read and write of $`\mathbf{s}` and $`\mathbf{l}` goes through the accessors below, which take
the key the paper's caller has ($`\mathbf{k}`, or $`(h, z)`):

{leanSource JAM.ServiceAccount.storageGet}

{leanSource JAM.ServiceAccount.storageWrite}

{leanSource JAM.ServiceAccount.requestGet}

{leanSource JAM.ServiceAccount.requestSet}

{leanSource JAM.ServiceAccount.requestErase}

Reading a request back decodes the stored octets with {api}`JAM.ServiceAccount.decodeSlots`, which
inverts the encoding on histories of at most three slots that each fit in 4 octets:

{mathdoc JAM.ServiceAccount.decodeSlots_encodeSlots}

What the model proves about the accessors: a write reads back, and it leaves the other keys of the
same kind unchanged (a storage write every other storage key, a request write every other request),
where "other" means a different state key. A request write or erase also leaves every storage key
with a different state key unchanged.

{leanSource JAM.ServiceAccount.storageGet_write_same}

{mathdoc JAM.ServiceAccount.storageGet_write_other}

{mathdoc JAM.ServiceAccount.requestGet_set_same}

{leanSource JAM.ServiceAccount.requestGet_set_other}

{leanSource JAM.ServiceAccount.requestGet_erase_same}

{leanSource JAM.ServiceAccount.requestGet_erase_other}

{mathdoc JAM.ServiceAccount.storageGet_requestSet}

{leanSource JAM.ServiceAccount.storageGet_requestErase}

A storage write leaves the preimages $`\mathbf{p}`, $`f`, $`c`, $`b`, $`g`, $`m`, $`r`, $`a` and
the parent $`p` unchanged (the theorem does not cover $`u`, $`d`, $`x` or $`\mathbf{l}`):

{mathdoc JAM.ServiceAccount.storageWrite_frame}

The "different state key" hypotheses are about $`C`'s 27-octet hashes. The paper assumes that
$`C` has no collisions on the inputs that occur (§D.1: "Cryptographic hashing ensures that there
will be no duplicate state-keys given that there are no duplicate inputs to $`C`"); the theorems
make that assumption explicit instead.

# Footprint and threshold balance (§9.3)
%%%
tag := "accounts-footprint"
%%%

The number of items an account stores, $`a_i`, and the octets they take, $`a_o`, set the
threshold balance $`a_t` the account must hold:

{gpeq "9.8"}

{leanSource JAM.ServiceAccount.minBalance}

The subtraction is on natural numbers, which stops at 0, so it computes the paper's
$`\max(0, \dots)`.

The paper defines $`a_i` and $`a_o` from $`\mathbf{s}` and $`\mathbf{l}`. Since the model does not
keep the storage keys $`\mathbf{k}`, it cannot recompute $`|\mathbf{k}|` in $`a_o`; it carries
$`a_i` and $`a_o` as fields instead, and each accessor that writes $`\mathbf{s}` or $`\mathbf{l}`
({api}`JAM.ServiceAccount.storageWrite`, {api}`JAM.ServiceAccount.requestSet`,
{api}`JAM.ServiceAccount.requestErase`) changes them by exactly the amount it adds to or removes
from the paper's sums. {ref "statemerkle"}[Appendix D] serializes $`a_i` and $`a_o` explicitly, so a loaded state brings
its own values. That the fields equal the paper's formulas on every state the model's transitions
build is stated in the structure's docstring; it is not yet a theorem.

# Service privileges (§9.4)
%%%
tag := "accounts-privileges"
%%%

Five kinds of privilege are held in $`\chi`: the manager $`m`, the delegator $`v` (who sets
$`\iota`), the registrar $`r` (who creates services in the protected range), one assigner per core
$`\mathbf{a}` (who alter $`\phi`), and the always-accumulate services $`\mathbf{z}` with their gas:

{gpeq "9.9, 9.10"}

The model keeps them as the fields `manager`, `delegator`, `registrar`, `assigners` and `alwaysAcc`
of the state {api}`JAM.State` and of the partial state {api}`JAM.PartialState` that accumulation
works on (see {ref "accumulation"}[§12]).

# Supervisors (§9.5)
%%%
tag := "accounts-supervisors"
%%%

Each service has a designated supervisor $`u`, which may make any non-privileged change to it, and
a supervisor balance $`x` that only the supervisor may transfer and that counts with $`b` against
the threshold balance. The creation slot $`d` recorded with $`u` stops a new service that reuses an
ejected supervisor's identifier from inheriting its power. The effective supervisor is:

{gpeq "9.11"}

{leanSource JAM.effectiveSupervisor}

When the effective supervisor of $`k` is some other service $`s`, $`k` names $`s` as its supervisor
and records $`s`'s creation slot:

{mathdoc JAM.effectiveSupervisor_eq}

# Readings chosen
%%%
tag := "accounts-readings"
%%%

These are recorded as notes v0.8.1-A40 to A45 of the model's
[notes on the paper](https://github.com/ascrivener/jam-lean/blob/main/docs/upstream-candidates.md#gray-paper-issues):

* *Note v0.8.1-A40, storage and requests by state key.* The model stores $`\mathbf{s}` and $`\mathbf{l}` under the
  27-octet hashes that the state keys keep, as §D.1 permits, and so assumes, as the paper does,
  that $`C` has no collisions on the keys that occur. The accessor theorems above carry that
  assumption as a hypothesis.
* *Note v0.8.1-A41, request lengths outside $`\mathbb{N}_P`.* The keys of $`\mathbf{l}` are $`(\mathbb{H}, \mathbb{N}_P)`
  with $`\mathbb{N}_P = \mathbb{N}_{2^{32}-2}` (GP v0.8.1, Definitions). A length outside it has no
  request: {api}`JAM.ServiceAccount.requestGet` returns `none` for it
  ({api}`JAM.ServiceAccount.requestLenBound`).
* *Note v0.8.1-A42, stored octets that are not a history.* A request value that does not decode as at most three
  4-octet slots can only come from a state the model did not build (a loaded state). The model
  reads it as no request, and {api}`JAM.ServiceAccount.requestSet` and
  {api}`JAM.ServiceAccount.requestErase` treat it the same way. The paper does not cover such states.
* *Note v0.8.1-A43, footprint carried.* $`a_i` and $`a_o` are fields updated by every accessor that writes, rather than recomputed
  from $`\mathbf{s}` and $`\mathbf{l}` (see {ref "accounts-footprint"}[§9.3]).
* *Note v0.8.1-A44, wider types.* The paper types balances as $`\mathbb{N}_B`, identifiers as $`\mathbb{N}_S`,
  slots as $`\mathbb{N}_T`, gas as $`\mathbb{N}_G` and the code hash as $`\mathbb{H}`. The model's
  fields are unbounded natural numbers and an octet list of any length, so the types do not
  enforce these bounds.
* *Note v0.8.1-A45, totality.* $`I` is given for histories of length 0 to 3, the type $`\llbracket \mathbb{N}_T \rrbracket_{:3}`;
  {api}`JAM.ServiceAccount.availableAt` returns false for longer lists. $`\mathbf{d}[s]_e` is
  defined for $`s \in \mathcal{K}(\mathbf{d})`; {api}`JAM.effectiveSupervisor` returns $`s` for any
  other $`s`, which §12 relies on when a service without an account appears in a round.
