import VersoManual
import Companion.Source
import Companion.Paper
import Companion.Docstring
import JAM.Trie
import JAM.State
import JAM.StateDecode
import JAM.Account

open Verso.Genre Manual
open Companion
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Appendix D: state Merklization" =>
%%%
tag := "statemerkle"
shortTitle := "D. State Merklization"
file := "state-merklization"
%%%

*In the paper:* {gpchapter}`sec:statemerklization`.

Appendix D of GP v0.8.1 commits to the whole state $`\sigma` with one 32-octet hash, the state root
$`\mathcal{M}_\sigma(\sigma)`, which headers carry as $`\mathbf{H}_R`. It does this in two stages:

* *serialization* (§D.1): $`T(\sigma)` maps $`\sigma` to a dictionary from 31-octet *state keys* to octet
  sequences;
* *Merklization* (§D.2): $`M` turns that dictionary into the root of a binary Patricia Merkle
  trie.

In the model the key constructor and the trie are in `JAM/Trie.lean`, $`T` is
{api}`JAM.State.serializeList` in `JAM/State.lean`, and its inverse, which rebuilds $`\sigma` from its
key-value pairs, is in `JAM/StateDecode.lean`.

# State keys (§D.1)
%%%
tag := "statemerkle-keys"
%%%

A state key is built from a state-component index, from an index and a service, or from a service
and an octet sequence:

$$`C\colon \left\{\begin{aligned} \mathbb{N}_{2^8} \cup (\mathbb{N}_{2^8}, \mathbb{N}_S) \cup (\mathbb{N}_S, \mathbb{B}) &\to \mathbb{B}_{31} \\ i \in \mathbb{N}_{2^8} &\mapsto [i, 0, 0, \dots] \\ (i, s \in \mathbb{N}_S) &\mapsto [i, n_0, 0, n_1, 0, n_2, 0, n_3, 0, 0, \dots] \\ &\phantom{\mapsto}\ \text{where } n = \mathcal{E}_4(s) \\ (s, h) &\mapsto [n_0, a_0, n_1, a_1, n_2, a_2, n_3, a_3, a_4, a_5, \dots, a_{26}] \\ &\phantom{\mapsto}\ \text{where } n = \mathcal{E}_4(s), a = \mathcal{H}(h) \end{aligned}\right. \quad \text{(D.1)}`

The three cases are three functions:

{leanSource JAM.Trie.keyOfIndex}

{leanSource JAM.Trie.keyOfService}

{leanSource JAM.Trie.keyOfServiceData}

The third case keeps only the first 27 octets of $`\mathcal{H}(h)`. The paper notes that "only the
Merklisation-ready serialisation is important", so an implementation need not store the storage keys
themselves. The model takes that option: a service account holds its storage $`\mathbf{a}_\mathbf{s}` and
its requests $`\mathbf{a}_\mathbf{l}` in one dictionary, `entries`, keyed by those 27 octets, and the
state key is rebuilt from them by {api}`JAM.Trie.keyOfServiceHash`:

{leanSource JAM.Trie.keyOfServiceHash}

{mathdoc JAM.Trie.keyOfServiceHash_eq}

The 27 octets of a storage key and of a request are {api}`JAM.ServiceAccount.storageKey` and
{api}`JAM.ServiceAccount.requestKey`, and the account's accessors read `entries` through them:

{leanSource JAM.ServiceAccount.storageKey}

{leanSource JAM.ServiceAccount.requestKey}

{mathdoc JAM.ServiceAccount.storageGet_eq}

{api}`JAM.ServiceAccount.requestGet` reads a request the same way, with two cases where it returns `none`: a
length $`z \geq 2^{32} - 2` (outside $`\mathbb{N}_P = \mathbb{N}_{2^{32}-2}`, the lengths a request can have), and a stored value that does not decode as a
sequence of at most three timeslots (which only a state not built by the model can hold).

# The serialization T (§D.1)
%%%
tag := "statemerkle-serialize"
%%%

$`T(\sigma)` puts each state component under its own key $`C(1)` to $`C(16)`, and each service account's
fields, storage, preimages and requests under keys built from its index:

$$`T(\sigma) \equiv \left\{\begin{aligned} &C(1) \mapsto \mathcal{E}\left(\left[\updownarrow x \;\middle|\; x \mathrel{<\mkern-7mu-} \alpha\right]\right), \\ &C(2) \mapsto \mathcal{E}(\phi), \\ &C(3) \mapsto \mathcal{E}\big(\updownarrow\left[(h, b, s, \mathcal{E}_4(t), \updownarrow\mathbf{p}) \;\middle|\; (h, b, s, t, \mathbf{p}) \mathrel{<\mkern-7mu-} \beta_H\right], \mathcal{E}_M(\beta_B)\big), \\ &C(4) \mapsto \mathcal{E}\left(\updownarrow\gamma_P, \gamma_Z, \begin{cases} 0 & \text{if } \gamma_S \in \llbracket\mathbb{T}\rrbracket_{\mathsf{E}} \\ 1 & \text{if } \gamma_S \in \llbracket\overset{\backsim}{\mathbb{H}}\rrbracket_{\mathsf{E}} \end{cases}, \gamma_S, \updownarrow\gamma_A\right), \\ &C(5) \mapsto \mathcal{E}\big(\updownarrow[x \in \psi_G \wr x], \updownarrow[x \in \psi_B \wr x], \updownarrow[x \in \psi_W \wr x], \updownarrow[x \in \psi_O \wr x]\big), \\ &C(6) \mapsto \mathcal{E}(\eta), \quad C(7) \mapsto \mathcal{E}(\updownarrow\iota), \quad C(8) \mapsto \mathcal{E}(\updownarrow\kappa), \quad C(9) \mapsto \mathcal{E}(\updownarrow\lambda), \\ &C(10) \mapsto \mathcal{E}\left(\left[\text{¿}(\mathbf{g}, \mathcal{E}_4(t)) \;\middle|\; (\mathbf{g}, t) \mathrel{<\mkern-7mu-} \rho\right]\right), \\ &C(11) \mapsto \mathcal{E}_4(\tau), \\ &C(12) \mapsto \mathcal{E}_4(\chi_m, \chi_\mathbf{a}, \chi_v, \chi_r) \frown {} \\ &\qquad \mathcal{E}\left(\updownarrow\left[(\mathcal{E}_4(s), \mathcal{E}_8(\chi_\mathbf{z}[s])) \;\middle|\; s \in \mathcal{K}(\chi_\mathbf{z}) \wr s\right]\right), \\ &C(13) \mapsto \mathcal{E}\big(\updownarrow\pi_V, \updownarrow\pi_L, \pi_C, \updownarrow\left[(\mathcal{E}_4(s), \mathcal{E}(\pi_S[s])) \;\middle|\; s \in \mathcal{K}(\pi_S) \wr s\right]\big), \\ &C(14) \mapsto \mathcal{E}\left(\left[\updownarrow\left[(\mathbf{r}, \updownarrow\mathbf{d}) \;\middle|\; (\mathbf{r}, \mathbf{d}) \mathrel{<\mkern-7mu-} \mathbf{i}\right] \;\middle|\; \mathbf{i} \mathrel{<\mkern-7mu-} \omega\right]\right), \\ &C(15) \mapsto \mathcal{E}\left(\left[\updownarrow\mathbf{i} \;\middle|\; \mathbf{i} \mathrel{<\mkern-7mu-} \xi\right]\right), \\ &C(16) \mapsto \mathcal{E}\left(\updownarrow\left[(\mathcal{E}_4(s), \mathcal{E}(h)) \;\middle|\; (s, h) \mathrel{<\mkern-7mu-} \theta\right]\right), \\ &\forall (s \mapsto \mathbf{a}) \in \delta\colon \\ &\qquad C(255, s) \mapsto \mathcal{E}\left(0, \mathbf{a}_c, \mathcal{E}_4(\mathbf{a}_u, \mathbf{a}_d), \mathcal{E}_8(\mathbf{a}_b, \mathbf{a}_x, \mathbf{a}_g, \mathbf{a}_m, \mathbf{a}_o, \mathbf{a}_f)\right) \frown {} \\ &\qquad\qquad \mathcal{E}_4(\mathbf{a}_i, \mathbf{a}_r, \mathbf{a}_a, \mathbf{a}_p), \\ &\forall (s \mapsto \mathbf{a}) \in \delta, (\mathbf{k} \mapsto \mathbf{v}) \in \mathbf{a}_\mathbf{s}\colon \\ &\qquad C(s, \mathcal{E}_4(2^{32} - 1) \frown \mathbf{k}) \mapsto \mathbf{v}, \\ &\forall (s \mapsto \mathbf{a}) \in \delta, (h \mapsto \mathbf{p}) \in \mathbf{a}_\mathbf{p}\colon \\ &\qquad C(s, \mathcal{E}_4(2^{32} - 2) \frown h) \mapsto \mathbf{p}, \\ &\forall (s \mapsto \mathbf{a}) \in \delta, ((h, l) \mapsto \mathbf{t}) \in \mathbf{a}_\mathbf{l}\colon \\ &\qquad C(s, \mathcal{E}_4(l) \frown h) \mapsto \mathcal{E}\left(\updownarrow\left[\mathcal{E}_4(x) \;\middle|\; x \mathrel{<\mkern-7mu-} \mathbf{t}\right]\right) \end{aligned}\right. \quad \text{(D.2)}`

The model's $`T` lists the same rows as (key, value) pairs. The component rows come in the paper's
order; the account rows are grouped by account. Order does not matter, since $`T(\sigma)` is a dictionary:

{leanSource JAM.State.serializeList}

Most rows' values are a function in `JAM.Serialize`, named after the component they encode; $`C(1)`,
$`C(2)`, $`C(6)` and $`C(11)` are written inline. For
example, $`C(4)`, Safrole's state, with the discriminator that says whether $`\gamma_S` holds tickets or
fallback keys (the model's `match` on the two cases, where the paper writes a brace):

{leanSource JAM.Serialize.gamma}

and $`C(255, s)`, a service account's fields:

{leanSource JAM.Serialize.accountInfo}

The last four rows, from $`C(255, s)` on, are {api}`JAM.Serialize.account`. A preimage is keyed as in the paper. Storage and
requests are already held under the 27-octet hash part of their keys, and with the values $`T`
gives them (a request's value is {api}`JAM.ServiceAccount.encodeSlots` of its timeslots), so the row
only rebuilds the full key:

{leanSource JAM.ServiceAccount.encodeSlots}

{leanSource JAM.Serialize.account}

The dictionary is {api}`JAM.State.serialize`, and the state root is the trie root of it:

{leanSource JAM.State.serialize}

{leanSource JAM.State.root}

The model also inverts $`T`: {api}`JAM.StateDecode.decodeState` rebuilds a state from its key-value
pairs, decoding each component with the decoders of {ref "codec"}[Appendix C]. The trace test
(`Tests/TraceTest.lean`) works on every state of the block-import traces, which were made for GP
v0.8.0. Its independent check is that the model's trie root of each state's key-value pairs equals
the root the trace records. It then rewrites the $`C(13)` and $`C(255, s)` values into v0.8.1's layout,
which changes the root, so it replaces the root with the model's own; for these rewritten states it
checks that serializing the decoded state gives back the same pairs, key by key, and the same root,
a round-trip check rather than an independent one.

{leanSource JAM.StateDecode.decodeState}

# Merklization (§D.2)
%%%
tag := "statemerkle-trie"
%%%

A trie is identified by the hash of its root node, and an empty one by the zero hash $`\mathbb{H}_0`. Every
node is 512 bits. Its first bit tells a branch from a leaf; a leaf's second bit tells a leaf with its
value embedded (at most 32 octets) from a leaf that holds the hash of its value:

$$`B\colon \left\{\begin{aligned} (\mathbb{H}, \mathbb{H}) &\to \text{𝕓}_{512} \\ (l, r) &\mapsto [0] \frown \text{bits}(l)_{1\dots} \frown \text{bits}(r) \end{aligned}\right. \qquad \text{(D.3)}`

$$`L\colon \left\{\begin{aligned} (\mathbb{B}_{31}, \mathbb{B}) &\to \text{𝕓}_{512} \\ (k, v) &\mapsto \begin{cases} \begin{aligned} &[1, 0] \frown \text{bits}(\mathcal{E}_1(|v|))_{2\dots} \frown \text{bits}(k) \\ &\quad \frown \text{bits}(v) \frown [0, 0, \dots] \end{aligned} & \text{if } |v| \le 32 \\ [1, 1, 0, 0, 0, 0, 0, 0] \frown \text{bits}(k) \frown \text{bits}(\mathcal{H}(v)) & \text{otherwise} \end{cases} \end{aligned}\right. \qquad \text{(D.4)}`

$`\text{bits}` orders the bits of each octet most significant first (§3.7), so the paper's first bit of a
node is the high bit of its first octet. The model builds the 64 octets directly: a branch clears the
high bit of the left child's first octet, an embedded leaf's first octet is $`2^7 + |v|`, and a regular
leaf's is $`2^7 + 2^6`:

{leanSource JAM.Trie.branch}

{leanSource JAM.Trie.leaf}

The root of a dictionary is defined by recursion on the bits of its keys. A dictionary of one entry
is the hash of its leaf; otherwise the entries are split by their first bit, and the two halves'
roots form a branch:

$$`\mathcal{M}_\sigma(\sigma) \equiv M\left(\left\{\, (\text{bits}(k) \mapsto (k, v)) \;\middle|\; (k \mapsto v) \in T(\sigma) \,\right\}\right) \qquad \text{(D.5)}`

$$`M(d\colon \langle \text{𝕓} \to (\mathbb{B}_{31}, \mathbb{B}) \rangle) \equiv \begin{cases} \mathbb{H}_0 & \text{if } |d| = 0 \\ \mathcal{H}(\text{bits}^{-1}(L(k, v))) & \text{if } \mathcal{V}(d) = \{(k, v)\} \\ \mathcal{H}(\text{bits}^{-1}(B(M(l), M(r)))) & \text{otherwise} \end{cases}`

$$`\text{where } \forall b, p\colon (b \mapsto p) \in d \Leftrightarrow (b_{1\dots} \mapsto p) \in \begin{cases} l & \text{if } b_0 = 0 \\ r & \text{if } b_0 = 1 \end{cases} \qquad \text{(D.6)}`

{leanSource JAM.Trie.merkle}

{leanSource JAM.Trie.root}

The paper removes one bit from every key at each level. The model keeps the keys whole and counts
the bits removed in `depth`, testing bit `depth` of each key ({api}`JAM.Trie.bit`). The recursion is
bounded by `fuel`, because Lean needs every function to terminate. {api}`JAM.Trie.root` gives it 248,
the number of bits in a 31-octet key: two different 31-octet keys differ in one of their 248 bits, so
on the dictionaries $`T` produces the split separates every pair of entries before the fuel runs out.
The model does not state this as a theorem. The trie test (`Tests/TrieTest.lean`) checks
$`M` against the roots of the GP v0.8.0 trie vectors.

{leanSource JAM.Trie.bit}

# Readings chosen
%%%
tag := "statemerkle-readings"
%%%

* *Storage keys are not kept.* The model uses the freedom the paper gives at the end of §D.1: storage
  and request entries are held under the 27 hash octets of their state keys, not under their keys
  (`ServiceAccount.entries`). A service cannot enumerate its storage keys in the paper either.
* *The fuel of $`M`.* On keys longer than 31 octets that agree in their first 248 bits, the model's
  $`M` returns $`\mathbb{H}_0` for that subtrie. $`T` produces only 31-octet keys, so this does not arise.
* *The trie vectors' keys.* The trie test vectors give 32-octet keys, while §D.1's state keys are 31
  octets; the roots match with the last octet dropped. This is note 27 of the model's
  [notes on the paper and the vectors](https://github.com/ascrivener/jam-lean/blob/main/docs/upstream-candidates.md#paper-and-vectors).
