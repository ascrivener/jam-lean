import VersoManual
import Companion.Source
import Companion.Docstring
import PVM.Blob
import PVM.Logic.Steps
import PVM.Logic.Words
import JAM.Codec
import JAM.Decode
import JAM.Block
import JAM.Work

open Verso.Genre Manual
open Companion
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Appendix C: the serialization codec" =>
%%%
tag := "codec"
shortTitle := "C. Codec"
file := "codec"
%%%

Appendix C of GP v0.8.1 defines $`\mathcal{E}`, the function that turns a term into a sequence of
octets, and its inverse $`\mathcal{E}^{-1}`. The paper uses $`\mathcal{E}` wherever a term is hashed,
signed, stored in the state or passed to the PVM. The appendix has two parts: the encodings of the
common kinds of term (§C.1), and the encodings of the block and the work-package family built from
them (§C.2).

In the model the encoders are functions to `List UInt8`, in the namespace `JAM.Codec`
(`JAM/Codec.lean`). The natural-number encodings $`\mathcal{E}` and $`\mathcal{E}_l` are defined once in the
PVM model (`PVM.Blob.encodeNat`, `PVM.Num.encodeLE`), so the program blob of Appendix A and the rest of
the protocol use the same definitions. The decoders are in `JAM/Decode.lean`.

# Trivial encodings (§C.1.1)
%%%
tag := "codec-trivial"
%%%

$$`\mathcal{E}(\emptyset) \equiv [\,] \qquad \text{(C.1)} \qquad\qquad \mathcal{E}(x \in \mathbb{B}) \equiv x \qquad \text{(C.2)}`

$$`\mathcal{E}(\bot) \equiv [0], \qquad \mathcal{E}(\top) \equiv [1] \qquad \text{(C.3)}`

$$`\mathcal{E}((a, b, \dots)) \equiv \mathcal{E}(a) \frown \mathcal{E}(b) \frown \dots \qquad \text{(C.4)} \qquad\qquad \mathcal{E}(a, b, \dots) \equiv \mathcal{E}((a, b, \dots)) \qquad \text{(C.5)}`

An octet sequence encodes as itself, and a tuple as the concatenation of its parts. In the model a
tuple's encoding is written out with `++` in each encoder; an octet sequence is
{api}`JAM.Codec.blob`, and a Boolean is {api}`JAM.encodeBool`:

{leanSource JAM.Codec.blob}

{leanSource JAM.encodeBool}

# Natural numbers (§C.1.1, §C.1.7)
%%%
tag := "codec-naturals"
%%%

The general encoding of a natural below $`2^{64}` takes one to nine octets. The number of leading one
bits of the first octet says how many octets follow:

$$`\mathcal{E}\colon \left\{\begin{aligned} \mathbb{N}_{2^{64}} &\to \mathbb{B}_{1:9} \\ x &\mapsto \begin{cases} [0] & \text{if } x = 0 \\ \left[2^8 - 2^{8-l} + \left\lfloor \frac{x}{2^{8l}} \right\rfloor\right] \frown \mathcal{E}_l(x \bmod 2^{8l}) & \text{if } \exists l \in \mathbb{N}_8 : 2^{7l} \le x < 2^{7(l+1)} \\ [2^8 - 1] \frown \mathcal{E}_8(x) & \text{otherwise if } x < 2^{64} \end{cases} \end{aligned}\right. \quad \text{(C.6)}`

{leanSource PVM.Blob.encodeNat}

The model searches $`l \in \mathbb{N}_8` in increasing order. The ranges $`[2^{7l}, 2^{7(l+1)})` are disjoint, so
at most one $`l` qualifies and the order of the search does not matter. The theorem below states the
middle case for $`l < 5`, the case that covers every nonzero $`x < 2^{35}`, and the next one bounds the length for
32-bit values:

{mathdoc PVM.encodeNat_of_lt}

{mathdoc PVM.encodeNat_len_le5}

The fixed-length encoding $`\mathcal{E}_l` (eq. (C.13)) is little-endian, in exactly $`l` octets:

$$`\mathcal{E}_{l \in \mathbb{N}}\colon \left\{\begin{aligned} \mathbb{N}_{2^{8l}} &\to \mathbb{B}_l \\ x &\mapsto \begin{cases} [\,] & \text{if } l = 0 \\ [x \bmod 256] \frown \mathcal{E}_{l-1}\left(\left\lfloor \frac{x}{256} \right\rfloor\right) & \text{otherwise} \end{cases} \end{aligned}\right. \qquad \text{(C.13)}`

{leanSource PVM.Num.encodeLE}

Applied to a tuple or a sequence, $`\mathcal{E}_l` encodes each element with $`\mathcal{E}_l` and concatenates the results (eqs. (C.14)–(C.16)).
In the model these are written out where they are used, for example `[a.items, a.created, a.lastAcc, a.parent].flatMap (fixed 4)`
for $`\mathcal{E}_4(a_i, a_r, a_a, a_p)` in the state serialization ({ref "statemerkle"}[Appendix D]).
{api}`JAM.Codec.nat` and {api}`JAM.Codec.fixed` give the two encodings their codec names.

What the model proves about $`\mathcal{E}_l`: the result has $`l` octets, decoding it gives back $`x \bmod 2^{8l}`
(so $`x` itself when $`x < 2^{8l}`, the paper's domain), and every $`l`-octet sequence is the encoding of its
decoded value:

{leanSource PVM.Num.length_encodeLE}

{leanSource PVM.Num.decodeLE_encodeLE}

{leanSource PVM.encodeLE_decodeLE}

# Sequences, discriminators and optional terms (§C.1.2, §C.1.3)
%%%
tag := "codec-sequences"
%%%

$$`\mathcal{E}([\mathbf{i}_0, \mathbf{i}_1, \dots]) \equiv \mathcal{E}(\mathbf{i}_0) \frown \mathcal{E}(\mathbf{i}_1) \frown \dots \qquad \text{(C.7)}`

$$`\updownarrow x \equiv (|x|, x) \quad \text{thus} \quad \mathcal{E}(\updownarrow x) \equiv \mathcal{E}(|x|) \frown \mathcal{E}(x) \qquad \text{(C.8)}`

$$`\text{¿}x \equiv \begin{cases} 0 & \text{if } x = \emptyset \\ (1, x) & \text{otherwise} \end{cases} \qquad \text{(C.9)}`

A sequence is the concatenation of its elements' encodings, with no length. A term of variable size
is written $`\updownarrow x` and carries its length, encoded with the general $`\mathcal{E}`. An optional term $`\text{¿}x` is
prefixed by 0 or 1. Each encoder takes the encoder of the elements as an argument:

{leanSource JAM.Codec.seq}

{leanSource JAM.Codec.varSeq}

{leanSource JAM.Codec.var}

{leanSource JAM.Codec.opt}

`opt` writes the discriminator as the octet 0 or 1, which is $`\mathcal{E}(0)` and $`\mathcal{E}(1)` under eq. (C.6).

# Bit sequences (§C.1.4)
%%%
tag := "codec-bits"
%%%

Bits are packed eight to an octet, least significant first:

$$`\mathcal{E}(b \in \mathbb{b}) \equiv \begin{cases} [\,] & \text{if } b = [\,] \\ \left[\sum_{i=0}^{i < \min(8, |b|)} b_i \cdot 2^i\right] \frown \mathcal{E}(b_{8\dots}) & \text{otherwise} \end{cases} \qquad \text{(C.10)}`

{leanSource JAM.encodeBits}

The model builds the $`\lceil |b| / 8 \rceil` octets directly instead of recursing; a bit past the end of $`b`
counts as 0, so the high bits of a short last octet are zero, as the sum in eq. (C.10) leaves them.
The model uses it in the assurances extrinsic (eq. (C.21)) and to build the message an assurance signs
(§11.2).

# Dictionaries and sets (§C.1.5, §C.1.6)
%%%
tag := "codec-dicts"
%%%

$$`\forall K, V\colon \mathcal{E}(d \in \langle K \to V \rangle) \equiv \mathcal{E}\left(\updownarrow\left[\, (\mathcal{E}(k), \mathcal{E}(d[k])) \;\middle|\; k \in \mathcal{K}(d) \wr k \,\right]\right) \qquad \text{(C.11)}`

$$`\mathcal{E}(\{a, b, c, \dots\}) \equiv \mathcal{E}(a) \frown \mathcal{E}(b) \frown \mathcal{E}(c) \frown \dots \quad \text{where } a < b < c < \dots \qquad \text{(C.12)}`

A dictionary is encoded as its pairs in key order, with a length; a set as its elements in order.
Where the paper uses a set of hashes $`\left\{\mkern-5mu\left[\,\mathbb{H}\,\right]\mkern-5mu\right\}` or a dictionary $`\langle \mathbb{H} \to \mathbb{H} \rangle`, the model holds it as
{api}`JAM.OctetSet` or {api}`JAM.OctetDict`. Both are extensional search trees over octet lists, so
iterating over one already gives the elements in ascending order, and no sort is needed:

{leanSource JAM.Codec.varHashSet}

{leanSource JAM.Codec.varHashDict}

The sets in the terms of blocks, work packages and the state, such as the prerequisites $`\mathbf{p}` of a
refinement context, are written with a length discriminator, so the model's set encoder for them is
$`\mathcal{E}(\updownarrow[\dots])` of the ordered elements. Not every set in the paper is: the set §17.3 encodes for an
audit announcement has none (see the {ref "auditing"}[auditing chapter]).

Dictionaries need care. Eq. (C.11) already gives a dictionary its length, and eq. (C.30) writes the
work report's segment-root lookup as $`\updownarrow\mathbf{r}_\mathbf{l}`, which read literally would put a second length before it.
The model writes one length ({api}`JAM.Codec.varHashDict`); see {ref "codec-readings"}[Readings chosen].

# Decoding
%%%
tag := "codec-decoding"
%%%

The paper defines $`\mathcal{E}^{-1}` as "the inverse of $`\mathcal{E}`", and says the codec is designed so
that exactly one value is encoded into any given sequence of octets. The model gives the inverse
as decoders: a {api}`JAM.Decoder` reads a term at a position in an octet sequence, and
{api}`JAM.Decoder.run` accepts the sequence only if the term uses every octet:

{leanSource JAM.Decoder}

{leanSource JAM.Decoder.run}

Since $`\mathcal{E}^{-1}` must give back the value whose encoding the input *is*, each primitive decoder
rejects input that its encoder never produces. For the general natural, the decoder reads the value
the first octet announces, then encodes it again with {api}`PVM.Blob.encodeNat` and accepts only if
the result is exactly the octets it read. This rejects, for example, $`[128, 5]`, which would read as 5
but is not $`\mathcal{E}(5) = [5]`:

{leanSource PVM.Blob.decodeNat?}

The other primitives are {api}`JAM.Decoder.fixed`, {api}`JAM.Decoder.bytes`,
{api}`JAM.Decoder.varSeq`, {api}`JAM.Decoder.var`, {api}`JAM.Decoder.opt` (which accepts only the
discriminators 0 and 1), {api}`JAM.Decoder.bits` (which rejects nonzero padding bits),
{api}`JAM.Decoder.bool`, and {api}`JAM.Decoder.varHashSet` and {api}`JAM.Decoder.varHashDict`
(which reject elements or keys out of ascending order, or repeated). For example:

{leanSource JAM.Decoder.opt}

{leanSource JAM.Decoder.varHashSet}

The model proves the round trip for $`\mathcal{E}_l`, above. It does not yet prove that the general
natural's decoder or the composite decoders are inverse to their encoders. Instead, the codec test
(`Tests/CodecTest.lean`) runs the GP v0.8.0 codec vectors, with the assurance encoding changed as
v0.8.1 requires: for each vector, encoding its term gives its octets, decoding its octets and encoding
the result again gives them back, and the decoder rejects the octets with their last octet dropped or with a zero octet appended.

# Blocks and the work-package family (§C.2)
%%%
tag := "codec-block"
%%%

A block is serialized as its header followed by its extrinsics, each of them a tuple of its
elements in order, with the encodings of §C.1:

$$`\mathcal{E}(\mathbf{B}) = \mathcal{E}\left(\mathbf{H}, \mathcal{E}_T(\mathbf{E}_T), \mathcal{E}_P(\mathbf{E}_P), \mathcal{E}_G(\mathbf{E}_G), \mathcal{E}_A(\mathbf{E}_A), \mathcal{E}_D(\mathbf{E}_D)\right) \qquad \text{(C.17)}`

{leanSource JAM.Block.encode}

{leanSource JAM.Extrinsic.encode}

The header has a regular encoding and an unsigned one, $`\mathcal{E}_U`, without the seal $`\mathbf{H}_S`:

$$`\mathcal{E}(\mathbf{H}) = \mathcal{E}(\mathcal{E}_U(\mathbf{H}), \mathbf{H}_S) \qquad \text{(C.23)}`

$$`\mathcal{E}_U(\mathbf{H}) = \mathcal{E}\left(\mathbf{H}_P, \mathbf{H}_R, \mathbf{H}_X, \mathcal{E}_4(\mathbf{H}_T), \mathcal{E}_E(\mathbf{H}_E), \text{¿}\mathbf{H}_W, \mathcal{E}_2(\mathbf{H}_I), \mathbf{H}_V, \updownarrow\mathbf{H}_O\right) \qquad \text{(C.24)}`

$$`\mathcal{E}_E(\emptyset) = \mathcal{E}(0) \qquad \text{(C.25)} \qquad\qquad \mathcal{E}_E((\eta_0, \eta_1, \mathbf{k})) = \mathcal{E}(1, \eta_0, \eta_1, \updownarrow\mathbf{k}) \qquad \text{(C.26)}`

{leanSource JAM.Header.encodeUnsigned}

{leanSource JAM.encodeEpochMark}

A work result is encoded by $`O`, which puts a discriminator before an output blob and gives each of
the six work errors its own number:

$$`O(o \in \mathbb{E} \cup \mathbb{B}) \equiv \begin{cases} (0, \updownarrow o) & \text{if } o \in \mathbb{B} \\ 1 & \text{if } o = \infty \\ 2 & \text{if } o = \text{☇} \\ 3 & \text{if } o = \circledcirc \\ 4 & \text{if } o = \ominus \\ 5 & \text{if } o = \texttt{BAD} \\ 6 & \text{if } o = \texttt{BIG} \end{cases} \qquad \text{(C.38)}`

{leanSource JAM.WorkResult.encode}

An imported segment is named by a segment root or by a work-package hash $`r^\boxplus`; the two are told apart by
adding $`2^{15}` to the index:

$$`I((h \in \mathbb{H} \cup \mathbb{H}^\boxplus, i \in \mathbb{N}_{2^{15}})) \equiv \begin{cases} (h, \mathcal{E}_2(i)) & \text{if } h \in \mathbb{H} \\ (r, \mathcal{E}_2(i + 2^{15})) & \text{if } \exists r \in \mathbb{H}, h = r^\boxplus \end{cases} \qquad \text{(C.39)}`

{leanSource JAM.encodeImport}

The other equations of §C.2 are implemented field by field, in the paper's order:

* (C.18) $`\mathcal{E}_T`, the tickets: {api}`JAM.encodeTickets`;
* (C.19) $`\mathcal{E}_P`, the preimages: {api}`JAM.encodePreimages`;
* (C.20) $`\mathcal{E}_G`, the guarantees: {api}`JAM.encodeGuarantees`;
* (C.21) $`\mathcal{E}_A`, the assurances: {api}`JAM.encodeAssurances`;
* (C.22) $`\mathcal{E}_D`, the disputes: {api}`JAM.Disputes.encode` and {api}`JAM.Judgment.encode`;
* (C.27) a refinement context $`\mathbb{C}`: {api}`JAM.RefineContext.encode`;
* (C.28) an availability specification $`\mathbb{Y}`: {api}`JAM.AvailabilitySpec.encode`;
* (C.29) a work digest $`\mathbb{D}`: {api}`JAM.WorkDigest.encode`;
* (C.30) a work report $`\mathbb{R}`: {api}`JAM.WorkReport.encode`;
* (C.31), (C.32) a guarantee $`\mathbb{G}` and its credential: {api}`JAM.Guarantee.encode` and {api}`JAM.encodeCredential`;
* (C.33) a work package $`\mathbb{P}`: {api}`JAM.WorkPackage.encode`;
* (C.34) a work item $`\mathbb{W}`: {api}`JAM.WorkItem.encode`;
* (C.35) a ticket $`\mathbb{T}`: {api}`JAM.Ticket.encode`;
* (C.36) a deferred transfer: {api}`JAM.DeferredTransfer.encode`;
* (C.37) an operand tuple $`\mathbb{U}`: {api}`JAM.OperandTuple.encode`.

For example, the work item of eq. (C.34):

{leanSource JAM.WorkItem.encode}

The block and the work-package family also have decoders ({api}`JAM.Block.decode`,
{api}`JAM.WorkPackage.decode`, {api}`JAM.WorkReport.decode`, …), built from the primitive decoders
above, field by field in the same order.

# Readings chosen
%%%
tag := "codec-readings"
%%%

* *Values outside the domain.* $`\mathcal{E}` is defined on $`\mathbb{N}_{2^{64}}` and $`\mathcal{E}_l` on $`\mathbb{N}_{2^{8l}}`. The model's functions
  take any natural, so that they are total. Outside the paper's domain, $`\mathcal{E}_l` encodes $`x \bmod 2^{8l}`
  (`Num.decodeLE_encodeLE` above), and $`\mathcal{E}` gives $`[2^8 - 1] \frown \mathcal{E}_8(x \bmod 2^{64})`: the last case of eq. (C.6),
  applied whatever its condition. So $`\mathcal{E}(2^{64} + 5) = [255, 5, 0, \dots, 0]`, not $`\mathcal{E}(5) = [5]`. Likewise
  {api}`JAM.encodeImport` accepts an index $`i \geq 2^{15}`, outside eq. (C.39)'s $`\mathbb{N}_{2^{15}}`: $`\mathcal{E}_2` keeps only the low 16
  bits, of $`i` for a segment root and of $`i + 2^{15}` for a work-package hash, and a segment root whose kept
  index is $`2^{15}` or more decodes as a work-package hash.
  The paper never encodes such values.
* *The order of a set.* Eq. (C.12) orders a set's elements by $`<` but does not define $`<` on octet
  sequences. The model uses the lexicographic order of octet lists (Lean's `<` and `Ord` on
  `List UInt8`), which {api}`JAM.OctetSet` and {api}`JAM.OctetDict` keep and the set and dictionary decoders
  check. For the 32-octet hashes it is used on, this is the order of the hashes read as big-endian
  numbers.
* *What $`\mathcal{E}^{-1}` rejects.* "The inverse of $`\mathcal{E}`" accepts only octet sequences that are
  encodings. The model's decoders therefore reject non-canonical naturals, discriminators outside
  their range (an optional value's other than 0 and 1, a work result's above 6, and the epoch
  marker's other than 0 and 1), nonzero padding bits, sets and dictionaries out of order, lengths beyond the end of the
  input, and octets left over at the end.
* *A dictionary's length (note v0.8.1-A60).* Eq. (C.11) encodes a dictionary with its length, and
  eq. (C.30) writes $`\updownarrow\mathbf{r}_\mathbf{l}` for the work report's segment-root lookup, which read literally gives two
  length prefixes. The model writes one ({api}`JAM.Codec.varHashDict`, used by {api}`JAM.WorkReport.encode`).
  This is recorded in the model's
  [notes on the paper](https://github.com/ascrivener/jam-lean/blob/main/docs/upstream-candidates.md#gray-paper-issues).
