import VersoManual
import Companion.Source
import Companion.Paper
import Companion.Docstring
import JAM.Crypto
import JamCrypto.Crypto
import JamCrypto.Ring
import JamCrypto.ThinVrf
import JamCrypto.Reading
import JamCrypto.Fast.Crypto
import JamCrypto.Fast.Ring
import JamCrypto.Model

open Verso.Genre Manual
open Companion
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Appendix G: the Bandersnatch VRF, and cryptography as a parameter" =>
%%%
tag := "bandersnatch"
shortTitle := "G. Bandersnatch VRF"
file := "bandersnatch"
%%%

*In the paper:* {gpchapter}`sec:bandersnatch`.

*In brief.* Block production ({ref "safrole"}[§6]) needs two kinds of signature beyond ordinary
Ed25519 ones, both on the Bandersnatch elliptic curve. A *VRF signature* also yields a 32-octet
output, fixed by the key and the signature's context alone (not the rest of the signed message),
which anyone can check against the signer's public key; blocks are sealed with such signatures,
their outputs feed the chain's entropy, and auditors use one to pick what they audit
({ref "auditing"}[§17]). A *Ring VRF proof* shows that its signer holds one of the keys in a set
(the ring, committed to by a ring root) without revealing which; validators use them to submit
anonymous tickets, so the tickets that win the slots of an epoch are public while their owners stay
hidden until each seals its block. The appendix names the curve and refers to external
specifications for the schemes themselves, fixing only what the rest of the paper uses: which octet
sequences are valid signatures and proofs, their outputs, and the ring root.

Appendix G of GP v0.8.1 defines the two Bandersnatch primitives that Safrole ({ref "safrole"}[§6]) uses: VRF
signatures, which seal blocks and yield their entropy, and Ring VRF proofs, with which validators
submit anonymous tickets. The appendix does not define the cryptography itself. It names the
curve and refers to the specifications that define the schemes, and it fixes only the sets the rest
of the paper uses: which octet sequences are valid signatures or proofs, their outputs, and the ring
root of a sequence of keys.

The model follows the same division. It takes the primitives as a parameter, the structure
{api}`JAM.Crypto`, which every transition that checks a signature receives; it does not implement
them. Separately, the repository contains `JamCrypto`, an implementation of that parameter in plain
Lean. This chapter describes the interface, then the implementation, then what is proved about the
implementation: that its fast code computes the same functions as its reference code. Nothing in
the repository proves a cryptographic property, such as the unforgeability of a signature.

# The paper's definitions (Appendix G)
%%%
tag := "bandersnatch-paper"
%%%

The VRF signatures are "a formulation under the *Thin* VRF template" of the Bandersnatch VRF
specification (GP v0.8.1 cites its Draft 35; v0.8.0 used the IETF VRF). A signature is 96 octets,
and its output $`\mathcal{Y}` is 32 octets:

{gpeq "G.1"}

{gpeq "G.2"}

The Ring VRF proofs are a zk-SNARK-enabled analogue built on the Pedersen VRF. They verify against a
ring root $`\mathcal{O}(\mathbf{k})`, a commitment to a sequence of keys, and are 784 octets:

{gpeq "G.3"}

{gpeq "G.4"}

{gpeq "G.5"}

A key with no corresponding curve point is replaced by the specification's padding point when the
ring is built. The paper's other signature scheme, Ed25519 (§3.8.2), is defined there:
$`\bar{\mathbb{V}}_k\langle m \rangle \subset \mathbb{B}_{64}` is the set of valid Ed25519 signatures of RFC 8032, with the validation criteria of
ZIP 215 where RFC 8032 admits alternatives.

# The parameter `JAM.Crypto`
%%%
tag := "bandersnatch-interface"
%%%

Each field of {api}`JAM.Crypto` stands for one of these sets or functions: `edVerify` for membership
in $`\bar{\mathbb{V}}_k\langle m \rangle`, `bsVerify` for {eq}`G.1`, `bsOut` for {eq}`G.2`, `bsRingRoot` for {eq}`G.3`,
`bsRingVerify` for {eq}`G.4` and `bsRingOut` for {eq}`G.5`. Membership in a set is a Boolean function of the
key (or root), the context, the message and the signature, in the paper's argument order:

{leanSource JAM.Crypto}

The model does not implement this structure. A caller supplies it: an implementation such as
`JamCrypto`, or, in the state-transition tests, functions that give each test vector's expected
verdicts. The Bandersnatch fields have defaults that reject everything and output nothing, so that a
caller that needs only Ed25519 can omit them; a transition that uses a field must be given a real one.
For example, on an epoch change the Safrole transition ({ref "safrole"}[§6]) computes the new ring
root $`\gamma'_Z = \mathcal{O}([k_b \mid k \mathrel{<\mkern-7mu-} \gamma'_P])` with `bsRingRoot`, and it checks each ticket's proof with
`bsRingVerify`.

Contexts such as $`\mathsf{X}_T = \texttt{\$jam\_ticket\_seal}` are written in the paper with a leading `$`. The model reads the
`$` as the paper's notation for a string, not as an octet of it:

{leanSource JAM.contextString}

# JamCrypto: an implementation in plain Lean
%%%
tag := "bandersnatch-jamcrypto"
%%%

`JamCrypto` implements the parameter in Lean, with Lean's core library and Std only. Each part is
written from its specification: RFC 8032 and ZIP 215 for Ed25519; the Bandersnatch VRF
specification for the Thin VRF, the IETF VRF and the Pedersen VRF; the ring proof of eprint 2023/002,
over BLS12-381 with a KZG setup; and RFC 9380 for hashing to the curve. The model never imports it.

It carries the primitives of both GP v0.8.0 and GP v0.8.1, selected by {api}`JamCrypto.GpVersion`.
The default is v0.8.0, because the model is tested against the published v0.8.0 test vectors until
v0.8.1 vectors exist; the v0.8.1 path uses
the Thin VRF and Draft 35 of the VRF specification, which GP v0.8.1 cites.
{api}`JamCrypto.withSignatures` fills in the Ed25519 and VRF-signature fields:

{leanSource JamCrypto.withSignatures}

and {api}`JamCrypto.Ring.crypto` the ring fields, from the KZG setup and, on the v0.8.0 path, the number of
validators (on the v0.8.1 path the count is ignored and the ring's domain is 2048 by default; `dom081` is a
parameter):

{leanSource JamCrypto.Ring.crypto}

On the v0.8.1 path, signature verification is {api}`JamCrypto.Bandersnatch.Thin.verify`, which follows
§3.2 of Draft 35:

{leanSource JamCrypto.Bandersnatch.Thin.verify}

Where Draft 35's prose and its own test vectors disagree (the zero padding inside hashing to the
curve, the three fixed points derived from it, and the ring proof's transcript label), the v0.8.1
path takes a {api}`JamCrypto.Reading`. The default, `.prose`, follows the prose of the cited draft;
`.vectors` follows its vectors. One step of the prose is followed under neither reading: §5's "Push R
to the transcript after instancing", which leaves R undefined in §5 and gives no label or encoding
for it; both readings push nothing there, as the vectors do:

{leanSource JamCrypto.Reading}

`JamCrypto`'s tests check it against the published vectors of the specifications it implements. On
the v0.8.1 path those vectors agree with the `.vectors` reading. No published vector follows the
`.prose` reading. Under it, the expansion step of hashing to the curve (`expand_message_xmd`) is
checked against RFC 9380's own vectors (Appendix K.3); the rest is tested only for internal
consistency (signing then verifying, and the properties of the derived points). The ring VRF under
`.prose` is not exercised by any accepted proof: `JamCrypto` has no ring prover, and the tests only
check that the draft's own ring proofs fail under `.prose`.

# The closed state-transition function
%%%
tag := "bandersnatch-closed"
%%%

{api}`JamCrypto.Model.crypto` fixes every choice above: the v0.8.1 path, Ed25519 under ZIP 215, the
Thin VRF, and the Draft 35 ring root and ring VRF over the 2048 domain, in the `.vectors` reading
(the one the published vectors and the fuzzer's blocks follow). Every field of the result is
computed by `JamCrypto`; the only input left is the ring VRF's public KZG setup, the SRS published
with the VRF specification:

{leanSource JamCrypto.Model.crypto}

{api}`JamCrypto.Model.importBlock` is $`\Upsilon` ({api}`JAM.importBlock`) with that crypto fixed.
It is the closed function a conformance proof targets: such a statement fixes the SRS, the chain's
{api}`JAM.Params`, and then quantifies over the ancestors, the prior state and the block. The model
itself still takes the crypto as a parameter and never imports `JamCrypto`;
{api}`JamCrypto.Model.importBlock_eq` states that the closed function is the parametric one at
{api}`JamCrypto.Model.crypto`.

# Fast implementations, proved equal to the reference
%%%
tag := "bandersnatch-fast"
%%%

`JamCrypto`'s reference code computes on arbitrary-precision naturals and follows the
specifications closely, which is slow. The modules under `JamCrypto/Fast/` compute the same functions
on fixed-size limbs (Montgomery arithmetic in the fields of Ed25519, Bandersnatch and BLS12-381),
and each fast function is proved equal to its reference function. The compiler is then told to run the fast code in place of the reference code
(`@[csimp]`); since `@[csimp]` takes a proved equality, the compiled program computes exactly the
reference functions. The equalities are kernel-checked proofs, not tests.

At the level of the parameter, the fast signature fields are the reference ones, for every version,
Ed25519 rule set and reading:

{mathdoc JamCrypto.Fast.withSignatures_eq}

The ring fields are handled differently. `JamCrypto.Ring.Fast.crypto` restates the text of
`JamCrypto.Ring.crypto` so that its compiled code calls the fast operations, and
{api}`JamCrypto.Ring.Fast.crypto_eq` proves the two equal essentially by `rfl`:

{leanSource JamCrypto.Ring.Fast.crypto_eq}

The substantive equalities are the `@[csimp]` proofs of the operations underneath: decoding,
scalar multiplication and hashing on the Bandersnatch curve, scalar and multi-scalar multiplication
and decompression in BLS12-381's group G1, and the pairing check.

These theorems say that the fast code computes the same functions as the reference code. They say
nothing about whether the reference code is a correct or secure implementation of the
specifications: that rests on the tests against the specifications' vectors.

# Readings chosen
%%%
tag := "bandersnatch-readings"
%%%

The first three are recorded in the model's
[notes on the paper](https://github.com/ascrivener/jam-lean/blob/main/docs/upstream-candidates.md#gray-paper-issues);
the fourth is in the same file's section on Draft 35 of the VRF specification:

* *Note v0.8.1-A6, the 96-octet signature.* The paper gives Thin VRF signatures as 96 octets and reads
  $`\mathcal{Y}` from the signature, but Draft 35 encodes only the proof $`(R, s)`, 64 octets. `JamCrypto` reads a
  signature as the output point $`O`, then $`R`, then $`s`
  ({api}`JamCrypto.Bandersnatch.Thin.thinDecode`). This was raised with the paper as
  gavofyork/graypaper#593, and the VRF specification's author confirmed the order $`O \frown R \frown s`
  and opened davxy/bandersnatch-vrf-spec#30.
* *Note v0.8.1-A5, the ring's size.* $`\mathcal{O}(\mathbf{k})` does not fix the ring size, on which the ring proof's
  domain depends. On the v0.8.1 path `JamCrypto` uses the fixed domain of 2048 that §5 of Draft 35
  states, for every number of validators; on the v0.8.0 path it sizes the ring by the number of
  validators, as the v0.8.0 vectors require.
* *Note v0.8.1-A7, context strings.* The paper's wording leaves open whether the `$` of
  $`\texttt{\$jam\_ticket\_seal}` is an octet of the context. Every signature of the GP v0.8.0 test vectors verifies only without it,
  and the model drops it ({api}`JAM.contextString`).
* *Draft 35's prose and vectors.* Where they disagree, the v0.8.1 path follows the prose by default
  and the vectors on request ({api}`JamCrypto.Reading`), as described above, except for the transcript
  step that neither follows.

{api}`JamCrypto.Bandersnatch.Thin.thinDecode`, which note v0.8.1-A6 above refers to:

{leanSource JamCrypto.Bandersnatch.Thin.thinDecode}
