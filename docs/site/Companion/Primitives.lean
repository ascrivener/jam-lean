import VersoManual
import Companion.Source
import Companion.Paper
import Companion.Docstring
import JAM.Blake2b
import JAM.Keccak
import JAM.Sha512
import JAM.Fast.Keccak
import JAM.Constants
import JAM.Params
import JAM.Safrole
import JAM.History

open Verso.Genre Manual
open Companion
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "§3 Primitives: hash functions and constants" =>
%%%
tag := "primitives"
shortTitle := "§3 Primitives"
file := "primitives"
%%%

*In the paper:* {gpchapter}`sec:notation`.

*In brief.* This chapter is the toolbox. Before the paper can say anything about blocks or
validators it fixes a common vocabulary (how it writes sets, sequences and dictionaries) and a few
ingredients that everything else is built from. The most used are two hash functions, which turn any
data into a short fixed-size fingerprint: Blake2b, the paper's default, which identifies blocks, code
and work-packages by hash, and Keccak, which the paper uses where it wants compatibility with existing
systems, such as the Accumulation Output Log of {ref "history"}[§7]. The chapter also lists the
protocol's fixed numbers, for example 341 cores, 1023 validators and epochs of 600 six-second
timeslots, which every later chapter uses. How data is written as octets, also basic, has its own
chapter, {ref "codec"}[Appendix C].

GP v0.8.1 §3 fixes the notation the rest of the paper uses. Most of it (sets, sequences,
dictionaries) maps directly onto Lean's own types. This chapter covers the part of §3 that the model has to
implement, the hash functions of §3.8.1, and also the protocol constants, which are not part of §3
but are listed in the paper's index of notation (Appendix I.4.4).

# Hashing (§3.8.1)
%%%
tag := "primitives-hashing"
%%%

The paper writes $`\mathbb{H}` for the set of 256-bit values, the same as $`\mathbb{B}_{32}`, and $`\mathbb{H}_0` for the zero hash
$`[0]_{32}`. It assumes two hash functions:

$$`\mathcal{H}(m \in \mathbb{B}) \in \mathbb{H} \;\text{(Blake2b, 256-bit)} \qquad \mathcal{H}_K(m \in \mathbb{B}) \in \mathbb{H} \;\text{(Keccak, 256-bit)}`

§3.8.1 has no numbered equations. The paper gives no definition of either function beyond its
citation (RFC 7693 for Blake2b, and Bertoni et al. for Keccak). The model implements both in plain
Lean: there is no foreign code, and every function is total.

## Blake2b-256

$`\mathcal{H}` is Blake2b with a 32-octet digest, {api}`JAM.Blake2b.hash256`:

{leanSource JAM.Blake2b.hash256}

{leanSource JAM.Blake2b.hash}

The compression function {api}`JAM.Blake2b.compress`, the mixing function {api}`JAM.Blake2b.mix`
and the constants {api}`JAM.Blake2b.iv` and {api}`JAM.Blake2b.sigma` follow RFC 7693 §2–§3. The
digest octets are read from the eight-word state with `getD`. For a digest of at most 64 octets
the default is never used. {api}`JAM.Blake2b.hash_getD_unused` is the arithmetic fact behind this: for $`n \le 64` and
$`k < n`, $`\lfloor k / 8 \rfloor < 8`, so every word index is within the eight-word state.

{leanSource JAM.Blake2b.compress}

{leanSource JAM.Blake2b.mix}

{leanSource JAM.Blake2b.iv}

{leanSource JAM.Blake2b.sigma}

Most of the model works on `List UInt8`, so it calls $`\mathcal{H}` through a list wrapper,
{api}`JAM.blake`:

{leanSource JAM.blake}

## Keccak-256

$`\mathcal{H}_K` is Keccak-256.
The paper uses $`\mathcal{H}_K` in recent history ({ref "history"}[§7]), for the Accumulation Output Log and the Merkle root of
the accumulation outputs, and in the super-peak function $`\mathcal{M}_R` of {ref "merkle"}[Appendix E.2]. Keccak-256 and SHA3-256 share the Keccak-f\[1600\]
permutation and differ only in their padding. The paper means the original Keccak, so
{api}`JAM.Keccak.keccak256` pads with the domain octet `0x01`. {api}`JAM.Keccak.sha3_256` pads with
`0x06` (FIPS 202) and exists only so that the permutation can be tested against standard SHA3
implementations.

{leanSource JAM.Keccak.sha3_256}

{leanSource JAM.Keccak.keccak256}

{leanSource JAM.Keccak.sponge256}

## Faster compiled code

The definitions above are the ones every theorem sees. For running the tests, the model also has
faster versions (in `JAM/Fast/`), proved equal to these and registered with Lean's `@[csimp]`
attribute, so the compiler substitutes them. The equalities are {api}`JAM.Blake2b.hash_eq_hashFast`
(`@hash = @hashFast`), {api}`JAM.Blake2b.blocks_eq_blocksFast` and
{api}`JAM.Keccak.sponge256_eq_sponge256Fast` (`@sponge256 = @sponge256Fast`).

## Tests

The hashes are checked by evaluation against reference digests: Blake2b against RFC 7693
Appendix A and Python's `hashlib.blake2b` at the 128-octet block boundaries
([`Tests/Blake2bTest.lean`](https://github.com/ascrivener/jam-lean/blob/main/Tests/Blake2bTest.lean));
SHA3-256 against Python's `hashlib.sha3_256` at the 136-octet rate boundaries, and Keccak-256
against its published values for the empty string and `"abc"`
([`Tests/KeccakTest.lean`](https://github.com/ascrivener/jam-lean/blob/main/Tests/KeccakTest.lean)).

## SHA-512, used below the paper

SHA-512 is not one of the paper's functions. The paper defers its signature schemes to their
specifications (§3.8.2 and {ref "bandersnatch"}[Appendix G]), and two of those use SHA-512: Ed25519 (RFC 8032) and the
Bandersnatch VRF, whose output $`\mathcal{Y}` is the first 32 octets of a SHA-512 hash. The model keeps all
signature verification behind a parameter (`JAM.Crypto`), so the model itself never calls SHA-512.
`JamCrypto`, the plain-Lean implementation of that parameter, does, through {api}`JAM.Sha512.hash`
(FIPS 180-4):

{leanSource JAM.Sha512.hash}

It is checked against the FIPS 180-2 examples and Python's `hashlib.sha512`
([`Tests/Sha512Test.lean`](https://github.com/ascrivener/jam-lean/blob/main/Tests/Sha512Test.lean)).

# Constants (Appendix I.4.4)
%%%
tag := "primitives-constants"
%%%

The paper's protocol constants are listed in Appendix I.4.4, each with a sans-serif symbol:
$`\mathsf{C} = 341` cores, epochs of $`\mathsf{E} = 600` slots of $`\mathsf{P} = 6` seconds, and so on. The model does not
transcribe them by hand. The file `JAM/Constants.lean` is generated by `scripts/gen_constants.py`
from the paper's own source (`text/definitions.tex` at tag v0.8.1), and CI regenerates it and
fails on any difference. For example:

{leanSource JAM.Constants.Ccorecount}

{leanSource JAM.Constants.Cepochlen}

The names follow the paper's TeX macros: `Ccorecount` is the paper's `\Ccorecount`, printed
$`\mathsf{C}`. The whole list is on the module's
[API page](https://ascrivener.github.io/jam-lean/api/JAM/Constants.html).

## Chain parameters

The paper defines one chain. The published test vectors also use a smaller one, the *tiny* chain,
which changes a few constants so that tests run quickly. So the transitions that depend on these
constants take them as an argument, a {api}`JAM.Params` record. Its fields are the constants that
the `fetch` host call reports (case 0, {ref "invocations"}[Appendix B]), in that order:

{leanSource JAM.Params}

{api}`JAM.Params.full` is the paper's chain, built from `JAM.Constants`:

{leanSource JAM.Params.full}

{api}`JAM.Params.tiny` keeps every value of the full chain except these:

:::table +header
*
  * Constant
  * Full chain (the paper)
  * Tiny chain
*
  * $`\mathsf{C}`, cores
  * 341
  * 2
*
  * $`\mathsf{D}`, expunge period
  * 19200
  * 32
*
  * $`\mathsf{E}`, epoch length
  * 600
  * 12
*
  * $`\mathsf{Y}`, ticket submission end
  * 500
  * 10
*
  * $`\mathsf{K}`, tickets per extrinsic
  * 16
  * 3
*
  * $`\mathsf{R}`, rotation period
  * 10
  * 4
*
  * $`\mathsf{G}_T`, total accumulation gas
  * 16 450 000 000
  * 20 000 000
*
  * $`\mathsf{G}_R`, refine gas
  * 23 500 000 000
  * 1 000 000 000
*
  * $`\mathsf{L}`, lookup-anchor age
  * 14400
  * 24
:::

The tiny values are test configuration, not part of the paper. They come from the test vectors'
README, except $`\mathsf{L}`, which the README does not list; the tiny vectors use 24
([paper and vectors](https://github.com/ascrivener/jam-lean/blob/main/docs/upstream-candidates.md#paper-and-vectors), note 32).

The test vectors the model runs were made for GP v0.8.0, before v0.8.1 changed five of the paper's
constants ($`\mathsf{G}_A`, $`\mathsf{G}_I`, $`\mathsf{G}_R`, $`\mathsf{G}_T` and $`\mathsf{W}_A`). The test harnesses therefore run them with two further chains,
`full080` and `tiny080`, which carry the v0.8.0 values
([`Tests/V080.lean`](https://github.com/ascrivener/jam-lean/blob/main/Tests/V080.lean)). For the tiny chain these are
$`\mathsf{G}_A = 10\,000\,000`, $`\mathsf{G}_I = 50\,000\,000` and $`\mathsf{W}_A = 64\,000`. {api}`JAM.Params.tiny` itself pairs the tiny values with v0.8.1's
$`\mathsf{G}_A = 47\,000\,000`, so it does not meet the paper's guidance that $`\mathsf{G}_T` be no smaller than
$`\mathsf{G}_A \cdot \mathsf{C} + \sum_{g \in \mathcal{V}(\chi_\mathbf{z})} g`: with $`\mathsf{C} = 2`, $`\mathsf{G}_A \cdot \mathsf{C} = 94\,000\,000 > \mathsf{G}_T = 20\,000\,000`.

# Readings chosen
%%%
tag := "primitives-readings"
%%%

Note v0.8.1-A33 is in the model's [notes on the paper](https://github.com/ascrivener/jam-lean/blob/main/docs/upstream-candidates.md#gray-paper-issues).

* *Keccak's padding (note v0.8.1-A33).* The paper cites Keccak as "proposed by Bertoni et al." and "utilized by"
  the Ethereum Yellow Paper. The model reads that as the original Keccak padding (`0x01`), not the
  FIPS 202 SHA3 padding (`0x06`).
* *The tiny chain.* The paper says nothing about the smaller chain the test vectors use. The model
  takes it from the vectors' README, with $`\mathsf{L} = 24` taken from the tiny vectors themselves.
