import VersoManual
import Companion.Source
import Companion.Paper
import Companion.Docstring
import JAM.Work
import JAM.Refine
import JAM.Segments
import JAM.Guarantee

open Verso.Genre Manual
open Companion
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "§14 Work packages and work reports" =>
%%%
tag := "work"
shortTitle := "§14 Work packages"
file := "work"
%%%

*In the paper:* {gpchapter}`sec:workpackagesandworkreports`.

*In brief.* JAM divides work into two halves: the heavy computation is done *in-core*, by the few
validators assigned to a core, and only its results go on chain, where every node processes them.
A *work-package* is the unit of in-core work: it carries an authorization and a list of work-items,
each naming a service and carrying a payload for that service's Refine code. This chapter defines
work-packages and the *work-report* computed from one: the package's authorization is checked, each
item is refined by a PVM invocation ({ref "invocations"}[Appendix B]), and the report records one
digest per item, the context the package was built against, and a specifier of the data made
available to other validators. Guarantors sign the report ({ref "guaranteeing"}[§15]),
{ref "reports"}[§11] puts it on chain, and once its data is available its results go to each
service's Accumulate code ({ref "accumulation"}[§12]). For example, a package with two items, for
two different services, yields a report with two digests, and each service accumulates its own.

*Key terms:*

* $`\workpackage`, work-packages, and $`\workitem`, work-items.
* $`\workreport`, work-reports, and $`\workdigest`, the work digest that each item yields.
* $`\computereport`, the computation of a work-report from a work-package.

A work-package is what a service's users submit to a core: an authorization, a context, and a
sequence of work-items, each naming a service and carrying a payload. §14 of GP v0.8.1 defines
these terms and the work-report computation $`\Xi`, which turns a work-package into the work-report
that guarantors sign and that {ref "reports"}[§11] puts on chain. Around $`\Xi` the section defines the item-to-digest
function $`C`, the implied authorizer $`\mathbf{p}_a`, the import and extrinsic data of an item, the bundle
assembly $`B` and the availability specifier $`A`.

$`\Xi` is off-chain logic: no state transition calls it. In the model it is one function,
{api}`JAM.Guarantee.computeReport`, defined in `JAM/Guarantee.lean` with the terms around it. The
work-package types are in `JAM/Work.lean`, and the two PVM invocations $`\Xi` uses, $`\Psi_I` and $`\Psi_R`
({ref "invocations"}[Appendix B]), are in `JAM/Refine.lean`. §15 (guaranteeing) and §16 (availability assurance) are
modelled only as far as this refinement: the networking, chunk distribution and signing they
describe are not.

The API pages are [JAM.Guarantee](https://ascrivener.github.io/jam-lean/api/JAM/Guarantee.html),
[JAM.Work](https://ascrivener.github.io/jam-lean/api/JAM/Work.html) and
[JAM.Refine](https://ascrivener.github.io/jam-lean/api/JAM/Refine.html).

# Packages and items (§14.3)
%%%
tag := "work-packages"
%%%

A work-package holds an authorization token $`\mathbf{j}`, the service $`h` that hosts the authorization code,
the code's hash $`u`, a configuration blob $`\mathbf{f}`, a context $`\mathbf{c}` and its work-items $`\mathbf{w}`:

{gpeq "14.2"}

{leanSource JAM.WorkPackage}

A work-item names its service $`s`, the service's code hash $`c`, a payload $`\mathbf{y}`, the gas limits
$`g` (refine) and $`a` (accumulate), the number $`e` of segments it exports, the segments $`\mathbf{i}` it imports and
its extrinsics $`\mathbf{x}`, each given by hash and length:

{gpeq "14.3"}

{leanSource JAM.WorkItem}

An item imports and exports *segments*, blobs of $`\mathsf{W}_G` octets:

{gpeq "14.1"}

The model has no separate type for $`\mathbb{J}`: a segment is an octet list of length $`\mathsf{W}_G`
({api}`JAM.Constants.Csegmentsize`), checked where an auditor reads one ({api}`JAM.Guarantee.checkImports`).

An import names its segment either by a segment root, from $`\mathbb{H}`, or by the hash of the work-package that
exported it, from the tagged $`\mathbb{H}^{\boxplus}`. The model's {api}`JAM.SegmentRoot` has one constructor for each.

{leanSource JAM.SegmentRoot}

The paper bounds every work-package: at most $`\mathsf{J}` dependencies,

{gpeq "14.4"}

at most $`\mathsf{W}_X` exports, $`\mathsf{W}_M` imports and $`\mathsf{T}` extrinsics,

{gpeq "14.5"}

at most $`\mathsf{W}_I` octets of input data, an imported segment counting $`\mathsf{W}_F` octets for itself and its proof,

{gpeq "14.6, 14.7, 14.8"}

so that a bundle has at most $`\mathsf{W}_B` octets,

{gpeq "14.9"}

and gas limits summing to at most $`\mathsf{G}_A` and $`\mathsf{G}_R`:

{gpeq "14.10"}

The model's types do not carry these bounds, and its $`\Xi` does not check them (see
{ref "work-readings"}[Readings chosen]). The chain checks the corresponding bounds on each work report instead
({ref "reports"}[§11], {eq}`11.3` and {eq}`11.33`), and the model has the constants $`\mathsf{W}_F`, $`\mathsf{W}_I` and
$`\mathsf{W}_B` as their values ({api}`JAM.Constants.Csegmentfootprint`, {api}`JAM.Constants.Cmaxinputsize`,
{api}`JAM.Constants.Cmaxbundlesize`), not derived from the formulas.

# Item to digest (§14.3)
%%%
tag := "work-digest"
%%%

Given the result $`\mathbf{l}` and the gas used $`u` of a work-item, $`C` gives its work-digest:

{gpeq "14.11"}

The mark $`\mathrel{\genfrac{}{}{0pt}{3}{\blacktriangleright}{\blacktriangleright}}` names a field and gives its value: $`y \mathrel{\genfrac{}{}{0pt}{3}{\blacktriangleright}{\blacktriangleright}} \mathcal{H}(\mathbf{y})` is the field $`y` with value $`\mathcal{H}(\mathbf{y})`.

{leanSource JAM.Guarantee.itemToDigest}

The hash function is a parameter `H` of the model's §14 functions; $`\Xi` fixes it to Blake2b-256, the
paper's $`\mathcal{H}`.

# The implied authorizer and the authorization code (§14.3)
%%%
tag := "work-authorizer"
%%%

{gpeq "14.12"}

{leanSource JAM.WorkPackage.authorizer}

The authorization code $`\mathbf{p}_\mathbf{u}` is the historical lookup $`\Lambda` ({ref "accounts"}[§9]) of the code hash in the host
service, at the timeslot $`t` of the lookup anchor. It is `none` in the model when the service or the
preimage is missing; {api}`JAM.psiI` then gives the error BAD.

{leanSource JAM.WorkPackage.authCode}

# Paged proofs (§14.3.1)
%%%
tag := "work-pagedproofs"
%%%

Besides its exported segments, a work-package places in the long-term store pages of segment
hashes with Merkle proofs, from which an import can later be justified against the segment root:

{gpeq "14.13"}

$`\mathcal{J}_6` and $`\mathcal{L}_6` are the subtree justification and leaf page of the constant-depth Merkle tree
({ref "merkle"}[Appendix E]). The model's $`P` is in `JAM/Segments.lean`:

{leanSource JAM.Segments.pagedProofs}

{mathdoc JAM.Segments.length_pagedProofs}

{mathdoc JAM.Segments.pagedProofs_verify}

# The work-report computation Ξ (§14.4)
%%%
tag := "work-xi"
%%%

$`\Xi` takes a work-package $`\mathbf{p}`, a core $`c`, a segment-root dictionary $`\mathbf{l}` and the number $`v` of assurers,
and gives a work-report or the error $`\nabla`:

{gpeq "14.14"}

where

$$`\begin{aligned} (\mathbf{t}, g) &= \Psi_I(\mathbf{p}, c) \\ E &= \mathbf{t} \notin \mathbb{B}_{:\mathsf{W}_R} \vee \mathcal{K}(\mathbf{l}) \ne \left\{ h \;\middle|\; \mathbf{w} \in \mathbf{p}_\mathbf{w}, (h^{\boxplus}, n) \in \mathbf{w}_\mathbf{i} \right\} \\ (\mathbf{d}, \overline{\mathbf{e}}) &= {}^{\text{T}}\left[ \left(C(\mathbf{p}_\mathbf{w}[j], r, u), \mathbf{e}\right) \;\middle|\; (r, u, \mathbf{e}) = I(\mathbf{p}, j),\, j \mathrel{\mathrlap{<}{-}} \mathbb{N}_{|\mathbf{p}_\mathbf{w}|} \right] \end{aligned}`

and $`I(\mathbf{p}, j)` refines item $`j`:

$$`I(\mathbf{p}, j) \equiv \begin{cases} \left(r, u, [\mathbb{J}_0, \mathbb{J}_0, \dots]_{\dots m_e}\right) & \text{if } r \notin \mathbb{B} \\ \left(\circleddash, u, [\mathbb{J}_0, \mathbb{J}_0, \dots]_{\dots m_e}\right) & \text{otherwise if } |r| + z > \mathsf{W}_R \\ \left(\circledcirc, u, [\mathbb{J}_0, \mathbb{J}_0, \dots]_{\dots m_e}\right) & \text{otherwise if } |\mathbf{e}| \ne m_e \\ (r, u, \mathbf{e}) & \text{otherwise} \end{cases}`

$$`\begin{aligned} &\text{where } (r, \mathbf{e}, u) = \Psi_R\left(c, j, \mathbf{p}, \mathbf{t}, S^\#_\mathbf{l}(\mathbf{p}_\mathbf{w}), \ell\right) \\ &\text{and } h = \mathcal{H}(\mathbf{p}),\; m = \mathbf{p}_\mathbf{w}[j],\; \ell = \sum_{k < j} \mathbf{p}_\mathbf{w}[k]_e \\ &\text{and } z = |\mathbf{t}| + \sum_{k < j,\, (r \in \mathbb{B}, \dots) = I(\mathbf{p}, k)} |r| \end{aligned}`

$`\circleddash` and $`\circledcirc` are the work errors for an oversized output and for a wrong number of exports;
in both cases "the work-item's exported segments are replaced by a sequence of zero-segments equal in size
to the export segment count", $`m_e` copies of $`\mathbb{J}_0`.
The model computes $`I` for all items in one left-to-right pass, carrying the export offset $`\ell` and the
size $`z`:

{leanSource JAM.Guarantee.itemResult}

{leanSource JAM.Guarantee.refineItems}

$`\Xi` itself. The model's $`\Xi` has two extra arguments: the account state $`\delta` that $`\Psi_I` and $`\Psi_R`
read, and the data of every item, $`(X(\mathbf{w}), S_\mathbf{l}(\mathbf{w}), J_\mathbf{l}(\mathbf{w}))`, defined in the next section:

{leanSource JAM.Guarantee.computeReport}

The availability specifier is the last line of §14.4's definitions:

{gpeq "14.18"}

$`\overgroup{\overline{\mathbf{e}}}` is the concatenation of every item's exports, `outs.flatMap (·.exports)` in the model.

What the model proves about $`I` and $`\Xi`: every item exports exactly $`m_e` segments, whichever case of $`I`
applies; and $`\Xi` succeeds, with the availability specifier of an empty export sequence, when
three conditions hold together: $`\Psi_I` returns a trace $`t` of at most $`\mathsf{W}_R` octets, the keys of $`\mathbf{l}`
are exactly the imported package hashes, and no item exports anything.

{mathdoc JAM.Guarantee.length_exports_itemResult}

{mathdoc JAM.Guarantee.refineItems_exports}

The one-pass computation is $`I` itself: output $`j` is $`I(\mathbf{p}, j)` with $`\ell` and $`z` as the paper defines them.

{mathdoc JAM.Guarantee.refineItems_getElem}

{mathdoc JAM.Guarantee.computeReport_noExports}

The paper also asks a guarantor to choose $`\mathbf{l}` so that every pair $`h \mapsto e` in it is the hash and segment root
of some work-package:

{gpeq "14.15"}

That is a condition on the guarantor's choice of $`\mathbf{l}`, and the model's $`\Xi` does not check it.

# The data of an item (§14.4)
%%%
tag := "work-data"
%%%

$`\Xi` and $`B` use the extrinsic data $`X`, the segment-root lookup $`L_\mathbf{l}`, the import data $`S_\mathbf{l}` and its
justifications $`J_\mathbf{l}`:

{gpeq "14.16"}

$`X` and $`S_\mathbf{l}` range over data the paper does not pass as arguments: the preimage of each
extrinsic hash, which "we make an assumption … is known by the guarantor", and the whole sequence
$`\mathbf{b}` of segments behind each segment root. The model takes both from a
{api}`JAM.Guarantee.DataSource`, and each function returns `none` when the data is missing or does not match:

{leanSource JAM.Guarantee.DataSource}

{leanSource JAM.Guarantee.lookupRoot}

{leanSource JAM.Guarantee.extrinsicOne}

{leanSource JAM.Guarantee.importOne}

{api}`JAM.Guarantee.extrinsicData` and {api}`JAM.Guarantee.importData` map these over $`\mathbf{w}_\mathbf{x}` and $`\mathbf{w}_\mathbf{i}`, and
{api}`JAM.Guarantee.packageData` collects $`(X(\mathbf{w}), S_\mathbf{l}(\mathbf{w}), J_\mathbf{l}(\mathbf{w}))` for every item of $`\mathbf{p}` (each item's triple is {api}`JAM.Guarantee.itemData`).

{leanSource JAM.Guarantee.extrinsicData}

{leanSource JAM.Guarantee.importData}

{leanSource JAM.Guarantee.itemData}

{leanSource JAM.Guarantee.packageData}

# Bundle assembly B (§14.4)
%%%
tag := "work-bundle"
%%%

{gpeq "14.17"}

"Note the lack of length prefixes: only the Merkle paths for the justifications have a length
prefix." The model concatenates the encoded package, every extrinsic, every imported segment, and
every justification path with its length prefix:

{leanSource JAM.Guarantee.bundle}

# The availability specifier A (§14.4.1)
%%%
tag := "work-avspec"
%%%

{gpeq "14.19"}

$$`\begin{aligned} \text{where } u &= \mathcal{M}_B\left( \left[ \overgroup{\mathbf{x}} \;\middle|\; \mathbf{x} \mathrel{\mathrlap{<}{-}} {}^{\text{T}}\left[\mathbf{b}^\clubsuit, \mathbf{s}^\clubsuit\right] \right] \right) \\ \text{and } \mathbf{b}^\clubsuit &= \mathcal{H}^\#\left(\mathcal{C}^{v}_{\lceil |\mathbf{b}|/z \rceil}\left(\mathcal{P}_z(\mathbf{b})\right)\right) \\ \text{and } \mathbf{s}^\clubsuit &= \mathcal{M}_B^\#\left({}^{\text{T}}_{v}\,\mathcal{C}^{v\#}_{\mathsf{W}_G/z}\left(\mathbf{s} \frown P(\mathbf{s})\right)\right) \\ \text{and } z &= 2 \cdot \mathcal{D}(v) \end{aligned}`

$`\mathcal{C}` is erasure coding and $`\mathcal{D}(v)` the number of original chunks for $`v` validators ({ref "erasure"}[Appendix H]);
$`\mathcal{M}` and $`\mathcal{M}_B` are the constant-depth and simple binary Merkle roots ({ref "merkle"}[Appendix E]). $`{}^{\text{T}}_v` is the transpose of a
sequence of sequences whose result has $`v` items, so that $`{}^{\text{T}}_v[]` is $`v` empty sequences:

{leanSource JAM.Guarantee.sizedTranspose}

{leanSource JAM.Guarantee.bundleClub}

{leanSource JAM.Guarantee.segmentsClub}

{leanSource JAM.Guarantee.erasureRoot}

{leanSource JAM.Guarantee.availabilitySpec}

The zero-padding function $`\mathcal{P}_n` takes an octet sequence to a multiple of $`n` in length:

{gpeq "14.20"}

{leanSource JAM.Segments.zeroPad}

What the model proves about $`A`. The second theorem is the paper's remark that "if no segments are
exported, each item of $`\mathbf{s}^\clubsuit` is the zero hash $`\mathbb{H}_0`":

{mathdoc JAM.Guarantee.length_segmentsClub}

{mathdoc JAM.Guarantee.segmentsClub_nil}

{mathdoc JAM.Guarantee.availabilitySpec_segmentRoot}

{mathdoc JAM.Guarantee.sizedTranspose_get}

# Checking a bundle (§17.2)
%%%
tag := "work-checks"
%%%

An auditor rebuilds a bundle from erasure-coded chunks and must check it before refining it again
({ref "auditing"}[§17.2], "Data Fetching"). The paper states these checks in prose only: the extrinsics' hashes must
equal those in their work-item, and each imported segment's justification must show that the
segment is included under its Merkle root at its index. The model decodes a bundle into the
package and the data of each item, the remaining lengths being "determinable through the work
package itself", and then checks it:

{leanSource JAM.Guarantee.checkBundle}

{leanSource JAM.Guarantee.verifyBundle}

The check of one imported segment is {api}`JAM.Segments.verifySegment`. Every segment verifies against the
segment root of its sequence with the $`\mathcal{J}_0` justification $`J_\mathbf{l}` uses. Building on that,
{api}`JAM.Guarantee.checkBundle` accepts a package together with the item data the data source
gives for it ({api}`JAM.Guarantee.packageData`), provided every segment the data source holds for the imports is $`\mathsf{W}_G` octets and the
keys of $`\mathbf{l}` are exactly the imported package hashes. The theorem is about the decoded form
that `checkBundle` takes. No round trip through the bundle's encoding is proved, so it does not
show that {api}`JAM.Guarantee.verifyBundle` accepts the encoded bundle:

{mathdoc JAM.Segments.verifySegment_justify}

{mathdoc JAM.Guarantee.checkBundle_packageData}

# The ancestor set (§11.4.1)
%%%
tag := "work-ancestors"
%%%

A lookup anchor must be a block the node has recorded. {ref "reports"}[§11.4.1] asks nodes to keep "the series of the
last $`\mathsf{L}` headers as the ancestor set $`\mathbf{A}`". The model keeps them in a {api}`JAM.Chain`:

{leanSource JAM.Chain.extend}

{mathdoc JAM.Chain.extend_spec}

# Readings chosen
%%%
tag := "work-readings"
%%%

Where the paper leaves a point open, the model picks one meaning. The notes cited are in the
model's [notes on the paper](https://github.com/ascrivener/jam-lean/blob/main/docs/upstream-candidates.md#gray-paper-issues).

* *The data $`\Xi` is not given (note v0.8.1-A16).* $`X` and $`S_\mathbf{l}` are written as comprehensions over the
  extrinsic preimages and over whole segment sequences, which are not arguments of $`\Xi`. The model takes
  them from a {api}`JAM.Guarantee.DataSource`, and its $`\Xi` takes the resulting data of every item as an argument,
  as its $`\Psi_R` already takes the extrinsic data of every item. $`L_\mathbf{l}(h^{\boxplus})` is undefined when $`h` is not a key
  of $`\mathbf{l}`, and $`\mathbf{b}[n]` names nothing when $`n \ge |\mathbf{b}|`: the model returns `none` in both cases. (That $`\mathcal{H}(\mathbf{p})`
  is $`\mathcal{H}(\mathcal{E}(\mathbf{p}))` is not a reading: §3.8 passes the inputs of a hash function through $`\mathcal{E}`.)
* *The running size $`z` (note v0.8.1-A17).* $`z` is defined through $`I` itself: it sums the outputs of the earlier items
  as $`I` returns them, so an output that $`I` replaced by $`\circleddash` or $`\circledcirc` adds nothing. The model follows the
  formula ({api}`JAM.Guarantee.refineItems`, {api}`JAM.Guarantee.refineItems_getElem`).
* *The bundle checks (note v0.8.1-A18).* {ref "auditing"}[§17.2] gives the checks on a bundle only in prose. The model decodes
  the bundle (rejecting trailing octets) and checks one data entry per item, each extrinsic's hash
  and length, each segment's size $`\mathsf{W}_G` and its justification against $`L_\mathbf{l}(r)` at index $`n`, and that the keys
  of $`\mathbf{l}` are the imported work-package hashes ({api}`JAM.Guarantee.checkBundle`). Comparing the package's
  hash with the report is left to the caller.
* *How a justification is checked (note v0.8.1-A13).* The paper defines how justifications are made, not how
  they are checked. The model's {api}`JAM.Segments.verifySegment` recomputes the root from the segment and
  its path.
* *The pages of $`P` (note v0.8.1-A15).* The prose after {eq}`14.19` calls each page "a page of 64 hashes of
  segments"; the model follows the equation, whose page $`\mathcal{L}_6` holds the leaf hashes of the segments, and
  whose last page is short when 64 does not divide $`|\mathbf{s}|`.
* *Package limits.* {eq}`14.4`–{eq}`14.10` are stated for every $`\mathbf{p} \in \mathbb{P}`. The model's types do not enforce
  them and its $`\Xi` does not check them, so it computes a report for any package.
* *Malformed data argument.* The model's $`\Xi` expects one data entry per item; a missing entry reads as
  empty.
