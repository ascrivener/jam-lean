import JAM.Refine
import JAM.Segments
import JAM.Erasure
import JAM.Decode
import JAM.BlockImport

/-!
# Work-package refinement: the work-report $\Xi$, the bundle $B$ and the availability specifier $A$
(GP v0.8.1 §14.3, §14.4, §14.4.1, with the bundle checks of §17.2)

From GP v0.8.1 §14 (`work_packages_and_reports.tex`):

* $p_a = \mathcal{H}(p_u \frown p_f)$, the implied authorizer (§14.3) — `WorkPackage.authorizer`;
* $C(w, r, u)$, item to digest (§14.3) — `itemToDigest`;
* $L_l$, $X$, $S_l$, $J_l$, the segment-root lookup and the data of an item (§14.4) — `lookupRoot`,
  `extrinsicData`, `importData`, `itemData`;
* $B(p, l)$, bundle assembly (eq. `makebundle`) — `bundle`, `bundleOf`;
* $I(p, j)$, one item's refinement with the error order of GP #568 (eq. `computereport`) —
  `itemResult`, `refineItems`;
* $\Xi(p, c, l, v)$, the work-report (eq. `computereport`) — `computeReport`;
* $A(h, b, s, v)$, the availability specifier (§14.4.1), with the sized transpose ${}^\text{T}_m$ of Appendix H
  (eq. `transpose`, as GP #583 states it) — `sizedTranspose`, `bundleClub`, `segmentsClub`,
  `availabilitySpec`.

From §17.2 (`auditing.tex`, "Data Fetching"), the checks on a decoded bundle: extrinsics against
their (hash, length), imported segments against their roots with their justifications, and the
segment-root dictionary's keys (the second disjunct of $E$ in eq. `computereport`) — `Bundle.decode`,
`checkBundle`, `verifyBundle`.

From §11.4.1, the ancestor set $\mathbf{A}$ kept as the last $\mathsf{L}$ headers — `Chain.extend`.

**Data the paper does not pass.** $X$, $S_l$ and $J_l$ (§14.4) are comprehensions over data the guarantor
is assumed to hold: the preimage of each extrinsic hash, and the whole exported-segment sequence
behind each segment root. The model takes that data from a `DataSource` (Option where it is
missing), and $\Xi$ takes the resulting per-item data as an argument, as `psiR` already takes $\bar{x}$
(upstream candidate v0.8.1-A16).

The hash function $H$ is a parameter of the pure parts ($B$'s checks, $A$), as in `JAM.Segments`; the
paper's $H$ is Blake2b, and $\Xi$ fixes it to `Blake2b.hash256`, as $\Psi_R$ does.

Main results: `length_segmentsClub` ($|\mathbf{s}^\clubsuit| = v$), `segmentsClub_nil` (no exports: every item of
$\mathbf{s}^\clubsuit$ is $\zerohash$), `availabilitySpec_segmentRoot` (the segment root is $\mathcal{M}(\mathbf{s})$), `length_exports_itemResult`
and `refineItems_exports` ($I$ exports exactly $w_e$ segments on every branch),
`computeReport_noExports` ($\Xi$ succeeds with the $\zerohash$ columns when nothing is exported), and
`checkBundle_packageData` (the checks accept the bundle built from genuine data).
-/

namespace JAM.Guarantee

/-- An octet sequence as a list (the form `JAM.Segments` and `JAM.Merkle` use). -/
abbrev Octets := List UInt8

open JAM.Segments (zeroHash cdRoot justify pagedProofs zeroPad verifySegment)

/-! ## §14.3: the implied authorizer and item-to-digest -/

/-- $p_a \equiv \mathcal{H}(p_u \frown p_f)$ (GP v0.8.1 §14.3): the hash of the authorization code hash concatenated
    with the configuration. -/
def _root_.JAM.WorkPackage.authorizer (H : ByteArray → ByteArray) (p : WorkPackage) : Hash :=
  H (p.authCodeHash ++ p.authConfig)

/-- $C(w, r, u)$ (GP v0.8.1 §14.3, the item-to-digest function): the digest of item $w$ with result $r$
    and refine gas used $u$: $s$, $c$, $y = \mathcal{H}(w_y)$, $g = w_a$, $l = r$, $u$, $i = |w_i|$, $e = w_e$, $x = |w_x|$ and
    $z = \sum_{(h, z) \in w_x} z$. -/
def itemToDigest (H : ByteArray → ByteArray) (w : WorkItem) (r : WorkResult) (u : Nat) :
    WorkDigest :=
  { service := w.service, codeHash := w.codeHash, payloadHash := H w.payload,
    gasLimit := w.accumulateGasLimit, result := r, gasUsed := u,
    importCount := w.importSegments.length, extrinsicCount := w.extrinsics.length,
    extrinsicSize := (w.extrinsics.map (·.2)).sum, exportCount := w.exportCount }

/-! ## §14.4: the data of an item -/

/-- What a guarantor holds besides the package (GP v0.8.1 §14.3: "we make an assumption that the
    preimage to each extrinsic hash in each work-item is known by the guarantor"; §14.4: the
    segments $\hat{s}$ behind each segment root, which $X$, $S_l$ and $J_l$ range over). Both are partial: data
    the guarantor lacks is `none`. -/
structure DataSource where
  /-- the preimage of an extrinsic hash -/
  preimage : List UInt8 → Option Octets
  /-- the exported segments $\hat{s}$ committed to by a segment root -/
  exports : List UInt8 → Option (List Octets)

/-- The data of one work item, as §14.4 defines it from the package and a segment-root
    dictionary: $X(w)$, $S_l(w)$ and $J_l(w)$. -/
structure ItemData where
  /-- $X(w)$, the extrinsic data -/
  extrinsics : List Octets
  /-- $S_l(w)$, the imported segments -/
  imports : List Octets
  /-- $J_l(w)$, the $J_0$ justification of each imported segment -/
  justifications : List (List Octets)
  deriving DecidableEq, Repr

/-- The set $\{h \mid w \in p_w, (h^\boxplus, n) \in w_i\}$ of work-package hashes that $p$'s items import through
    (GP v0.8.1 eq. `computereport`, $E$). -/
def packageImports (p : WorkPackage) : OctetSet :=
  Std.ExtTreeSet.ofList (p.items.flatMap fun w => w.importSegments.filterMap fun
    | (.package h, _) => some h.toList
    | (.root _, _) => none)

/-- $\mathcal{K}(l) = \{h \mid w \in p_w, (h^\boxplus, n) \in w_i\}$ (GP v0.8.1 eq. `computereport`, the negation of $E$'s
    second disjunct): the dictionary has exactly the imported work-package hashes as keys. Both
    sides are in ascending order. -/
def lookupMatches (p : WorkPackage) (l : OctetDict) : Bool :=
  decide (l.keys = (packageImports p).toList)

/-- $L_l(r)$ (GP v0.8.1 §14.4, the segment-root lookup): $r$ itself for a segment root, $l[h]$ for $h^\boxplus$.
    `none` when $h \notin \mathcal{K}(l)$, where the paper's $L_l$ is undefined. -/
def lookupRoot (l : OctetDict) : SegmentRoot → Option Octets
  | .root h => some h.toList
  | .package h => l.get? h.toList

/-- One extrinsic reference $(h, n)$ resolved: the preimage $\mathbf{d}$ of $h$, if $|\mathbf{d}| = n$ and
    $\mathcal{H}(\mathbf{d}) = h$ (GP v0.8.1 §14.4, $X$). -/
def extrinsicOne (H : ByteArray → ByteArray) (src : DataSource) (hn : Hash × Nat) :
    Option Octets := do
  let x ← src.preimage hn.1.toList
  if Segments.hashL H x = hn.1.toList ∧ x.length = hn.2 then some x else none

/-- $X(w) = [\mathbf{d} \mid (\mathcal{H}(\mathbf{d}), |\mathbf{d}|) \leftarrow w_x]$ (GP v0.8.1 §14.4): the preimage of each extrinsic
    reference, checked against its hash and length. `none` if any is missing or wrong. -/
def extrinsicData (H : ByteArray → ByteArray) (src : DataSource) (w : WorkItem) :
    Option (List Octets) :=
  w.extrinsics.mapM (extrinsicOne H src)

/-- One import reference $(r, n)$ resolved against $l$ and the data source: the segment $\hat{s}[n]$ and its
    justification $J_0(\hat{s}, n)$, for the $\hat{s}$ with $\mathcal{M}(\hat{s}) = L_l(r)$ (GP v0.8.1 §14.4, $S_l$ and $J_l$). -/
def importOne (H : ByteArray → ByteArray) (src : DataSource) (l : OctetDict)
    (rn : SegmentRoot × Nat) : Option (Octets × List Octets) := do
  let root ← lookupRoot l rn.1
  let s ← src.exports root
  if h : cdRoot H s = root ∧ rn.2 < s.length then some (s[rn.2]'h.2, justify H 0 s rn.2)
  else none

/-- $S_l(w) = [\hat{s}[n] \mid \mathcal{M}(\hat{s}) = L_l(r), (r, n) \leftarrow w_i]$ and $J_l(w) = [J_0(\hat{s}, n) \mid \dots]$ (GP v0.8.1 §14.4),
    together. -/
def importData (H : ByteArray → ByteArray) (src : DataSource) (l : OctetDict) (w : WorkItem) :
    Option (List Octets × List (List Octets)) :=
  (w.importSegments.mapM (importOne H src l)).map List.unzip

/-- $(X(w), S_l(w), J_l(w))$ for one item. -/
def itemData (H : ByteArray → ByteArray) (src : DataSource) (l : OctetDict) (w : WorkItem) :
    Option ItemData := do
  let xs ← extrinsicData H src w
  let (ss, js) ← importData H src l w
  some ⟨xs, ss, js⟩

/-- The data of every item of $p$. -/
def packageData (H : ByteArray → ByteArray) (src : DataSource) (l : OctetDict) (p : WorkPackage) :
    Option (List ItemData) :=
  p.items.mapM (itemData H src l)

/-! ## $B$: bundle assembly -/

/-- $B(p, l) = \mathcal{E}(p, X^\#(p_w), S_l^\#(p_w), J_l^\#(p_w))$ (GP v0.8.1 eq. `makebundle`), from the
    per-item data: the encoded package, then every extrinsic, then every imported segment, then
    every justification. "Note the lack of length prefixes: only the Merkle paths for the
    justifications have a length prefix": each path is $\updownarrow$ (a sequence of hashes), everything else
    is concatenated. -/
def bundle (p : WorkPackage) (data : List ItemData) : Octets :=
  p.encode ++ (data.flatMap (·.extrinsics)).flatten ++ (data.flatMap (·.imports)).flatten ++
    (data.flatMap (·.justifications)).flatMap (Codec.varSeq id)

/-- $B(p, l)$ from a data source (GP v0.8.1 eq. `makebundle`). -/
def bundleOf (H : ByteArray → ByteArray) (src : DataSource) (l : OctetDict) (p : WorkPackage) :
    Option Octets :=
  (packageData H src l p).map (bundle p)

/-! ## $A$: the availability specifier (§14.4.1) -/

/-- ${}^\text{T}_m\mathbf{x}$ (GP v0.8.1 eq. `transpose` and the sentence after it, GP #583): the transpose of a
    sequence of sequences where the result is known to have $m$ items. Column $i$ is item $i$ of every
    row; ${}^\text{T}_m[]$ is $m$ empty sequences. For rows of length $m$ it is the transpose (`sizedTranspose_get`);
    `d` fills short rows, which the paper never transposes. -/
def sizedTranspose {α : Type} (m : Nat) (d : α) (x : List (List α)) : List (List α) :=
  (List.range m).map fun i => x.map fun row => row.getD i d

/-- $\fnerasurecode{v}{k}$ for $v$ validators on an octet list (GP v0.8.1 eq. `erasurecoding`; $k$ is read from the
    length). `[]` if the length is not a multiple of $2 \cdot \fnecoriginalshards(v)$, which $A$ never asks for
    (`length_chunks`). -/
def chunks (v : Nat) (b : Octets) : List Octets :=
  match Erasure.encode v ⟨b.toArray⟩ with
  | some cs => cs.map (·.toList)
  | none => []

/-- $z = 2 \cdot \fnecoriginalshards(v)$ (GP v0.8.1 §14.4.1). -/
def pieceSize (v : Nat) : Nat := 2 * Erasure.originalShards v

/-- $\mathbf{b}^\clubsuit = \mathcal{H}^\#(\mathcal{E}_{C_v}^{\lceil |\mathbf{b}|/z \rceil}(\mathcal{P}_z(\mathbf{b})))$ (GP v0.8.1 §14.4.1): the hash of each of the $v$
    chunks of the zero-padded bundle. -/
def bundleClub (H : ByteArray → ByteArray) (b : Octets) (v : Nat) : List Octets :=
  (chunks v (zeroPad (pieceSize v) b)).map (Segments.hashL H)

/-- $\mathbf{s}^\clubsuit = \mathcal{M}_B^\#({}^\text{T}_v \mathcal{E}_{C_v}^{\mathsf{W}_G/z\,\#}(\mathbf{s} \frown P(\mathbf{s})))$ (GP v0.8.1 §14.4.1, with ${}^\text{T}_v$ as GP #583
    states it): each exported segment and each paged-proof segment is coded into $v$ chunks; column
    $i$ (chunk $i$ of every segment) is Merklized with $\mathcal{M}_B$. With no exports every column is [] and its
    root is $\mathcal{M}_B([]) = \zerohash$ (`segmentsClub_nil`, the paper's "if no segments are exported, each item
    of $\mathbf{s}^\clubsuit$ is the zero hash"). -/
def segmentsClub (H : ByteArray → ByteArray) (s : List Octets) (v : Nat) : List Octets :=
  (sizedTranspose v [] ((s ++ pagedProofs H s).map (chunks v))).map (Merkle.root H)

/-- $u = \mathcal{M}_B([\frown\mathbf{x} \mid \mathbf{x} \leftarrow {}^\text{T}[\mathbf{b}^\clubsuit, \mathbf{s}^\clubsuit]])$ (GP v0.8.1 §14.4.1): the erasure root, over the
    $v$ pairs $(\mathbf{b}^\clubsuit_i, \mathbf{s}^\clubsuit_i)$ concatenated. -/
def erasureRoot (H : ByteArray → ByteArray) (b : Octets) (s : List Octets) (v : Nat) : Octets :=
  Merkle.root H ((sizedTranspose v [] [bundleClub H b v, segmentsClub H s v]).map List.flatten)

/-- $A(h, \mathbf{b}, \mathbf{s}, v) = (h, l = |\mathbf{b}|, u, v, e = \mathcal{M}(\mathbf{s}), n = |\mathbf{s}|)$ (GP v0.8.1 §14.4.1):
    the availability specifier of a package with hash $h$, bundle $\mathbf{b}$, exported segments $\mathbf{s}$ and
    $v$ assurers. -/
def availabilitySpec (H : ByteArray → ByteArray) (h : Hash) (b : Octets) (s : List Octets) (v : Nat) :
    AvailabilitySpec :=
  { packageHash := h, bundleLength := b.length, erasureRoot := ⟨(erasureRoot H b s v).toArray⟩,
    erasureShards := v, segmentRoot := ⟨(cdRoot H s).toArray⟩, segmentCount := s.length }

/-! ## $I$: one item's refinement -/

/-- The result of $I(p, j)$: the result or error $r$, the gas used $u$ and the exported segments $\mathbf{e}$. -/
structure ItemOut where
  result : WorkResult
  gasUsed : Nat
  exports : List Octets

/-- $[\segment_0, \segment_0, \dots]_{\cdots w_e}$: $w_e$ zero segments of $\mathsf{W}_G$ octets (GP v0.8.1 eq. `computereport`). -/
def zeroSegments (n : Nat) : List Octets := List.replicate n (List.replicate Constants.Csegmentsize 0)

/-- $I(p, j)$ given $\Psi_R$'s output $(r, \mathbf{e}, u)$ for item $m = p_w[j]$ and $z$, the trace length plus the
    output lengths of the earlier items (GP v0.8.1 eq. `computereport`, with the order of GP #568):

    * $(r, u, \text{zeros})$ when $r \notin \mathbb{B}$;
    * $(\circleddash, u, \text{zeros})$ otherwise when $|r| + z > \mathsf{W}_R$;
    * $(\circledcirc, u, \text{zeros})$ otherwise when $|\mathbf{e}| \ne m_e$;
    * $(r, u, \mathbf{e})$ otherwise,

    zeros being $m_e$ zero segments. `wR` is $\mathsf{W}_R$. -/
def itemResult (wR : Nat) (m : WorkItem) (z : Nat) (out : RefineOut) : ItemOut :=
  match out.result with
  | .err e => ⟨.err e, out.gasUsed, zeroSegments m.exportCount⟩
  | .ok r =>
    if r.size + z > wR then ⟨.err .oversize, out.gasUsed, zeroSegments m.exportCount⟩
    else if out.exports.length ≠ m.exportCount then
      ⟨.err .badExports, out.gasUsed, zeroSegments m.exportCount⟩
    else ⟨.ok r, out.gasUsed, out.exports⟩

/-- The size an item's result contributes to $z$: $|r|$ for $r \in \mathbb{B}$, else 0. -/
def resultSize : WorkResult → Nat
  | .ok r => r.size
  | .err _ => 0

/-- $[I(p, j) \mid j \leftarrow \mathbb{N}_{|p_w|}]$ (GP v0.8.1 eq. `computereport`), in order, given `refine j ℓ`, the
    output of $\Psi_R(c, j, p, t, S_l^\#(p_w), \ell)$. The fold carries $\ell = \sum_{k<j} p_w[k]_e$, the export
    offset, and $z = |t| + \sum_{k<j, (r \in \mathbb{B}, \dots) = I(p, k)} |r|$, which counts the results of $I$, so an
    output replaced by $\circleddash$ or $\circledcirc$ adds nothing (upstream candidate v0.8.1-A17). `t` is $|t|$. -/
def refineItems (wR : Nat) (refine : Nat → Nat → RefineOut) (items : List WorkItem) (t : Nat) :
    List ItemOut :=
  go 0 0 t items
where
  /-- Items from index $j$ on, with export offset $\ell$ and size so far $z$. -/
  go (j ℓ z : Nat) : List WorkItem → List ItemOut
    | [] => []
    | m :: ms =>
      let o := itemResult wR m z (refine j ℓ)
      o :: go (j + 1) (ℓ + m.exportCount) (z + resultSize o.result) ms

/-! ## $\Xi$: the work-report -/

/-- $\Xi(p, c, l, v)$ (GP v0.8.1 eq. `computereport`) over accounts $\mathbf{d}$, with the per-item data
    `data` = $[(X(w), S_l(w), J_l(w)) \mid w \leftarrow p_w]$ (`packageData`):

    * $(t, g) = \Psi_I(p, c)$;
    * $\nabla$ (`none`) when $t \notin \mathbb{B}[:\mathsf{W}_R]$ or $\mathcal{K}(l) \ne \{h \mid w \in p_w, (h^\boxplus, n) \in w_i\}$ ($E$);
    * otherwise $(\mathbf{d}, \bar{\mathbf{e}}) = {}^\text{T}[(C(p_w[j], r, u), \mathbf{e}) \mid (r, u, \mathbf{e}) = I(p, j), j \leftarrow \mathbb{N}_{|p_w|}]$,
      and the report $(s, c = p_c, c, a = p_a, g, t, l, \mathbf{d})$ with
      $s = A(\mathcal{H}(p), B(p, l), \frown\bar{\mathbf{e}}, v)$.

    `data` must have one entry per item; a missing entry reads as empty. -/
def computeReport (params : Params) (d : Accounts) (p : WorkPackage) (c : Nat) (l : OctetDict)
    (v : Nat) (data : List ItemData) : Option WorkReport :=
  let H := Blake2b.hash256
  match psiI params d p c with
  | (.err _, _) => none
  | (.ok t, g) =>
    if t.size > params.maxReportVarSize ∨ !lookupMatches p l then none
    else
      let imports := data.map (·.imports)
      let xs := data.map (·.extrinsics)
      let outs := refineItems params.maxReportVarSize
        (fun j ℓ => psiR params d c j p t.toList imports xs ℓ) p.items t.size
      let digests := (p.items.zip outs).map fun (w, o) => itemToDigest H w o.result o.gasUsed
      let exports := outs.flatMap (·.exports)
      some { spec := availabilitySpec H (H ⟨p.encode.toArray⟩) (bundle p data) exports v,
             context := p.context, core := c, authorizerHash := p.authorizer H, authGasUsed := g,
             authTrace := t, segmentRootLookup := l, digests }

/-! ## §17.2: checking a bundle -/

/-- A bundle decoded into the package and the data of each item. -/
structure Bundle where
  package : WorkPackage
  items : List ItemData

/-- $\mathcal{E}^{-1}$ of a bundle (GP v0.8.1 eq. `makebundle`, "all other sequence lengths are determinable
    through the work package itself"): the package; then, item by item, each extrinsic at the
    length its reference gives; then $\mathsf{W}_G$ octets per imported segment; then a $\updownarrow$ path of 32-octet
    hashes per imported segment. The decoded data is split per item. -/
def Bundle.decode : Decoder Bundle := do
  let p ← WorkPackage.decode
  let xs ← p.items.mapM fun w => w.extrinsics.mapM fun (_, n) => do
    return (← Decoder.bytes n).toList
  let ss ← p.items.mapM fun w => w.importSegments.mapM fun _ => do
    return (← Decoder.bytes Constants.Csegmentsize).toList
  let js ← p.items.mapM fun w => w.importSegments.mapM fun _ => do
    return (← Decoder.varSeq (Decoder.bytes 32)).map (·.toList)
  return ⟨p, ((xs.zip ss).zip js).map fun ((x, s), j) => ⟨x, s, j⟩⟩

/-- The extrinsics of item $w$ check against $w_x$ (GP v0.8.1 §17.2, "ensuring their hashes are each
    equivalent to those found in the relevant work-item", and $X$ of §14.4): one per reference, each
    with the referenced hash and length. -/
def checkExtrinsics (H : ByteArray → ByteArray) (w : WorkItem) (xs : List Octets) : Bool :=
  xs.length == w.extrinsics.length &&
    (xs.zip w.extrinsics).all fun (x, h, n) => Segments.hashL H x == h.toList && x.length == n

/-- The imports of item $w$ check against $w_i$ (GP v0.8.1 §17.2, "a justification must follow the
    concatenated segments which allows verification that each segment's hash is included in the
    referencing Merkle root and index of the corresponding work-item"): one segment and one
    justification per reference; each segment is $\mathsf{W}_G$ octets and verifies (`verifySegment`)
    against $L_l(r)$ at index $n$ with its justification. -/
def checkImports (H : ByteArray → ByteArray) (l : OctetDict) (w : WorkItem) (ss : List Octets)
    (js : List (List Octets)) : Bool :=
  ss.length == w.importSegments.length && js.length == w.importSegments.length &&
    ((w.importSegments.zip ss).zip js).all fun (((r, n), s), j) =>
      s.length == Constants.Csegmentsize &&
        match lookupRoot l r with
        | some root => verifySegment H root n s j
        | none => false

/-- The checks on a decoded bundle against a segment-root dictionary $l$ (GP v0.8.1 §17.2 and
    eq. `computereport`): $\mathcal{K}(l)$ is the set of imported work-package hashes, there is one data entry
    per item, and each item's extrinsics and imports check. The paper states these checks only in
    prose (upstream candidate v0.8.1-A18). -/
def checkBundle (H : ByteArray → ByteArray) (l : OctetDict) (b : Bundle) : Bool :=
  lookupMatches b.package l && b.items.length == b.package.items.length &&
    (b.package.items.zip b.items).all fun (w, x) =>
      checkExtrinsics H w x.extrinsics && checkImports H l w x.imports x.justifications

/-- Decode and check a bundle (GP v0.8.1 §17.3: "a failure to decode or verify the bundle implies
    an invalid work-report"). -/
def verifyBundle (H : ByteArray → ByteArray) (l : OctetDict) (bs : Octets) : Option Bundle :=
  match Decoder.run Bundle.decode ⟨bs.toArray⟩ with
  | .ok b => if checkBundle H l b then some b else none
  | .error _ => none

/-! ## §11.4.1: the ancestor set -/

/-- The retained headers after importing $\mathbf{H}$ (GP v0.8.1 §11.4.1: "retaining the series of the last
    $\mathsf{L}$ headers as the ancestor set $\mathbf{A}$"): $\mathbf{H}$ appended, then only the last $\mathsf{L}$ kept. -/
def _root_.JAM.Chain.extend (params : Params) (c : Chain) (h : Header) : Chain :=
  ⟨(c.ancestors ++ [h]).drop (c.ancestors.length + 1 - params.maxLookupAnchorAge)⟩

/-! ## Theorems -/

theorem length_sizedTranspose {α : Type} (m : Nat) (d : α) (x : List (List α)) :
    (sizedTranspose m d x).length = m := by
  simp [sizedTranspose]

/-- ${}^\text{T}_m[]$ is $m$ empty sequences (GP v0.8.1, after eq. `transpose`). -/
theorem sizedTranspose_nil {α : Type} (m : Nat) (d : α) :
    sizedTranspose m d [] = List.replicate m [] := by
  simp [sizedTranspose, List.map_const']

/-- On rows of length $m$, ${}^\text{T}_m$ is the transpose (GP v0.8.1 eq. `transpose`): item $j$ of column $i$ is
    item $i$ of row $j$. -/
theorem sizedTranspose_get {α : Type} (m : Nat) (d : α) (x : List (List α)) (i j : Nat)
    (hi : i < m) (hj : j < x.length) (hrow : ∀ r ∈ x, r.length = m) :
    ((sizedTranspose m d x)[i]'(by simp [sizedTranspose, hi]))[j]'(by simp [sizedTranspose, hj]) =
      (x[j]'hj)[i]'(by rw [hrow _ (List.getElem_mem hj)]; exact hi) := by
  have : i < (x[j]'hj).length := by rw [hrow _ (List.getElem_mem hj)]; exact hi
  simp [sizedTranspose, List.getD_eq_getElem?_getD, this]

/-- $|\mathbf{s}^\clubsuit| = v$ (GP v0.8.1 §14.4.1). -/
theorem length_segmentsClub (H : ByteArray → ByteArray) (s : List Octets) (v : Nat) :
    (segmentsClub H s v).length = v := by
  simp [segmentsClub, length_sizedTranspose]

theorem pagedProofs_nil (H : ByteArray → ByteArray) : pagedProofs H [] = [] := by
  simp [pagedProofs]

/-- With no exports, every item of $\mathbf{s}^\clubsuit$ is the zero hash $\zerohash$ (GP v0.8.1 §14.4.1, "if no segments
    are exported, each item of $\mathbf{s}^\clubsuit$ is the zero hash"; GP #583). -/
theorem segmentsClub_nil (H : ByteArray → ByteArray) (v : Nat) :
    segmentsClub H [] v = List.replicate v zeroHash := by
  simp [segmentsClub, pagedProofs_nil, sizedTranspose_nil, Merkle.root, Merkle.node, zeroHash]

/-- $A$'s segment root is $\mathcal{M}(\mathbf{s})$ and its count $|\mathbf{s}|$ (GP v0.8.1 §14.4.1). -/
theorem availabilitySpec_segmentRoot (H : ByteArray → ByteArray) (h : Hash) (b : Octets)
    (s : List Octets) (v : Nat) :
    (availabilitySpec H h b s v).segmentRoot = ⟨(cdRoot H s).toArray⟩ ∧
      (availabilitySpec H h b s v).segmentCount = s.length ∧
      (availabilitySpec H h b s v).erasureShards = v := ⟨rfl, rfl, rfl⟩

/-- $I(p, j)$ exports exactly $m_e$ segments, on every branch (GP v0.8.1 eq. `computereport`). -/
theorem length_exports_itemResult (wR : Nat) (m : WorkItem) (z : Nat) (out : RefineOut) :
    (itemResult wR m z out).exports.length = m.exportCount := by
  unfold itemResult
  split
  · simp [zeroSegments]
  · split
    · simp [zeroSegments]
    · split
      · simp [zeroSegments]
      · simp_all

theorem length_refineItems_go (wR : Nat) (refine : Nat → Nat → RefineOut) :
    ∀ (items : List WorkItem) (j ℓ z : Nat),
      (refineItems.go wR refine j ℓ z items).length = items.length
  | [], _, _, _ => rfl
  | _ :: ms, j, ℓ, z => by simp [refineItems.go, length_refineItems_go wR refine ms]

theorem length_refineItems (wR : Nat) (refine : Nat → Nat → RefineOut) (items : List WorkItem)
    (t : Nat) : (refineItems wR refine items t).length = items.length :=
  length_refineItems_go wR refine items 0 0 t

theorem refineItems_go_exports (wR : Nat) (refine : Nat → Nat → RefineOut) :
    ∀ (items : List WorkItem) (j ℓ z : Nat),
      (refineItems.go wR refine j ℓ z items).map (·.exports.length) = items.map (·.exportCount)
  | [], _, _, _ => rfl
  | m :: ms, j, ℓ, z => by
    simp only [refineItems.go, List.map_cons, length_exports_itemResult,
      refineItems_go_exports wR refine ms]

/-- Item $j$ of $[I(p, j) \mid j \leftarrow \mathbb{N}_{|p_w|}]$ exports exactly $p_w[j]_e$ segments (GP v0.8.1
    eq. `computereport`): the export counts of the outputs are those of the items. -/
theorem refineItems_exports (wR : Nat) (refine : Nat → Nat → RefineOut) (items : List WorkItem)
    (t : Nat) :
    (refineItems wR refine items t).map (·.exports.length) = items.map (·.exportCount) :=
  refineItems_go_exports wR refine items 0 0 t

/-- The total number of exported segments is $\sum_j p_w[j]_e$. -/
theorem length_flatMap_exports (wR : Nat) (refine : Nat → Nat → RefineOut)
    (items : List WorkItem) (t : Nat) :
    ((refineItems wR refine items t).flatMap (·.exports)).length =
      (items.map (·.exportCount)).sum := by
  rw [List.length_flatMap, ← refineItems_exports wR refine items t]

/-- $\Xi$ succeeds with the $\zerohash$ columns when nothing is exported (GP v0.8.1 eq. `computereport`,
    §14.4.1): if $\Psi_I$ gives a trace $t \in \mathbb{B}[:\mathsf{W}_R]$, $l$ has exactly the imported package hashes as keys,
    and every item has $w_e = 0$, then $\Xi$ gives a report whose availability specifier is
    $A(\mathcal{H}(p), B(p, l), [], v)$, so its segment root is $\mathcal{M}([])$ and its segment count 0, and every
    item of the $\mathbf{s}^\clubsuit$ behind its erasure root is $\zerohash$. -/
theorem computeReport_noExports (params : Params) (d : Accounts) (p : WorkPackage) (c : Nat)
    (l : OctetDict) (v : Nat) (data : List ItemData) (t : ByteArray) (g : Nat)
    (hI : psiI params d p c = (.ok t, g)) (ht : t.size ≤ params.maxReportVarSize)
    (hl : lookupMatches p l = true) (he : ∀ w ∈ p.items, w.exportCount = 0) :
    ∃ r, computeReport params d p c l v data = some r ∧
      r.spec = availabilitySpec Blake2b.hash256 (Blake2b.hash256 ⟨p.encode.toArray⟩)
        (bundle p data) [] v ∧
      segmentsClub Blake2b.hash256 [] v = List.replicate v zeroHash := by
  have hsum : (p.items.map (·.exportCount)).sum = 0 := by
    have key : ∀ ws : List WorkItem, (∀ w ∈ ws, w.exportCount = 0) →
        (ws.map (·.exportCount)).sum = 0 := by
      intro ws h
      induction ws with
      | nil => rfl
      | cons w ws ih => simp_all
    exact key _ he
  have hnil : ∀ (refine : Nat → Nat → RefineOut),
      (refineItems params.maxReportVarSize refine p.items t.size).flatMap (·.exports) = [] := by
    intro refine
    apply List.eq_nil_of_length_eq_zero
    rw [length_flatMap_exports, hsum]
  have hc : ¬(t.size > params.maxReportVarSize ∨ (!lookupMatches p l) = true) := by
    simp [hl]; omega
  simp only [computeReport, hI, hc, ↓reduceIte]
  refine ⟨_, rfl, ?_, segmentsClub_nil _ v⟩
  simp only [hnil]

/-! ### The checks accept genuine data -/

theorem extrinsicOne_check (H : ByteArray → ByteArray) (src : DataSource) (hn : Hash × Nat)
    (x : Octets) (h : extrinsicOne H src hn = some x) :
    Segments.hashL H x = hn.1.toList ∧ x.length = hn.2 := by
  unfold extrinsicOne at h
  cases hx : src.preimage hn.1.toList with
  | none => simp [hx] at h
  | some y =>
    simp only [hx, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; assumption
    · simp at h

theorem extrinsicData_check (H : ByteArray → ByteArray) (src : DataSource) (w : WorkItem)
    (xs : List Octets) (h : extrinsicData H src w = some xs) : checkExtrinsics H w xs = true := by
  unfold extrinsicData at h
  unfold checkExtrinsics
  generalize w.extrinsics = es at h ⊢
  induction es generalizing xs with
  | nil => simp at h; subst h; simp
  | cons e es ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind] at h
    cases h1 : extrinsicOne H src e with
    | none => simp [h1] at h
    | some x =>
      cases h2 : es.mapM (extrinsicOne H src) with
      | none => simp [h1, h2] at h
      | some ys =>
        simp only [h1, h2, Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        have ih' := ih ys h2
        have hc := extrinsicOne_check H src e x h1
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ih' ⊢
        simp only [List.length_cons, List.zip_cons_cons, List.mem_cons, forall_eq_or_imp]
        refine ⟨by omega, ⟨by simp [hc.1], by simp [hc.2]⟩, ih'.2⟩

theorem importOne_check (H : ByteArray → ByteArray) (src : DataSource) (l : OctetDict)
    (hseg : ∀ r s, src.exports r = some s → ∀ x ∈ s, x.length = Constants.Csegmentsize)
    (rn : SegmentRoot × Nat) (sj : Octets × List Octets) (h : importOne H src l rn = some sj) :
    sj.1.length = Constants.Csegmentsize ∧
      ∃ root, lookupRoot l rn.1 = some root ∧ verifySegment H root rn.2 sj.1 sj.2 = true := by
  unfold importOne at h
  cases hr : lookupRoot l rn.1 with
  | none => simp [hr] at h
  | some root =>
    cases hs : src.exports root with
    | none => simp [hr, hs] at h
    | some s =>
      simp only [hr, hs, Option.bind_eq_bind, Option.bind_some] at h
      split at h
      · rename_i hc
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨hseg _ _ hs _ (List.getElem_mem _), root, rfl, ?_⟩
        have := Segments.verifySegment_justify H s rn.2 hc.2
        simpa [hc.1] using this
      · simp at h

theorem importData_check (H : ByteArray → ByteArray) (src : DataSource) (l : OctetDict)
    (hseg : ∀ r s, src.exports r = some s → ∀ x ∈ s, x.length = Constants.Csegmentsize)
    (w : WorkItem) (ss : List Octets) (js : List (List Octets))
    (h : importData H src l w = some (ss, js)) : checkImports H l w ss js = true := by
  unfold importData at h
  unfold checkImports
  generalize w.importSegments = is at h ⊢
  induction is generalizing ss js with
  | nil => simp at h; obtain ⟨rfl, rfl⟩ := h; simp
  | cons rn is ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind] at h
    cases h1 : importOne H src l rn with
    | none => simp [h1] at h
    | some sj =>
      cases h2 : is.mapM (importOne H src l) with
      | none => simp [h1, h2] at h
      | some rest =>
        simp only [h1, h2, Option.bind_some, Option.map_some, Option.pure_def,
          List.unzip_cons, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have ih' := ih rest.unzip.1 rest.unzip.2 (by rw [h2]; rfl)
        obtain ⟨hlen, root, hroot, hv⟩ := importOne_check H src l hseg rn sj h1
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ih' ⊢
        simp only [List.length_cons, List.zip_cons_cons, List.mem_cons, forall_eq_or_imp]
        refine ⟨⟨by omega, by omega⟩, ?_, ih'.2⟩
        simp [hlen, hroot, hv]

/-- The bundle checks accept the bundle built from genuine data (GP v0.8.1 §14.4, §17.2): if
    every item's $(X(w), S_l(w), J_l(w))$ comes from the data source (`packageData`), every
    segment the data source holds (the segments this package imports, `hseg`) is $\mathsf{W}_G$ octets, and $\mathcal{K}(l)$ is the set of imported package hashes, then
    `checkBundle` accepts the package with that data. -/
theorem checkBundle_packageData (H : ByteArray → ByteArray) (src : DataSource) (l : OctetDict)
    (p : WorkPackage) (data : List ItemData)
    (hseg : ∀ r s, src.exports r = some s → ∀ x ∈ s, x.length = Constants.Csegmentsize)
    (hl : lookupMatches p l = true) (h : packageData H src l p = some data) :
    checkBundle H l ⟨p, data⟩ = true := by
  unfold packageData at h
  unfold checkBundle
  simp only [hl, Bool.true_and]
  generalize p.items = ws at h ⊢
  induction ws generalizing data with
  | nil => simp at h; subst h; simp
  | cons w ws ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind] at h
    cases h1 : itemData H src l w with
    | none => simp [h1] at h
    | some x =>
      cases h2 : ws.mapM (itemData H src l) with
      | none => simp [h1, h2] at h
      | some rest =>
        simp only [h1, h2, Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        have ih' := ih rest h2
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ih' ⊢
        simp only [List.length_cons, List.zip_cons_cons, List.mem_cons, forall_eq_or_imp]
        refine ⟨by omega, ?_, ih'.2⟩
        unfold itemData at h1
        cases hx : extrinsicData H src w with
        | none => simp [hx] at h1
        | some xs =>
          cases hi : importData H src l w with
          | none => simp [hx, hi] at h1
          | some sj =>
            obtain ⟨ss, js⟩ := sj
            simp [hx, hi] at h1
            subst h1
            exact ⟨extrinsicData_check H src w xs hx, importData_check H src l hseg w ss js hi⟩

/-! ### The ancestor set -/

/-- `Chain.extend` keeps at most $\mathsf{L}$ headers, ends with the new header when $\mathsf{L} \ge 1$, and keeps a
    suffix of the old headers followed by the new one (GP v0.8.1 §11.4.1). When fewer than $\mathsf{L}$
    headers were kept, nothing is dropped. -/
theorem _root_.JAM.Chain.extend_spec (params : Params) (c : Chain) (h : Header) :
    (c.extend params h).ancestors.length ≤ params.maxLookupAnchorAge ∧
      (c.extend params h).ancestors <:+ c.ancestors ++ [h] ∧
      (1 ≤ params.maxLookupAnchorAge → (c.extend params h).ancestors.getLast? = some h) ∧
      (c.ancestors.length < params.maxLookupAnchorAge →
        (c.extend params h).ancestors = c.ancestors ++ [h]) := by
  simp only [Chain.extend]
  refine ⟨by simp; omega, List.drop_suffix _ _, fun h1 => ?_, fun h2 => ?_⟩
  · rw [List.getLast?_drop]
    have : c.ancestors.length + 1 - params.maxLookupAnchorAge < c.ancestors.length + 1 := by omega
    simp [this]
  · rw [show c.ancestors.length + 1 - params.maxLookupAnchorAge = 0 by omega]
    simp

end JAM.Guarantee
