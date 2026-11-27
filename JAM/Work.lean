import JAM.Codec

/-!
# Work packages, work items and work reports (GP v0.8.1 §11, §14) and their encodings (Appendix C)

Not yet modelled: the deferred-transfer field $u$ of GP v0.8.1 #539 (junior services, phase 2).

The terms that refine and is-authorized take as input and produce as output, with $\mathcal{E}$ as
Appendix C defines it for each.
-/

namespace JAM

open Codec

/-- A service identifier $\mathbb{N}_S = \mathbb{N}_{2^{32}}$. -/
abbrev ServiceId := Nat

/-- The refinement context $\mathbb{C}$ (GP eq. `workcontext`). -/
structure RefineContext where
  /-- $a$, the anchor header hash -/
  anchorHash : Hash
  /-- $n$, the anchor timeslot -/
  anchorSlot : Nat
  /-- $s$, the anchor posterior state root -/
  anchorStateRoot : Hash
  /-- $b$, the anchor accumulation-output-log super-peak -/
  anchorAccOutLog : Hash
  /-- $l$, the lookup-anchor header hash -/
  lookupAnchorHash : Hash
  /-- $t$, the lookup-anchor timeslot -/
  lookupAnchorSlot : Nat
  /-- $r$, the lookup-anchor posterior state root -/
  lookupAnchorStateRoot : Hash
  /-- $\mathbf{p}$, the prerequisite work-package hashes, a set $[\![ \mathbb{H} ]\!]$ -/
  prerequisites : OctetSet := ∅

/-- $\mathcal{E}(x \in \mathbb{C})$ (GP Appendix C). -/
def RefineContext.encode (x : RefineContext) : List UInt8 :=
  blob x.anchorHash ++ fixed 4 x.anchorSlot ++ blob x.anchorStateRoot ++ blob x.anchorAccOutLog ++
    blob x.lookupAnchorHash ++ fixed 4 x.lookupAnchorSlot ++ blob x.lookupAnchorStateRoot ++
    varHashSet x.prerequisites

/-- An imported segment's identifier: a segment root $h \in \mathbb{H}$, or a work-package hash
    $h^\boxplus \in \mathbb{H}^\boxplus$ (GP eq. `workitem`). -/
inductive SegmentRoot where
  | root (h : Hash)
  | package (h : Hash)

/-- $I((h, i))$: $\mathcal{E}(h) \frown \mathcal{E}_2(i)$ for a segment root,
    $\mathcal{E}(r) \frown \mathcal{E}_2(i + 2^{15})$ for $r^\boxplus$ (GP Appendix C). -/
def encodeImport : SegmentRoot × Nat → List UInt8
  | (.root h, i) => blob h ++ fixed 2 i
  | (.package r, i) => blob r ++ fixed 2 (i + 2 ^ 15)

/-- A work item $\mathbb{W}$ (GP eq. `workitem`). -/
structure WorkItem where
  /-- $s$, the service -/
  service : ServiceId
  /-- $c$, the service's code hash -/
  codeHash : Hash
  /-- $\mathbf{y}$, the payload -/
  payload : Blob
  /-- $g$, the refine gas limit -/
  refineGasLimit : Nat
  /-- $a$, the accumulate gas limit -/
  accumulateGasLimit : Nat
  /-- $e$, the number of exported segments -/
  exportCount : Nat
  /-- $\mathbf{i}$, the imported segments -/
  importSegments : List (SegmentRoot × Nat)
  /-- $\mathbf{x}$, the extrinsics (hash, length) -/
  extrinsics : List (Hash × Nat)

/-- $\mathcal{E}(w \in \mathbb{W})$ (GP Appendix C). -/
def WorkItem.encode (w : WorkItem) : List UInt8 :=
  fixed 4 w.service ++ blob w.codeHash ++ fixed 8 w.refineGasLimit ++ fixed 8 w.accumulateGasLimit ++
    fixed 2 w.exportCount ++ var w.payload ++ varSeq encodeImport w.importSegments ++
    varSeq (fun (h, i) => blob h ++ fixed 4 i) w.extrinsics

/-- A work package $\mathbb{P}$ (GP eq. `workpackage`). -/
structure WorkPackage where
  /-- $\mathbf{j}$, the authorization token -/
  authToken : Blob
  /-- $h$, the service hosting the authorization code -/
  authCodeHost : ServiceId
  /-- $u$, the authorization code hash -/
  authCodeHash : Hash
  /-- $\mathbf{f}$, the authorizer configuration -/
  authConfig : Blob
  /-- $\mathbf{c}$, the refinement context -/
  context : RefineContext
  /-- $\mathbf{w}$, the work items -/
  items : List WorkItem

/-- $\mathcal{E}(p \in \mathbb{P})$ (GP Appendix C). -/
def WorkPackage.encode (p : WorkPackage) : List UInt8 :=
  fixed 4 p.authCodeHost ++ blob p.authCodeHash ++ p.context.encode ++ var p.authToken ++
    var p.authConfig ++ varSeq WorkItem.encode p.items

/-- The work errors $\mathbb{E}$ (GP eq. `workerror`): $\infty$, ☇, $\circledcirc$, $\circleddash$,
    BAD, BIG. -/
inductive WorkError where
  | outOfGas
  | panic
  | badExports
  | oversize
  | bad
  | big
  deriving DecidableEq, Repr

/-- A work result: an output blob or a work error. -/
inductive WorkResult where
  | ok (o : Blob)
  | err (e : WorkError)

/-- $O(o)$ (GP Appendix C): $(0, \updownarrow o)$ for a blob, 1–6 for the errors. -/
def WorkResult.encode : WorkResult → List UInt8
  | .ok o => 0 :: var o
  | .err .outOfGas => [1]
  | .err .panic => [2]
  | .err .badExports => [3]
  | .err .oversize => [4]
  | .err .bad => [5]
  | .err .big => [6]

/-- A work digest $\mathbb{D}$ (GP eq. `workdigest`). -/
structure WorkDigest where
  /-- $s$ -/
  service : ServiceId
  /-- $c$ -/
  codeHash : Hash
  /-- $y$, the payload hash -/
  payloadHash : Hash
  /-- $g$, the accumulate gas limit -/
  gasLimit : Nat
  /-- $\mathbf{l}$, the result -/
  result : WorkResult
  /-- $u$, gas used in refine -/
  gasUsed : Nat
  /-- $i$, segments imported -/
  importCount : Nat
  /-- $x$, extrinsics used -/
  extrinsicCount : Nat
  /-- $z$, total extrinsic size -/
  extrinsicSize : Nat
  /-- $e$, segments exported -/
  exportCount : Nat

/-- $\mathcal{E}(d \in \mathbb{D})$ (GP Appendix C). The five load figures use the variable-length
    $\mathcal{E}$. -/
def WorkDigest.encode (d : WorkDigest) : List UInt8 :=
  fixed 4 d.service ++ blob d.codeHash ++ blob d.payloadHash ++ fixed 8 d.gasLimit ++
    d.result.encode ++ nat d.gasUsed ++ nat d.importCount ++ nat d.extrinsicCount ++
    nat d.extrinsicSize ++ nat d.exportCount

/-- An availability specification $\mathbb{Y}$ (GP eq. `avspec`). -/
structure AvailabilitySpec where
  packageHash : Hash
  bundleLength : Nat
  erasureRoot : Hash
  erasureShards : Nat
  segmentRoot : Hash
  segmentCount : Nat

/-- $\mathcal{E}(s \in \mathbb{Y})$ (GP Appendix C). -/
def AvailabilitySpec.encode (s : AvailabilitySpec) : List UInt8 :=
  blob s.packageHash ++ fixed 4 s.bundleLength ++ blob s.erasureRoot ++ fixed 2 s.erasureShards ++
    blob s.segmentRoot ++ fixed 2 s.segmentCount

/-- A work report $\mathbb{R} = (\mathbf{s}, \mathbf{c}, c, a, g, \mathbf{t}, \mathbf{l}, \mathbf{d})$ (GP v0.8.1 eq. `workreport`; #537 moved
    $g$ to fifth place, matching Appendix C, where v0.8.0's tuple had it last). -/
structure WorkReport where
  /-- $\mathbf{s}$ -/
  spec : AvailabilitySpec
  /-- $\mathbf{c}$ -/
  context : RefineContext
  /-- $c$, the core index -/
  core : Nat
  /-- $a$, the authorizer hash -/
  authorizerHash : Hash
  /-- $g$, gas used by is-authorized -/
  authGasUsed : Nat
  /-- $\mathbf{t}$, the authorizer trace -/
  authTrace : Blob
  /-- $\mathbf{l}$, the segment-root lookup dictionary $\mathbb{H} \to \mathbb{H}$ -/
  segmentRootLookup : OctetDict := ∅
  /-- $\mathbf{d}$, the work digests -/
  digests : List WorkDigest

/-- $\mathcal{E}(r \in \mathbb{R})$ (GP Appendix C). -/
def WorkReport.encode (r : WorkReport) : List UInt8 :=
  r.spec.encode ++ r.context.encode ++ nat r.core ++ blob r.authorizerHash ++ nat r.authGasUsed ++
    var r.authTrace ++ varHashDict r.segmentRootLookup ++ varSeq WorkDigest.encode r.digests

end JAM

namespace JAM

open Codec

/-- An operand tuple $\mathbb{U}$, the accumulation input from one work item (GP eq. `operandtuple`). -/
structure OperandTuple where
  /-- $p$, the work-package hash -/
  packageHash : Hash
  /-- $e$, the segment root -/
  segmentRoot : Hash
  /-- $a$, the authorizer hash -/
  authorizer : Hash
  /-- $y$, the payload hash -/
  payloadHash : Hash
  /-- $g$, the accumulate gas limit -/
  gasLimit : Nat
  /-- $\mathbf{t}$, the authorizer trace -/
  authTrace : Blob
  /-- $\mathbf{l}$, the work result -/
  result : WorkResult

/-- $\mathcal{E}(o \in \mathbb{U}) = \mathcal{E}(0, p, e, a, y, g, O(\mathbf{l}), \updownarrow \mathbf{t})$
    (GP Appendix C). -/
def OperandTuple.encode (o : OperandTuple) : List UInt8 :=
  nat 0 ++ blob o.packageHash ++ blob o.segmentRoot ++ blob o.authorizer ++ blob o.payloadHash ++
    nat o.gasLimit ++ o.result.encode ++ var o.authTrace

/-- A deferred transfer $\text{𝕥}$ (GP eq. `defxfer`). -/
structure DeferredTransfer where
  source : ServiceId
  dest : ServiceId
  /-- whether the destination's supervisor balance is credited rather than its balance
      (GP v0.8.1 eq. `defxfer`, GP #539) -/
  destSupervisor : Bool := false
  amount : Nat
  /-- the $\mathsf{W}_T$-octet memo -/
  memo : Blob
  gas : Nat

/-- $\mathcal{E}(x \in \text{𝕥}) = \mathcal{E}(1, \mathcal{E}_4(s), \mathcal{E}_4(d), x_u,
    \mathcal{E}_8(a), m, \mathcal{E}_8(g))$ with $x_u$ the destination-supervisor flag (GP v0.8.1
    Appendix C, GP #539). -/
def DeferredTransfer.encode (x : DeferredTransfer) : List UInt8 :=
  nat 1 ++ fixed 4 x.source ++ fixed 4 x.dest ++ nat (if x.destSupervisor then 1 else 0) ++
    fixed 8 x.amount ++ blob x.memo ++ fixed 8 x.gas

/-- An accumulation input: an operand tuple or a deferred transfer (GP §12, the union $\mathbb{U}
    \cup \text{𝕥}$). -/
inductive AccumulateInput where
  | operand (o : OperandTuple)
  | transfer (x : DeferredTransfer)

/-- $\mathcal{E}$ of an accumulation input. -/
def AccumulateInput.encode : AccumulateInput → List UInt8
  | .operand o => o.encode
  | .transfer x => x.encode

end JAM
