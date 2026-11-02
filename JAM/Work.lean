import JAM.Codec

/-!
# Work packages, work items and work reports (GP v0.8.0 §11, §14) and their encodings (Appendix C)

The terms that refine and is-authorized take as input and produce as output, with ℰ as Appendix C
defines it for each.
-/

namespace JAM

open Codec

/-- A service identifier ℕ_S = ℕ_{2^32}. -/
abbrev ServiceId := Nat

/-- The refinement context 𝕏 (GP eq. `workcontext`). -/
structure RefineContext where
  /-- a, the anchor header hash -/
  anchorHash : Hash
  /-- t, the anchor timeslot -/
  anchorSlot : Nat
  /-- s, the anchor posterior state root -/
  anchorStateRoot : Hash
  /-- b, the anchor accumulation-output-log super-peak -/
  anchorAccOutLog : Hash
  /-- l, the lookup-anchor header hash -/
  lookupAnchorHash : Hash
  /-- t, the lookup-anchor timeslot -/
  lookupAnchorSlot : Nat
  /-- s, the lookup-anchor posterior state root -/
  lookupAnchorStateRoot : Hash
  /-- p, the prerequisite work-package hashes (a set) -/
  prerequisites : List Hash

/-- ℰ(x ∈ 𝕏) (GP Appendix C). -/
def RefineContext.encode (x : RefineContext) : List UInt8 :=
  blob x.anchorHash ++ fixed 4 x.anchorSlot ++ blob x.anchorStateRoot ++ blob x.anchorAccOutLog ++
    blob x.lookupAnchorHash ++ fixed 4 x.lookupAnchorSlot ++ blob x.lookupAnchorStateRoot ++
    varHashSet x.prerequisites

/-- An imported segment's identifier: a segment root h ∈ ℍ, or a work-package hash h^⊞ ∈ ℍ^⊞
    (GP eq. `workitem`). -/
inductive SegmentRoot where
  | root (h : Hash)
  | package (h : Hash)

/-- I((h, i)): ℰ(h) ⌢ ℰ_2(i) for a segment root, ℰ(r) ⌢ ℰ_2(i + 2^15) for r^⊞ (GP Appendix C). -/
def encodeImport : SegmentRoot × Nat → List UInt8
  | (.root h, i) => blob h ++ fixed 2 i
  | (.package r, i) => blob r ++ fixed 2 (i + 2 ^ 15)

/-- A work item 𝕀 (GP eq. `workitem`). -/
structure WorkItem where
  /-- s, the service -/
  service : ServiceId
  /-- c, the service's code hash -/
  codeHash : Hash
  /-- y, the payload -/
  payload : Blob
  /-- g, the refine gas limit -/
  refineGasLimit : Nat
  /-- a, the accumulate gas limit -/
  accumulateGasLimit : Nat
  /-- e, the number of exported segments -/
  exportCount : Nat
  /-- i, the imported segments -/
  importSegments : List (SegmentRoot × Nat)
  /-- x, the extrinsics (hash, length) -/
  extrinsics : List (Hash × Nat)

/-- ℰ(w ∈ 𝕀) (GP Appendix C). -/
def WorkItem.encode (w : WorkItem) : List UInt8 :=
  fixed 4 w.service ++ blob w.codeHash ++ fixed 8 w.refineGasLimit ++ fixed 8 w.accumulateGasLimit ++
    fixed 2 w.exportCount ++ var w.payload ++ varSeq encodeImport w.importSegments ++
    varSeq (fun (h, i) => blob h ++ fixed 4 i) w.extrinsics

/-- A work package ℙ (GP eq. `workpackage`). -/
structure WorkPackage where
  /-- j, the authorization token -/
  authToken : Blob
  /-- h, the service hosting the authorization code -/
  authCodeHost : ServiceId
  /-- u, the authorization code hash -/
  authCodeHash : Hash
  /-- f, the authorizer configuration -/
  authConfig : Blob
  /-- c, the refinement context -/
  context : RefineContext
  /-- w, the work items -/
  items : List WorkItem

/-- ℰ(p ∈ ℙ) (GP Appendix C). -/
def WorkPackage.encode (p : WorkPackage) : List UInt8 :=
  fixed 4 p.authCodeHost ++ blob p.authCodeHash ++ p.context.encode ++ var p.authToken ++
    var p.authConfig ++ varSeq WorkItem.encode p.items

/-- The work errors 𝕁 (GP eq. `workerror`): ∞, ☇, ⊚, ⊖, BAD, BIG. -/
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

/-- O(o) (GP Appendix C): (0, ↕o) for a blob, 1–6 for the errors. -/
def WorkResult.encode : WorkResult → List UInt8
  | .ok o => 0 :: var o
  | .err .outOfGas => [1]
  | .err .panic => [2]
  | .err .badExports => [3]
  | .err .oversize => [4]
  | .err .bad => [5]
  | .err .big => [6]

/-- A work digest 𝔻 (GP eq. `workdigest`). -/
structure WorkDigest where
  /-- s -/
  service : ServiceId
  /-- c -/
  codeHash : Hash
  /-- y, the payload hash -/
  payloadHash : Hash
  /-- g, the accumulate gas limit -/
  gasLimit : Nat
  /-- l, the result -/
  result : WorkResult
  /-- u, gas used in refine -/
  gasUsed : Nat
  /-- i, segments imported -/
  importCount : Nat
  /-- x, extrinsics used -/
  extrinsicCount : Nat
  /-- z, total extrinsic size -/
  extrinsicSize : Nat
  /-- e, segments exported -/
  exportCount : Nat

/-- ℰ(d ∈ 𝔻) (GP Appendix C). The five load figures use the variable-length ℰ. -/
def WorkDigest.encode (d : WorkDigest) : List UInt8 :=
  fixed 4 d.service ++ blob d.codeHash ++ blob d.payloadHash ++ fixed 8 d.gasLimit ++
    d.result.encode ++ nat d.gasUsed ++ nat d.importCount ++ nat d.extrinsicCount ++
    nat d.extrinsicSize ++ nat d.exportCount

/-- An availability specification 𝕐 (GP eq. `avspec`). -/
structure AvailabilitySpec where
  packageHash : Hash
  bundleLength : Nat
  erasureRoot : Hash
  erasureShards : Nat
  segmentRoot : Hash
  segmentCount : Nat

/-- ℰ(s ∈ 𝕐) (GP Appendix C). -/
def AvailabilitySpec.encode (s : AvailabilitySpec) : List UInt8 :=
  blob s.packageHash ++ fixed 4 s.bundleLength ++ blob s.erasureRoot ++ fixed 2 s.erasureShards ++
    blob s.segmentRoot ++ fixed 2 s.segmentCount

/-- A work report ℝ (GP eq. `workreport`). -/
structure WorkReport where
  /-- s -/
  spec : AvailabilitySpec
  /-- c -/
  context : RefineContext
  /-- c, the core index -/
  core : Nat
  /-- a, the authorizer hash -/
  authorizerHash : Hash
  /-- t, the authorizer trace -/
  authTrace : Blob
  /-- l, the segment-root lookup dictionary -/
  segmentRootLookup : List (Hash × Hash)
  /-- d, the work digests -/
  digests : List WorkDigest
  /-- g, gas used by is-authorized -/
  authGasUsed : Nat

/-- ℰ(r ∈ ℝ) (GP Appendix C). -/
def WorkReport.encode (r : WorkReport) : List UInt8 :=
  r.spec.encode ++ r.context.encode ++ nat r.core ++ blob r.authorizerHash ++ nat r.authGasUsed ++
    var r.authTrace ++ varHashDict r.segmentRootLookup ++ varSeq WorkDigest.encode r.digests

end JAM
