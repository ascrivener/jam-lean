import JAM.Assurances
import JAM.History
import JAM.Shuffle
import JAM.Account

/-!
# Guarantor assignments and work-report guarantees (GP v0.8.0 §11.3–§11.5)

The guarantor assignments M and M* (eq. `priorassignments`), the validity conditions on the
guarantees extrinsic 𝔼_G (eqs. `guaranteesextrinsic`–`reportcodesarecorrect`), the reporters set
G (eq. `guarantorsig`) and the posterior assignments ρ' (§11.5), from ρ after assurances
(`JAM.assurances`).

Signatures are checked with `Crypto.edVerify`.

Two inputs of the paper are not in the state the transition reads, and are arguments:
* the set of work-package hashes already in the pipeline,
  ⋃_{x ∈ β_H} K(x_p) ∪ ⋃_{x ∈ ξ} x ∪ **q** ∪ **a** (§11.4.1), computed by `knownPackages`;
* the ancestor-set condition on lookup anchors (h, h' ∈ A), which needs the last 𝖫 headers.

The paper names no errors and gives no order between the conditions. The errors are the test
vectors' names; the order is described at `guarantees`.
-/

namespace JAM

/-- A validator's keys k ∈ 𝕂 as the reports transition reads them: its Ed25519 key k_e. -/
abbrev EdKey := List UInt8

/-- Φ(**k**) (GP eq. `blacklistfilter`): the keys of offenders in ψ'_O replaced by the null key. Only
    the Ed25519 part is kept here; a null key is 32 zero octets. -/
def blacklist (offenders : OctetSet) (k : List EdKey) : List EdKey :=
  k.map fun e => if offenders.contains e then List.replicate 32 0 else e

/-- R(**c**, n) (GP §11.3): each core index rotated by n, modulo |**c**|/3. -/
def rotate (c : List Nat) (n : Nat) : List Nat :=
  c.map fun x => (x + n) % (c.length / 3)

/-- P(v, e, t) (GP §11.3): the core of each of v validators, ℱ([⌊i/3⌋ | i ← ℕ_v], e) rotated by
    ⌊(t mod 𝖤)/𝖱⌋. -/
def permute (params : Params) (v : Nat) (e : Hash) (t : Nat) : List Nat :=
  rotate (Shuffle.shuffleHash ((List.range v).map (· / 3)) e)
    ((t % params.epochLen) / params.rotationPeriod)

/-- Guarantor assignments: a core per validator, and the validators' (filtered) keys. -/
structure Assignments where
  cores : List Nat
  keys : List EdKey

/-- What the guarantees transition reads besides ρ, 𝔼_G and the accounts. -/
structure ReportsInput where
  /-- τ' = H_T. -/
  slot : Nat
  /-- (κ'_v)_e. -/
  activeEd : List EdKey
  /-- (λ'_v)_e. -/
  previousEd : List EdKey
  /-- η'_2. -/
  entropy2 : Hash
  /-- η'_3. -/
  entropy3 : Hash
  /-- ψ'_O. -/
  offenders : OctetSet
  /-- β_H^†, the recent blocks with the parent's state root corrected (GP eq.
      `correctlaststateroot`). Its reported packages are those of β_H. -/
  recent : List RecentBlock
  /-- α, the authorizer pools. -/
  authPools : List (List (List UInt8))
  /-- The work-package hashes already in the pipeline (`knownPackages`). -/
  known : OctetSet
  /-- The ancestor-set condition on a lookup anchor (GP §11.4.1: ∃ h, h' ∈ A with h_T = x_t,
      ℋ(h) = x_l, h'_P = ℋ(h) and h'_R = x_s). -/
  lookupAnchorKnown : RefineContext → Bool

/-- M = (P(|κ'|, η'_2, τ'), Φ(κ')) (GP §11.3). -/
def assignments (params : Params) (i : ReportsInput) : Assignments :=
  { cores := permute params i.activeEd.length i.entropy2 i.slot,
    keys := blacklist i.offenders i.activeEd }

/-- M* (GP eq. `priorassignments`): M under the previous rotation, with (κ', η'_2) when τ' − 𝖱 is
    in the same epoch as τ', and (λ', η'_3) otherwise. τ' − 𝖱 is truncated at 0. -/
def priorAssignments (params : Params) (i : ReportsInput) : Assignments :=
  let t := i.slot - params.rotationPeriod
  let (k, e) := if t / params.epochLen = i.slot / params.epochLen then (i.activeEd, i.entropy2)
    else (i.previousEd, i.entropy3)
  { cores := permute params k.length e t, keys := blacklist i.offenders k }

/-- The work-package hashes already in the pipeline (GP §11.4.1): those reported in β_H, those
    accumulated in ξ, those of the ready queue's reports (**q**) and those of the prior assignments
    ρ (**a**). -/
def knownPackages (recent : List RecentBlock) (accumulated : List OctetSet)
    (ready : List WorkReport) (ρ : AvailAssignments) : OctetSet :=
  let hs := recent.flatMap (·.reported.keys) ++ accumulated.flatMap (·.toList) ++
    ready.map (·.spec.packageHash.toList) ++
    ρ.filterMap (·.map (·.guarantee.report.spec.packageHash.toList))
  Std.ExtTreeSet.ofList hs

/-- Why a guarantees extrinsic is invalid. The paper names no errors; these are the vectors'. -/
inductive ReportsError where
  | badCoreIndex
  | futureReportSlot
  | reportEpochBeforeLast
  | insufficientGuarantees
  | outOfOrderGuarantee
  | notSortedOrUniqueGuarantors
  | wrongAssignment
  | coreEngaged
  | anchorNotRecent
  | badServiceId
  | badCodeHash
  | dependencyMissing
  | duplicatePackage
  | badStateRoot
  | badBeefyMmrRoot
  | coreUnauthorized
  | badValidatorIndex
  | workReportGasTooHigh
  | serviceItemGasTooLow
  | tooManyDependencies
  | segmentRootLookupInvalid
  | badSignature
  | workReportTooBig
  | bannedValidator
  | lookupAnchorNotRecent
  | missingWorkResults
  | badAnchorSlot
  | badErasureShards
  deriving BEq, Repr

/-- The posterior of the guarantees transition: ρ', the reporters G, and the reported packages
    {(r_s)_p ↦ (r_s)_e | r ∈ **I**} that recent history records (GP §7). -/
structure ReportsOutput where
  assignments : AvailAssignments
  reporters : OctetSet
  reported : OctetDict

/-- L(d_l) (GP eq. `limitworkreportsize`): the length of a successful output, 0 for an error. -/
def resultSize : WorkResult → Nat
  | .ok b => b.size
  | .err _ => 0

/-- The conditions on a work report alone (GP §11.1): 1 ≤ |r_d| ≤ 𝖨 (eq. `workreport`),
    |r_l| + |(r_c)_p| ≤ 𝖩 (eq. `limitreportdeps`) and |r_t| + ∑ L(d_l) ≤ 𝖶_R
    (eq. `limitworkreportsize`). -/
def checkReportShape (params : Params) (r : WorkReport) : Except ReportsError Unit := do
  unless 1 ≤ r.digests.length ∧ r.digests.length ≤ params.maxPackageItems do throw .missingWorkResults
  unless r.segmentRootLookup.size + r.context.prerequisites.size ≤ params.maxReportDeps do
    throw .tooManyDependencies
  unless r.authTrace.size + (r.digests.map (resultSize ·.result)).sum ≤ params.maxReportVarSize do
    throw .workReportTooBig

/-- The conditions on one guarantee (r, t, **a**) (GP eq. `guarantorsig` and §11.4): the core index
    below 𝖢; 2 ≤ |**a**| ≤ 3 and ordered by validator index; t no later than τ' and no earlier
    than the previous rotation; for each (v, s): v < |**k**|, **c**_v = r_c, r_c < |κ'|/3, the key
    not nulled by Φ, and s ∈ 𝕍̄_{(**k**_v)_e}⟨X_G ⌢ ℋ(r)⟩. (**c**, **k**) is M when t is in τ''s
    rotation and M* otherwise. Returns the signers' keys. -/
def checkGuarantee (params : Params) (crypto : Crypto) (i : ReportsInput) (g : Guarantee) :
    Except ReportsError (List EdKey) := do
  let r := g.report
  unless r.core < params.coreCount do throw .badCoreIndex
  unless 2 ≤ g.credential.length ∧ g.credential.length ≤ 3 do throw .insufficientGuarantees
  unless orderedUniqByNat (·.1) g.credential do throw .notSortedOrUniqueGuarantors
  if g.slot > i.slot then throw .futureReportSlot
  unless params.rotationPeriod * (i.slot / params.rotationPeriod - 1) ≤ g.slot do
    throw .reportEpochBeforeLast
  let m := if i.slot / params.rotationPeriod = g.slot / params.rotationPeriod
    then assignments params i else priorAssignments params i
  let h := (Blake2b.hash256 ⟨r.encode.toArray⟩).toList
  g.credential.mapM fun (v, s) => do
    unless v < m.keys.length do throw .badValidatorIndex
    unless m.cores.getD v 0 = r.core do throw .wrongAssignment
    unless r.core < i.activeEd.length / 3 do throw .badCoreIndex
    let k := m.keys.getD v []
    if k == List.replicate 32 0 then throw .bannedValidator
    unless crypto.edVerify k (Xguarantee ++ h) s.toList do throw .badSignature
    return k

/-- The anchor condition (GP §11.4.1): some y ∈ β_H^† has the anchor's header hash, state root,
    accumulation-output super-peak and timeslot. A context whose anchor hash is in no entry is
    not recent; one whose hash is found but whose other fields differ names the first that does. -/
def checkAnchor (recent : List RecentBlock) (x : RefineContext) : Except ReportsError Unit := do
  let ys := recent.filter (·.headerHash == x.anchorHash.toList)
  if ys.isEmpty then throw .anchorNotRecent
  unless ys.any (·.stateRoot == x.anchorStateRoot.toList) do throw .badStateRoot
  unless ys.any (·.accRoot == x.anchorAccOutLog.toList) do throw .badBeefyMmrRoot
  unless ys.any fun y => y.stateRoot == x.anchorStateRoot.toList &&
      y.accRoot == x.anchorAccOutLog.toList && y.slot == x.anchorSlot do throw .badAnchorSlot

/-- The guarantees transition (GP §11.4–§11.5). Conditions are checked in this order:
    1. 𝔼_G ordered and unique by core (eq. `guaranteesextrinsic`);
    2. for each guarantee in turn: `checkGuarantee`, `checkReportShape`, the erasure-shard count
       |κ'|, the core free in ρ (eq. `reportcoresareunused`), the authorizer in α[r_c], and each
       digest's service: present in δ, d_g ≥ its minimum gas, then ∑ d_g ≤ 𝖦_A;
    3. no two reports of one package;
    4. for each report: its anchor (`checkAnchor`), the lookup anchor's age (x_t ≥ τ' − 𝖫) and
       ancestry, the package not already known, the segment-root lookup within the extrinsic's
       and β's reported packages, the prerequisites present, and each digest's code hash.

    The segment-root lookup is checked before the prerequisites, so a lookup entry missing from
    both is reported as an invalid lookup rather than a missing dependency. -/
def guarantees (params : Params) (crypto : Crypto) (i : ReportsInput) (δ : Accounts)
    (ρ : AvailAssignments) (xs : List Guarantee) : Except ReportsError ReportsOutput := do
  unless orderedUniqByNat (·.report.core) xs do throw .outOfOrderGuarantee
  let mut reporters : OctetSet := ∅
  for g in xs do
    let r := g.report
    let ks ← checkGuarantee params crypto i g
    reporters := ks.foldl (·.insert ·) reporters
    checkReportShape params r
    unless r.spec.erasureShards = i.activeEd.length do throw .badErasureShards
    unless (ρ.getD r.core none).isNone do throw .coreEngaged
    unless (i.authPools.getD r.core []).contains r.authorizerHash.toList do throw .coreUnauthorized
    for d in r.digests do
      let some a := δ.get? d.service | throw .badServiceId
      unless d.gasLimit ≥ a.minAccGas do throw .serviceItemGasTooLow
    unless (r.digests.map (·.gasLimit)).sum ≤ params.reportAccGas do throw .workReportGasTooHigh
  let reports := xs.map (·.report)
  let p : OctetDict := Std.ExtTreeMap.ofList
    (reports.map fun r => (r.spec.packageHash.toList, r.spec.segmentRoot.toList))
  unless p.size = reports.length do throw .duplicatePackage
  let recentReported := i.recent.flatMap (·.reported.toList)
  for r in reports do
    checkAnchor i.recent r.context
    unless r.context.lookupAnchorSlot + params.maxLookupAnchorAge ≥ i.slot do
      throw .lookupAnchorNotRecent
    unless i.lookupAnchorKnown r.context do throw .lookupAnchorNotRecent
    if i.known.contains r.spec.packageHash.toList then throw .duplicatePackage
    for e in r.segmentRootLookup.toList do
      unless p.get? e.1 == some e.2 || recentReported.contains e do throw .segmentRootLookupInvalid
    for q in r.context.prerequisites.toList do
      unless p.contains q || recentReported.any (·.1 == q) do throw .dependencyMissing
    for d in r.digests do
      unless (δ.get? d.service).map (·.codeHash) == some d.codeHash.toList do throw .badCodeHash
  let ρ' := ρ.mapIdx fun c a =>
    match xs.find? (·.report.core == c) with
    | some g => some { guarantee := g, time := i.slot }
    | none => a
  return { assignments := ρ', reporters, reported := p }

end JAM
