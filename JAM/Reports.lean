import JAM.Fast.Blake2b
import JAM.Assurances
import JAM.History
import JAM.Shuffle
import JAM.Account

/-!
# Guarantor assignments and work-report guarantees (GP v0.8.1 §11.3–§11.5)

The guarantor assignments $\mathbf{M}$ and $\mathbf{M}^{\ast}$ (eq. `priorassignments`), the validity
conditions on the guarantees extrinsic $\mathbf{E}_G$ (eqs. `guaranteesextrinsic`–`reportcodesarecorrect`),
the reporters set $\mathbf{G}$ (eq. `guarantorsig`) and the posterior assignments $\rho'$ (§11.5),
from $\rho$ after assurances
(`JAM.assurances`).

Signatures are checked with `Crypto.edVerify`.

Two inputs of the paper are not in the state the transition reads, and are arguments:
* the set of work-package hashes already in the pipeline,
  $\bigcup_{x \in \beta_H} \mathcal{K}(x_p) \cup \bigcup_{x \in \xi} x \cup \mathbf{q} \cup \mathbf{a}$
  (§11.4.1), computed by `knownPackages`;
* the ancestor-set condition on lookup anchors ($h, h' \in \mathbf{A}$), which needs the last
  $\mathsf{L}$ headers.

The paper names no errors and gives no order between the conditions. The errors are the test
vectors' names; the order is described at `guarantees`.
-/

namespace JAM

/-- A validator's keys $k \in \mathbb{K}$ as the reports transition reads them: its Ed25519 key
    $k_e$. -/
abbrev EdKey := List UInt8

/-- $\Phi(\mathbf{k})$ (GP v0.8.1 eq. `blacklistfilter`): the keys of offenders in $\psi'_O$
    replaced by the null key $\mathbb{K}^{\emptyset}$ (eq. `nullvalkey`). Only the Ed25519 part is
    kept here: `nullEdKey` = [2, 0, …]. -/
def blacklist (offenders : OctetSet) (k : List EdKey) : List EdKey :=
  k.map fun e => if offenders.contains e then nullEdKey else e

-- Regression test (GP v0.8.1 #543): an offender's Ed25519 key becomes [2, 0, …], not zeros.
#guard blacklist (Std.ExtTreeSet.ofList [List.replicate 32 (7 : UInt8)])
    [List.replicate 32 7, List.replicate 32 1] = [2 :: List.replicate 31 0, List.replicate 32 1]

/-- $R(\mathbf{c}, n)$ (GP §11.3): each core index rotated by $n$, modulo $|\mathbf{c}|/3$. -/
def rotate (c : List Nat) (n : Nat) : List Nat :=
  c.map fun x => (x + n) % (c.length / 3)

/-- $P(v, e, t)$ (GP §11.3): the core of each of $v$ validators,
    $\mathcal{F}([\lfloor i/3 \rfloor \mid i \leftarrow \mathbb{N}_v], e)$ rotated by
    $\lfloor (t \bmod \mathsf{E}) / \mathsf{R} \rfloor$. -/
def permute (params : Params) (v : Nat) (e : Hash) (t : Nat) : List Nat :=
  rotate (Shuffle.shuffleHash ((List.range v).map (· / 3)) e)
    ((t % params.epochLen) / params.rotationPeriod)

/-- Guarantor assignments: a core per validator, and the validators' (filtered) keys. -/
structure Assignments where
  cores : List Nat
  keys : List EdKey

/-- What the guarantees transition reads besides $\rho$, $\mathbf{E}_G$ and the accounts. -/
structure ReportsInput where
  /-- $\tau' = \mathbf{H}_T$. -/
  slot : Nat
  /-- $(\kappa'_v)_e$. -/
  activeEd : List EdKey
  /-- $(\lambda'_v)_e$. -/
  previousEd : List EdKey
  /-- $\eta'_2$. -/
  entropy2 : Hash
  /-- $\eta'_3$. -/
  entropy3 : Hash
  /-- $\psi'_O$. -/
  offenders : OctetSet
  /-- $\beta_H^\dagger$, the recent blocks with the parent's state root corrected (GP eq.
      `correctlaststateroot`). Its reported packages are those of $\beta_H$. -/
  recent : List RecentBlock
  /-- $\alpha$, the authorizer pools. -/
  authPools : List (List (List UInt8))
  /-- The work-package hashes already in the pipeline (`knownPackages`). -/
  known : OctetSet
  /-- The ancestor-set condition on a lookup anchor (GP §11.4.1: $\exists h, h' \in \mathbf{A}$ with
      $h_T = x_t$, $\mathcal{H}(h) = x_l$, $h'_P = \mathcal{H}(h)$ and $h'_R = x_s$). -/
  lookupAnchorKnown : RefineContext → Bool

/-- $\mathbf{M} = (P(|\kappa'|, \eta'_2, \tau'), \Phi(\kappa'))$ (GP §11.3). -/
def assignments (params : Params) (i : ReportsInput) : Assignments :=
  { cores := permute params i.activeEd.length i.entropy2 i.slot,
    keys := blacklist i.offenders i.activeEd }

/-- $\mathbf{M}^{\ast}$ (GP eq. `priorassignments`): $\mathbf{M}$ under the previous rotation, with
    $(\kappa', \eta'_2)$ when $\tau' - \mathsf{R}$ is in the same epoch as $\tau'$, and
    $(\lambda', \eta'_3)$ otherwise. $\tau' - \mathsf{R}$ is truncated at 0. -/
def priorAssignments (params : Params) (i : ReportsInput) : Assignments :=
  let t := i.slot - params.rotationPeriod
  let (k, e) := if t / params.epochLen = i.slot / params.epochLen then (i.activeEd, i.entropy2)
    else (i.previousEd, i.entropy3)
  { cores := permute params k.length e t, keys := blacklist i.offenders k }

/-- The work-package hashes already in the pipeline (GP §11.4.1): those reported in $\beta_H$, those
    accumulated in $\xi$, those of the ready queue's reports ($\mathbf{q}$) and those of the prior
    assignments $\rho$ ($\mathbf{a}$). -/
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
  | refineLoadTooHigh
  | badExportsCount
  | bundleTooBig
  | authGasTooHigh
  deriving BEq, Repr

/-- The posterior of the guarantees transition: $\rho'$, the reporters $\mathbf{G}$, and the reported
    packages $\{ (r_s)_p \mapsto (r_s)_e \mid r \in \mathbf{I} \}$ that recent history records (GP §7). -/
structure ReportsOutput where
  assignments : AvailAssignments
  reporters : OctetSet
  reported : OctetDict

/-- $L(d_l)$ (GP eq. `limitworkreportsize`): the length of a successful output, 0 for an error. -/
def resultSize : WorkResult → Nat
  | .ok b => b.size
  | .err _ => 0

/-- The conditions on a work report alone (GP §11.1): $1 \leq |r_d| \leq \mathsf{I}$ (eq.
    `workreport`), $|r_l| + |(r_c)_p| \leq \mathsf{J}$ (eq. `limitreportdeps`) and
    $|r_t| + \sum L(d_l) \leq \mathsf{W}_R$ (eq. `limitworkreportsize`). -/
def checkReportShape (params : Params) (r : WorkReport) : Except ReportsError Unit := do
  unless 1 ≤ r.digests.length ∧ r.digests.length ≤ params.maxPackageItems do throw .missingWorkResults
  unless r.segmentRootLookup.size + r.context.prerequisites.size ≤ params.maxReportDeps do
    throw .tooManyDependencies
  unless r.authTrace.size + (r.digests.map (resultSize ·.result)).sum ≤ params.maxReportVarSize do
    throw .workReportTooBig

/-- The work-package limits on a work report (GP v0.8.1 eq. `reportrefineload`, #563): over the
    digests, $\sum u \leq \mathsf{G}_R$, $\sum i \leq \mathsf{W}_M$, $(r_s)_n = \sum e \leq \mathsf{W}_X$,
    $\sum x \leq \mathsf{T}$ and $\sum (z + i \cdot \mathsf{W}_F) \leq \mathsf{W}_I$; then
    $(r_s)_l \leq \mathsf{W}_B$ and $r_g \leq \mathsf{G}_I$. The paper names no errors and gives no
    order; the errors are the vectors' (davxy/jam-test-vectors after v0.8.0, errors 28–31):
    `badExportsCount` when the segment count is not the sum of the export counts,
    `refineLoadTooHigh` for any sum over its limit, `bundleTooBig` and `authGasTooHigh`. The rows
    are checked in the paper's order. $\mathsf{W}_B$ is `Constants.Cmaxbundlesize`, as `fetch` does
    not report it. -/
def checkReportLoad (params : Params) (r : WorkReport) : Except ReportsError Unit := do
  let ds := r.digests
  let sum (f : WorkDigest → Nat) := (ds.map f).sum
  unless sum (·.gasUsed) ≤ params.packageRefGas do throw .refineLoadTooHigh
  unless sum (·.importCount) ≤ params.maxPackageImports do throw .refineLoadTooHigh
  unless r.spec.segmentCount = sum (·.exportCount) do throw .badExportsCount
  unless sum (·.exportCount) ≤ params.maxPackageExports do throw .refineLoadTooHigh
  unless sum (·.extrinsicCount) ≤ params.maxPackageXts do throw .refineLoadTooHigh
  unless sum (fun d => d.extrinsicSize + d.importCount * Constants.Csegmentfootprint) ≤
      params.maxInputSize do throw .refineLoadTooHigh
  unless r.spec.bundleLength ≤ Constants.Cmaxbundlesize do throw .bundleTooBig
  unless r.authGasUsed ≤ params.packageAuthGas do throw .authGasTooHigh

/-- The conditions on one guarantee $(r, t, \mathbf{a})$ (GP eq. `guarantorsig` and §11.4): the core
    index below $\mathsf{C}$; $2 \leq |\mathbf{a}| \leq 3$ and ordered by validator index; $t$ no later
    than $\tau'$ and no earlier than the previous rotation; for each $(v, s)$: $v < |\mathbf{k}|$,
    $\mathbf{c}_v = r_c$, $r_c < |\kappa'|/3$, the key not nulled by $\Phi$, and
    $s \in \bar{\mathbb{V}}_{(\mathbf{k}_v)_e}\langle \mathsf{X}_G \frown \mathcal{H}(r) \rangle$.
    $(\mathbf{c}, \mathbf{k})$ is $\mathbf{M}$ when $t$ is in $\tau'$'s rotation and
    $\mathbf{M}^{\ast}$ otherwise. Returns the signers' keys. -/
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
    if k == nullEdKey then throw .bannedValidator
    unless crypto.edVerify k (Xguarantee ++ h) s.toList do throw .badSignature
    return k

/-- The anchor condition (GP §11.4.1): some $y \in \beta_H^\dagger$ has the anchor's header hash, state root,
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
    1. $\mathbf{E}_G$ ordered and unique by core (eq. `guaranteesextrinsic`);
    2. for each guarantee in turn: `checkGuarantee`, `checkReportShape`, the erasure-shard count
       $|\kappa'|$, the core free in $\rho$ (eq. `reportcoresareunused`), the authorizer in
       $\alpha[r_c]$, and each digest's service: present in $\delta$, $d_g \geq$ its minimum gas,
       then $\sum d_g \leq \mathsf{G}_A$, then the
       work-package limits (`checkReportLoad`, GP v0.8.1 eq. `reportrefineload`);
    3. no two reports of one package;
    4. for each report: its anchor (`checkAnchor`), the lookup anchor's age
       ($x_t \geq \tau' - \mathsf{L}$) and
       ancestry, the package not already known, the segment-root lookup within the extrinsic's
       and $\beta$'s reported packages, the prerequisites present, and each digest's code hash.

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
    checkReportLoad params r
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
