import JAM.Work
import JAM.Accumulation

/-!
# Statistics (GP v0.8.0 §13, `sec:bookkeeping`)

The activity statistics π = (π_V, π_L, π_C, π_S) (eq. `activityspec`): per-validator records for
the current and the last epoch, per-core records and per-service records for the current block.

The validator update reads the reporters set G of eq. `guarantorsig`, the Ed25519 keys of the
validators whose signatures are in E_G's credentials. Computing it needs the guarantor
assignments M or M* (signatures are verified there, not here), so it is an argument.
-/

namespace JAM

/-- A validator's record (GP eq. `activityspec`): blocks b, tickets t, preimages p, preimage
    octets d, guarantees g and assurances a. -/
structure ValidatorRecord where
  blocks : Nat := 0
  tickets : Nat := 0
  preimages : Nat := 0
  preimagesSize : Nat := 0
  guarantees : Nat := 0
  assurances : Nat := 0
  deriving BEq, Repr, Inhabited

/-- A core's record (GP §13.2): DA load d, popularity p, imports i, extrinsic count x, extrinsic
    size z, exports e, bundle length l and refine gas u. -/
structure CoreRecord where
  daLoad : Nat := 0
  popularity : Nat := 0
  imports : Nat := 0
  xtCount : Nat := 0
  xtSize : Nat := 0
  exports : Nat := 0
  bundleLen : Nat := 0
  gasUsed : Nat := 0
  deriving BEq, Repr, Inhabited

/-- A service's record (GP §13.2): provision p = (count, size), refinement r = (count, gas),
    imports i, extrinsic count x, extrinsic size z, exports e, and accumulation
    a = (count, transfers, gas). -/
structure ServiceRecord where
  provided : Nat × Nat := (0, 0)
  refinement : Nat × Nat := (0, 0)
  imports : Nat := 0
  xtCount : Nat := 0
  xtSize : Nat := 0
  exports : Nat := 0
  accumulation : Nat × Nat × Nat := (0, 0, 0)
  deriving BEq, Repr, Inhabited

/-- What the validator update reads from the block. -/
structure ValidatorStatsInput where
  /-- τ, the prior timeslot. -/
  priorSlot : Nat
  /-- τ' = H_t. -/
  slot : Nat
  /-- H_i, the block author's index. -/
  author : Nat
  /-- |E_T|. -/
  ticketCount : Nat
  /-- E_P, the preimages extrinsic (s, **d**). -/
  preimages : List (Nat × List UInt8)
  /-- a_v for each a ∈ E_A. -/
  assurers : List Nat
  /-- (κ'_v)_e, the posterior active set's Ed25519 keys. -/
  activeEd : List (List UInt8)
  /-- G, the reporters set (GP eq. `guarantorsig`). -/
  reporters : OctetSet

/-- The validator update (π_V, π_L) ↦ (π_V', π_L') (GP §13.1). π_V^† credits assurances over
    N_{|κ|}, which is |π_V| (eq. `activityspec`). On an epoch change π_L' = π_V^† and the new
    accumulator starts at zero; its length is |κ'|, as |π_V'| = |κ'| requires. Then the author
    is credited its block, tickets and preimages, and each v with (κ'_v)_e ∈ G a guarantee.
    The paper writes κ'_v ∈ G; G holds Ed25519 keys, so we compare (κ'_v)_e. -/
def validatorStats (params : Params) (curr last : List ValidatorRecord) (i : ValidatorStatsInput) :
    List ValidatorRecord × List ValidatorRecord :=
  let dagger := curr.mapIdx fun v r =>
    { r with assurances := r.assurances + if i.assurers.contains v then 1 else 0 }
  let (ddagger, last') :=
    if i.priorSlot / params.epochLen = i.slot / params.epochLen then (dagger, last)
    else (List.replicate i.activeEd.length {}, dagger)
  let curr' := (List.range i.activeEd.length).map fun v =>
    let r := ddagger.getD v {}
    let a := v = i.author
    { r with
      blocks := r.blocks + if a then 1 else 0
      tickets := r.tickets + if a then i.ticketCount else 0
      preimages := r.preimages + if a then i.preimages.length else 0
      preimagesSize := r.preimagesSize + if a then (i.preimages.map (·.2.length)).sum else 0
      guarantees := r.guarantees + if i.reporters.contains (i.activeEd.getD v []) then 1 else 0 }
  (curr', last')

/-- π_C' (GP §13.2) from the incoming reports **I** (eq. `incomingworkreports`), the newly
    available reports **R** (eq. `availableworkreports`) and the assurances' bitfields a_f. -/
def coreStats (params : Params) (incoming available : List WorkReport) (bitfields : List (List Bool)) :
    List CoreRecord :=
  (List.range params.coreCount).map fun c =>
    let ds := (incoming.filter (·.core == c)).flatMap (·.digests)
    { imports := (ds.map (·.importCount)).sum, xtCount := (ds.map (·.extrinsicCount)).sum,
      xtSize := (ds.map (·.extrinsicSize)).sum, exports := (ds.map (·.exportCount)).sum,
      gasUsed := (ds.map (·.gasUsed)).sum,
      -- L(c)
      bundleLen := ((incoming.filter (·.core == c)).map (·.spec.bundleLength)).sum,
      -- D(c): l + 𝖶_G ⌈n · 65/64⌉
      daLoad := ((available.filter (·.core == c)).map fun r =>
        r.spec.bundleLength + Constants.Csegmentsize * ((r.spec.segmentCount * 65 + 63) / 64)).sum,
      popularity := (bitfields.map fun f => if f.getD c false then 1 else 0).sum }

/-- π_S' (GP §13.2) for **s** = **s**^R ∪ **s**^P ∪ K(S), from the incoming reports **I**, the
    preimages extrinsic E_P and the accumulation statistics S. Services outside **s** have no
    record. In the provision sum ∑_{(s, **d**) ∈ E_P}, s is already bound by ∀ s ∈ **s**, so it
    ranges over the pairs for that service. -/
def serviceStats (incoming : List WorkReport) (preimages : List (Nat × List UInt8))
    (acc : List (Nat × AccStat)) : Std.ExtTreeMap Nat ServiceRecord :=
  let digests := incoming.flatMap (·.digests)
  let active := (digests.map (·.service) ++ preimages.map (·.1) ++ acc.map (·.1)).eraseDups
  Std.ExtTreeMap.ofList <| active.map fun s =>
    let ds := digests.filter (·.service == s)
    let ps := preimages.filter (·.1 == s)
    let r : ServiceRecord :=
      { provided := (ps.length, (ps.map fun p => p.2.length).sum),
        refinement := (ds.length, (ds.map (·.gasUsed)).sum),
        imports := (ds.map (·.importCount)).sum, xtCount := (ds.map (·.extrinsicCount)).sum,
        xtSize := (ds.map (·.extrinsicSize)).sum, exports := (ds.map (·.exportCount)).sum,
        accumulation := (acc.lookup s).getD (0, 0, 0) }
    (s, r)

end JAM
