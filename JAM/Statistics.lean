import JAM.Work
import JAM.Accumulation

/-!
# Statistics (GP v0.8.1 §13, `sec:bookkeeping`)

The activity statistics $\pi = (\pi_V, \pi_L, \pi_C, \pi_S)$ (eq. `activityspec`): per-validator records for
the current and the last epoch, per-core records and per-service records for the current block.

The validator update reads the reporters set $\mathbf{G}$ of eq. `guarantorsig`, the Ed25519 keys of the
validators whose signatures are in $\mathbf{E}_G$'s credentials. Computing it needs the guarantor
assignments $\mathbf{M}$ or $\mathbf{M}^{\ast}$ (signatures are verified there, not here), so it is
an argument.
-/

namespace JAM

/-- A validator's record (GP eq. `activityspec`): blocks $b$, tickets $t$, preimages $p$, preimage
    octets $d$, guarantees $g$ and assurances $a$. -/
structure ValidatorRecord where
  blocks : Nat := 0
  tickets : Nat := 0
  preimages : Nat := 0
  preimagesSize : Nat := 0
  guarantees : Nat := 0
  assurances : Nat := 0
  deriving BEq, Repr, Inhabited

/-- A core's record (GP §13.2): DA load $d$, popularity $p$, imports $i$, extrinsic count $x$,
    extrinsic size $z$, exports $e$, bundle length $l$ and refine gas $u$. -/
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

/-- A service's record (GP §13.2): provision $p = (\text{count}, \text{size})$, refinement
    $r = (\text{count}, \text{gas})$, imports $i$, extrinsic count $x$, extrinsic size $z$, exports
    $e$, and accumulation $a = (\text{count}, \text{transfers}, \text{gas})$. -/
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
  /-- $\tau$, the prior timeslot. -/
  priorSlot : Nat
  /-- $\tau' = \mathbf{H}_T$. -/
  slot : Nat
  /-- $\mathbf{H}_I$, the block author's index. -/
  author : Nat
  /-- $|\mathbf{E}_T|$. -/
  ticketCount : Nat
  /-- $\mathbf{E}_P$, the preimages extrinsic $(s, \mathbf{d})$. -/
  preimages : List (Nat × List UInt8)
  /-- $a_v$ for each $a \in \mathbf{E}_A$. -/
  assurers : List Nat
  /-- $(\kappa'_v)_e$, the posterior active set's Ed25519 keys. -/
  activeEd : List (List UInt8)
  /-- $\mathbf{G}$, the reporters set (GP eq. `guarantorsig`). -/
  reporters : OctetSet

/-- The validator update $(\pi_V, \pi_L) \mapsto (\pi'_V, \pi'_L)$ (GP §13.1). $\pi_V^\dagger$
    credits assurances over $\mathbb{N}_{|\kappa|}$, which is $|\pi_V|$ (eq. `activityspec`). On an
    epoch change $\pi'_L = \pi_V^\dagger$ and the new accumulator starts at zero; its length is
    $|\kappa'|$, as $|\pi'_V| = |\kappa'|$ requires. Then the author is credited its block, tickets,
    preimages and preimage octets $\sum_{\mathbf{p} \in \mathbf{E}_P} |\mathbf{p}_d|$, and each $v$
    with $(\kappa'_v)_e \in \mathbf{G}$ a guarantee. v0.8.1 writes both as the model reads them
    (GP #565; v0.8.0 wrote $\sum_{d \in \mathbf{E}_P} |d|$ and $\kappa'_v \in \mathbf{G}$). -/
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

/-- $\pi'_C$ (GP §13.2) from the incoming reports $\mathbf{I}$ (eq. `incomingworkreports`), the
    newly available reports $\mathbf{R}$ (eq. `availableworkreports`) and the assurances' bitfields
    $a_f$. -/
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

/-- $\pi'_S$ (GP v0.8.1 §13.2) for $\mathbf{s} = \mathbf{s}^R \cup \mathbf{s}^P \cup \mathcal{K}(\mathbf{S})$,
    from the incoming reports $\mathbf{I}$, the preimages extrinsic $\mathbf{E}_P$ and the
    accumulation statistics $\mathbf{S}$. Services outside $\mathbf{s}$ have no record. The
    provision is $\sum_{\mathbf{p} \in \mathbf{E}_P, \mathbf{p}_s = s} (1, |\mathbf{p}_d|)$ (v0.8.1
    states the filter on $s$, which v0.8.0 left implicit). -/
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
