import JAM.Fast.Blake2b
import JAM.State
import JAM.Reports
import JAM.Assurances
import JAM.Preimages
import JAM.Authorization

/-!
# The block-level state transition $\Upsilon(\sigma, B) = \sigma'$ (GP v0.8.1 §4, §5)

$\Upsilon$ is the composition of the section-level transitions along the dependency graph of GP eq.
`transitionfunctioncomposition`:

1. $\tau' = \mathbf{H}_T$ (eq. `timeslotindex`) and $\beta_H^\dagger$ (eq. `betadagger`).
2. $\psi'$ and $\availassignmentspostjudgment$ from $\mathbf{E}_D$ and $\psi$, $\rho$ (§10).
3. $\gamma'$, $\eta'$, $\kappa'$, $\lambda'$ from $\mathbf{H}$, $\tau$, $\mathbf{E}_T$, $\gamma$,
   $\iota$, $\eta$ and $\psi'_O$ (§6).
4. $\availassignmentspostassurances$ and the newly available reports $\mathbf{R}$ from $\mathbf{E}_A$ and $\availassignmentspostjudgment$
   (§11.2).
5. $\rho'$ from $\mathbf{E}_G$, $\availassignmentspostassurances$, $\kappa'$, $\lambda'$, $\eta'$, $\psi'_O$ and $\tau'$
   (§11.3–§11.5).
6. $\omega'$, $\xi'$, $\delta^\ddagger$, $\chi'$, $\iota'$, $\phi'$, $\theta'$ and the accumulation
   statistics from $\mathbf{R}$ (§12).
7. $\beta'$ from $\mathbf{H}$, $\mathbf{E}_G$, $\beta_H^\dagger$ and $\theta'$ (§7).
8. $\delta'$ from $\mathbf{E}_P$, $\delta^\ddagger$ and $\tau'$ (§12.4); the preimages are checked
   against the prior $\delta$.
9. $\alpha'$ from $\mathbf{H}$, $\mathbf{E}_G$, $\phi'$ and $\alpha$ (§8).
10. $\pi'$ from $\mathbf{E}_G$, $\mathbf{E}_P$, $\mathbf{E}_A$, $\mathbf{E}_T$, $\tau$, $\kappa'$,
    $\pi$, $\mathbf{H}$ and the accumulation statistics (§13).

The block is valid only if every transition accepts its extrinsic and the header satisfies §5:
$\mathbf{H}_P$ is the hash of the parent header, $\mathbf{H}_R = \mathcal{M}_\sigma(\sigma)$,
$\mathbf{H}_X$ commits to the extrinsic (eq. `extrinsichash`), $\mathbf{H}_I$ indexes $\kappa'$, the
markers $\mathbf{H}_E$, $\mathbf{H}_W$ and $\mathbf{H}_O$ are those the transitions produce, and the
seal and entropy source are valid (§6.4, `JAM.sealValid`). The wall-clock bound
$\mathbf{H}_T \cdot \mathsf{P} \le \mathcal{T}$ is not checked: $\Upsilon$ has no clock.

Cryptography enters through `JAM.Crypto`. The ancestor set $\mathbf{A}$ of §11.4.1 is not part of
$\sigma$; the caller supplies the headers it retains (`Chain`).
-/

namespace JAM

/-- Why a block is invalid. -/
inductive BlockError where
  /-- A header condition of §5 fails; the message names it. -/
  | header (msg : String)
  | disputes (e : DisputesError)
  | safrole (e : SafroleError)
  | assurances (e : AssurancesError)
  | reports (e : ReportsError)
  | preimages (e : PreimageError)
  /-- Accumulation makes the block invalid (GP v0.8.1 §12.2): two services created the same new
      service index in one round. -/
  | accumulation (e : AccumulationError)
  deriving BEq, Repr

/-- The headers an importer retains besides $\sigma$: the ancestors of the block being imported,
    oldest first, ending with its parent. They give $\mathbf{H}_P$'s check and the ancestor set
    $\mathbf{A}$ of §11.4.1. -/
structure Chain where
  ancestors : List Header

/-- $\mathcal{H}$ on octet lists (Blake2b-256). -/
def hashL (m : List UInt8) : List UInt8 := (Blake2b.hash256 ⟨m.toArray⟩).toList

/-- $\mathcal{H}(\mathcal{E}(\mathbf{H}))$, a header's hash. -/
def Header.hash (h : Header) : List UInt8 := hashL h.encode

open Codec in
/-- $\mathbf{a} = [\mathcal{E}_T(\mathbf{E}_T), \mathbf{p}, \mathbf{g}, \mathcal{E}_A(\mathbf{E}_A),
    \mathcal{E}_D(\mathbf{E}_D)]$ of GP eq. `extrinsichash`, with
    $\mathbf{p} = \mathcal{E}(\updownarrow[(\mathcal{E}_4(s), \mathcal{H}(\mathbf{d})) \mid
    (s, \mathbf{d}) \leftarrow \mathbf{E}_P])$ and
    $\mathbf{g} = \mathcal{E}(\updownarrow[(\mathcal{H}(\mathbf{r}), \mathcal{E}_4(t), \encodecredentials{a}) \mid
    (\mathbf{r}, t, a) \leftarrow \mathbf{E}_G])$, where
    $\encodecredentials{a} = \mathcal{E}(\updownarrow[(\mathcal{E}_2(v), s) \mid (v, s) \leftarrow a])$ is the
    credential encoding of Appendix C (GP v0.8.1 eq. 5.7; v0.8.0 wrote $\updownarrow a$ there, and
    #560 introduced $\mathcal{E}_C$; the model already encoded $v$ with $\mathcal{E}_2$). -/
def Extrinsic.hashParts (x : Extrinsic) : List (List UInt8) :=
  let p := varSeq (fun (q : Preimage) => fixed 4 q.requester ++ hashL q.blob.toList) x.preimages
  let g := varSeq (fun (g : Guarantee) => hashL g.report.encode ++ fixed 4 g.slot ++
    encodeCredential g.credential) x.guarantees
  [encodeTickets x.tickets, p, g, encodeAssurances x.assurances, x.disputes.encode]

/-- $\mathbf{H}_X = \mathcal{H}(\mathcal{E}(\mathcal{H}^\#(\mathbf{a})))$ (GP v0.8.1 eq.
    `extrinsichash`), $\mathbf{a}$ = `Extrinsic.hashParts`. -/
def Extrinsic.hash (x : Extrinsic) : List UInt8 :=
  hashL (x.hashParts.flatMap hashL)

/-- The ancestor-set condition of §11.4.1 (GP v0.8.1 eq. 11.38) for a refinement context $x$: some
    $h, h' \in \mathbf{A}$ with $h_T = x_{\text{lookupanchortime}}$,
    $\mathcal{H}(h) = x_{\text{lookupanchor}}$, $h'_P = \mathcal{H}(h)$ and
    $h'_R = x_{\text{lookupanchorpoststate}}$: the lookup anchor's posterior state root, the prior
    state root of its child (not the anchor's $x_{\text{stateroot}}$). $\mathbf{A}$ is the retained
    headers together with the block's own header, so that the parent can be a lookup anchor. -/
def lookupAnchorKnown (anc : List Header) (x : RefineContext) : Bool :=
  anc.any fun h =>
    h.slot == x.lookupAnchorSlot && h.hash == x.lookupAnchorHash.toList &&
      anc.any fun h' => h'.parent.toList == h.hash && h'.priorStateRoot == x.lookupAnchorStateRoot

/-- The intermediate values of $\Upsilon$ that are not part of $\sigma'$, for inspection. -/
structure ImportTrace where
  /-- $\mathbf{R}$, the newly available reports. -/
  available : List WorkReport
  /-- The accumulation output root. -/
  accRoot : List UInt8

/-- $\Upsilon(\sigma, B)$ (GP eq. `transitionfunctioncomposition`), with the block's validity conditions. -/
def importBlock (params : Params) (c : Crypto) (chain : Chain) (σ : State) (B : Block) :
    Except BlockError (State × ImportTrace) := do
  let H := B.header
  let X := B.extrinsic
  let xh := X.hash
  let hdr (ok : Bool) (msg : String) : Except BlockError Unit :=
    if ok then pure () else throw (.header msg)
  -- §5: the parent, the prior state root and the extrinsic hash.
  match chain.ancestors.getLast? with
  | some p => hdr (H.parent.toList == p.hash) "H_P is not the parent header's hash"
  | none => pure ()
  hdr (H.priorStateRoot.toList == σ.root) "H_R ≠ M_σ(σ)"
  hdr (H.extrinsicHash.toList == xh) "H_X does not commit to the extrinsic"
  -- τ' = H_T; τ < H_T is Safrole's `badSlot`.
  let slot := H.slot
  -- β_H^† (eq. `betadagger`).
  let recentDagger := Recent.withParentRoot σ.recent.history H.priorStateRoot.toList
  -- §10: ψ' and ρ^†.
  let dIn : DisputesInput :=
    { slot := σ.tau, activeEd := σ.active.map ValidatorKey.ed,
      previousEd := σ.prev.map ValidatorKey.ed }
  let dOut ← (disputesTransition params c dIn σ.disputes σ.avail X.disputes).mapError .disputes
  let psi' := dOut.state
  hdr (H.offendersMark.map (·.toList) == dOut.offendersMark) "H_O is not the offenders marker"
  -- §6: Safrole, with Y(H_V) as the entropy contribution.
  let sIn : SafroleInput :=
    { slot, entropy := c.bsOut H.vrfSig.toList, tickets := X.tickets,
      offenders := psi'.offenders.toList }
  let (saf', sOut) ← (safrole params c σ.safrole sIn).mapError .safrole
  hdr (match H.epochMark, sOut.epochMark with
       | none, none => true
       | some a, some b => a.entropy == b.entropy && a.ticketsEntropy == b.ticketsEntropy &&
           a.validators.map (fun (x, y) => (x.toList, y.toList)) ==
             b.validators.map (fun (x, y) => (x.toList, y.toList))
       | _, _ => false) "H_E is not the epoch marker"
  hdr (match H.winnersMark, sOut.ticketsMark with
       | none, none => true
       | some a, some b => a.map (fun t => (t.id.toList, t.attempt)) ==
           b.map (fun t => (t.id.toList, t.attempt))
       | _, _ => false) "H_W is not the winning-tickets marker"
  -- §5, §6.4: the author and the seal.
  hdr (H.authorIndex < saf'.active.length) "H_I is not an index of κ'"
  let author := (saf'.active.getD H.authorIndex ValidatorKey.null).bs
  hdr (sealValid params c saf'.sealKeys (saf'.eta.getD 3 []) author H)
    "the seal or the entropy source is invalid"
  -- §11.2: assurances.
  let aIn : AssurancesInput :=
    { slot, parent := H.parent, activeEd := σ.active.map ValidatorKey.ed,
      postActiveCount := saf'.active.length }
  let (avail, rhoDD) ← (assurances params c aIn dOut.assignments X.assurances).mapError .assurances
  -- §11.3–§11.5: guarantees.
  let anc := chain.ancestors ++ [H]
  let rIn : ReportsInput :=
    { slot, activeEd := saf'.active.map ValidatorKey.ed, previousEd := saf'.prev.map ValidatorKey.ed,
      entropy2 := ⟨(saf'.eta.getD 2 []).toArray⟩, entropy3 := ⟨(saf'.eta.getD 3 []).toArray⟩,
      offenders := psi'.offenders, recent := recentDagger, authPools := σ.authPools,
      known := knownPackages σ.recent.history σ.accumulated (σ.ready.flatten.map (·.1)) σ.avail,
      lookupAnchorKnown := lookupAnchorKnown anc }
  let gOut ← (guarantees params c rIn σ.accounts rhoDD X.guarantees).mapError .reports
  -- §12: accumulation of **R**.
  let accPre : AccState :=
    { slot := σ.tau, entropy := saf'.eta.getD 0 [], ready := σ.ready,
      accumulated := σ.accumulated, pstate := σ.partialState }
  let acc ← (accumulate params accPre slot avail).mapError .accumulation
  let ps := acc.state.pstate
  -- §7: recent history.
  let recent' := recentHistory params { σ.recent with history := σ.recent.history }
    { headerHash := H.hash, parentStateRoot := H.priorStateRoot.toList, accRoot := acc.root,
      slot, reported := gOut.reported.toList }
  -- §12.4: preimages.
  let xp := X.preimages.map fun p => (p.requester, p.blob.toList)
  let accounts' ← (preimages σ.accounts ps.accounts xp slot).mapError .preimages
  -- §8: authorizations.
  let authPools' := authorizations params σ.authPools ps.authQueue slot
    (X.guarantees.map fun g => (g.report.core, g.report.authorizerHash.toList))
  -- §13: statistics.
  let incoming := X.guarantees.map (·.report)
  let (valStats', valStatsLast') := validatorStats params σ.valStats σ.valStatsLast
    { priorSlot := σ.tau, slot, author := H.authorIndex, ticketCount := X.tickets.length,
      preimages := xp, assurers := X.assurances.map (·.assurer),
      activeEd := saf'.active.map ValidatorKey.ed, reporters := gOut.reporters }
  let σ' : State :=
    { authPools := authPools', authQueue := ps.authQueue, recent := recent',
      lastAccOut := acc.outputs, pending := saf'.pending, ringRoot := saf'.ringRoot,
      sealKeys := saf'.sealKeys, accumulator := saf'.accumulator, accounts := accounts',
      eta := saf'.eta, staging := ps.staging, active := saf'.active, prev := saf'.prev,
      avail := gOut.assignments, tau := slot, manager := ps.manager, assigners := ps.assigners,
      delegator := ps.delegator, registrar := ps.registrar, alwaysAcc := ps.alwaysAcc,
      disputes := psi', valStats := valStats', valStatsLast := valStatsLast',
      coreStats := coreStats params incoming avail (X.assurances.map (·.bitfield)),
      serviceStats := serviceStats incoming xp acc.stats,
      ready := acc.state.ready, accumulated := acc.state.accumulated }
  return (σ', { available := avail, accRoot := acc.root })

end JAM
