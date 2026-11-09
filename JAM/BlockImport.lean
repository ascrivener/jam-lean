import JAM.State
import JAM.Reports
import JAM.Assurances
import JAM.Preimages
import JAM.Authorization

/-!
# The block-level state transition Υ(σ, B) = σ' (GP v0.8.0 §4, §5)

Υ is the composition of the section-level transitions along the dependency graph of GP eq.
`transitionfunctioncomposition`:

1. τ' = H_T (eq. `timeslotindex`) and β_H^† (eq. `betadagger`).
2. ψ' and ρ^† from 𝔼_D and ψ, ρ (§10).
3. γ', η', κ', λ' from H, τ, 𝔼_T, γ, ι, η and ψ'_O (§6).
4. ρ^‡ and the newly available reports **R** from 𝔼_A and ρ^† (§11.2).
5. ρ' from 𝔼_G, ρ^‡, κ', λ', η', ψ'_O and τ' (§11.3–§11.5).
6. ω', ξ', δ^‡, χ', ι', φ', θ' and the accumulation statistics from **R** (§12).
7. β' from H, 𝔼_G, β_H^† and θ' (§7).
8. δ' from 𝔼_P, δ^‡ and τ' (§12.4); the preimages are checked against the prior δ.
9. α' from H, 𝔼_G, φ' and α (§8).
10. π' from 𝔼_G, 𝔼_P, 𝔼_A, 𝔼_T, τ, κ', π, H and the accumulation statistics (§13).

The block is valid only if every transition accepts its extrinsic and the header satisfies §5:
H_P is the hash of the parent header, H_R = M_σ(σ), H_X commits to the extrinsic
(eq. `extrinsichash`), H_I indexes κ', the markers H_E, H_W and H_O are those the transitions
produce, and the seal and entropy source are valid (§6.4, `JAM.sealValid`). The wall-clock bound
H_T·𝖯 ≤ 𝒯 is not checked: Υ has no clock.

Cryptography enters through `JAM.Crypto`. The ancestor set 𝒜 of §11.4.1 is not part of σ; the
caller supplies the headers it retains (`Chain`).
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
  deriving BEq, Repr

/-- The headers an importer retains besides σ: the ancestors of the block being imported, oldest
    first, ending with its parent. They give H_P's check and the ancestor set 𝒜 of §11.4.1. -/
structure Chain where
  ancestors : List Header

/-- ℋ on octet lists (Blake2b-256). -/
def hashL (m : List UInt8) : List UInt8 := (Blake2b.hash256 ⟨m.toArray⟩).toList

/-- ℋ(ℰ(H)), a header's hash. -/
def Header.hash (h : Header) : List UInt8 := hashL h.encode

open Codec in
/-- H_X = ℋ(ℰ(ℋ#(**a**))) with **a** = [ℰ_T(𝔼_T), **p**, **g**, ℰ_A(𝔼_A), ℰ_D(𝔼_D)],
    **p** = ℰ(↕[(ℰ_4(s), ℋ(**d**)) | (s, **d**) ← 𝔼_P]) and
    **g** = ℰ(↕[(ℋ(r), ℰ_4(t), ↕a) | (r, t, a) ← 𝔼_G]) (GP eq. `extrinsichash`). -/
def Extrinsic.hash (x : Extrinsic) : List UInt8 :=
  let p := varSeq (fun (q : Preimage) => fixed 4 q.requester ++ hashL q.blob.toList) x.preimages
  let g := varSeq (fun (g : Guarantee) => hashL g.report.encode ++ fixed 4 g.slot ++
    varSeq (fun (v, s) => fixed 2 v ++ blob s) g.credential) x.guarantees
  let a := [encodeTickets x.tickets, p, g, encodeAssurances x.assurances, x.disputes.encode]
  hashL (a.flatMap hashL)

/-- The ancestor-set condition of §11.4.1 for a refinement context x: some h, h' ∈ 𝒜 with
    h_T = x_t, ℋ(h) = x_l, h'_P = ℋ(h) and h'_R = x_s. 𝒜 is the retained headers together with
    the block's own header, so that the parent can be a lookup anchor. -/
def lookupAnchorKnown (anc : List Header) (x : RefineContext) : Bool :=
  anc.any fun h =>
    h.slot == x.lookupAnchorSlot && h.hash == x.lookupAnchorHash.toList &&
      anc.any fun h' => h'.parent.toList == h.hash && h'.priorStateRoot == x.anchorStateRoot

/-- The intermediate values of Υ that are not part of σ', for inspection. -/
structure ImportTrace where
  /-- **R**, the newly available reports. -/
  available : List WorkReport
  /-- The accumulation output root. -/
  accRoot : List UInt8

/-- Υ(σ, B) (GP eq. `transitionfunctioncomposition`), with the block's validity conditions. -/
def importBlock (params : Params) (c : Crypto) (chain : Chain) (σ : State) (B : Block) :
    Except BlockError (State × ImportTrace) := do
  let H := B.header
  let X := B.extrinsic
  let hdr (ok : Bool) (msg : String) : Except BlockError Unit :=
    if ok then pure () else throw (.header msg)
  -- §5: the parent, the prior state root and the extrinsic hash.
  match chain.ancestors.getLast? with
  | some p => hdr (H.parent.toList == p.hash) "H_P is not the parent header's hash"
  | none => pure ()
  hdr (H.priorStateRoot.toList == σ.root) "H_R ≠ M_σ(σ)"
  hdr (H.extrinsicHash.toList == X.hash) "H_X does not commit to the extrinsic"
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
  let acc := accumulate params accPre slot avail
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
