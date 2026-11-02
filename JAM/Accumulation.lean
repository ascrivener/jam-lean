import JAM.Accumulate
import JAM.Merkle

/-!
# Accumulation (GP v0.8.0 §12, `sec:accumulation`)

The accumulation state transition: the queue functions E, Q and P (§12.1), the single, parallel
and outer accumulation functions Δ_1, Δ_* and Δ_+ (eqs. `accone`, `accpar`, `accseq`), and the
final state integration (§12.3), together with the accumulation output root of §7
(eq. `accoutbeltdef`: ℳ_B over ℰ_4(s) ⌢ h with Keccak).
-/

namespace JAM

/-- A work-package hash as a key. -/
abbrev PkgHash := List UInt8

/-- The package hash of a report. -/
def WorkReport.pkg (r : WorkReport) : PkgHash := r.spec.packageHash.toList

/-- A ready-queue entry: a report and its unaccumulated dependencies. -/
abbrev ReadyEntry := WorkReport × List PkgHash

/-- E(**r**, **x**) (GP §12.1): drop entries whose package is in **x**, and remove **x** from the
    remaining dependencies. -/
def editQueue (r : List ReadyEntry) (x : List PkgHash) : List ReadyEntry :=
  (r.filter fun (w, _) => !x.contains w.pkg).map fun (w, d) => (w, d.filter (!x.contains ·))

/-- P(**r**): the package hashes of a set of reports. -/
def pkgs (r : List WorkReport) : List PkgHash := r.map (·.pkg)

/-- Q(**r**) (GP §12.1): reports whose dependencies are all met, repeatedly. Each round removes at
    least one entry, so |**r**| + 1 rounds suffice. -/
def readyOrder : Nat → List ReadyEntry → List WorkReport
  | 0, _ => []
  | fuel + 1, r =>
    let g := r.filterMap fun (w, d) => if d.isEmpty then some w else none
    if g.isEmpty then [] else g ++ readyOrder fuel (editQueue r (pkgs g))

/-- D(r) = (r, {prerequisites} ∪ K(segment-root lookup)). -/
def deps (r : WorkReport) : ReadyEntry :=
  (r, (r.context.prerequisites.map (·.toList) ++ r.segmentRootLookup.map (·.1.toList)).eraseDups)

/-- The accumulation statistics of one service: (N, T, G). -/
abbrev AccStat := Nat × Nat × Nat

/-- The parts of state accumulation reads and writes (the accumulate STF's state). -/
structure AccState where
  slot : Nat
  entropy : List UInt8
  ready : List (List ReadyEntry)
  accumulated : List (List PkgHash)
  pstate : PartialState

/-- The result of the accumulation STF: the posterior state, the output root, and the statistics. -/
structure AccResult where
  state : AccState
  root : List UInt8
  stats : List (Nat × AccStat)

section
variable (params : Params) (entropy : List UInt8) (slot : Nat)

/-- Δ_1(**e**, **t**, **r**, **f**, s) (GP eq. `accone`). -/
def accOne (e : PartialState) (t : List DeferredTransfer) (r : List WorkReport)
    (f : Std.ExtTreeMap Nat Nat) (s : Nat) : AccOut :=
  let iT := (t.filter (·.dest == s)).map AccumulateInput.transfer
  let iU := r.flatMap fun w => (w.digests.filter (·.service == s)).map fun d =>
    AccumulateInput.operand
      { packageHash := w.spec.packageHash, segmentRoot := w.spec.segmentRoot,
        authorizer := w.authorizerHash, payloadHash := d.payloadHash, gasLimit := d.gasLimit,
        authTrace := w.authTrace, result := d.result }
  let g := f.getD s 0 + ((t.filter (·.dest == s)).map (·.gas)).sum +
    (r.flatMap fun w => (w.digests.filter (·.service == s)).map (·.gasLimit)).sum
  psiA params entropy e slot s g (iT ++ iU)

/-- R(o, a, b): b if a = o, otherwise a. -/
def pick (o a b : Nat) : Nat := if a = o then b else a

/-- I(**d**, **p**) (GP §12.2): integrate the provisions whose request is still `[]`. -/
def integrateProvisions (d : Accounts) (p : List (Nat × List UInt8)) : Accounts :=
  p.foldl (fun d (s, i) =>
    let h := (Blake2b.hash256 ⟨i.toArray⟩).toList
    match d.get? s with
    | some a =>
      if a.requests.get? (h, i.length) == some [] then
        d.insert s { a with requests := a.requests.insert (h, i.length) [slot],
                             preimages := a.preimages.insert h i }
      else d
    | none => d) d

/-- Δ_*(**e**, **t**, **r**, **f**) (GP eq. `accpar`): accumulate every service with work, free gas
    or incoming transfers, and merge the results. -/
def accPar (e : PartialState) (t : List DeferredTransfer) (r : List WorkReport)
    (f : Std.ExtTreeMap Nat Nat) :
    PartialState × List DeferredTransfer × List (Nat × List UInt8) × List (Nat × Nat) :=
  let ss := ((r.flatMap fun w => w.digests.map (·.service)) ++ f.keys ++ t.map (·.dest)).eraseDups.mergeSort
  -- every service whose result is used, each accumulated once
  let needed := (ss ++ [e.manager, e.delegator, e.registrar] ++ e.assigners).eraseDups
  let results : List (Nat × AccOut) := needed.map fun s => (s, accOne params entropy slot e t r f s)
  let acc (s : Nat) : AccOut := (results.lookup s).getD ⟨e, [], none, 0, []⟩
  let u := ss.map fun s => (s, (acc s).gasUsed)
  let b := ss.filterMap fun s => (acc s).yield.map (s, ·)
  let t' := ss.flatMap fun s => (acc s).xfers
  let d := e.accounts
  -- **n**: each service's own account and the accounts it created
  let n := ss.foldl (fun (n : Accounts) s =>
    (acc s).state.accounts.foldl (fun n k a => if d.contains k ∧ k ≠ s then n else n.insert k a) n) ∅
  -- **m**: the accounts some service removed
  let m := ss.flatMap fun s => d.keys.filter fun k => !(acc s).state.accounts.contains k
  let merged := (n.foldl (fun d k a => d.insert k a) d)
  let merged := m.foldl (fun d k => d.erase k) merged
  let accounts := integrateProvisions slot merged (ss.flatMap fun s => (acc s).provisions)
  let eStar := (acc e.manager).state
  let assigners := (List.range e.assigners.length).map fun c =>
    let o := e.assigners.getD c 0
    pick o (eStar.assigners.getD c 0) ((acc o).state.assigners.getD c 0)
  let authQueue := (List.range e.authQueue.length).map fun c =>
    (acc (e.assigners.getD c 0)).state.authQueue.getD c []
  let st : PartialState :=
    { accounts, staging := (acc e.delegator).state.staging, authQueue,
      manager := eStar.manager, assigners,
      delegator := pick e.delegator eStar.delegator (acc e.delegator).state.delegator,
      registrar := pick e.registrar eStar.registrar (acc e.registrar).state.registrar,
      alwaysAcc := eStar.alwaysAcc }
  (st, t', b, u)

/-- Δ_+(g, **t**, **r**, **e**, **f**) (GP eq. `accseq`): accumulate as many reports as fit in the
    gas, then recurse with the transfers they produced. `fuel` bounds the rounds. -/
def accSeq : Nat → Int → List DeferredTransfer → List WorkReport → PartialState →
    Std.ExtTreeMap Nat Nat →
    Nat × PartialState × List (Nat × List UInt8) × List (Nat × Nat) × List DeferredTransfer
  | 0, _, _, _, e, _ => (0, e, [], [], [])
  | fuel + 1, g, t, r, e, f =>
    let fixedGas : Int := ((t.map (·.gas)).sum + f.values.sum : Nat)
    let prefixGas (k : Nat) : Int := ((r.take k).flatMap fun w => w.digests.map (·.gasLimit)).sum
    let i := ((List.range (r.length + 1)).filter fun k => prefixGas k + fixedGas ≤ g).getLast?.getD 0
    let n := i + t.length + f.size
    if n = 0 then (0, e, [], [], [])
    else
      let (eStar, tStar, bStar, uStar) := accPar params entropy slot e t (r.take i) f
      let gStar : Int := g + ((tStar.map (·.gas)).sum : Nat) - ((uStar.map (·.2)).sum : Nat)
      let (j, e', b, u, tDagger) := accSeq fuel gStar tStar (r.drop i) eStar ∅
      (i + j, e', bStar ++ b, uStar ++ u, t ++ tDagger)

end

/-- The accumulation state transition (GP §12) for the block with timeslot `slot` and newly
    available reports **R**, with the accumulation output root (GP eq. `accoutbeltdef`). -/
def accumulate (params : Params) (pre : AccState) (slot : Nat) (reports : List WorkReport) : AccResult :=
  let E := params.epochLen
  let m := slot % E
  let accumulatedAll := pre.accumulated.flatten
  let rBang := reports.filter fun r => r.context.prerequisites.isEmpty ∧ r.segmentRootLookup.isEmpty
  let rQ := editQueue ((reports.filter fun r => !(r.context.prerequisites.isEmpty ∧ r.segmentRootLookup.isEmpty)).map deps)
    accumulatedAll
  let q := editQueue ((pre.ready.drop m).flatten ++ (pre.ready.take m).flatten ++ rQ) (pkgs rBang)
  let rStar := rBang ++ readyOrder (q.length + 1) q
  let e := pre.pstate
  let g : Nat := max params.blockAccGas (params.reportAccGas * params.coreCount + e.alwaysAcc.values.sum)
  let rounds := rStar.length + g / Constants.CgasT + 2
  let (n, e', b, u, t) := accSeq params pre.entropy slot rounds g [] rStar e e.alwaysAcc
  -- statistics S(s) = (N(s), T(s), G(s))
  let accounted := rStar.take n
  let svcs := ((accounted.flatMap fun w => w.digests.map (·.service)) ++ t.map (·.dest) ++ u.map (·.1)).eraseDups.mergeSort
  let stats := svcs.filterMap fun s =>
    let N : Nat := (accounted.flatMap fun w => w.digests.filter (·.service == s)).length
    let T : Nat := (t.filter (·.dest == s)).length
    let G : Nat := ((u.filter (·.1 == s)).map (·.2)).sum
    if N = 0 ∧ T = 0 ∧ G = 0 then none else some (s, (N, T, G))
  let accounts := stats.foldl (fun (d : Accounts) (s, _) =>
    match d.get? s with
    | some a => d.insert s { a with lastAcc := slot }
    | none => d) e'.accounts
  -- ξ'_{E−1} = P(**R***_{…n}) is a set ⟦ℍ⟧; we keep sets in ascending order, as they are encoded
  let newAcc := (pkgs accounted).eraseDups.mergeSort fun a b => decide (a ≤ b)
  let accumulated := pre.accumulated.drop 1 ++ [newAcc]
  let ready := (List.range E).map fun idx =>
    -- idx = (m − i) mod E
    let i := (m + E - idx) % E
    if i = 0 then editQueue rQ newAcc
    else if i < slot - pre.slot then []
    else editQueue (pre.ready.getD idx []) newAcc
  let outs := (b.mergeSort fun x y => x.1 ≤ y.1).map fun (s, h) => Codec.fixed 4 s ++ h
  { state := { slot, entropy := pre.entropy, ready, accumulated, pstate := { e' with accounts } },
    root := Merkle.root Keccak.keccak256 outs, stats }

end JAM
