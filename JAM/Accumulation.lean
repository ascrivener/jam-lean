import JAM.Fast.Keccak
import JAM.Fast.Blake2b
import JAM.Accumulate
import JAM.Merkle

/-!
# Accumulation (GP v0.8.1 §12, `sec:accumulation`)

The accumulation state transition: the queue functions $E$, $Q$ and $P$ (§12.1), the single,
parallel and outer accumulation functions $\Delta_1$, $\Delta_{\ast}$ and $\Delta_+$ (eqs. `accone`,
`accpar`, `accseq`), and the final state integration (§12.3), together with the accumulation output
root of §7 (eq. `accoutbeltdef`: $\mathcal{M}_B$ over $\mathcal{E}_4(s) \frown h$ with Keccak).
-/

namespace JAM

/-- A work-package hash as a key. -/
abbrev PkgHash := List UInt8

/-- The package hash of a report. -/
def WorkReport.pkg (r : WorkReport) : PkgHash := r.spec.packageHash.toList

/-- A ready-queue entry: a report and the set of its unaccumulated dependencies. -/
abbrev ReadyEntry := WorkReport × OctetSet

/-- $E(\mathbf{r}, \mathbf{x})$ (GP §12.1): drop entries whose package is in $\mathbf{x}$, and remove
    $\mathbf{x}$ from the remaining dependencies. -/
def editQueue (r : List ReadyEntry) (x : OctetSet) : List ReadyEntry :=
  (r.filter fun (w, _) => !x.contains w.pkg).map fun (w, d) => (w, d.diff x)

/-- $P(\mathbf{r})$: the set of package hashes of a set of reports. -/
def pkgs (r : List WorkReport) : OctetSet := .ofList (r.map (·.pkg))

/-- One round of $Q$ shortens the queue: every report in $\mathbf{g}$ (those with no unmet
    dependencies) is dropped by $E(\mathbf{r}, P(\mathbf{g}))$, since its own package hash is in
    $P(\mathbf{g})$. -/
theorem editQueue_length_lt (r : List ReadyEntry) (g : List WorkReport)
    (hg : (r.filterMap fun (w, d) => if d.isEmpty then some w else none) = g) (hne : g ≠ []) :
    (editQueue r (pkgs g)).length < r.length := by
  unfold editQueue
  rw [List.length_map, List.length_filter_lt_length_iff_exists]
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil g hne
  have hw' := hw
  rw [← hg, List.mem_filterMap] at hw'
  obtain ⟨⟨w', d⟩, hmem, hsome⟩ := hw'
  refine ⟨(w', d), hmem, ?_⟩
  have : w' = w := by
    dsimp only at hsome; split at hsome <;> simp_all
  subst this
  simp only [pkgs, Std.ExtTreeSet.contains_ofList, Bool.not_eq_true', Bool.not_eq_false]
  exact List.elem_iff.mpr (List.mem_map_of_mem hw)

/-- $Q(\mathbf{r})$ (GP §12.1): reports whose dependencies are all met, repeatedly. Each round
    removes at least one entry (`editQueue_length_lt`), so the recursion ends. -/
def readyOrder (r : List ReadyEntry) : List WorkReport :=
  match _hg : r.filterMap fun (w, d) => if d.isEmpty then some w else none with
  | [] => []
  | w :: ws => (w :: ws) ++ readyOrder (editQueue r (pkgs (w :: ws)))
termination_by r.length
decreasing_by exact editQueue_length_lt r _ _hg (List.cons_ne_nil w ws)

/-- $D(r) = (r, \{\text{prerequisites}\} \cup \mathcal{K}(\text{segment-root lookup}))$. -/
def deps (r : WorkReport) : ReadyEntry :=
  (r, r.context.prerequisites.insertMany r.segmentRootLookup.keys)

/-- The accumulation statistics of one service: $(N, T, G)$. -/
abbrev AccStat := Nat × Nat × Nat

/-- The parts of state accumulation reads and writes (the accumulate STF's state). -/
structure AccState where
  slot : Nat
  entropy : List UInt8
  ready : List (List ReadyEntry)
  accumulated : List OctetSet
  pstate : PartialState

/-- The result of the accumulation STF: the posterior state, the output root, and the statistics. -/
structure AccResult where
  state : AccState
  root : List UInt8
  stats : List (Nat × AccStat)
  /-- $\theta' = [(s, h) \in \mathbf{b}]$ (GP v0.8.1 eq. `finalstateaccumulation`,
      accumulation.tex:401): the set $\mathbf{b}$ without repeats, ordered by service and then hash;
      `root` is the Merkle root of its encoding. -/
  outputs : List (Nat × List UInt8) := []

section
variable (params : Params) (entropy : List UInt8) (slot : Nat)

/-- $\Delta_1(\mathbf{e}, \mathbf{t}, \mathbf{r}, \mathbf{f}, s)$ (GP eq. `accone`). -/
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

/-- $R(o, a, b)$: $b$ if $a = o$, otherwise $a$. -/
def pick (o a b : Nat) : Nat := if a = o then b else a

/-- $I(\mathbf{d}, \mathbf{p})$ (GP §12.2): integrate the provisions whose request is still `[]`. -/
def integrateProvisions (d : Accounts) (p : Provisions) : Accounts :=
  p.foldl (fun d (s, i) =>
    let h := (Blake2b.hash256 ⟨i.toArray⟩).toList
    match d.get? s with
    | some a =>
      if a.requestGet h i.length == some [] then
        d.insert s { a.requestSet h i.length [slot] with preimages := a.preimages.insert h i }
      else d
    | none => d) d

/-- $N$ (GP v0.8.1 eq. `accpar`): service $s$'s $\Delta_1$ outcome `os`, discarded (keeping only its
    gas use and provisions) when both $s$ and its effective supervisor $u = E(\mathbf{d}, s) \ne s$
    modified $s$, given $u$'s outcome `ou`.

    GP v0.8.1 leaves $N(\mathbf{o})$'s post-state without a value (every other field has one). It is
    taken to be the round's input state $\mathbf{e}$, as the prose before eq. `accseq` says
    ("discard all results of the service's execution", its footnote excepting only provided
    preimages). Reading it as $\mathbf{o}$'s post-state would keep a discarded run's new accounts
    and privilege, staging and queue changes while $M(s)$ drops its own account change. This is a
    project decision; the paper gap is
    [`docs/upstream-candidates.md`](https://github.com/ascrivener/jam-lean/blob/main/docs/upstream-candidates.md#gray-paper-issues) v0.8.1-A1, raised as graypaper#592. -/
def discardIfBoth (e : PartialState) (s u : Nat) (os ou : AccOut) : AccOut :=
  if os.modified.contains s ∧ u ≠ s ∧ ou.modified.contains s then
    ⟨e, ∅, [], none, os.gasUsed, os.provisions⟩
  else os

/-- Why accumulation makes a block invalid. -/
inductive AccumulationError where
  /-- Two services created an account with the same new index in one round of $\Delta_*$
      (GP v0.8.1 §12.2, the paragraph after the definitions of $I$ and $Y$: "different services may not each
      contribute the same index for a new service \dots In the unlikely event of a conflict, the
      block must be considered invalid"). -/
  | newServiceConflict (index : Nat)
  /-- $\Delta_+$ (GP v0.8.1 eq. `accseq`) did not finish within the model's bound on its rounds
      (`accSeq`'s fuel). The paper's recursion has no such bound (note v0.8.1-A47); no theorem yet
      shows the bound is never reached, and reaching it makes the block invalid rather than
      silently stopping accumulation. -/
  | fuelExhausted
  deriving BEq, Repr

/-- $\mathbf{n} = \bigcup_{s \in \mathbf{s}}((\Delta(s)_\mathbf{e})_\mathbf{d} \setminus \mathcal{K}(\mathbf{d}))$
    (GP v0.8.1 eq. `accpar`), from each service's post-state accounts `outs` (in the order of
    $\mathbf{s}$). The union must be disjoint: an index outside $\mathcal{K}(\mathbf{d})$ in the
    accounts of two services is a conflict, and the block is invalid (GP v0.8.1 §12.2, the
    paragraph after the definitions of $I$ and $Y$). -/
def collectNew (d : Accounts) (outs : List Accounts) : Except AccumulationError Accounts :=
  outs.foldlM (fun (n : Accounts) (acc : Accounts) =>
    acc.foldlM (fun (n' : Accounts) k a =>
      if d.contains k then .ok n'
      else if n.contains k then .error (.newServiceConflict k)
      else .ok (n'.insert k a)) n) ∅

/-- $\Delta_{\ast}(\mathbf{e}, \mathbf{t}, \mathbf{r}, \mathbf{f})$ (GP v0.8.1 eq. `accpar`):
    accumulate every service with work, free gas or incoming transfers, and merge the results.

* A service's results are discarded, keeping only its gas use and provisions ($N$), when both it
  and its effective supervisor $E(\mathbf{d}, s) \ne s$ modified $s$'s account in this round.
* Each existing account is taken from the run of the service itself if it modified it, and
  otherwise from the run of its effective supervisor ($M$); new accounts come from their creators
  ($\mathbf{n}$, `collectNew`); a removed account is one whose $M$ is none. Two services creating
  the same new index is an error, `AccumulationError.newServiceConflict`: the block is invalid
  (GP v0.8.1 §12.2, after the definitions of $I$ and $Y$).
* Privileges, staging set and authorizer queue through $X(s)$ and $R$ (unchanged from GP v0.8.0).

A service that is neither accumulated nor needed for the privileges has no inputs and no gas; its
$\Delta_1$ is the unchanged state with nothing modified ($\Psi_A$ with $g = 0$ runs out of gas at
once, or has no code), which `acc` returns for it without running $\Psi_A$. -/
def accPar (e : PartialState) (t : List DeferredTransfer) (r : List WorkReport)
    (f : Std.ExtTreeMap Nat Nat) :
    Except AccumulationError
      (PartialState × List DeferredTransfer × List (Nat × List UInt8) × List (Nat × Nat)) := do
  let ss := ((r.flatMap fun w => w.digests.map (·.service)) ++ f.keys ++ t.map (·.dest)).eraseDups.mergeSort
  let d := e.accounts
  let E := effectiveSupervisor d
  -- every service whose Δ_1 result is used, each run once
  let needed := (ss ++ ss.map E ++ d.keys.map E ++ [e.manager, e.delegator, e.registrar] ++
    e.assigners).eraseDups
  let raw : List (Nat × AccOut) := needed.map fun s => (s, accOne params entropy slot e t r f s)
  let o (s : Nat) : AccOut := (raw.lookup s).getD ⟨e, ∅, [], none, 0, ∅⟩
  let acc (s : Nat) : AccOut := discardIfBoth e s (E s) (o s) (o (E s))
  let u := ss.map fun s => (s, (acc s).gasUsed)
  let b := ss.filterMap fun s => (acc s).yield.map (s, ·)
  let t' := ss.flatMap fun s => (acc s).xfers
  -- M(s): s's account from its own run if it modified it, else from its effective supervisor's
  let M (s : Nat) : Option ServiceAccount :=
    if (acc s).modified.contains s then (acc s).state.accounts.get? s
    else (acc (E s)).state.accounts.get? s
  let m : Accounts := d.keys.foldl (fun mm s => match M s with
    | some a => mm.insert s a
    | none => mm) ∅
  -- **n**: the accounts each service created
  let n ← collectNew d (ss.map fun s => (acc s).state.accounts)
  let merged := n.foldl (fun mm k a => mm.insert k a) m
  let accounts := integrateProvisions slot merged (ss.foldl (fun p s => p.union (acc s).provisions) ∅)
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
  return (st, t', b, u)

/-- $T(\mathbf{t}, \mathbf{s}, \mathbf{d})$ (GP v0.8.1 eq. `accseq`'s partition $T$): split the
    deferred transfers into those accumulated in this round ($\mathbf{t}^!$) and those deferred to a
    later one ($\mathbf{t}^Q$). A transfer waits if its destination's effective supervisor is
    accumulated (in $\mathbf{s}$) or already receives a transfer this round (in $\mathbf{i}$), or if
    it is itself the effective supervisor of a service in $\mathbf{i}$; otherwise its destination
    joins $\mathbf{i}$. -/
def partitionXfers (s : List Nat) (d : Accounts) :
    List DeferredTransfer → List Nat → List DeferredTransfer × List DeferredTransfer
  | [], _ => ([], [])
  | t :: ts, i =>
    let E := effectiveSupervisor d
    let q : Bool :=
      (d.contains t.dest && (s.contains (E t.dest) || i.contains (E t.dest)) && E t.dest != t.dest) ||
        i.any fun x => x != t.dest && E x == t.dest
    let i' := if q || !d.contains t.dest then i else t.dest :: i
    let (bang, wait) := partitionXfers s d ts i'
    if q then (bang, t :: wait) else (t :: bang, wait)

/-- $\Delta_+(g, \mathbf{t}, \mathbf{r}, \mathbf{e}, \mathbf{f})$ (GP v0.8.1 eq. `accseq`):
    accumulate as many reports as fit in the gas, with the transfers `partitionXfers` lets through,
    then recurse with the deferred ones and those this round produced. `fuel` bounds the rounds;
    running out of it is the error `AccumulationError.fuelExhausted` (note v0.8.1-A47). -/
def accSeq : Nat → Int → List DeferredTransfer → List WorkReport → PartialState →
    Std.ExtTreeMap Nat Nat →
    Except AccumulationError
      (Nat × PartialState × List (Nat × List UInt8) × List (Nat × Nat) × List DeferredTransfer)
  | 0, _, _, _, _, _ => .error .fuelExhausted
  | fuel + 1, g, t, r, e, f =>
    let fixedGas : Int := ((t.map (·.gas)).sum + f.values.sum : Nat)
    let prefixGas (k : Nat) : Int := ((r.take k).flatMap fun w => w.digests.map (·.gasLimit)).sum
    let i := ((List.range (r.length + 1)).filter fun k => prefixGas k + fixedGas ≤ g).getLast?.getD 0
    let svcs := ((r.take i).flatMap fun w => w.digests.map (·.service)) ++ f.keys
    let (tBang, tQ) := partitionXfers svcs e.accounts t []
    let n := i + tBang.length + f.size
    if n = 0 then .ok (0, e, [], [], [])
    else do
      let (eStar, tStar, bStar, uStar) ← accPar params entropy slot e tBang (r.take i) f
      let gStar : Int := g + ((tStar.map (·.gas)).sum : Nat) - ((uStar.map (·.2)).sum : Nat)
      let (j, e', b, u, tDagger) ← accSeq fuel gStar (tQ ++ tStar) (r.drop i) eStar ∅
      return (i + j, e', bStar ++ b, uStar ++ u, tBang ++ tDagger)

end

/-- The accumulation state transition (GP §12) for the block with timeslot `slot` and newly
    available reports $\mathbf{R}$, with the accumulation output root (GP eq. `accoutbeltdef`). -/
def accumulate (params : Params) (pre : AccState) (slot : Nat) (reports : List WorkReport) :
    Except AccumulationError AccResult := do
  let E := params.epochLen
  let m := slot % E
  let accumulatedAll : OctetSet := pre.accumulated.foldl .union ∅
  let rBang := reports.filter fun r => r.context.prerequisites.isEmpty ∧ r.segmentRootLookup.isEmpty
  let rQ := editQueue ((reports.filter fun r => !(r.context.prerequisites.isEmpty ∧ r.segmentRootLookup.isEmpty)).map deps)
    accumulatedAll
  let q := editQueue ((pre.ready.drop m).flatten ++ (pre.ready.take m).flatten ++ rQ) (pkgs rBang)
  let rStar := rBang ++ readyOrder q
  let e := pre.pstate
  let g : Nat := max params.blockAccGas (params.reportAccGas * params.coreCount + e.alwaysAcc.values.sum)
  let rounds := rStar.length + g / Constants.CgasT + 2
  let (n, e', b, u, t) ← accSeq params pre.entropy slot rounds g [] rStar e e.alwaysAcc
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
  -- ξ'_{E−1} = P(**R***_{…n}), a set ⟦ℍ⟧
  let newAcc := pkgs accounted
  let accumulated := pre.accumulated.drop 1 ++ [newAcc]
  let ready := (List.range E).map fun idx =>
    -- idx = (m − i) mod E
    let i := (m + E - idx) % E
    if i = 0 then editQueue rQ newAcc
    else if i < slot - pre.slot then []
    else editQueue (pre.ready.getD idx []) newAcc
  -- θ' ≡ [(s, h) ∈ **b**] (GP v0.8.1 accumulation.tex:401): **b** = **b*** ∪ **b** is a set
  -- ⟦(ℕ_S, ℍ)⟧ (accumulation.tex:147), so each pair appears once, in the set's order (s, then h),
  -- as merklization.tex:93 serializes it. A service yielding in two rounds of a block gives two
  -- entries ordered by hash, and the same (s, h) twice gives one.
  let theta := (Std.ExtTreeSet.ofList b : Provisions).toList
  let outs := theta.map fun (s, h) => Codec.fixed 4 s ++ h
  let res : AccResult :=
    { state := { slot, entropy := pre.entropy, ready, accumulated, pstate := { e' with accounts } },
      root := Merkle.root Keccak.keccak256 outs, stats, outputs := theta }
  return res

end JAM
