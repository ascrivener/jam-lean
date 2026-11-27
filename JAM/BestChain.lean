import JAM.Auditing
import JAM.Safrole
import JAM.Constants

/-!
# The best chain (GP v0.8.1 §19, `best_chain.tex`)

Off-chain logic: which known block a validator treats as the head of the best chain,
$\mathbf{B}^\flat$, the block it builds on and votes for in GRANDPA. GRANDPA itself is not modelled:
the latest finalized block $\mathbf{B}^\natural$ is an input. Nothing here is part of the state transition.

The paper's inputs that are local to the node become explicit data. A block is known to the node
through a `BlockInfo`: its header hash, $\mathbf{H}_P$, $\mathbf{H}_T$, the ticketed marker
$\mathbf{T}$, and the node's own view of the audited condition $\mathbf{U}$ and of the disregard
rule of §17.3. A store (`List (BlockInfo H)`) is the set of valid blocks the node has seen; it is
generic in the hash type `H` (the model's `Hash` in `BlockInfo.ofHeader`, small numbers in the
tests).

## Rules modelled

* $\mathbf{A}$ (§5, eq. `ancestors`):
  $h \in \mathbf{A} \Leftrightarrow h = \mathbf{H} \lor (\exists i \in \mathbf{A} : h = P(i))$, within
  the store (`ancestry`). A parent link is followed only when $P(\mathbf{H})_T < \mathbf{H}_T$ (the
  timeslot rule of §5); a valid block always satisfies it, and it makes the recursion well founded.
* (19.1) $\mathbf{A}(\mathbf{H}^\flat) \ni \mathbf{H}^\natural$: the best block has the finalized
  block as an ancestor (or is it).
* (19.2) $\mathbf{U}^\flat \equiv \top$: the best block is considered audited. Two readings,
  `AuditReading` (note v0.8.1-A21): `head` is the formula (only the head's own $\mathbf{U}$);
  `chain` also asks every unfinalized ancestor to be audited.
* (19.3) $\neg\exists \mathbf{H}^A, \mathbf{H}^B : \mathbf{H}^A \neq \mathbf{H}^B \land \mathbf{H}^A_T = \mathbf{H}^B_T \land \mathbf{H}^A \in \mathbf{A}(\mathbf{H}^\flat) \land \mathbf{H}^A \notin \mathbf{A}(\mathbf{H}^\natural)$:
  no unfinalized ancestor shares its timeslot with another seen block (`equivocates`; note
  v0.8.1-A23).
* §17.3, best-block paragraph: "we pointedly disregard chains which include the accumulation of a
  report which we know at least ⅓ of validators judge as being invalid": no ancestor is a
  disregarded block (`BlockInfo.disregarded`, computable with `disregardedBlock` from
  `JAM.Auditing.disregarded`; note v0.8.1-A22).
* (19.4) $m = \sum_{\mathbf{H}^A \in \mathbf{A}^\flat} \mathbf{T}^A$: the number of ticket-sealed
  ancestors (`metric`), with $\mathbf{T}$ from eqs. `ticketconditiontrue` / `ticketconditionfalse`
  (`ticketedOf`).
* $\mathbf{B}^\flat$: an acceptable block maximising $m$ (`bestHeads`, all of them; the paper sets
  no tie-break, note v0.8.1-A24; `bestHead?` takes the first in store order).
* §5, the timeslot rule
  $P(\mathbf{H})_T < \mathbf{H}_T \land \mathbf{H}_T \cdot \mathsf{P} \leq \mathcal{T}$ (`slotTimely`).

The GRANDPA vote payload (the header of $\mathbf{B}^\flat$ with its posterior state root) is not
modelled.

## Facts (`JAM.Theorems.BestChain`)

Every best head is acceptable, extends $\mathbf{B}^\natural$ and maximises $m$ among acceptable blocks
(`mem_bestHeads_iff`), the set of best heads does not depend on the order of the store when hashes
are unique (`mem_bestHeads_perm`), the finalized block is acceptable when audited and undisputed
so a best head then exists (`bestHeads_ne_nil`), and a child adds its own $\mathbf{T}$ to $m$
(`metric_child`).
-/

namespace JAM.BestChain

/-- What the node knows about one valid block (GP §19): $\mathcal{H}(\mathbf{H})$, $\mathbf{H}_P$
    and $\mathbf{H}_T$ from the header, $\mathbf{T}$ (eqs. `ticketconditiontrue` /
    `ticketconditionfalse`), the node's view of $\mathbf{U}$ (§17.3, e.g.
    `JAM.Auditing.blockAudited`), and whether the block accumulates a report at least ⅓ of the
    validators are known to judge invalid (§17.3, e.g. `disregardedBlock`). -/
structure BlockInfo (H : Type) where
  /-- $\mathcal{H}(\mathcal{E}(\mathbf{H}))$, the header hash. -/
  hash : H
  /-- $\mathbf{H}_P$, the parent header hash. -/
  parent : H
  /-- $\mathbf{H}_T$, the timeslot. -/
  slot : Nat
  /-- $\mathbf{T}$, sealed with a ticket rather than a fallback key. -/
  ticketed : Bool
  /-- $\mathbf{U}$, the node's view of the audited condition. -/
  audited : Bool
  /-- The block includes the accumulation of a report the §17.3 disregard rule names. -/
  disregarded : Bool
  deriving Repr, DecidableEq

/-- $\mathbf{T}$ from the posterior slot-sealer sequence $\gamma'_S$ (eqs. `ticketconditiontrue`,
    `ticketconditionfalse`): 1 when $\gamma'_S \in [\![ \mathbb{T} ]\!]$ (tickets), 0 when
    $\gamma'_S \in [\![ \bskey ]\!]$ (fallback keys). -/
def ticketedOf : SealKeys → Bool
  | .tickets _ => true
  | .keys _ => false

/-- The §17.3 disregard rule for one block: it includes the accumulation of some report (given by
    the caller, from the block's accumulation) which at least ⅓ of the validators are known to judge
    invalid (`JAM.Auditing.disregarded`). -/
def disregardedBlock (V : Nat) (view : Auditing.View) (accumulated : List WorkReport) : Bool :=
  accumulated.any fun w => Auditing.disregarded V view (Auditing.reportHash w)

/-- A `BlockInfo` from a model header: `hash` is $\mathcal{H}(\mathcal{E}(\mathbf{H}))$ (the caller
    hashes, the model takes hashing as a parameter), $\mathbf{T}$ comes from $\gamma'_S$
    (`ticketedOf`), and $\mathbf{U}$ and the disregard flag from
    the node's audit view. -/
def BlockInfo.ofHeader (hash : Hash) (hdr : Header) (sealKeys' : SealKeys) (audited disregarded : Bool) :
    BlockInfo Hash :=
  { hash, parent := hdr.parent, slot := hdr.slot, ticketed := ticketedOf sealKeys', audited,
    disregarded }

/-- The timeslot rule of §5:
    $P(\mathbf{H})_T < \mathbf{H}_T \land \mathbf{H}_T \cdot \mathsf{P} \leq \mathcal{T}$, with
    `wallclock` = $\mathcal{T}$ in seconds since the JAM common era and $\mathsf{P} = 6$. A block
    failing only the second conjunct may become valid as $\mathcal{T}$ advances. -/
def slotTimely (parentSlot slot wallclock : Nat) : Bool :=
  decide (parentSlot < slot) && decide (slot * Constants.Cslotseconds ≤ wallclock)

variable {H : Type} [DecidableEq H]

/-- $P$ on the store: the known block with hash $h$ (the first, if the store repeats a hash). -/
def lookup (bs : List (BlockInfo H)) (h : H) : Option (BlockInfo H) :=
  bs.find? fun b => decide (b.hash = h)

/-- $\mathbf{A}(\mathbf{H})$ (§5, eq. `ancestors`) within the store, $\mathbf{H}$ first and then its
    ancestors youngest first. A parent is followed only while it is known and
    $P(\mathbf{H})_T < \mathbf{H}_T$ (the §5 timeslot rule). -/
def ancestry (bs : List (BlockInfo H)) (b : BlockInfo H) : List (BlockInfo H) :=
  b :: match lookup bs b.parent with
    | some p => if p.slot < b.slot then ancestry bs p else []
    | none => []
termination_by b.slot

/-- $\mathbf{A}(\mathbf{H}^\natural)$ as hashes: the finalized block's ancestry (empty when the store lacks it). -/
def finalizedAncestors (bs : List (BlockInfo H)) (fin : H) : List H :=
  match lookup bs fin with
  | some f => (ancestry bs f).map (·.hash)
  | none => []

/-- (19.3), for one ancestor $\mathbf{H}^A$: some other seen block $\mathbf{H}^B \neq \mathbf{H}^A$
    has $\mathbf{H}^B_T = \mathbf{H}^A_T$ ("two valid blocks at the same timeslot"). -/
def equivocates (bs : List (BlockInfo H)) (a : BlockInfo H) : Bool :=
  bs.any fun c => decide (c.hash ≠ a.hash) && decide (c.slot = a.slot)

/-- How (19.2) $\mathbf{U}^\flat \equiv \top$ is read (note v0.8.1-A21): `head` asks only the best
    block's own $\mathbf{U}$ (the formula); `chain` also asks $\mathbf{U}$ of each unfinalized
    ancestor. -/
inductive AuditReading where
  | head
  | chain
  deriving Repr, DecidableEq

/-- An acceptable block (GP §19, (19.1)–(19.3), with the §17.3 disregard rule):
    * (19.1) $\mathbf{H}^\natural \in \mathbf{A}(\mathbf{H})$;
    * (19.2) $\mathbf{U} \equiv \top$, read per `r`;
    * (19.3) no $\mathbf{H}^A \in \mathbf{A}(\mathbf{H}) \setminus \mathbf{A}(\mathbf{H}^\natural)$
      equivocates;
    * §17.3: no $\mathbf{H}^A \in \mathbf{A}(\mathbf{H})$ is disregarded. -/
def acceptable (r : AuditReading) (bs : List (BlockInfo H)) (fin : H) (b : BlockInfo H) : Bool :=
  let A := ancestry bs b
  let F := finalizedAncestors bs fin
  decide (fin ∈ A.map (·.hash)) && b.audited &&
    (match r with
      | .head => true
      | .chain => A.all fun a => decide (a.hash ∈ F) || a.audited) &&
    A.all (fun a => decide (a.hash ∈ F) || !equivocates bs a) &&
    A.all (fun a => !a.disregarded)

/-- (19.4) $m = \sum_{\mathbf{H}^A \in \mathbf{A}(\mathbf{H})} \mathbf{T}^A$: the ticket-sealed
    blocks among $\mathbf{H}$ and its ancestors in the store. -/
def metric (bs : List (BlockInfo H)) (b : BlockInfo H) : Nat :=
  (ancestry bs b).countP (·.ticketed)

/-- The largest $m$ among `l`, 0 for none. -/
def maxMetric (bs : List (BlockInfo H)) (l : List (BlockInfo H)) : Nat :=
  (l.map (metric bs)).foldl max 0

/-- The candidates for $\mathbf{B}^\flat$ (GP §19): the hashes of the acceptable blocks of the store
    that maximise $m$, in store order. The paper sets no tie-break (note v0.8.1-A24), so all are returned. -/
def bestHeads (r : AuditReading) (bs : List (BlockInfo H)) (fin : H) : List H :=
  let acc := bs.filter (acceptable r bs fin)
  let M := maxMetric bs acc
  (acc.filter fun b => metric bs b = M).map (·.hash)

/-- One best head: the first of `bestHeads` in store order (a model choice; the paper sets no
    tie-break, note v0.8.1-A24), `none` when no block is acceptable. -/
def bestHead? (r : AuditReading) (bs : List (BlockInfo H)) (fin : H) : Option H :=
  (bestHeads r bs fin).head?

end JAM.BestChain
