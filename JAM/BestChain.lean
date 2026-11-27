import JAM.Auditing
import JAM.Safrole
import JAM.Constants

/-!
# The best chain (GP v0.8.1 §19, `best_chain.tex`)

Off-chain logic: which known block a validator treats as the head of the best chain, 𝐁^♭, the block
it builds on and votes for in GRANDPA. GRANDPA itself is not modelled: the latest finalized block
𝐁^♮ is an input. Nothing here is part of the state transition.

The paper's inputs that are local to the node become explicit data. A block is known to the node
through a `BlockInfo`: its header hash, H_P, H_T, the ticketed marker 𝐓, and the node's own view
of the audited condition 𝐔 and of the disregard rule of §17.3. A store (`List (BlockInfo H)`) is
the set of valid blocks the node has seen; it is generic in the hash type `H` (the model's `Hash`
in `BlockInfo.ofHeader`, small numbers in the tests).

## Rules modelled

* 𝐀 (§5, eq. `ancestors`): h ∈ 𝐀 ⇔ h = H ∨ (∃ i ∈ 𝐀 : h = P(i)), within the store (`ancestry`).
  A parent link is followed only when P(H)_T < H_T (the timeslot rule of §5); a valid block always
  satisfies it, and it makes the recursion well founded.
* (19.1) 𝐀(H^♭) ∋ H^♮: the best block has the finalized block as an ancestor (or is it).
* (19.2) 𝐔^♭ ≡ ⊤: the best block is considered audited. Two readings, `AuditReading` (note
  v0.8.1-A21): `head` is the formula (only the head's own 𝐔); `chain` also asks every unfinalized
  ancestor to be audited.
* (19.3) ¬∃ H^A, H^B : H^A ≠ H^B ∧ H^A_T = H^B_T ∧ H^A ∈ 𝐀(H^♭) ∧ H^A ∉ 𝐀(H^♮): no unfinalized
  ancestor shares its timeslot with another seen block (`equivocates`; note v0.8.1-A23).
* §17.3, best-block paragraph: "we pointedly disregard chains which include the accumulation of a
  report which we know at least ⅓ of validators judge as being invalid": no ancestor is a
  disregarded block (`BlockInfo.disregarded`, computable with `disregardedBlock` from
  `JAM.Auditing.disregarded`; note v0.8.1-A22).
* (19.4) m = Σ_{H^A ∈ 𝐀^♭} 𝐓^A: the number of ticket-sealed ancestors (`metric`), with 𝐓 from
  eqs. `ticketconditiontrue` / `ticketconditionfalse` (`ticketedOf`).
* 𝐁^♭: an acceptable block maximising m (`bestHeads`, all of them; the paper sets no tie-break,
  note v0.8.1-A24; `bestHead?` takes the first in store order).
* §5, the timeslot rule P(H)_T < H_T ∧ H_T·𝖯 ≤ 𝒯 (`slotTimely`).

The GRANDPA vote payload (the header of 𝐁^♭ with its posterior state root) is not modelled.

## Facts (`JAM.Theorems.BestChain`)

Every best head is acceptable, extends 𝐁^♮ and maximises m among acceptable blocks
(`mem_bestHeads_iff`), the set of best heads does not depend on the order of the store when hashes
are unique (`mem_bestHeads_perm`), the finalized block is acceptable when audited and undisputed
so a best head then exists (`bestHeads_ne_nil`), and a child adds its own 𝐓 to m (`metric_child`).
-/

namespace JAM.BestChain

/-- What the node knows about one valid block (GP §19): ℋ(H), H_P and H_T from the header, 𝐓
    (eqs. `ticketconditiontrue` / `ticketconditionfalse`), the node's view of 𝐔 (§17.3, e.g.
    `JAM.Auditing.blockAudited`), and whether the block accumulates a report at least ⅓ of the
    validators are known to judge invalid (§17.3, e.g. `disregardedBlock`). -/
structure BlockInfo (H : Type) where
  /-- ℋ(ℰ(H)), the header hash. -/
  hash : H
  /-- H_P, the parent header hash. -/
  parent : H
  /-- H_T, the timeslot. -/
  slot : Nat
  /-- 𝐓, sealed with a ticket rather than a fallback key. -/
  ticketed : Bool
  /-- 𝐔, the node's view of the audited condition. -/
  audited : Bool
  /-- The block includes the accumulation of a report the §17.3 disregard rule names. -/
  disregarded : Bool
  deriving Repr, DecidableEq

/-- 𝐓 from the posterior slot-sealer sequence γ'_S (eqs. `ticketconditiontrue`,
    `ticketconditionfalse`): 1 when γ'_S ∈ ⟦𝕋⟧ (tickets), 0 when γ'_S ∈ ⟦ℍ_B⟧ (fallback keys). -/
def ticketedOf : SealKeys → Bool
  | .tickets _ => true
  | .keys _ => false

/-- The §17.3 disregard rule for one block: it includes the accumulation of some report (given by
    the caller, from the block's accumulation) which at least ⅓ of the validators are known to judge
    invalid (`JAM.Auditing.disregarded`). -/
def disregardedBlock (V : Nat) (view : Auditing.View) (accumulated : List WorkReport) : Bool :=
  accumulated.any fun w => Auditing.disregarded V view (Auditing.reportHash w)

/-- A `BlockInfo` from a model header: `hash` is ℋ(ℰ(H)) (the caller hashes, the model takes
    hashing as a parameter), 𝐓 comes from γ'_S (`ticketedOf`), and 𝐔 and the disregard flag from
    the node's audit view. -/
def BlockInfo.ofHeader (hash : Hash) (hdr : Header) (sealKeys' : SealKeys) (audited disregarded : Bool) :
    BlockInfo Hash :=
  { hash, parent := hdr.parent, slot := hdr.slot, ticketed := ticketedOf sealKeys', audited,
    disregarded }

/-- The timeslot rule of §5: P(H)_T < H_T ∧ H_T·𝖯 ≤ 𝒯, with `wallclock` = 𝒯 in seconds since the
    JAM common era and 𝖯 = 6. A block failing only the second conjunct may become valid as 𝒯
    advances. -/
def slotTimely (parentSlot slot wallclock : Nat) : Bool :=
  decide (parentSlot < slot) && decide (slot * Constants.Cslotseconds ≤ wallclock)

variable {H : Type} [DecidableEq H]

/-- P on the store: the known block with hash h (the first, if the store repeats a hash). -/
def lookup (bs : List (BlockInfo H)) (h : H) : Option (BlockInfo H) :=
  bs.find? fun b => decide (b.hash = h)

/-- 𝐀(H) (§5, eq. `ancestors`) within the store, H first and then its ancestors youngest first.
    A parent is followed only while it is known and P(H)_T < H_T (the §5 timeslot rule). -/
def ancestry (bs : List (BlockInfo H)) (b : BlockInfo H) : List (BlockInfo H) :=
  b :: match lookup bs b.parent with
    | some p => if p.slot < b.slot then ancestry bs p else []
    | none => []
termination_by b.slot

/-- 𝐀(H^♮) as hashes: the finalized block's ancestry (empty when the store lacks it). -/
def finalizedAncestors (bs : List (BlockInfo H)) (fin : H) : List H :=
  match lookup bs fin with
  | some f => (ancestry bs f).map (·.hash)
  | none => []

/-- (19.3), for one ancestor H^A: some other seen block H^B ≠ H^A has H^B_T = H^A_T ("two valid
    blocks at the same timeslot"). -/
def equivocates (bs : List (BlockInfo H)) (a : BlockInfo H) : Bool :=
  bs.any fun c => decide (c.hash ≠ a.hash) && decide (c.slot = a.slot)

/-- How (19.2) 𝐔^♭ ≡ ⊤ is read (note v0.8.1-A21): `head` asks only the best block's own 𝐔 (the
    formula); `chain` also asks 𝐔 of each unfinalized ancestor. -/
inductive AuditReading where
  | head
  | chain
  deriving Repr, DecidableEq

/-- An acceptable block (GP §19, (19.1)–(19.3), with the §17.3 disregard rule):
    * (19.1) H^♮ ∈ 𝐀(H);
    * (19.2) 𝐔 ≡ ⊤, read per `r`;
    * (19.3) no H^A ∈ 𝐀(H) \ 𝐀(H^♮) equivocates;
    * §17.3: no H^A ∈ 𝐀(H) is disregarded. -/
def acceptable (r : AuditReading) (bs : List (BlockInfo H)) (fin : H) (b : BlockInfo H) : Bool :=
  let A := ancestry bs b
  let F := finalizedAncestors bs fin
  decide (fin ∈ A.map (·.hash)) && b.audited &&
    (match r with
      | .head => true
      | .chain => A.all fun a => decide (a.hash ∈ F) || a.audited) &&
    A.all (fun a => decide (a.hash ∈ F) || !equivocates bs a) &&
    A.all (fun a => !a.disregarded)

/-- (19.4) m = Σ_{H^A ∈ 𝐀(H)} 𝐓^A: the ticket-sealed blocks among H and its ancestors in the
    store. -/
def metric (bs : List (BlockInfo H)) (b : BlockInfo H) : Nat :=
  (ancestry bs b).countP (·.ticketed)

/-- The largest m among `l`, 0 for none. -/
def maxMetric (bs : List (BlockInfo H)) (l : List (BlockInfo H)) : Nat :=
  (l.map (metric bs)).foldl max 0

/-- The candidates for 𝐁^♭ (GP §19): the hashes of the acceptable blocks of the store that maximise
    m, in store order. The paper sets no tie-break (note v0.8.1-A24), so all are returned. -/
def bestHeads (r : AuditReading) (bs : List (BlockInfo H)) (fin : H) : List H :=
  let acc := bs.filter (acceptable r bs fin)
  let M := maxMetric bs acc
  (acc.filter fun b => metric bs b = M).map (·.hash)

/-- One best head: the first of `bestHeads` in store order (a model choice; the paper sets no
    tie-break, note v0.8.1-A24), `none` when no block is acceptable. -/
def bestHead? (r : AuditReading) (bs : List (BlockInfo H)) (fin : H) : Option H :=
  (bestHeads r bs fin).head?

end JAM.BestChain
