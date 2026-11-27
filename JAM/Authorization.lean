import JAM.Params

/-!
# Authorization (GP v0.8.1 §8, `sec:authorization`)

The authorizer pool $\alpha$ and queue $\phi$: each core's pool $\alpha[c]$ holds at most $\mathsf{O}$ authorizer hashes, and
each block it drops the authorizer used by that core's guarantee, if any, and takes the next one
from the queue $\phi'[c]$, which is set by accumulation.
-/

namespace JAM

/-- $\mathbf{s} \ominus \{v\}$: $\mathbf{s}$ without its left-most element equal to $v$ (GP §3, "sequence subtraction"). -/
def seqMinusLeft {α : Type} [BEq α] : List α → α → List α
  | [], _ => []
  | x :: xs, v => if x == v then xs else x :: seqMinusLeft xs v

/-- $F(c)$ (GP §8): $\alpha[c] \ominus \{(g_w)_a\}$ for the guarantee $g \in \mathbf{E}_G$ on core $c$, and $\alpha[c]$ if there is
    none. The paper binds $g$ only in the condition; we read the authorizer as that guarantee's.
    $\mathbf{E}_G$ has at most one guarantee per core (GP eq. `guaranteesextrinsic`); with more, each one's
    authorizer is removed in turn. -/
def poolUsed (pool : List (List UInt8)) (c : Nat) (used : List (Nat × List UInt8)) : List (List UInt8) :=
  (used.filter (·.1 == c)).foldl (fun p (_, a) => seqMinusLeft p a) pool

/-- $\alpha'[c] = \overleftarrow{F(c) \frown \phi'[c][\mathbf{H}_t]^{\circlearrowleft}}^{\mathsf{O}}$ (GP §8): keep the last $\mathsf{O}$ of $F(c)$ with the queue's entry for
    slot $\mathbf{H}_t$ (indices into $\phi'[c]$ are cyclic) appended. -/
def poolNext (params : Params) (pool queue : List (List UInt8)) (c slot : Nat)
    (used : List (Nat × List UInt8)) : List (List UInt8) :=
  let next := if queue.isEmpty then [] else [queue.getD (slot % queue.length) []]
  let p := poolUsed pool c used ++ next
  p.drop (p.length - params.authPoolSize)

/-- The authorization transition $\alpha \mapsto \alpha'$ (GP §8) for the block with timeslot $\mathbf{H}_t$, given the
    posterior queue $\phi'$ and, for each guarantee $g \in \mathbf{E}_G$, its core and authorizer hash
    $((g_w)_c, (g_w)_a)$. -/
def authorizations (params : Params) (pools queues : List (List (List UInt8))) (slot : Nat)
    (used : List (Nat × List UInt8)) : List (List (List UInt8)) :=
  (List.range params.coreCount).map fun c =>
    poolNext params (pools.getD c []) (queues.getD c []) c slot used

end JAM
