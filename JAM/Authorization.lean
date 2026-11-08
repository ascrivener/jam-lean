import JAM.Params

/-!
# Authorization (GP v0.8.0 §8, `sec:authorization`)

The authorizer pool α and queue φ: each core's pool α[c] holds at most 𝖮 authorizer hashes, and
each block it drops the authorizer used by that core's guarantee, if any, and takes the next one
from the queue φ'[c], which is set by accumulation.
-/

namespace JAM

/-- **s** ⊖ {v}: **s** without its left-most element equal to v (GP §3, "sequence subtraction"). -/
def seqMinusLeft {α : Type} [BEq α] : List α → α → List α
  | [], _ => []
  | x :: xs, v => if x == v then xs else x :: seqMinusLeft xs v

/-- F(c) (GP §8): α[c] ⊖ {(g_w)_a} for the guarantee g ∈ E_G on core c, and α[c] if there is
    none. The paper binds g only in the condition; we read the authorizer as that guarantee's.
    E_G has at most one guarantee per core (GP eq. `guaranteesextrinsic`); with more, each one's
    authorizer is removed in turn. -/
def poolUsed (pool : List (List UInt8)) (c : Nat) (used : List (Nat × List UInt8)) : List (List UInt8) :=
  (used.filter (·.1 == c)).foldl (fun p (_, a) => seqMinusLeft p a) pool

/-- α'[c] = ←(F(c) ⌢ φ'[c][H_t]↺)^𝖮 (GP §8): keep the last 𝖮 of F(c) with the queue's entry for
    slot H_t (indices into φ'[c] are cyclic) appended. -/
def poolNext (params : Params) (pool queue : List (List UInt8)) (c slot : Nat)
    (used : List (Nat × List UInt8)) : List (List UInt8) :=
  let next := if queue.isEmpty then [] else [queue.getD (slot % queue.length) []]
  let p := poolUsed pool c used ++ next
  p.drop (p.length - params.authPoolSize)

/-- The authorization transition α ↦ α' (GP §8) for the block with timeslot H_t, given the
    posterior queue φ' and, for each guarantee g ∈ E_G, its core and authorizer hash
    ((g_w)_c, (g_w)_a). -/
def authorizations (params : Params) (pools queues : List (List (List UInt8))) (slot : Nat)
    (used : List (Nat × List UInt8)) : List (List (List UInt8)) :=
  (List.range params.coreCount).map fun c =>
    poolNext params (pools.getD c []) (queues.getD c []) c slot used

end JAM
