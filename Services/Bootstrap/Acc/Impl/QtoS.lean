import Services.Bootstrap.Acc.Impl.ContractS
import Services.Bootstrap.Acc.ContractQ

/-!
# From Handlers A's answer lists to answer streams

`accContractQ` (ContractQ.lean) carries the answers of `gas` (0) and `checkpoint` (18) as a finite
list; `accContractS` as a stream. A list qs followed by any stream g is a stream, `qs ++ₛ g`, and a
step under `accContractQ` from (x, qs) to (x′, qs′) is a step under `accContractS` from
(x, qs ++ₛ g) to (x′, qs′ ++ₛ g) (`accContractQ_S`); so are runs (`FreeStepsH.qToS`).
-/

namespace Services.Bootstrap.Acc

open PVM JAM

/-- The list qs, then the stream g. -/
def Stream.append (qs : List Nat) (g : Stream) : Stream :=
  fun n => if h : n < qs.length then qs[n] else g (n - qs.length)

@[inherit_doc] infixr:67 " ++ₛ " => Stream.append

theorem Stream.append_cons (v : Nat) (qs : List Nat) (g : Stream) :
    (v :: qs) ++ₛ g = Stream.cons v (qs ++ₛ g) := by
  funext n
  unfold Stream.append Stream.cons
  cases n with
  | zero => simp
  | succ n => simp [Nat.succ_lt_succ_iff]

/-- **A step under `accContractQ` is a step under `accContractS`**, with the list's answers then g. -/
theorem accContractQ_S (env : AccEnv) (g : Stream) {h : Nat} {ω : Regs} {μ : Memory} {xq : AccCtxQ}
    {s : PVM.HostStatus} {ω' : Regs} {μ' : Memory} {xq' : AccCtxQ}
    (hq : accContractQ env h ω μ xq s ω' μ' xq') :
    accContractS env h ω μ (xq.1, xq.2 ++ₛ g) s ω' μ' (xq'.1, xq'.2 ++ₛ g) := by
  rcases hq with ⟨hh, hs, hq, hg⟩ | ⟨h018, hs, hm, hx, v, hv, hω⟩
  · exact .inl ⟨hh, hs, by simp only [hq], hg⟩
  · refine .inr ⟨h018, hs, hm, hx, ?_, ?_⟩
    · simp only [hv, Stream.append_cons, Stream.tail_cons]
    · rw [hω, hv, Stream.append_cons]; rfl

/-- **A run under `accContractQ` is a run under `accContractS`**, for the list's answers then any g. -/
theorem FreeStepsH.qToS {p : ByteArray} {env : AccEnv} (g : Stream) {i : Nat} {ω : Regs} {μ : Memory}
    {xq : AccCtxQ} {i' : Nat} {ω' : Regs} {μ' : Memory} {xq' : AccCtxQ} {n : Nat}
    (run : FreeStepsH p (accContractQ env) i ω μ xq i' ω' μ' xq' n) :
    FreeStepsH p (accContractS env) i ω μ (xq.1, xq.2 ++ₛ g) i' ω' μ' (xq'.1, xq'.2 ++ₛ g) n := by
  induction run with
  | refl => exact .refl
  | pad _ ih => exact .pad ih
  | next hn hc _ ih => exact .next hn hc ih
  | host hP hc hst hr _ ih => exact .host hP hc hst (accContractQ_S env g hr) ih

end Services.Bootstrap.Acc
