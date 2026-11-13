import Services.Bootstrap.Acc.HeapHost
import Services.Bootstrap.Acc.Impl.Impl
import Services.Bootstrap.Acc.Impl.ContractS

/-!
# Allocator runs under the stream contract

The allocator's only host call is `grow_heap` (1, GP v0.8.0 Appendix B), which changes neither x nor
y. So a run under `accGrowK` (the relation `alloc_implZ_callG` and its kin are stated under) is a run
of `accContractS` that keeps the context and the answer stream (`FreeStepsH.growS`).
-/

namespace Services.Bootstrap.Acc

open PVM JAM

/-- `grow_heap` keeps the context. -/
theorem grow_ctx (env : AccEnv) (g : UInt64) (ω : Regs) (μ : Memory) (x : AccCtx) :
    (accHostFn env 1 g ω μ x).ctx = x := by
  simp only [accHostFn, AccHost.dispatch, hostGrowHeap]

/-- **An `accGrowK` step is a step of `accContractS` keeping the context and the stream.** -/
theorem accGrowK_S {cap : Nat} {env : AccEnv} {h : Nat} {ω : Regs} {μ : Memory} {x : AccCtx}
    {s : PVM.HostStatus} {ω' : Regs} {μ' : Memory} {x' : AccCtx} (f : Stream)
    (hs : accGrowK cap env h ω μ x s ω' μ' x') :
    x' = x ∧ KeepCtx (accContractS env) h ω μ (x, f) s ω' μ' (x', f) := by
  obtain ⟨rfl, hgf, hno, he⟩ := hs
  have hx : x' = x := by
    have := congrArg PVM.HostResult.ctx he
    rw [grow_ctx] at this
    exact this.symm
  subst hx
  exact ⟨rfl, .inl ⟨hgf, hno, rfl, UInt64.ofNat cap, he⟩, rfl⟩

/-- **A run under `accGrowK` is a run of `accContractS` keeping the context and the stream.** -/
theorem FreeStepsH.growS {p : ByteArray} {cap : Nat} {env : AccEnv} {i : Nat} {ω : Regs} {μ : Memory}
    {x : AccCtx} {i' : Nat} {ω' : Regs} {μ' : Memory} {x' : AccCtx} {n : Nat} (f : Stream)
    (run : FreeStepsH p (accGrowK cap env) i ω μ x i' ω' μ' x' n) :
    x' = x ∧ FreeStepsH p (KeepCtx (accContractS env)) i ω μ (x, f) i' ω' μ' (x, f) n := by
  induction run with
  | refl => exact ⟨rfl, .refl⟩
  | pad _ ih => exact ⟨ih.1, .pad ih.2⟩
  | next hn hc _ ih => exact ⟨ih.1, .next hn hc ih.2⟩
  | host hP hc hst hr _ ih =>
    obtain ⟨e, hk⟩ := accGrowK_S f hr
    subst e
    exact ⟨ih.1, .host hP hc hst hk ih.2⟩

/-- **A run under R is a run under R′ with the stream kept**, when every continuing R step is an R′
    step with the stream kept. -/
theorem FreeStepsH.pairS {p : ByteArray} {R : HostRel AccCtx} {R' : HostRel (AccCtx × Stream)} (f : Stream)
    (hR : ∀ h ω μ x ω' μ' x', R h ω μ x .cont ω' μ' x' → R' h ω μ (x, f) .cont ω' μ' (x', f))
    {i ω μ x i' ω' μ' x' n} (run : FreeStepsH p R i ω μ x i' ω' μ' x' n) :
    FreeStepsH p R' i ω μ (x, f) i' ω' μ' (x', f) n := by
  induction run with
  | refl => exact .refl
  | pad _ ih => exact .pad ih
  | next hn hc _ ih => exact .next hn hc ih
  | host hP hc hst hr _ ih => exact .host hP hc hst (hR _ _ _ _ _ _ _ hr) ih

end Services.Bootstrap.Acc
