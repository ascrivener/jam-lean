import Services.Bootstrap.Acc.Impl.Prefix
import Services.Bootstrap.Acc.Impl.ContractS
import Services.Bootstrap.Acc.Checkpoint
import PVM.Theorems.Invocation
import JAM.Theorems.HostGas

/-!
# When Ψ_M runs out of gas

If Ψ_M (with Ψ_A's handler) ends in ∞, the context it returns has the y of a context that a run
under `accContractS` reaches at a host call, for some answer stream (`psiM_oog_pre`). Ψ_A then
reports that y (GP eq. `accinvocation`).

Two facts give this:
- a host call that runs out of gas keeps y (`accHostFn_oog_snd`: at `checkpoint` it keeps the whole
  context; elsewhere `accHostFn_ctx_snd`);
- the continuing host calls before it are steps of `accContractS`, as in `FreeRunH.toS`.
-/

namespace Services.Bootstrap.Acc

open PVM JAM

/-- A host call that runs out of gas keeps y. -/
theorem accHostFn_oog_snd (env : AccEnv) (n : Nat) (g : UInt64) (ω : Regs) (μ : Memory) (x : AccCtx)
    (h : (accHostFn env n g ω μ x).status = .oog) : (accHostFn env n g ω μ x).ctx.2 = x.2 := by
  rcases accHostFn_ctx_snd env n g ω μ x with e | ⟨rfl, -⟩
  · exact e
  · simp only [accHostFn] at h ⊢
    rw [dispatch_checkpoint] at h ⊢
    split at h
    · rename_i hg; rw [if_pos hg]
    · simp at h

/-- **Ψ_H\* out of gas**: its context has the y of a prefix of a run under `accContractS`. -/
theorem psiHStar_oog_pre (env : AccEnv) (p : ByteArray) :
    ∀ (m i : Nat) (gas : UInt64) (ch : Bool) (ω : Regs) (μ : Memory) (x : AccCtx),
      runMeasure p i gas ch < m → (psiHStar p i gas ch ω μ (accHostFn env) x).status = .oog →
      ∃ (f : Stream) (c₀ : AccCtx), Pre p (accContractS env) ⟨i, ω, μ, x, f⟩ c₀ ∧
        c₀.2 = (psiHStar p i gas ch ω μ (accHostFn env) x).ctx.2 := by
  have hf := accHostFn_gasNonIncreasing env
  intro m
  induction m with
  | zero => intros; omega
  | succ m ih =>
    intro i gas ch ω μ x hm hoog
    rw [psiHStar_eq p i gas ch ω μ _ hf x] at hoog ⊢
    dsimp only at hoog ⊢
    generalize hr : psi p i gas ch ω μ = r at hoog ⊢
    cases hst : r.status <;> simp only [hst] at hoog ⊢
    case host h =>
      have hps : (psi p i gas ch ω μ).status = .host h := by rw [hr, hst]
      obtain ⟨e, hrun, hpc⟩ := psi_freeRun (by rw [hps]; simp)
      rw [hr, hst] at hrun hpc
      simp [exitPcOf] at hpc
      generalize hy : accHostFn env h.toNat r.gas r.regs r.mem x = y at hoog ⊢
      cases hys : y.status <;> simp only [hys] at hoog ⊢
      case cont =>
        have hlt : runMeasure p (blobNext p r.pc) y.gas r.charged < m := by
          have h1 := psi_host_measure hps
          rw [hr] at h1
          have h2 := runMeasure_mono_gas p (blobNext p r.pc) r.charged
            (hy ▸ hf h.toNat r.gas r.regs r.mem x)
          omega
        obtain ⟨f', c₀, hpre, hc⟩ := ih _ _ _ _ _ _ hlt hoog
        rw [hpc] at hpre
        by_cases hgf : AccGasFreeId h.toNat
        · refine ⟨f', c₀, .host (c'' := y.ctx) (q'' := f') hrun
            (.inl ⟨hgf, by simp [hys], rfl, r.gas, ?_⟩) hpre, hc⟩
          rw [hy]; cases y; simp_all
        · have h018 : h.toNat = 0 ∨ h.toNat = 18 := by unfold AccGasFreeId at hgf; omega
          rcases gasCk_outcomeS env h018 r.gas r.regs r.mem x with ho | ⟨hs, hmem, hx, v, hv⟩
          · rw [hy, hys] at ho; cases ho
          · rw [hy] at hs hmem hx hv
            refine ⟨Stream.cons v f', c₀, .host (c'' := y.ctx) (q'' := f') hrun
              (.inr ⟨h018, rfl, hmem, hx, (Stream.tail_cons v f').symm, ?_⟩) hpre, hc⟩
            rw [hv]; simp [Stream.cons]
      case oog =>
        refine ⟨fun _ => 0, x, .here _, ?_⟩
        have := accHostFn_oog_snd env h.toNat r.gas r.regs r.mem x (by rw [hy, hys])
        rw [hy] at this
        exact this.symm
      all_goals simp [HostStatus.toStatus] at hoog
    case oog => exact ⟨fun _ => 0, x, .here _, rfl⟩
    all_goals exact absurd hoog (by simp)

/-- **Ψ_M out of gas**: Y succeeds, and the context it returns has the y of a prefix of a run under
    `accContractS` from Y's initial state. -/
theorem psiM_oog_pre (b : ByteArray) (i : Nat) (gas : UInt64) (a : ByteArray) (x : AccCtx) (env : AccEnv)
    (hoog : (psiM b i gas a (accHostFn env) x).2.1 = .oog) :
    ∃ p ω μ, standardInit b a = some (p, ω, μ) ∧ ∃ (f : Stream) (c₀ : AccCtx),
      Pre p (accContractS env) ⟨i, ω, μ, x, f⟩ c₀ ∧ c₀.2 = (psiM b i gas a (accHostFn env) x).2.2.2 := by
  unfold psiM at hoog ⊢
  split at hoog
  · cases hoog
  · rename_i p ω μ hY
    refine ⟨p, ω, μ, hY, ?_⟩
    simp only [invocationResult] at hoog ⊢
    generalize hr : psiH p i gas ω μ (accHostFn env) x = r at hoog ⊢
    have hs : r.status = .oog := by
      cases h : r.status <;> first | rfl | (simp [h] at hoog; done) |
        (simp only [h] at hoog; split at hoog <;> cases hoog)
    simp only [hs]
    rw [← hr]
    exact psiHStar_oog_pre env p _ i gas false ω μ x (Nat.lt_succ_self _) (by rw [← hr] at hs; exact hs)

end Services.Bootstrap.Acc
