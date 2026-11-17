import JAM.Theorems.KeepROAcc
import Services.Bootstrap.Acc.Impl.Impl
import Services.Bootstrap.Acc.Impl.ContractS

/-!
# Runs under `accContractS` keep what is not writable

`accContractS` keeps what is not writable off the heap's 48 … pb (`accContractS_keepsRO`): a step at a
gas-independent id is a model step (`accHostFn_keep`), and `gas` / `checkpoint` keep the memory. So
do `KeepCtx` and `YIn` of it, and their runs (`FreeStepsH.keepRO_of`): read-only data, below the heap,
reads the same throughout.
-/

namespace Services.Bootstrap.Acc

open PVM JAM

theorem accContractS_keepsRO (env : AccEnv) {pb : Nat} (hbd : heapBounds env.code = (48, pb)) :
    KeepsRO (accContractS env) 48 pb := by
  intro h ω μ xq ω' μ' xq' hr
  rcases hr with ⟨-, -, -, g, he⟩ | ⟨-, -, rfl, -, -, -⟩
  · have hs : (accHostFn env h g ω μ xq.1).status = .cont := by rw [he]
    have hm : (accHostFn env h g ω μ xq.1).mem = μ' := by rw [he]
    rw [← hm]
    exact accHostFn_keep env hbd h g ω μ xq.1 hs
  · exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem KeepsRO.mono {X : Type} {R R' : HostRel X} {lo hi : Nat} (h : KeepsRO R lo hi)
    (hR : ∀ h ω μ x s ω' μ' x', R' h ω μ x s ω' μ' x' → R h ω μ x s ω' μ' x') : KeepsRO R' lo hi :=
  fun a b c d e f g hr => h a b c d e f g (hR _ _ _ _ _ _ _ _ hr)

theorem keepCtx_keepsRO (env : AccEnv) {pb : Nat} (hbd : heapBounds env.code = (48, pb)) :
    KeepsRO (KeepCtx (accContractS env)) 48 pb :=
  KeepsRO.mono (accContractS_keepsRO env hbd) fun _ _ _ _ _ _ _ _ h => h.1

theorem yIn_keepsRO (env : AccEnv) {pb : Nat} (hbd : heapBounds env.code = (48, pb)) (a b : Implications) :
    KeepsRO (YIn (accContractS env) a b) 48 pb :=
  KeepsRO.mono (accContractS_keepsRO env hbd) fun _ _ _ _ _ _ _ _ h => h.1

end Services.Bootstrap.Acc
