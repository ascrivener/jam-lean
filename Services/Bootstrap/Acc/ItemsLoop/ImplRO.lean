import Services.Bootstrap.Acc.ItemsLoop.Inv
import Services.Bootstrap.Acc.Handlers.Dispatch
import Services.Bootstrap.Acc.Impl.Loop

/-!
# The read-only data along an `Impl` (R2)

`Impl.keepRO`: every state a post-condition of `Impl` (under `accContractS`) is asked of keeps the octets
below 196608, their readability, and their non-writability, as at the start: each segment of the run is
under `KeepCtx` or `YIn` of the contract, both of which keep what is not writable (`keepCtx_keepsRO`,
`yIn_keepsRO`, `ro_keep`).

(`OpRO`, the operand arm's read-only facts, is in `Inv.lean`, a field of `ItemsInv`.)
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap Services.Bootstrap.Alloc Picoalloc Services.Bootstrap.Spec

/-- What `Impl.keepRO` keeps: the octets below 196608, their access, not writable. -/
def LoKept (μ μ' : Memory) : Prop :=
  ∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a ∧ μ'.writable a = false

theorem LoKept.trans {μ μ' μ'' : Memory} (h1 : LoKept μ μ') (h2 : LoKept μ' μ'') : LoKept μ μ'' :=
  fun a ha => ⟨(h2 a ha).1.trans (h1 a ha).1, (h2 a ha).2.1.trans (h1 a ha).2.1, (h2 a ha).2.2⟩

/-- **`Impl` keeps the read-only data** (see the module doc). -/
theorem Impl.keepRO {p : ByteArray} {env : AccEnv} {pb : Nat} (hbd : heapBounds env.code = (48, pb))
    {Ab : St Stream → Prop} {α : Type} {Q : α → St Stream → Prop} :
    ∀ (prog : Prog AOp α) (s : St Stream), (∀ a, a < 196608 → s.μ.writable a = false) →
      Impl p (accContractS env) env Ab prog Q s →
      Impl p (accContractS env) env Ab prog (fun a s' => Q a s' ∧ LoKept s.μ s'.μ) s := by
  intro prog
  induction prog with
  | pure a =>
    intro s hw h
    rcases h with h | ⟨s', ⟨n, h1⟩, h2, h3⟩
    · exact .inl h
    · exact .inr ⟨s', ⟨n, h1⟩, h2, h3, ro_keep (keepCtx_keepsRO env hbd) h1 hw⟩
  | panic => intro s _ h; exact h
  | call op k ih =>
    intro s hw h
    unfold Impl at h ⊢
    rcases h with h | ⟨s₁, ⟨n₁, h1⟩, h2, h3⟩
    · exact .inl h
    have k1 := ro_keep (keepCtx_keepsRO env hbd) h1 hw
    refine .inr ⟨s₁, ⟨n₁, h1⟩, h2, ?_⟩
    revert h3
    cases ASem.step env op s.c with
    | some bc =>
      intro h3
      rcases h3 with h3 | ⟨s₂, ⟨n₂, g1⟩, g2, g3⟩
      · exact .inl h3
      · have k2 := ro_keep (yIn_keepsRO env hbd _ _) g1 (fun a ha => (k1 a ha).2.2)
        have k12 : LoKept s.μ s₂.μ := LoKept.trans k1 k2
        refine .inr ⟨s₂, ⟨n₂, g1⟩, g2, ?_⟩
        exact Impl.mono_post (fun _ _ ⟨hq, hk⟩ => ⟨hq, LoKept.trans k12 hk⟩) _ _
          (ih bc.1 s₂ (fun a ha => (k12 a ha).2.2) g3)
    | none => exact id

end Services.Bootstrap.Acc
