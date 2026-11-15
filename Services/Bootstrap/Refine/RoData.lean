import Services.Bootstrap.Refine.PassLoop

/-!
# The read-only data, as the fmt summaries read it

`RoIs ro μ`: memory holds `ro` at the read-only data's start 65536, over its 11608 octets (65536 … 77144).
GP v0.8.0 Appendix A.7 (Y(p): the read-only data at Z_Z = 2^16). A refine run keeps it (`RoIs.keep`), since that
data is never writable (`HeapCtx`); so it holds at every fmt site once it holds at refine's start.
-/

namespace Services.Bootstrap.Refine.RoData

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Decode.HeapCtx

/-- Memory holds `ro` over the read-only data, 65536 … 77144 (GP v0.8.0 Appendix A.7). -/
def RoIs (ro : List UInt8) (μ : Memory) : Prop :=
  ∀ o l, o + l ≤ 11608 → μ.readN (65536 + o) l = (ro.drop o).take l

/-- Memory that agrees with μ below 2^31 holds the same read-only data. -/
theorem RoIs.congr {ro : List UInt8} {μ μ' : Memory} (h : RoIs ro μ)
    (hk : ∀ a l, a + l ≤ 2147483648 → μ'.readN a l = μ.readN a l) : RoIs ro μ' :=
  fun o l hol => by rw [hk _ _ (by omega)]; exact h o l hol

/-- A refine run keeps the read-only data. -/
theorem RoIs.keep {p : ByteArray} {cap0 : Nat} {env : RefineHost.Env} {pb S0 S1 : Nat} {μ μ' : Memory}
    {s : State} {i i' n : Nat} {ω ω' : Regs} {x x' : RefineCtx} {ro : List UInt8}
    (H : HeapCtx env pb S0 S1 μ s) (run : FreeStepsH p (refineContractK cap0 env) i ω μ x i' ω' μ' x' n)
    (h : RoIs ro μ) : RoIs ro μ' := fun o l hol => by
  obtain ⟨kp, kr⟩ := FreeStepsH.keepRO H.bd run
  rw [← h o l hol]
  exact Memory.readN_congr (fun j hj => kr _ (by unfold two32; omega) (Or.inl (by unfold pageSize; omega))
    (H.ro _ (by omega)))

/-- A refine run to a state with the allocator's context keeps the read-only data (the pages below 48 are
    not changed, and that context makes them not writable at the end, hence at the start). -/
theorem RoIs.keep0 {p : ByteArray} {cap0 : Nat} {env : RefineHost.Env} {pb S0 S1 : Nat} {μ μ' : Memory}
    {s : State} {i i' n : Nat} {ω ω' : Regs} {x x' : RefineCtx} {ro : List UInt8}
    (H : HeapCtx env pb S0 S1 μ' s) (run : FreeStepsH p (refineContractK cap0 env) i ω μ x i' ω' μ' x' n)
    (h : RoIs ro μ) : RoIs ro μ' := fun o l hol => by
  obtain ⟨kp, kr⟩ := FreeStepsH.keepRO H.bd run
  have hw : ∀ b, b < 196608 → μ.writable b = false := fun b hb => by
    have := H.ro b hb
    unfold Memory.writable at this ⊢
    rw [← kp _ (Or.inl (by unfold pageSize; omega))]; exact this
  rw [← h o l hol]
  exact Memory.readN_congr (fun j hj => kr _ (by unfold two32; omega) (Or.inl (by unfold pageSize; omega))
    (hw _ (by omega)))

end Services.Bootstrap.Refine.RoData
