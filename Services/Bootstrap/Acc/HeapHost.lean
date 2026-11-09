import Services.Bootstrap.Acc.Contract
import Services.Bootstrap.Alloc.HeapContract

/-!
# The accumulate contract's `grow_heap` calls: a host fit for the allocator

The allocator's runs make one kind of host call, `grow_heap` (Ω_♊). `accGrowK cap env` is the
accumulate contract `accContractK cap env` (Ψ_A's handler F, GP v0.8.0 eq. `accinvocation`)
restricted to that id. `accHeapHost env` is it as a `HeapHost`, so the allocator's and the heap
decoders' host-generic theorems (`…G`) hold for it, and `FreeStepsH.ofAccGrow` lifts their runs
to `accContractK cap env`. The three facts:
- `grow`: a `grow_heap` call whose cost fits in the cap has Ω_♊'s outcome;
- `keep`: Ω_♊ sets heap pages only, so it keeps the page table outside the heap and every octet;
- `le`: a `grow_heap` call that does not run out of gas with `hostCostMax` does not with any
  larger cap either, and does the same.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap.Alloc

/-- **The accumulate contract's `grow_heap` calls**: `accContractK cap env` at id 1 only. -/
def accGrowK (cap : Nat) (env : AccEnv) : HostRel AccCtx :=
  fun h ω μ x s ω' μ' x' => h = 1 ∧ accContractK cap env h ω μ x s ω' μ' x'

/-- **A run under `accGrowK` is a run under the accumulate contract.** -/
theorem FreeStepsH.ofAccGrow {p : ByteArray} {cap : Nat} {env : AccEnv} {i : Nat} {ω : Regs}
    {μ : Memory} {x : AccCtx} {i' : Nat} {ω' : Regs} {μ' : Memory} {x' : AccCtx} {n : Nat}
    (run : FreeStepsH p (accGrowK cap env) i ω μ x i' ω' μ' x' n) :
    FreeStepsH p (accContractK cap env) i ω μ x i' ω' μ' x' n :=
  run.weaken fun _ _ _ _ _ _ _ hr => hr.2

/-- A `grow_heap` call that does not run out of gas with g₁ does not with any g₂ ≥ g₁. -/
theorem growHeap_noOog_mono (env : AccEnv) (ω : Regs) (μ : Memory) (c : AccCtx) {g₁ g₂ : Nat}
    (h12 : g₁ ≤ g₂) (h₁ : (AccHost.dispatch env 1 g₁ ω μ c).status ≠ .oog) :
    (AccHost.dispatch env 1 g₂ ω μ c).status ≠ .oog := by
  simp only [AccHost.dispatch] at *
  unfold hostGrowHeap at *
  generalize growHeapCore ω μ env.code = q at *
  obtain ⟨a, b, hp, w⟩ := q
  dsimp only at *
  by_cases hc : w ≤ hp ∨ w > b
  · simp [hc]
  · simp only [hc, ↓reduceIte] at h₁ ⊢
    by_cases c1 : g₁ < Constants.CgasGeminiconst + (w - hp) * Constants.CgasGeminilinear
    · simp [c1] at h₁
    · rw [if_neg (by omega)]; simp

/-- **A larger cap allows more `grow_heap` calls**: one `accGrowK hostCostMax` allows,
    `accGrowK cap` allows too, for any cap ≥ `hostCostMax`. -/
theorem accGrow_le {cap : Nat} (hc : hostCostMax ≤ cap) (hcap : cap < 2 ^ 64) (env : AccEnv)
    {h : Nat} {ω : Regs} {μ : Memory} {x : AccCtx} {ω' : Regs} {μ' : Memory} {x' : AccCtx}
    (hr : accGrowK hostCostMax env h ω μ x .cont ω' μ' x') : accGrowK cap env h ω μ x .cont ω' μ' x' := by
  obtain ⟨rfl, hh, hs, he⟩ := hr
  refine ⟨rfl, hh, hs, ?_⟩
  simp only [accHostFn, HostResult.mk.injEq] at he ⊢
  obtain ⟨e1, -, e3, e4, e5⟩ := he
  have hm : (UInt64.ofNat hostCostMax).toNat = hostCostMax := by decide
  have hm2 : (UInt64.ofNat cap).toNat = cap := UInt64.toNat_ofNat_of_lt' hcap
  rw [hm] at e1 e3 e4 e5
  rw [hm2]
  have n₁ : (AccHost.dispatch env 1 hostCostMax ω μ x).status ≠ .oog := by rw [e1]; exact hs
  have n₂ := growHeap_noOog_mono env ω μ x hc n₁
  obtain ⟨a, b, c, d⟩ := AccHost.dispatch_sameButGas env hh ω μ x n₁ n₂
  exact ⟨by rw [← a, e1], trivial, by rw [← b, e3], by rw [← c, e4], by rw [← d, e5]⟩

/-- **A continuing `grow_heap` call keeps what is not writable**: it changes no page outside the
    heap's 48 … pb and no octet. -/
theorem accGrowK_keep {cap : Nat} {env : AccEnv} {pb : Nat}
    (hbd : heapBounds env.code = (48, pb)) {h : Nat} {ω ω' : Regs} {μ μ' : Memory} {x x' : AccCtx}
    (hr : accGrowK cap env h ω μ x .cont ω' μ' x') :
    PagesOut 48 pb μ μ' ∧ ∀ b, b < two32 → μ.writable b = false → μ'.read b = μ.read b := by
  obtain ⟨rfl, -, -, he⟩ := hr
  simp only [accHostFn, HostResult.mk.injEq] at he
  obtain ⟨hs, -, -, hm, -⟩ := he
  subst hm
  generalize (UInt64.ofNat cap).toNat = g at hs ⊢
  simp only [AccHost.dispatch, hostGrowHeap, growHeapCore, hbd] at hs ⊢
  generalize hC : List.countP (fun k => μ.pages.get? (48 + k) == some Access.write) (List.range (pb - 48)) = C
    at hs ⊢
  have hCle : C ≤ pb - 48 := by
    rw [← hC]; exact Nat.le_trans List.countP_le_length (by simp)
  by_cases c1 : reg ω 7 ≤ 48 + C ∨ reg ω 7 > pb
  · rw [if_pos c1] at hs ⊢
    exact ⟨fun q hq => Memory.setPages_get_off _ _ _ _ _ (by dsimp only; omega), fun b _ _ => rfl⟩
  · rw [if_neg c1] at hs ⊢
    by_cases c2 : g < Constants.CgasGeminiconst + (reg ω 7 - (48 + C)) * Constants.CgasGeminilinear
    · rw [if_pos c2] at hs; simp at hs
    · rw [if_neg c2]
      exact ⟨fun q hq => Memory.setPages_get_off _ _ _ _ _ (by dsimp only; omega), fun b _ _ => rfl⟩

/-- **The accumulate contract's `grow_heap` calls are a host fit for the allocator**:
    `accGrowK cap env` for each cap. -/
def accHeapHost (env : AccEnv) : HeapHost AccCtx where
  code := env.code
  rel cap := accGrowK cap env
  grow cap hcap a pb hbd ω μ x h hp hah hhb hcost := by
    refine ⟨rfl, by unfold AccGasFreeId; decide, by decide, ?_⟩
    simp only [accHostFn, AccHost.dispatch, hostGrowHeap, growHeapCore_eq ω μ env.code hbd hp hah hhb,
      growTop] at hcost ⊢
    have hw := (ω.get 7).toNat_lt
    simp only [reg] at hw hcost ⊢
    by_cases hc : (ω.get 7).toNat ≤ h ∨ (ω.get 7).toNat > pb
    · simp [hc]
    · simp only [hc, ↓reduceIte] at hcost
      have : ¬ cap % 18446744073709551616 <
          Constants.CgasGeminiconst + ((ω.get 7).toNat - h) * Constants.CgasGeminilinear := by
        rw [Nat.mod_eq_of_lt hcap]
        omega
      simp [hc, this]
  keep cap pb hbd h ω μ x ω' μ' x' hr := accGrowK_keep hbd hr
  le cap hc hcap h ω μ x ω' μ' x' hr := accGrow_le hc hcap env hr

end Services.Bootstrap.Acc
