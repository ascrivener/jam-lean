import JAM.Theorems.RefineContract

/-!
# `grow_heap` in gas-free runs

Ω_♊ counts the writable pages in ℕ_{a…b} to find the heap's top h. In a symbolic run the memory
is not a concrete page map, so we describe its heap pages instead: `HeapPages μ a b h` says the
writable pages in ℕ_{a…b} are exactly those below h. From it `growHeapCore_eq` gives Ω_♊'s top
without counting, and `FreeStepsH.growHeapK` takes a whole `grow_heap` step under
`refineContractK cap`, for a call whose cost fits in `cap` (`FreeStepsH.growHeap`: under
`refineContract`).
-/

namespace JAM

open PVM

/-- In ℕ_{a…b}, the writable pages of μ are exactly those below h. -/
def HeapPages (μ : Memory) (a b h : Nat) : Prop :=
  ∀ p, a ≤ p → p < b → (μ.pages.get? p == some .write) = decide (p < h)

theorem countP_range_lt (n m : Nat) :
    (List.range n).countP (fun k => decide (k < m)) = min m n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih]
    by_cases h : n < m
    · simp [h]; omega
    · simp [h]; omega

/-- **The heap top from `HeapPages`.** -/
theorem growHeapCore_eq (ω : Regs) (μ : Memory) (jam : ByteArray) {a b h : Nat}
    (hb : heapBounds jam = (a, b)) (hp : HeapPages μ a b h) (hah : a ≤ h) (hhb : h ≤ b) :
    growHeapCore ω μ jam = (a, b, h, reg ω 7) := by
  unfold growHeapCore
  rw [hb]
  dsimp only
  have : (List.range (b - a)).countP (fun k => μ.pages.get? (a + k) == some .write) =
      (List.range (b - a)).countP (fun k => decide (k < h - a)) := by
    apply List.countP_congr
    intro k hk
    simp only [List.mem_range] at hk
    rw [hp (a + k) (by omega) (by omega)]
    simp only [decide_eq_true_eq]
    omega
  rw [this]
  have hc := countP_range_lt (b - a) (h - a)
  rw [hc]
  simp only [Prod.mk.injEq, and_true, true_and]
  omega

/-- The new top Ω_♊ sets: h if ω_7 ≤ h or ω_7 > b, else ω_7. -/
def growTop (w h b : Nat) : Nat := if w ≤ h ∨ w > b then h else w

/-- **A `grow_heap` step**, under `refineContractK cap`: from a memory whose heap is described by
    `HeapPages`, the call continues with ω'_7 = the new top `t` and pages a … t made writable,
    provided its cost 275 + 121 (t − h) fits in `cap`. The new top is named by `t` so that the
    memory term stays concrete. -/
theorem FreeStepsH.growHeapK (cap : Nat) (hcap : cap < 2 ^ 64) (env : RefineHost.Env)
    {p : ByteArray} {P : Program} {i n : Nat}
    {ω : Regs} {μ : Memory} {x : RefineCtx} {a b h : Nat} (t : Nat)
    {i'' : Nat} {ω'' : Regs} {μ'' : Memory} {x'' : RefineCtx} {k : Nat}
    (hd : deblob p i = some P ∧ P.decode i = some (.oneImm .ecalli 1) ∧ P.next i = n ∧
      P.blockCost (P.blockStartOf i) ≤ stepCostCap)
    (hb : heapBounds env.code = (a, b)) (hp : HeapPages μ a b h) (hah : a ≤ h) (hhb : h ≤ b)
    (hbs : b < 2 ^ 32) (ht : growTop (reg ω 7) h b = t)
    (hcost : Constants.CgasGeminiconst + (t - h) * Constants.CgasGeminilinear ≤ cap)
    (rest : FreeStepsH p (refineContractK cap env) n (setR7 ω t)
      (μ.setPages a (t - a) (some .write)) x i'' ω'' μ'' x'' k) :
    FreeStepsH p (refineContractK cap env) i ω μ x i'' ω'' μ'' x'' (k + 1) := by
  subst ht
  apply FreeStepsH.host_decode hd _ rest
  refine ⟨by unfold GasFreeId; decide, by decide, ?_⟩
  simp only [toHostFn, RefineHost.dispatch, hostGrowHeap, growHeapCore_eq ω μ env.code hb hp hah hhb,
    growTop] at hcost ⊢
  have hw := (ω.get 7).toNat_lt
  simp only [reg] at hw hcost ⊢
  by_cases hc : (ω.get 7).toNat ≤ h ∨ (ω.get 7).toNat > b
  · simp [hc]
  · simp only [hc, ↓reduceIte] at hcost
    have : ¬ cap % 18446744073709551616 <
        Constants.CgasGeminiconst + ((ω.get 7).toNat - h) * Constants.CgasGeminilinear := by
      rw [Nat.mod_eq_of_lt hcap]
      omega
    simp [hc, this]

/-- **A `grow_heap` step**, under `refineContract`: `growHeapK` at `hostCostMax`, so at most 14
    pages a call. -/
theorem FreeStepsH.growHeap (env : RefineHost.Env) {p : ByteArray} {P : Program} {i n : Nat}
    {ω : Regs} {μ : Memory} {x : RefineCtx} {a b h : Nat} (t : Nat)
    {i'' : Nat} {ω'' : Regs} {μ'' : Memory} {x'' : RefineCtx} {k : Nat}
    (hd : deblob p i = some P ∧ P.decode i = some (.oneImm .ecalli 1) ∧ P.next i = n ∧
      P.blockCost (P.blockStartOf i) ≤ stepCostCap)
    (hb : heapBounds env.code = (a, b)) (hp : HeapPages μ a b h) (hah : a ≤ h) (hhb : h ≤ b)
    (hbs : b < 2 ^ 32) (ht : growTop (reg ω 7) h b = t)
    (hcost : Constants.CgasGeminiconst + (t - h) * Constants.CgasGeminilinear ≤ hostCostMax)
    (rest : FreeStepsH p (refineContract env) n (setR7 ω t)
      (μ.setPages a (t - a) (some .write)) x i'' ω'' μ'' x'' k) :
    FreeStepsH p (refineContract env) i ω μ x i'' ω'' μ'' x'' (k + 1) :=
  FreeStepsH.growHeapK hostCostMax (by decide) env t hd hb hp hah hhb hbs ht hcost rest

/-- Prove `HeapPages` of a memory built from a starting memory by writes and `setPages`, given
    the starting memory's `HeapPages` fact `h`. -/
macro "heap_pages" h:term : tactic => `(tactic| (
  intro q h1 h2
  have hq := $h q h1 h2
  try simp only [PVM.Memory.writeN_pages, PVM.Memory.setPages_get?]
  repeat' split
  all_goals (try simp only [hq]) <;> (try simp) <;> omega))

end JAM
