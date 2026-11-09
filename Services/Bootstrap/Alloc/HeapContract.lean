import Services.Bootstrap.Alloc.Pages
import JAM.Theorems.GrowHeap
import JAM.Theorems.KeepRO

/-!
# What the allocator's proofs need of a host

The allocator's runs (`alloc`, `realloc`, `dealloc` and the decoders built on them) make one kind of
host call, `grow_heap` (Ω_♊, GP Appendix B). Their proofs need two facts about the family of host
contracts `rel cap` they run under, for code whose heap is pages a … pb:
- `grow`: `rel cap` allows a `grow_heap` call whose cost 275 + 121 (t − h) fits in `cap`, with
  Ω_♊'s outcome (the new top t in ω₇, pages a … t writable);
- `keep`: every continuing call `rel cap` allows keeps the page entries outside 48 … pb and every
  octet that is not writable;
- `le`: a call `rel hostCostMax` allows, `rel cap` allows too, for any larger cap.

`HeapHost X` bundles the code, the contracts and these two facts. `refineHeap env` is the
refine contract `refineContractK · env` (Ψ_R's dispatcher); `Acc.accHeapHost env` is the accumulate
contract (Ψ_A's F). `HeapHost.growHeapK`, `HeapHost.pagesOut` and `HeapHost.keepRO` are the
host-generic forms of `FreeStepsH.growHeapK`, `FreeStepsH.pagesOut` and `FreeStepsH.keepRO`, with
the same arguments.
-/

namespace Services.Bootstrap.Alloc

open PVM JAM

/-- **A host fit for the allocator** (see the module doc): code, a contract for each cap, and the
    `grow_heap` and keep facts. -/
structure HeapHost (X : Type) where
  code : ByteArray
  rel : Nat → HostRel X
  grow : ∀ (cap : Nat), cap < 2 ^ 64 → ∀ (a pb : Nat), heapBounds code = (a, pb) →
    ∀ (ω : Regs) (μ : Memory) (x : X) (h : Nat), HeapPages μ a pb h → a ≤ h → h ≤ pb →
    Constants.CgasGeminiconst + (growTop (reg ω 7) h pb - h) * Constants.CgasGeminilinear ≤ cap →
    rel cap 1 ω μ x .cont (setR7 ω (growTop (reg ω 7) h pb))
      (μ.setPages a (growTop (reg ω 7) h pb - a) (some .write)) x
  keep : ∀ (cap pb : Nat), heapBounds code = (48, pb) →
    ∀ (h : Nat) (ω : Regs) (μ : Memory) (x : X) (ω' : Regs) (μ' : Memory) (x' : X),
    rel cap h ω μ x .cont ω' μ' x' →
    PagesOut 48 pb μ μ' ∧ ∀ b, b < two32 → μ.writable b = false → μ'.read b = μ.read b
  le : ∀ (cap : Nat), hostCostMax ≤ cap → cap < 2 ^ 64 →
    ∀ (h : Nat) (ω : Regs) (μ : Memory) (x : X) (ω' : Regs) (μ' : Memory) (x' : X),
    rel hostCostMax h ω μ x .cont ω' μ' x' → rel cap h ω μ x .cont ω' μ' x'

/-- **The refine contract is a host fit for the allocator**: `refineContractK cap env` for each cap. -/
def refineHeap (env : RefineHost.Env) : HeapHost RefineCtx where
  code := env.code
  rel cap := refineContractK cap env
  grow cap hcap a pb hbd ω μ x h hp hah hhb hcost := by
    refine ⟨by unfold GasFreeId; decide, by decide, ?_⟩
    simp only [toHostFn, RefineHost.dispatch, hostGrowHeap, growHeapCore_eq ω μ env.code hbd hp hah hhb,
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
  keep cap pb hbd h ω μ x ω' μ' x' hr :=
    ⟨refineContractK_pagesOut hbd hr, (refineContractK_keep hbd hr).2⟩
  le cap hc hcap h ω μ x ω' μ' x' hr := refineContract_le hc hcap env hr

namespace HeapHost

variable {X : Type}

/-- **A `grow_heap` step** under a host fit for the allocator (`FreeStepsH.growHeapK`'s
    host-generic form, with the same arguments). -/
theorem growHeapK (cap : Nat) (hcap : cap < 2 ^ 64) (env : HeapHost X)
    {p : ByteArray} {P : Program} {i n : Nat}
    {ω : Regs} {μ : Memory} {x : X} {a b h : Nat} (t : Nat)
    {i'' : Nat} {ω'' : Regs} {μ'' : Memory} {x'' : X} {k : Nat}
    (hd : deblob p i = some P ∧ P.decode i = some (.oneImm .ecalli 1) ∧ P.next i = n ∧
      P.blockCost (P.blockStartOf i) ≤ stepCostCap)
    (hb : heapBounds env.code = (a, b)) (hp : HeapPages μ a b h) (hah : a ≤ h) (hhb : h ≤ b)
    (_hbs : b < 2 ^ 32) (ht : growTop (reg ω 7) h b = t)
    (hcost : Constants.CgasGeminiconst + (t - h) * Constants.CgasGeminilinear ≤ cap)
    (rest : FreeStepsH p (env.rel cap) n (setR7 ω t)
      (μ.setPages a (t - a) (some .write)) x i'' ω'' μ'' x'' k) :
    FreeStepsH p (env.rel cap) i ω μ x i'' ω'' μ'' x'' (k + 1) := by
  subst ht
  exact FreeStepsH.host_decode hd (env.grow cap hcap a b hb ω μ x h hp hah hhb hcost) rest

/-- **A run keeps every page outside the heap's** 48 … pb (`FreeStepsH.pagesOut`'s host-generic
    form, with the same arguments). -/
theorem pagesOut {p : ByteArray} {cap : Nat} {env : HeapHost X} {pb : Nat}
    (hbd : heapBounds env.code = (48, pb)) {i : Nat} {ω : Regs} {μ : Memory} {x : X}
    {i' : Nat} {ω' : Regs} {μ' : Memory} {x' : X} {n : Nat}
    (h : FreeStepsH p (env.rel cap) i ω μ x i' ω' μ' x' n) : PagesOut 48 pb μ μ' := by
  induction h with
  | refl => exact PagesOut.refl _ _ _
  | pad _ ih => exact ih
  | next hn _ _ ih =>
    obtain ⟨P, -, hs⟩ := hn
    exact (PagesOut.of_eq (freeStep_pages hs)).trans ih
  | host _ _ _ hr _ ih => exact (env.keep cap pb hbd _ _ _ _ _ _ _ hr).1.trans ih

/-- **A run keeps what is not writable** outside the heap (`FreeStepsH.keepRO`'s host-generic
    form, with the same arguments). -/
theorem keepRO {p : ByteArray} {cap : Nat} {env : HeapHost X} {pb : Nat}
    (hbd : heapBounds env.code = (48, pb)) {i i' n : Nat} {ω ω' : Regs} {μ μ' : Memory} {x x' : X}
    (run : FreeStepsH p (env.rel cap) i ω μ x i' ω' μ' x' n) :
    (∀ q, (q < 48 ∨ pb ≤ q) → μ'.pages.get? q = μ.pages.get? q) ∧
      ∀ b, b < two32 → (b / pageSize < 48 ∨ pb ≤ b / pageSize) → μ.writable b = false →
        μ'.read b = μ.read b := by
  induction run with
  | refl => exact ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  | pad _ ih => exact ih
  | next hn _ _ ih =>
    obtain ⟨P, -, hs⟩ := hn
    obtain ⟨hp, hk⟩ := P.freeStep_keep hs
    refine ⟨fun q hq => by rw [ih.1 q hq, hp], fun b hb hq hw => ?_⟩
    have hw2 : _ := hw
    unfold Memory.writable at hw2
    rw [ih.2 b hb hq (by unfold Memory.writable; rw [hp]; exact hw2), hk b hb hw]
  | host _ _ _ hr _ ih =>
    obtain ⟨hp, hk⟩ := env.keep cap pb hbd _ _ _ _ _ _ _ hr
    refine ⟨fun q hq => by rw [ih.1 q hq, hp q hq], fun b hb hq hw => ?_⟩
    have hw2 : _ := hw
    unfold Memory.writable at hw2
    rw [ih.2 b hb hq (by unfold Memory.writable; rw [hp _ hq]; exact hw2), hk b hb hw]

end HeapHost

end Services.Bootstrap.Alloc
