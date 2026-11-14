import JAM.Theorems.RefineContract
import PVM.Theorems.InitMem

/-!
# Page access outside the heap is kept

Every PVM instruction leaves the page table as it was: its memory is μ or a `writeN` of μ
(`exec_pages`, GP Appendix A, §A.5). Under `refineContractK`, the only host calls are `grow_heap`,
`fetch` and unknown ids (GP Appendix B). `fetch` only writes octets, an unknown id changes nothing,
and `grow_heap` sets pages 48 … t with t at most the heap's bound pb. So any run of a summary under
`refineContractK` keeps every page entry outside 48 … pb (`FreeStepsH.pagesOut`). In particular
readability and writability are kept below 196608 and from 4096·pb up (`PagesOut.readable`).

This is the page frame of the allocator's theorems (`alloc_wrap_refines*`, `realloc_wrap_cases*`),
and of every other summary run under the refine contract.
-/

namespace Services.Bootstrap.Alloc

open PVM JAM

/-- The page entries outside the pages lo … hi − 1 are kept. -/
def PagesOut (lo hi : Nat) (μ μ' : Memory) : Prop :=
  ∀ q, (q < lo ∨ hi ≤ q) → μ'.pages.get? q = μ.pages.get? q

theorem PagesOut.refl (lo hi : Nat) (μ : Memory) : PagesOut lo hi μ μ := fun _ _ => rfl

theorem PagesOut.trans {lo hi : Nat} {μ μ1 μ2 : Memory} (h1 : PagesOut lo hi μ μ1)
    (h2 : PagesOut lo hi μ1 μ2) : PagesOut lo hi μ μ2 := fun q hq => (h2 q hq).trans (h1 q hq)

theorem PagesOut.of_eq {lo hi : Nat} {μ μ' : Memory} (h : μ'.pages = μ.pages) : PagesOut lo hi μ μ' :=
  fun q _ => by rw [h]

/-- Readability outside the heap's pages is kept. -/
theorem PagesOut.readable {lo hi : Nat} {μ μ' : Memory} (h : PagesOut lo hi μ μ') {a : Nat}
    (ha : a < 4096 * lo ∨ 4096 * hi ≤ a) : μ'.readable a = μ.readable a := by
  unfold Memory.readable
  rw [h (a / pageSize) (by unfold pageSize; omega)]

/-- Writability outside the heap's pages is kept. -/
theorem PagesOut.writable {lo hi : Nat} {μ μ' : Memory} (h : PagesOut lo hi μ μ') {a : Nat}
    (ha : a < 4096 * lo ∨ 4096 * hi ≤ a) : μ'.writable a = μ.writable a := by
  unfold Memory.writable
  rw [h (a / pageSize) (by unfold pageSize; omega)]

/-- **An instruction keeps the page table** (GP §A.5): its memory is μ or a `writeN` of μ. -/
theorem exec_pages (P : Program) (i : Nat) (ins : Instr) (ω : Regs) (μ : Memory) :
    (P.exec i ins ω μ).mem.pages = μ.pages := by
  unfold Program.exec
  split <;> (try split) <;> simp [Memory.writeN_pages]

theorem freeStep_pages {P : Program} {i : Nat} {ω : Regs} {μ : Memory} {s : Status} {i' : Nat}
    {ω' : Regs} {μ' : Memory} (h : P.freeStep i ω μ = (s, i', ω', μ')) : μ'.pages = μ.pages := by
  unfold Program.freeStep Program.finalState at h
  split at h
  · cases h; rfl
  · dsimp only at h
    split at h
    · cases h; rfl
    · cases h; rfl
    · cases h; exact exec_pages _ _ _ _ _

/-- `writeValue` (`fetch`'s tail) writes octets only. -/
theorem writeValue_pages {X : Type} (out : HostOut X) (v : Except Unit (Option (List UInt8))) (o f z : Nat) :
    (writeValue out v o f z).mem.pages = out.mem.pages := by
  unfold writeValue
  dsimp only
  rcases v with _ | (_ | _) <;> simp only <;> (try split) <;> simp [Memory.writeN_pages]

/-- `grow_heap`, `fetch` and unknown ids keep every page outside 48 … pb, for a heap bounded by
    pb pages. -/
theorem refineContractK_pagesOut {cap : Nat} {env : RefineHost.Env} {pb : Nat}
    (hbd : heapBounds env.code = (48, pb)) {h : Nat} {ω : Regs} {μ : Memory} {x : RefineCtx}
    {ω' : Regs} {μ' : Memory} {x' : RefineCtx} (hR : refineContractK cap env h ω μ x .cont ω' μ' x') :
    PagesOut 48 pb μ μ' := by
  obtain ⟨hid, -, heq⟩ := hR
  unfold toHostFn at heq
  dsimp only at heq
  have hm := congrArg (fun o => o.mem) heq
  have hs := congrArg (fun o => o.status) heq
  dsimp only at hm hs
  generalize (UInt64.ofNat cap).toNat = g at hm hs
  subst hm
  intro q hq
  rcases hid with rfl | rfl | ⟨h3, h8⟩ | hlt
  · -- grow_heap
    simp only [RefineHost.dispatch] at hs ⊢
    unfold hostGrowHeap at hs ⊢
    unfold growHeapCore at hs ⊢
    rw [hbd] at hs ⊢
    dsimp only at hs ⊢
    generalize hcc : (List.range (pb - 48)).countP (fun k => μ.pages.get? (48 + k) == some .write) = c at hs ⊢
    have hc : c ≤ pb - 48 := by
      rw [← hcc]
      have := List.countP_le_length (p := fun k => μ.pages.get? (48 + k) == some .write) (l := List.range (pb - 48))
      simpa using this
    rw [Memory.setPages_get?]
    by_cases h1 : reg ω 7 ≤ 48 + c ∨ reg ω 7 > pb
    · simp only [h1, true_or, ↓reduceIte] at hs ⊢
      rw [if_neg (by omega)]
    · simp only [h1, ↓reduceIte] at hs ⊢
      by_cases h2 : g < Constants.CgasGeminiconst + (reg ω 7 - (48 + c)) * Constants.CgasGeminilinear
      · simp only [h2, ↓reduceIte] at hs
        exact absurd hs (by decide)
      · simp only [h2, ↓reduceIte]
        rw [if_neg (by omega)]
  · -- fetch
    simp only [RefineHost.dispatch]
    unfold hostFetch charged
    dsimp only
    split <;> (split <;> simp [writeValue_pages])
  · rcases (show h = 7 ∨ h = 8 ∨ (3 ≤ h ∧ h ≤ 6) by omega) with rfl | rfl | h36
    · -- historical_lookup
      simp only [RefineHost.dispatch]
      unfold RefineHost.historicalLookup charged
      dsimp only
      split <;> simp [writeValue_pages]
    · -- export
      simp only [RefineHost.dispatch]
      unfold RefineHost.exportSeg charged
      dsimp only
      split
      · rfl
      · split
        · rfl
        · split <;> rfl
    · have hu : RefineHost.dispatch env h g ω μ x = RefineHost.unknown g ω μ x := by
        unfold RefineHost.dispatch; split <;> first | omega | rfl
      rw [hu]
      rfl
  · -- an unknown id
    have hu : RefineHost.dispatch env h g ω μ x = RefineHost.unknown g ω μ x := by
      unfold RefineHost.dispatch; split <;> first | omega | rfl
    rw [hu]
    rfl

/-- **A run under the refine contract keeps every page outside the heap's** 48 … pb. -/
theorem FreeStepsH.pagesOut {p : ByteArray} {cap : Nat} {env : RefineHost.Env} {pb : Nat}
    (hbd : heapBounds env.code = (48, pb)) {i : Nat} {ω : Regs} {μ : Memory} {x : RefineCtx}
    {i' : Nat} {ω' : Regs} {μ' : Memory} {x' : RefineCtx} {n : Nat}
    (h : FreeStepsH p (refineContractK cap env) i ω μ x i' ω' μ' x' n) : PagesOut 48 pb μ μ' := by
  induction h with
  | refl => exact PagesOut.refl _ _ _
  | pad _ ih => exact ih
  | next hn _ _ ih =>
    obtain ⟨P, -, hs⟩ := hn
    exact (PagesOut.of_eq (freeStep_pages hs)).trans ih
  | host _ _ _ hR _ ih => exact (refineContractK_pagesOut hbd hR).trans ih

end Services.Bootstrap.Alloc
