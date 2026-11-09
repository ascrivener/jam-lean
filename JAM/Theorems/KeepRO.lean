import JAM.Theorems.RefineContract
import JAM.Theorems.Confinement

/-!
# Gas-free runs keep what is not writable

A step that continues writes only octets it may write (GP §A.4: ε^μ is ▸ only if every index
written is in 𝕍*_μ), and of the refine host calls a gas-free run can make, `grow_heap` changes only
heap pages' access and `fetch` writes only a writable range. So a gas-free run under
`refineContractK` changes no octet that is not writable, on a page below the heap or above its
bound (`FreeStepsH.keepRO`): read-only data, for one, is never touched.
-/

namespace PVM

/-- A write of a list keeps every octet not among its indices. -/
theorem Memory.read_writeN_off (μ : Memory) (a : Nat) (bs : List UInt8) (b : Nat)
    (h : ∀ j, j < bs.length → (a + j) % two32 ≠ b % two32) : (μ.writeN a bs).read b = μ.read b := by
  induction bs generalizing μ a with
  | nil => rfl
  | cons c cs ih =>
    simp only [Memory.writeN]
    rw [ih _ _ (fun j hj => by have := h (j + 1) (by simp; omega); rwa [show a + 1 + j = a + (j + 1) by omega])]
    exact Memory.read_write_of_ne μ c (fun e => h 0 (by simp) (by simpa using e))

@[simp] theorem Memory.pages_writeN (μ : Memory) (a : Nat) (bs : List UInt8) : (μ.writeN a bs).pages = μ.pages := by
  induction bs generalizing μ a with
  | nil => rfl
  | cons c cs ih => simp only [Memory.writeN]; rw [ih]; rfl

/-- **An instruction's memory**: the same pages, and every octet off its writes as it was. -/
theorem Program.exec_mem (P : Program) (i : Nat) (ins : Instr) (ω : Regs) (μ : Memory) :
    (P.exec i ins ω μ).mem.pages = μ.pages ∧
      ∀ b, (∀ w ∈ (P.exec i ins ω μ).writes, w % two32 ≠ b % two32) → (P.exec i ins ω μ).mem.read b = μ.read b := by
  unfold Program.exec
  split <;> (try split) <;> (try split) <;>
    simp (config := { failIfUnchanged := false }) only [Memory.pages_writeN] <;>
    (try exact ⟨rfl, fun _ _ => rfl⟩) <;>
    (try simp) <;>
    (intro b hb; exact Memory.read_writeN_off _ _ _ _ (fun j hj => hb _ (by
      simp only [Num.length_encodeLE] at hj; simp only [Exec.indices, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)))

/-- **A continuing step keeps every octet that is not writable**, and the pages. -/
theorem Program.freeStep_keep (P : Program) {i i' : Nat} {ω ω' : Regs} {μ μ' : Memory}
    (h : P.freeStep i ω μ = (.cont, i', ω', μ')) :
    μ'.pages = μ.pages ∧ ∀ b, b < two32 → μ.writable b = false → μ'.read b = μ.read b := by
  unfold Program.freeStep Program.finalState at h
  generalize hm : P.exec i ((P.decode i).getD (.noArgs .trap)) ω μ = m at h
  have hx := P.exec_mem i ((P.decode i).getD (.noArgs .trap)) ω μ
  rw [hm] at hx
  simp only [ne_eq, not_true_eq_false, ↓reduceIte] at h
  split at h
  · simp at h
  · simp at h
  · rename_i hme
    simp only [Prod.mk.injEq] at h
    obtain ⟨-, -, -, rfl⟩ := h
    refine ⟨hx.1, fun b hb32 hb => hx.2 b fun w hw e => ?_⟩
    unfold memoryException at hme
    simp only at hme
    split at hme
    · rename_i hmin
      have hnil := List.min?_eq_none_iff.mp hmin
      have : w ∈ m.writes.filter (fun i => !μ.writable (i % two32)) := by
        rw [List.mem_filter]
        refine ⟨hw, ?_⟩
        rw [e, Nat.mod_eq_of_lt hb32, hb]; rfl
      rw [List.append_eq_nil_iff] at hnil
      rw [hnil.2] at this
      simp at this
    · split at hme <;> simp at hme

/-- `setPages` leaves every page outside its range. -/
theorem Memory.setPages_get_off (μ : Memory) (f c : Nat) (a : Access) (q : Nat)
    (hq : q < f ∨ f + c ≤ q) : (μ.setPages f c (some a)).pages.get? q = μ.pages.get? q := by
  unfold Memory.setPages
  simp only
  generalize μ.pages = m
  induction c generalizing m with
  | zero => rfl
  | succ c ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hne : f + c ≠ q := by omega
    rw [JAM.get?_insert_ne _ _ (Ne.symm hne)]
    exact ih (by omega) m

/-- A writable range's octets are writable, and below 2^32. -/
theorem Memory.rangeWritable_at (μ : Memory) {o l : Nat} (h : μ.rangeWritable o l = true) (j : Nat)
    (hj : j < l) : μ.writable (o + j) = true ∧ o + j < two32 := by
  unfold Memory.rangeWritable at h
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  rcases h with h | ⟨hl, hall⟩
  · omega
  have hps : pageSize = 4096 := rfl
  have := hall ((o + j) / pageSize - o / pageSize) (by rw [hps]; omega)
  refine ⟨?_, by unfold two32; omega⟩
  unfold Memory.writable at this ⊢
  rw [show (o / pageSize + ((o + j) / pageSize - o / pageSize)) * pageSize / pageSize = (o + j) / pageSize by
    rw [hps]; omega] at this
  exact this

end PVM

namespace JAM

open PVM

/-- `writeValue` that continues keeps the pages and every octet that is not writable. -/
theorem writeValue_keep {X : Type} (out : HostOut X) (v : Option (List UInt8)) (o f z : Nat)
    (hs : (writeValue out (.ok v) o f z).status = .cont) :
    (writeValue out (.ok v) o f z).mem.pages = out.mem.pages ∧
      ∀ b, b < two32 → out.mem.writable b = false → (writeValue out (.ok v) o f z).mem.read b = out.mem.read b := by
  unfold writeValue at hs ⊢
  simp only at hs ⊢
  generalize hl : min z ((match Except.ok (ε := Unit) v with | .ok (some v) => v.length | _ => 0) -
    min f (match Except.ok (ε := Unit) v with | .ok (some v) => v.length | _ => 0)) = l at hs ⊢
  by_cases hw : out.mem.rangeWritable o l = true
  · simp only [hw, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hs ⊢
    cases v with
    | none => exact ⟨rfl, fun _ _ _ => rfl⟩
    | some w =>
      simp only
      refine ⟨Memory.pages_writeN _ _ _, fun b hb hnw => Memory.read_writeN_off _ _ _ _ fun j hj e => ?_⟩
      have hjl : j < l := by
        rw [← hl]; simp only [List.length_take, List.length_drop] at hj ⊢; omega
      obtain ⟨hwr, hlt⟩ := out.mem.rangeWritable_at hw j hjl
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hb] at e
      rw [e, hnw] at hwr; exact absurd hwr (by simp)
  · simp only [Bool.not_eq_true] at hw
    simp [hw] at hs

/-- **A refine host call keeps what is not writable**: under `refineContractK`, a continuing call
    (`grow_heap`, `fetch` or an unknown id) changes no page outside the heap's 48 … pb and no octet
    that is not writable. -/
theorem refineContractK_keep {cap : Nat} {env : RefineHost.Env} {pb : Nat}
    (hbd : heapBounds env.code = (48, pb)) {h : Nat} {ω ω' : Regs} {μ μ' : Memory} {x x' : RefineCtx}
    (hr : refineContractK cap env h ω μ x .cont ω' μ' x') :
    (∀ q, (q < 48 ∨ pb ≤ q) → μ'.pages.get? q = μ.pages.get? q) ∧
      ∀ b, b < two32 → μ.writable b = false → μ'.read b = μ.read b := by
  obtain ⟨hg, -, he⟩ := hr
  simp only [toHostFn, HostResult.mk.injEq] at he
  obtain ⟨hs, -, -, hm, -⟩ := he
  subst hm
  rcases hg with rfl | rfl | hg
  · simp only [RefineHost.dispatch, hostGrowHeap, growHeapCore, hbd] at hs ⊢
    generalize hC : List.countP (fun k => μ.pages.get? (48 + k) == some Access.write) (List.range (pb - 48)) = C
      at hs ⊢
    have hCle : C ≤ pb - 48 := by
      rw [← hC]; exact Nat.le_trans List.countP_le_length (by simp)
    by_cases c1 : reg ω 7 ≤ 48 + C ∨ reg ω 7 > pb
    · rw [if_pos c1] at hs ⊢
      exact ⟨fun q hq => Memory.setPages_get_off _ _ _ _ _ (by dsimp only; omega), fun b _ _ => rfl⟩
    · rw [if_neg c1] at hs ⊢
      by_cases c2 : (UInt64.ofNat cap).toNat < Constants.CgasGeminiconst + (reg ω 7 - (48 + C)) * Constants.CgasGeminilinear
      · rw [if_pos c2] at hs; simp at hs
      · rw [if_neg c2]
        exact ⟨fun q hq => Memory.setPages_get_off _ _ _ _ _ (by dsimp only; omega), fun b _ _ => rfl⟩
  · simp only [RefineHost.dispatch, hostFetch, charged] at hs ⊢
    generalize Constants.CgasY (if reg ω 10 < 16 then some (reg ω 10) else none) = cg at hs ⊢
    by_cases hc : (UInt64.ofNat cap).toNat < cg.fst + memGas cg.snd (reg ω 9)
    · rw [if_pos hc] at hs; simp at hs
    · rw [if_neg hc] at hs ⊢
      exact (writeValue_keep _ _ _ _ _ hs).imp (fun e q _ => by rw [e]) id
  · have e : ∀ g, RefineHost.dispatch env h g ω μ x = RefineHost.unknown g ω μ x := fun g => by
      unfold RefineHost.dispatch
      split <;> first | omega | rfl
    rw [e]
    exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- **A gas-free refine run keeps what is not writable**: every page outside the heap's 48 … pb keeps
    its access, and every octet on such a page that is not writable keeps its value. Read-only data,
    for one, is never touched. -/
theorem FreeStepsH.keepRO {p : ByteArray} {cap : Nat} {env : RefineHost.Env} {pb : Nat}
    (hbd : heapBounds env.code = (48, pb)) {i i' n : Nat} {ω ω' : Regs} {μ μ' : Memory} {x x' : RefineCtx}
    (run : FreeStepsH p (refineContractK cap env) i ω μ x i' ω' μ' x' n) :
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
  | host _ _ _ hR _ ih =>
    obtain ⟨hp, hk⟩ := refineContractK_keep hbd hR
    refine ⟨fun q hq => by rw [ih.1 q hq, hp q hq], fun b hb hq hw => ?_⟩
    have hw2 : _ := hw
    unfold Memory.writable at hw2
    rw [ih.2 b hb hq (by unfold Memory.writable; rw [hp _ hq]; exact hw2), hk b hb hw]

end JAM
