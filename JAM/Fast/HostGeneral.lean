import JAM.Host.General

/-!
# Fast compiled `grow_heap`, proved equal to `JAM.growHeapCore`

Moved out of the spec file `JAM/Host/General.lean`. `hostGrowHeap` is restated
(`hostGrowHeap_eq_hostGrowHeapFast`, `rfl`) so that its compiled code uses `growHeapCoreFast`;
its callers (the refine and accumulate dispatchers) import this module.
-/

namespace JAM

open PVM

/-! ### Fast compiled form of `growHeapCore`

`growHeapCore` counts the W pages by looking up every page index in ℕ_{a…b}, up to about 10^6 map
lookups per `grow_heap`. `growHeapCoreFast` counts them from the page map's own entries instead.
They are proved equal and registered with `@[csimp]`, so compiled code uses the fast form while the
kernel and every theorem see `growHeapCore`. -/

/-- The number of pages in ℕ_{a…b} that `pages` marks W, counted from the map's own entries. -/
def countWritable (pages : Std.ExtTreeMap Nat Access) (a b : Nat) : Nat :=
  pages.foldl (fun n k v => if a ≤ k ∧ k < b ∧ v = .write then n + 1 else n) 0

private theorem foldl_countP_succ {α : Type} (p : α → Bool) (l : List α) (n : Nat) :
    l.foldl (fun n x => if p x then n + 1 else n) n = n + l.countP p := by
  induction l generalizing n with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih, List.countP_cons]
    cases p x <;> simp <;> omega

theorem countWritable_eq (pages : Std.ExtTreeMap Nat Access) (a b : Nat) :
    countWritable pages a b
      = (List.range (b - a)).countP fun k => pages.get? (a + k) == some .write := by
  have h1 : countWritable pages a b = pages.toList.countP
      (fun e => decide (a ≤ e.1 ∧ e.1 < b ∧ e.2 = .write)) := by
    unfold countWritable
    rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
    have := foldl_countP_succ (fun e : Nat × Access => decide (a ≤ e.1 ∧ e.1 < b ∧ e.2 = .write))
      pages.toList 0
    simp only [decide_eq_true_eq, Nat.zero_add] at this
    exact this
  have h2 : (List.range (b - a)).countP (fun k => pages.get? (a + k) == some .write)
      = (List.range' a (b - a)).countP (fun k => pages.get? k == some .write) := by
    rw [List.range'_eq_map_range, List.countP_map]
    rfl
  rw [h1, h2, List.countP_eq_length_filter, List.countP_eq_length_filter, ← List.length_map
    (f := Prod.fst)]
  apply List.Perm.length_eq
  apply (List.perm_ext_iff_of_nodup _ _).2
  · intro k
    simp only [List.mem_map, List.mem_filter, List.mem_range', decide_eq_true_eq,
      Std.ExtTreeMap.get?_eq_getElem?, beq_iff_eq, Nat.one_mul]
    constructor
    · rintro ⟨⟨k', v⟩, ⟨hm, hk, hb, hv⟩, rfl⟩
      subst hv
      exact ⟨⟨k' - a, by omega, by omega⟩, Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.1 hm⟩
    · rintro ⟨⟨i, hi, rfl⟩, hm⟩
      exact ⟨⟨a + i, .write⟩, ⟨Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.2 hm, by omega, by omega, rfl⟩, rfl⟩
  · apply List.Pairwise.map _ _ (List.Pairwise.filter _ Std.ExtTreeMap.distinct_keys_toList)
    intro x y h hxy
    exact h (by rw [hxy]; exact Nat.compare_eq_eq.2 rfl)
  · exact (List.nodup_range' ).filter _

/-- `growHeapCore`, counting the W pages with `countWritable`. -/
def growHeapCoreFast (ω : Regs) (μ : Memory) (jam : ByteArray) : Nat × Nat × Nat × Nat :=
  let (a, b) := heapBounds jam
  (a, b, a + countWritable μ.pages a b, reg ω 7)

@[csimp] theorem growHeapCore_eq_growHeapCoreFast : @growHeapCore = @growHeapCoreFast := by
  funext ω μ jam
  simp only [growHeapCore, growHeapCoreFast, countWritable_eq]

/-- Ω_♊ (`hostGrowHeap`), restated so that its compiled code uses `growHeapCoreFast`. -/
def hostGrowHeapFast {X : Type} (gas : Nat) (ω : Regs) (μ : Memory) (jam : ByteArray) (x : X) :
    HostOut X :=
  let (a, b, h, w) := growHeapCore ω μ jam
  let r7 := if w ≤ h ∨ w > b then h else w
  let g := Constants.CgasGeminiconst + (r7 - h) * Constants.CgasGeminilinear
  charged g gas ω μ x fun out =>
    { out with regs := setR7 ω r7, mem := μ.setPages a (r7 - a) (some .write) }

@[csimp] theorem hostGrowHeap_eq_hostGrowHeapFast : @hostGrowHeap = @hostGrowHeapFast := rfl

end JAM
