import PVM.Logic.Go

/-!
# The allocator's writable memory

A standard program's memory (GP Appendix A, eq. `conditions`) is writable only in its read-write
region, which `grow_heap` extends, and its stack. The read-only data, the arguments and
everything unmapped are not writable. The allocator's proofs therefore assume only:

- the heap region, from 196608 (bootstrap's read-write region, which holds the allocator's state)
  up to `HT`;
- the stack, from `S0` up to `S1`.

Each step proof says which addresses it touches lie in these regions. A step that only reads and
writes leaves every page's writability as it was (`∀ a, μ'.writable a = μ.writable a`), so the
regions carry over (`WrAt.of_eq`).
-/

namespace Services.Bootstrap.Alloc

open PVM

/-- The allocator's writable memory: the heap region from 196608 below `HT`, and the stack from
    `S0` below `S1`. -/
abbrev WrAt (μ : Memory) (HT S0 S1 : Nat) : Prop :=
  ∀ a, (196608 ≤ a ∧ a < HT) ∨ (S0 ≤ a ∧ a < S1) → μ.writable a = true

/-- The same regions, readable. -/
abbrev RdAt (μ : Memory) (HT S0 S1 : Nat) : Prop :=
  ∀ a, (196608 ≤ a ∧ a < HT) ∨ (S0 ≤ a ∧ a < S1) → μ.readable a = true

theorem WrAt.rd {μ : Memory} {HT S0 S1 : Nat} (h : WrAt μ HT S0 S1) : RdAt μ HT S0 S1 :=
  fun a ha => Memory.readable_of_writable (h a ha)

/-- Writes keep the pages, so the writable regions. -/
theorem WrAt.of_pages {μ μ' : Memory} {HT S0 S1 : Nat} (h : WrAt μ HT S0 S1) (hp : μ'.pages = μ.pages) :
    WrAt μ' HT S0 S1 := fun a ha => by
  have := h a ha
  unfold Memory.writable at this ⊢
  rw [hp]; exact this

theorem RdAt.of_pages {μ μ' : Memory} {HT S0 S1 : Nat} (h : RdAt μ HT S0 S1) (hp : μ'.pages = μ.pages) :
    RdAt μ' HT S0 S1 := fun a ha => by
  have := h a ha
  unfold Memory.readable at this ⊢
  rw [hp]; exact this

/-- A step that leaves every page's writability carries the regions. -/
theorem WrAt.of_eq {μ μ' : Memory} {HT S0 S1 : Nat} (h : WrAt μ HT S0 S1)
    (he : ∀ a, μ'.writable a = μ.writable a) : WrAt μ' HT S0 S1 := fun a ha => by rw [he]; exact h a ha

/-- Smaller regions. -/
theorem WrAt.mono {μ : Memory} {HT S0 S1 HT' S0' S1' : Nat} (h : WrAt μ HT S0 S1) (hH : HT' ≤ HT)
    (h0 : S0 ≤ S0') (h1 : S1' ≤ S1) : WrAt μ HT' S0' S1' := fun a ha => h a (by omega)

end Services.Bootstrap.Alloc
