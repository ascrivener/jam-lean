import Services.Picoalloc.Walk

/-!
# Chunk alignment

The allocator's chunks tile [base, top) in 32-octet units from a 32-aligned base (`WF`, `TilesOk`), so
every chunk's address, and its data address (32 octets on), is a multiple of 32, in particular 8-aligned.
R5's entry uses it for the instructions buffer (`EntryHyp`).
-/

namespace Picoalloc

/-- In a tiling from a 32-aligned start, every chunk's address is 32-aligned. -/
theorem Tiles.addr_mod32 {a limit : Nat} {cs : List Chunk} (h : Tiles a limit cs) (ha : a % 32 = 0) :
    ∀ c ∈ cs, c.addr % 32 = 0 := by
  induction cs generalizing a with
  | nil => simp
  | cons d cs ih =>
    obtain ⟨h1, -, h3⟩ := h
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · omega
    · exact ih h3 (by omega) c hc

/-- **An allocated chunk's address is 32-aligned** in a well-formed state. -/
theorem chunk_addr_mod32 {s : State} (hwf : WF s) {c : Chunk} (hc : c ∈ chunks s) : c.addr % 32 = 0 := by
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  exact Tiles.addr_mod32 ht hwf.2.1 c hc

/-- **A chunk's data address is 8-aligned** in a well-formed state. -/
theorem chunk_data_mod8 {s : State} (hwf : WF s) {c : Chunk} (hc : c ∈ chunks s) : (c.addr + 32) % 8 = 0 := by
  have := chunk_addr_mod32 hwf hc
  omega

end Picoalloc
