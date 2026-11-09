import Services.Bootstrap.Alloc.Dealloc

/-!
# Writes inside an allocated block keep the allocator's state

`Rep μ s` reads the allocator's fields (from `A0`) and the first 16 octets of every chunk's header.
Chunks tile the heap without overlap (`Tiles.disjoint`), so a write that stays inside one chunk's
data, from 16 octets past its start to its end, or above 2^31, keeps `Rep` (`Rep.congr_data`). And
`alloc` keeps every allocated chunk (`alloc_keeps_used`, from `alloc_chunks`): a block the decoder
writes into stays allocated while other elements allocate.
-/

namespace Services.Bootstrap.Decode.HeapFrame

open PVM Picoalloc Services.Bootstrap.Alloc

/-- Distinct chunks of a tiling do not overlap. -/
theorem Tiles.disjoint {a limit : Nat} {cs : List Chunk} (h : Tiles a limit cs) :
    ∀ c ∈ cs, ∀ d ∈ cs, c ≠ d → c.addr + 32 * c.size ≤ d.addr ∨ d.addr + 32 * d.size ≤ c.addr := by
  induction cs generalizing a with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨h1, h2, h3⟩ := h
    have hlt := h3.mem_lt
    intro c hc d hd hcd
    rcases List.mem_cons.mp hc with rfl | hc' <;> rcases List.mem_cons.mp hd with rfl | hd'
    · exact absurd rfl hcd
    · have := hlt d hd'; omega
    · have := hlt c hc'; omega
    · exact ih h3 c hc' d hd' hcd

/-- **Writes inside a chunk's data keep `Rep`**: memory unchanged below 2^31 outside the octets from
    16 past chunk c's start to its end. -/
theorem Rep.congr_data {μ μ' : Memory} {s : State} {c : Chunk} (h : Rep μ s) (hwf : WF s)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hc : c ∈ chunks s)
    (wf : ∀ a, a < 2147483648 → (a < c.addr + 16 ∨ c.addr + 32 * c.size ≤ a) → μ'.read a = μ.read a) :
    Rep μ' s := by
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hmem : ∀ d ∈ chunks s, s.base ≤ d.addr ∧ d.addr + 32 * d.size ≤ s.top ∧ 0 < d.size :=
    ht.mem_lt
  have hcc := hmem c hc
  -- a chunk's header octets are outside c's data
  have hdr : ∀ d ∈ chunks s, ∀ j, j < 16 → (d.addr + j < c.addr + 16 ∨ c.addr + 32 * c.size ≤ d.addr + j) := by
    intro d hd j hj
    by_cases e : d = c
    · subst e; omega
    · have := hmem d hd
      rcases Tiles.disjoint ht d hd c hc e with h' | h' <;> omega
  have keep : ∀ d ∈ chunks s, ∀ k n, k + n ≤ 16 → rdN μ' (d.addr + k) n = rdN μ (d.addr + k) n := by
    intro d hd k n hkn
    have := hmem d hd
    exact rdN_frame fun j hj => by
      rw [show d.addr + k + j = d.addr + (k + j) by omega]
      exact wf _ (by omega) (hdr d hd (k + j) (by omega))
  refine ⟨fun b hb => ?_, fun q hq => ?_, ?_, ?_, ?_, fun d hd => ?_, fun d hd => ?_, fun d hd _ => ?_,
    fun d hd _ => ?_⟩
  · rw [← h.heads b hb]; unfold A0; unfold binCount at hb
    exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · rw [← h.sec q hq]; unfold A0; exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · rw [← h.pri]; unfold A0; exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · rw [← h.base]; unfold A0; exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · rw [← h.alloc]; unfold A0; exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · rw [← h.prev d hd]; exact keep d hd 0 4 (by omega)
  · rw [← h.size d hd]; exact keep d hd 4 4 (by omega)
  · rw [← h.next d hd ‹_›]; exact keep d hd 8 4 (by omega)
  · rw [← h.prevL d hd ‹_›]; exact keep d hd 12 4 (by omega)

/-- **`alloc` keeps every allocated chunk.** -/
theorem alloc_keeps_used {grow : Grow} {hb r p : Nat} {s s' : State} (hwf : WF s)
    (h : alloc grow hb 1 r s = some (p, s')) : ∀ c ∈ chunks s, c.used = true → c ∈ chunks s' := by
  obtain ⟨pre, post, S, e, -, e'⟩ := alloc_chunks hwf h
  intro c hc hu
  rw [e] at hc; rw [e']
  rcases List.mem_append.mp hc with hc | hc
  · exact List.mem_append_left _ hc
  · rcases List.mem_cons.mp hc with rfl | hc
    · simp at hu
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _ hc))

end Services.Bootstrap.Decode.HeapFrame
