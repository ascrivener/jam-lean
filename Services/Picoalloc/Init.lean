import Services.Picoalloc.Realloc

/-!
# `init`

From the allocator's zeroed static state, `init` makes one free chunk spanning the address space:
the heap invariant holds from the start.
-/

namespace Picoalloc

/-- **`init` makes a well-formed heap**: from a zeroed allocator, one free chunk of `maxSize` units
    at the heap base. -/
theorem init_wf {grow : Grow} {hb : Nat} {s s' : State} (hb0 : hb ≠ 0) (hbal : hb % 32 = 0)
    (hfit : hb + 32 * maxSize < 2 ^ 32) (hs0 : s.base = 0) (hheads : ∀ b, s.heads b = 0)
    (hsec : ∀ p, s.secondary p = 0) (hpri : s.primary = 0) (h : init grow hb s = some s') :
    chunks s' = [⟨hb, maxSize, false⟩] ∧ WF s' := by
  unfold init at h
  simp only [hs0, ne_eq, not_true_eq_false, ↓reduceIte] at h
  split at h
  · simp at h
  simp only [Option.some.injEq] at h
  have hbin : binDown maxSize < binCount := toBin_lt false (Nat.min_le_right _ _)
  have hmax : 0 < maxSize := by rw [maxSize_val]; decide
  -- the new state's fields
  have e_base : s'.base = hb := by rw [← h]; rfl
  have e_alloc : s'.allocated = 1 := by rw [← h]; rfl
  have e_hdr : ∀ x, s'.hdr x = if x = hb then ⟨0, sizeWord maxSize false, 0, 0⟩ else s.hdr x := by
    intro x; rw [← h]; show upd _ _ _ x = _; unfold upd; rfl
  have e_heads : ∀ b, s'.heads b = if b = binDown maxSize then hb else 0 := by
    intro b; rw [← h]; show upd _ _ _ b = _; unfold upd
    by_cases hbb : b = binDown maxSize
    · rw [if_pos hbb, if_pos hbb]
    · rw [if_neg hbb, if_neg hbb]; exact hheads b
  have e_bits : BitsOk s'.secondary s'.primary s'.heads := by
    have z : BitsOk s.secondary s.primary s.heads := by
      refine ⟨fun b _ => ?_, fun p _ => ?_, fun p _ => ?_, ?_⟩
      · rw [hsec, hheads]; simp
      · rw [hsec, hpri]; simp
      · rw [hsec]; decide
      · rw [hpri]; decide
    have := setBit_ok (s := { s with base := hb, allocated := 1 }) (hs := s'.heads) hbin z
      (fun b hb' => by rw [e_heads, if_neg hb']; exact (hheads b).symm) (by rw [e_heads, if_pos rfl]; exact hb0)
    rw [← h] at this ⊢
    exact this
  have htop : s'.top = hb + 32 * maxSize := by unfold State.top; rw [e_base]
  have hchunks : chunks s' = [⟨hb, maxSize, false⟩] := by
    apply chunks_eq
    · rw [e_base, htop]; exact ⟨rfl, hmax, rfl⟩
    · intro c hc
      simp only [List.mem_singleton] at hc
      subst hc
      rw [Chunk.addr_mk', e_hdr, if_pos rfl]
  refine ⟨hchunks, by rw [e_base]; exact hb0, by rw [e_base]; exact hbal, by rw [htop]; exact hfit, ?_, ?_, ?_, ?_, ?_⟩
  · unfold TilesOk; rw [hchunks, e_base, htop]; exact ⟨rfl, hmax, rfl⟩
  · unfold CoalOk; rw [hchunks]; trivial
  · unfold PrevsOk; rw [hchunks]; trivial
  · unfold ListsOk'; rw [hchunks]
    obtain ⟨b1, b2, b3, b4⟩ := e_bits
    refine ⟨fun b hb' => ?_, b1, b2, b3, b4⟩
    by_cases hbb : b = binDown maxSize
    · subst hbb
      refine ⟨[hb], ⟨by rw [e_heads, if_pos rfl], hb0, ?_⟩, ⟨?_, trivial⟩, by simp, fun a => ?_⟩
      · show (s'.hdr hb).next = 0
        rw [e_hdr, if_pos rfl]
      · rw [e_hdr, if_pos rfl]
      · simp only [List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false]
        constructor
        · rintro rfl; exact ⟨_, rfl, rfl, rfl, rfl⟩
        · rintro ⟨c, rfl, h1, -, -⟩; exact h1.symm
    · refine ⟨[], by show s'.heads b = 0; rw [e_heads, if_neg hbb], trivial, by simp, fun a => ?_⟩
      simp only [List.not_mem_nil, false_iff, List.mem_singleton]
      rintro ⟨c, rfl, -, -, h3⟩
      exact hbb h3.symm
  · unfold SpaceOk; rw [hchunks, e_base, e_alloc]
    intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    exact ⟨fun h => by simp at h, by simp only; omega⟩

theorem init_self {grow : Grow} {hb : Nat} {s : State} (h : s.base ≠ 0) : init grow hb s = some s := by
  unfold init; simp [h]

theorem alloc_after_init {grow : Grow} {hb r : Nat} {s s0 : State} (hi : init grow hb s = some s0)
    (h0 : s0.base ≠ 0) : alloc grow hb 1 r s = alloc grow hb 1 r s0 := by
  unfold alloc
  rw [hi, init_self h0]

/-- **The first `alloc`** on a zeroed allocator leaves a well-formed heap. -/
theorem alloc_wf_fresh {grow : Grow} {hb r p : Nat} {s s' : State} (hb0 : hb ≠ 0) (hbal : hb % 32 = 0)
    (hfit : hb + 32 * maxSize < 2 ^ 32) (hs0 : s.base = 0) (hheads : ∀ b, s.heads b = 0)
    (hsec : ∀ p, s.secondary p = 0) (hpri : s.primary = 0) (h : alloc grow hb 1 r s = some (p, s')) :
    WF s' := by
  cases hi : init grow hb s with
  | none =>
    unfold alloc at h
    simp [hi] at h
  | some s0 =>
    have hw0 := (init_wf hb0 hbal hfit hs0 hheads hsec hpri hi).2
    rw [alloc_after_init hi hw0.1] at h
    exact alloc_wf hw0 h

end Picoalloc
