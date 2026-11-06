import Services.Bootstrap.Alloc.Rep

/-!
# `register` against memory

The model's `register` field by field (`register_heads`, `register_sec`, …), and `register_rep`:
the memory the binary's `register_free_space` leaves (`reg_write`'s facts) holds the model's
result.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc

theorem register_heads {s : State} {n prev size : Nat} (hs : size ≠ 0) (b : Nat) :
    (register s n prev size).1.heads b = if b = binDown size then n else s.heads b := by
  unfold register
  simp only [hs, ↓reduceIte]
  split <;> simp [setBit, setHdr, upd]

theorem register_sec {s : State} {n prev size : Nat} (hs : size ≠ 0) :
    (register s n prev size).1.secondary = upd s.secondary (binDown size / 64)
      (s.secondary (binDown size / 64) ||| 2 ^ (binDown size % 64)) ∧
    (register s n prev size).1.primary = s.primary ||| 2 ^ (binDown size / 64) := by
  unfold register
  simp only [hs, ↓reduceIte]
  split <;> exact ⟨rfl, rfl⟩

theorem register_prevL {s : State} {n prev size x : Nat} (hs : size ≠ 0) (hx : x ≠ n) :
    ((register s n prev size).1.hdr x).prevL =
      if x = s.heads (binDown size) ∧ x ≠ 0 then n else (s.hdr x).prevL := by
  unfold register
  simp only [hs, ↓reduceIte, setBit_hdr]
  split
  · rename_i h0
    rw [setHdr_other hx]
    simp only [setHdr]
    split
    · rename_i h; exact absurd (h.1.trans h0) h.2
    · rfl
  · rename_i h0
    by_cases hh : x = s.heads (binDown size)
    · subst hh
      rw [setHdr_self, if_pos ⟨rfl, h0⟩]
    · rw [setHdr_other hh, setHdr_other hx, if_neg (fun h => hh h.1)]


/-- **`register` against memory**: if μ holds `s` at `H` and `F` (headers of chunks above the
    allocator, 16 octets apart from M and from the bin's old head), the memory the binary's
    `register_free_space` leaves (`reg_write`) holds `register s M pv size` at `H` and `F` and at
    M. -/
theorem register_rep {μ μ' : Memory} {s : State} {H F : Nat → Prop} {M pv size : Nat}
    (h : RepAt μ s H F) (hs : size ≠ 0) (hB : binDown size < binCount) (hMold : s.heads (binDown size) ≠ M)
    (w1 : rdN μ' (binDown size * 4 + 196792) 4 = M) (w2 : rdN μ' M 4 = pv)
    (w3 : rdN μ' (M + 4) 4 = 2 * size) (w4 : rdN μ' (M + 8) 4 = s.heads (binDown size))
    (w5 : rdN μ' (M + 12) 4 = 0)
    (w6 : s.heads (binDown size) ≠ 0 → rdN μ' (s.heads (binDown size) + 12) 4 = M)
    (w7 : rdN μ' (204984 + binDown size / 64 * 8 + 1544) 8 =
      rdN μ (204984 + binDown size / 64 * 8 + 1544) 8 ||| 2 ^ (binDown size % 64))
    (w8 : rdN μ' 206832 8 = rdN μ 206832 8 ||| 2 ^ (binDown size / 64))
    (wf : ∀ a, a < 4294967296 → (a < binDown size * 4 + 196792 ∨ binDown size * 4 + 196796 ≤ a) →
      (a < M ∨ M + 16 ≤ a) →
      (s.heads (binDown size) = 0 ∨ a < s.heads (binDown size) + 12 ∨ s.heads (binDown size) + 16 ≤ a) →
      (a < 204984 + binDown size / 64 * 8 + 1544 ∨ 204984 + binDown size / 64 * 8 + 1552 ≤ a) →
      (a < 206832 ∨ 206840 ≤ a) → μ'.read a = μ.read a)
    (hMa : 206864 ≤ M) (hM32 : M + 16 < 4294967296)
    (hold : s.heads (binDown size) ≠ 0 → 206864 ≤ s.heads (binDown size))
    (hHa : ∀ a, H a ∨ F a → 206864 ≤ a ∧ a + 16 < 4294967296 ∧ (a = M ∨ a + 16 ≤ M ∨ M + 16 ≤ a) ∧
      (s.heads (binDown size) = 0 ∨ a = s.heads (binDown size) ∨ a + 16 ≤ s.heads (binDown size) ∨
        s.heads (binDown size) + 16 ≤ a)) :
    RepAt μ' (register s M pv size).1 (fun a => H a ∨ a = M) (fun a => F a ∨ a = M) := by
  generalize hbin : binDown size = bin at *
  generalize hO : s.heads bin = old at *
  have hb38 : bin / 64 < 38 := by unfold binCount at hB; omega
  obtain ⟨hsec, hpri⟩ := register_sec (s := s) (n := M) (prev := pv) hs
  rw [hbin] at hsec hpri
  unfold binCount at hB
  have hbs : bin * 4 + 196792 < 206864 := by omega
  refine ⟨fun b hb => ?_, fun q hq => ?_, ?_, ?_, ?_, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_,
    fun a ha => ?_⟩
  · -- heads
    rw [register_heads hs, hbin]
    unfold A0 at *
    by_cases hbb : b = bin
    · subst hbb; rw [if_pos rfl, show 196792 + 4 * b = b * 4 + 196792 by omega, w1]
    · rw [if_neg hbb, ← h.heads b hb]
      unfold A0
      unfold binCount at hb
      exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · -- secondary words
    rw [hsec]
    unfold A0 at *
    by_cases hqq : q = bin / 64
    · subst hqq
      rw [upd_self, show 196792 + 9736 + 8 * (bin / 64) = 204984 + bin / 64 * 8 + 1544 by omega, w7,
        show 204984 + bin / 64 * 8 + 1544 = 196792 + 9736 + 8 * (bin / 64) by omega]
      have := h.sec _ hb38
      unfold A0 at this
      rw [this]
    · rw [upd_ne _ _ hqq, ← h.sec q hq]
      unfold A0
      exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · -- primary
    rw [hpri]
    have := h.pri
    unfold A0 at *
    rw [show 196792 + 10040 = 206832 from rfl] at this ⊢
    rw [w8, this]
  · -- base
    rw [register_base, ← h.base]
    unfold A0
    exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · -- allocated
    rw [register_allocated, ← h.alloc]
    unfold A0
    exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · -- prev
    rcases ha with ha | rfl
    · obtain ⟨a1, a2, a3, a4⟩ := hHa a (Or.inl ha)
      by_cases haM : a = M
      · subst haM
        rw [w2, register_hdr_self hs (by rw [hbin, hO]; exact hMold)]
      · rw [(register_hdr_other haM).1, ← h.prev a ha]
        exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · rw [w2, register_hdr_self hs (by rw [hbin, hO]; exact hMold)]
  · -- size
    rcases ha with ha | rfl
    · obtain ⟨a1, a2, a3, a4⟩ := hHa a (Or.inl ha)
      by_cases haM : a = M
      · subst haM
        rw [w3, register_hdr_self hs (by rw [hbin, hO]; exact hMold)]
        simp [sizeWord]
      · rw [(register_hdr_other haM).2.1, ← h.size a ha]
        exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · rw [w3, register_hdr_self hs (by rw [hbin, hO]; exact hMold)]
      simp [sizeWord]
  · -- next
    rcases ha with ha | rfl
    · obtain ⟨a1, a2, a3, a4⟩ := hHa a (Or.inr ha)
      by_cases haM : a = M
      · subst haM
        rw [w4, register_hdr_self hs (by rw [hbin, hO]; exact hMold), hbin, hO]
      · rw [(register_hdr_other haM).2.2, ← h.next a ha]
        exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · rw [w4, register_hdr_self hs (by rw [hbin, hO]; exact hMold), hbin, hO]
  · -- prevL
    rcases ha with ha | rfl
    · obtain ⟨a1, a2, a3, a4⟩ := hHa a (Or.inr ha)
      by_cases haM : a = M
      · subst haM
        rw [w5, register_hdr_self hs (by rw [hbin, hO]; exact hMold)]
      · rw [register_prevL hs haM, hbin, hO]
        by_cases hao : a = old ∧ a ≠ 0
        · rw [if_pos hao]
          obtain ⟨rfl, h0⟩ := hao
          exact w6 h0
        · rw [if_neg hao, ← h.prevL a ha]
          exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · rw [w5, register_hdr_self hs (by rw [hbin, hO]; exact hMold)]

end Services.Bootstrap.Alloc
