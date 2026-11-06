import Services.Bootstrap.Alloc.RegisterRep

/-!
# `unregister` against memory

The memory the binary's unlinking (`nx_unlink_head`, `nx_unlink_head0` with `nx_clear`,
`nx_unlink_mid`) leaves holds the model's `unregister`.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc

/-- **Unlinking from inside a list**: `prv`'s next becomes `nxt`, and `nxt`'s back link `prv`. -/
theorem unregister_rep_mid {μ μ' : Memory} {s : State} {H F : Nat → Prop} {c bin : Nat}
    (h : RepAt μ s H F) (hc : s.heads bin ≠ c)
    (w1 : rdN μ' ((s.hdr c).prevL + 8) 4 = (s.hdr c).next)
    (w2 : (s.hdr c).next ≠ 0 → rdN μ' ((s.hdr c).next + 12) 4 = (s.hdr c).prevL)
    (wf : ∀ a, a < 2147483648 → (a < (s.hdr c).prevL + 8 ∨ (s.hdr c).prevL + 12 ≤ a) →
      ((s.hdr c).next = 0 ∨ a < (s.hdr c).next + 12 ∨ (s.hdr c).next + 16 ≤ a) → μ'.read a = μ.read a)
    (hp : 206864 ≤ (s.hdr c).prevL) (hn : (s.hdr c).next ≠ 0 → 206864 ≤ (s.hdr c).next)
    (hpn : (s.hdr c).next ≠ 0 → (s.hdr c).next ≠ (s.hdr c).prevL)
    (hHa : ∀ a, H a ∨ F a → 206864 ≤ a ∧ a + 16 < 2147483648 ∧
      (a = (s.hdr c).prevL ∨ a + 16 ≤ (s.hdr c).prevL ∨ (s.hdr c).prevL + 16 ≤ a) ∧
      ((s.hdr c).next = 0 ∨ a = (s.hdr c).next ∨ a + 16 ≤ (s.hdr c).next ∨ (s.hdr c).next + 16 ≤ a)) :
    RepAt μ' (unregister s c bin) H F := by
  generalize hP : (s.hdr c).prevL = prv at *
  generalize hN : (s.hdr c).next = nxt at *
  have e : unregister s c bin = if nxt = 0 then setHdr s prv (fun h => { h with next := nxt })
      else setHdr (setHdr s prv (fun h => { h with next := nxt })) nxt (fun h => { h with prevL := prv }) := by
    unfold unregister; rw [if_neg hc, hP, hN]
  rw [e]
  -- the new headers, field by field
  have hdr : ∀ x, (if nxt = 0 then setHdr s prv (fun h => { h with next := nxt })
      else setHdr (setHdr s prv (fun h => { h with next := nxt })) nxt (fun h => { h with prevL := prv })).hdr x =
      { prev := (s.hdr x).prev, size := (s.hdr x).size,
        next := if x = prv then nxt else (s.hdr x).next,
        prevL := if nxt ≠ 0 ∧ x = nxt then prv else (s.hdr x).prevL } := by
    intro x
    split
    · rename_i h0
      by_cases hx : x = prv
      · subst hx; rw [setHdr_self]; simp [h0]
      · rw [setHdr_other hx]; simp [hx, h0]
    · rename_i h0
      by_cases hx2 : x = nxt
      · subst hx2
        rw [setHdr_self, setHdr_other (hpn h0)]
        simp [h0, hpn h0]
      · rw [setHdr_other hx2]
        by_cases hx : x = prv
        · subst hx; rw [setHdr_self]; simp [hx2]
        · rw [setHdr_other hx]; simp [hx, hx2]
  have hfld : ∀ t : State, t = (if nxt = 0 then setHdr s prv (fun h => { h with next := nxt })
      else setHdr (setHdr s prv (fun h => { h with next := nxt })) nxt (fun h => { h with prevL := prv })) →
      t.heads = s.heads ∧ t.secondary = s.secondary ∧ t.primary = s.primary ∧ t.base = s.base ∧
        t.allocated = s.allocated := by
    intro t ht; subst ht; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨f1, f2, f3, f4, f5⟩ := hfld _ rfl
  refine ⟨fun b hb => ?_, fun q hq => ?_, ?_, ?_, ?_, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_,
    fun a ha => ?_⟩
  · rw [f1, ← h.heads b hb]; unfold A0; unfold binCount at hb
    exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega)
  · rw [f2, ← h.sec q hq]; unfold A0
    exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega)
  · rw [f3, ← h.pri]; unfold A0
    exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega)
  · rw [f4, ← h.base]; unfold A0
    exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega)
  · rw [f5, ← h.alloc]; unfold A0
    exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega)
  · obtain ⟨a1, a2, a3, a4⟩ := hHa a (Or.inl ha)
    rw [hdr, ← h.prev a ha]
    exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega)
  · obtain ⟨a1, a2, a3, a4⟩ := hHa a (Or.inl ha)
    rw [hdr, ← h.size a ha]
    exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega)
  · obtain ⟨a1, a2, a3, a4⟩ := hHa a (Or.inr ha)
    rw [hdr]
    simp only
    by_cases hx : a = prv
    · subst hx; rw [if_pos rfl, w1]
    · rw [if_neg hx, ← h.next a ha]
      exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega)
  · obtain ⟨a1, a2, a3, a4⟩ := hHa a (Or.inr ha)
    rw [hdr]
    simp only
    by_cases hx : nxt ≠ 0 ∧ a = nxt
    · rw [if_pos hx]; obtain ⟨h0, rfl⟩ := hx; exact w2 h0
    · rw [if_neg hx, ← h.prevL a ha]
      exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by
        by_cases h0 : nxt = 0
        · exact Or.inl h0
        · have : a ≠ nxt := fun e => hx ⟨h0, e⟩
          omega)


/-- **Popping a list's head** with a successor `nxt`: the bin's head becomes `nxt`, whose back
    link is cleared. -/
theorem unregister_rep_head {μ μ' : Memory} {s : State} {H F : Nat → Prop} {c bin : Nat}
    (h : RepAt μ s H F) (hc : s.heads bin = c) (hb : bin < binCount) (hn0 : (s.hdr c).next ≠ 0)
    (w1 : rdN μ' (196792 + bin * 4) 4 = (s.hdr c).next) (w2 : rdN μ' ((s.hdr c).next + 12) 4 = 0)
    (wf : ∀ a, a < 2147483648 → (a < 196792 + bin * 4 ∨ 196792 + bin * 4 + 4 ≤ a) →
      (a < (s.hdr c).next + 12 ∨ (s.hdr c).next + 16 ≤ a) → μ'.read a = μ.read a)
    (hn : 206864 ≤ (s.hdr c).next)
    (hHa : ∀ a, H a ∨ F a → 206864 ≤ a ∧ a + 16 < 2147483648 ∧
      (a = (s.hdr c).next ∨ a + 16 ≤ (s.hdr c).next ∨ (s.hdr c).next + 16 ≤ a)) :
    RepAt μ' (unregister s c bin) H F := by
  generalize hN : (s.hdr c).next = nxt at *
  have e : unregister s c bin =
      setHdr { s with heads := upd s.heads bin nxt } nxt (fun h => { h with prevL := 0 }) := by
    unfold unregister unregisterFirst; rw [if_pos hc]; simp only [hN, hn0, ↓reduceIte]
  rw [e]
  unfold binCount at hb
  refine ⟨fun b hb' => ?_, fun q hq => ?_, ?_, ?_, ?_, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_,
    fun a ha => ?_⟩
  · show rdN μ' (A0 + 4 * b) 4 = upd s.heads bin nxt b
    unfold A0; unfold binCount at hb'
    by_cases hbb : b = bin
    · subst hbb; rw [upd_self, show 196792 + 4 * b = 196792 + b * 4 by omega, w1]
    · rw [upd_ne _ _ hbb, ← h.heads b (by unfold binCount; omega)]; unfold A0
      exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega)
  · show rdN μ' (A0 + 9736 + 8 * q) 8 = s.secondary q
    rw [← h.sec q hq]; unfold A0
    exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega)
  · show rdN μ' (A0 + 10040) 8 = s.primary
    rw [← h.pri]; unfold A0
    exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega)
  · show rdN μ' (A0 + 9728) 8 = s.base
    rw [← h.base]; unfold A0
    exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega)
  · show rdN μ' (A0 + 10048) 4 = s.allocated
    rw [← h.alloc]; unfold A0
    exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega)
  all_goals obtain ⟨a1, a2, a3⟩ := hHa a (by first | exact Or.inl ha | exact Or.inr ha)
  · rw [setHdr_prev_or a nxt, ← h.prev a ha]
    exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega)
  · rw [setHdr_size_or a nxt, ← h.size a ha]
    exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega)
  · rw [setHdr_next_or a nxt, ← h.next a ha]
    exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega)
  · by_cases hx : a = nxt
    · subst hx; rw [setHdr_self, w2]
    · rw [setHdr_other hx, ← h.prevL a ha]
      exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega)
where
  setHdr_prev_or (a n : Nat) {t : State} :
      ((setHdr t n (fun h => { h with prevL := 0 })).hdr a).prev = (t.hdr a).prev := by
    by_cases hx : a = n
    · subst hx; rw [setHdr_self]
    · rw [setHdr_other hx]
  setHdr_size_or (a n : Nat) {t : State} :
      ((setHdr t n (fun h => { h with prevL := 0 })).hdr a).size = (t.hdr a).size := by
    by_cases hx : a = n
    · subst hx; rw [setHdr_self]
    · rw [setHdr_other hx]
  setHdr_next_or (a n : Nat) {t : State} :
      ((setHdr t n (fun h => { h with prevL := 0 })).hdr a).next = (t.hdr a).next := by
    by_cases hx : a = n
    · subst hx; rw [setHdr_self]
    · rw [setHdr_other hx]

/-- **Popping a list's last element**: the bin's head becomes 0, its bit is cleared in its
    secondary word, and, if that leaves the word 0, the word's bit in the primary word. -/
theorem unregister_rep_last {μ μ' : Memory} {s : State} {H F : Nat → Prop} {c bin : Nat}
    (h : RepAt μ s H F) (hc : s.heads bin = c) (hb : bin < binCount) (hn0 : (s.hdr c).next = 0)
    (w1 : rdN μ' (196792 + bin * 4) 4 = 0)
    (w2 : rdN μ' (204984 + bin / 64 * 8 + 1544) 8 =
      rdN μ (204984 + bin / 64 * 8 + 1544) 8 &&& ((2 ^ 64 - 1) ^^^ 2 ^ (bin % 64)))
    (w3 : rdN μ' 206832 8 = (if rdN μ (204984 + bin / 64 * 8 + 1544) 8 &&& ((2 ^ 64 - 1) ^^^ 2 ^ (bin % 64)) = 0
      then rdN μ 206832 8 &&& ((2 ^ 64 - 1) ^^^ 2 ^ (bin / 64)) else rdN μ 206832 8))
    (wf : ∀ a, a < 2147483648 → (a < 196792 + bin * 4 ∨ 196792 + bin * 4 + 4 ≤ a) →
      (a < 204984 + bin / 64 * 8 + 1544 ∨ 204984 + bin / 64 * 8 + 1552 ≤ a) →
      (a < 206832 ∨ 206840 ≤ a) → μ'.read a = μ.read a)
    (hHa : ∀ a, H a ∨ F a → 206864 ≤ a ∧ a + 16 < 2147483648) :
    RepAt μ' (unregister s c bin) H F := by
  have e : unregister s c bin = unsetBit { s with heads := upd s.heads bin 0 } bin := by
    unfold unregister unregisterFirst; rw [if_pos hc]; simp only [hn0, ↓reduceIte]
  rw [e]
  unfold binCount at hb
  have hsec := h.sec (bin / 64) (by omega)
  have hpri := h.pri
  unfold A0 at hsec hpri
  rw [show 196792 + 9736 + 8 * (bin / 64) = 204984 + bin / 64 * 8 + 1544 by omega] at hsec
  rw [show 196792 + 10040 = 206832 by rfl] at hpri
  rw [hsec] at w2 w3
  rw [hpri] at w3
  refine ⟨fun b hb' => ?_, fun q hq => ?_, ?_, ?_, ?_, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_,
    fun a ha => ?_⟩
  · show rdN μ' (A0 + 4 * b) 4 = upd s.heads bin 0 b
    unfold A0; unfold binCount at hb'
    by_cases hbb : b = bin
    · subst hbb; rw [upd_self, show 196792 + 4 * b = 196792 + b * 4 by omega, w1]
    · rw [upd_ne _ _ hbb, ← h.heads b (by unfold binCount; omega)]; unfold A0
      exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega) (by omega)
  · show rdN μ' (A0 + 9736 + 8 * q) 8 = upd s.secondary (bin / 64) _ q
    unfold A0
    by_cases hqq : q = bin / 64
    · subst hqq; rw [upd_self, show 196792 + 9736 + 8 * (bin / 64) = 204984 + bin / 64 * 8 + 1544 by omega, w2]
    · rw [upd_ne _ _ hqq, ← h.sec q hq]; unfold A0
      exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega) (by omega)
  · show rdN μ' (A0 + 10040) 8 = _
    unfold A0; rw [show 196792 + 10040 = 206832 by rfl, w3]; unfold unsetBit; rfl
  · show rdN μ' (A0 + 9728) 8 = s.base
    rw [← h.base]; unfold A0
    exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega) (by omega)
  · show rdN μ' (A0 + 10048) 4 = s.allocated
    rw [← h.alloc]; unfold A0
    exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega) (by omega)
  all_goals obtain ⟨a1, a2⟩ := hHa a (by first | exact Or.inl ha | exact Or.inr ha)
  · show rdN μ' a 4 = (s.hdr a).prev
    rw [← h.prev a ha]; exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega) (by omega)
  · show rdN μ' (a + 4) 4 = (s.hdr a).size
    rw [← h.size a ha]; exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega) (by omega)
  · show rdN μ' (a + 8) 4 = (s.hdr a).next
    rw [← h.next a ha]; exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega) (by omega)
  · show rdN μ' (a + 12) 4 = (s.hdr a).prevL
    rw [← h.prevL a ha]; exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega) (by omega)

end Services.Bootstrap.Alloc
