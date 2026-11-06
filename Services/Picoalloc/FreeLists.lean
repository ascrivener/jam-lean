import Services.Picoalloc.Lists
import Services.Picoalloc.Bits

/-!
# The free lists against a membership predicate

`FreeLists s F`: each bin `b`'s list, linked from its head and back, without repeats, holds
exactly the addresses `a` with `F b a`. Popping a bin's head removes it from `F`; pushing a chunk
that no bin holds adds it to its bin; writes that keep the heads and the `next` and `prevL` fields
keep every list.
-/

namespace Picoalloc

def FreeLists (s : State) (F : Nat → Nat → Prop) : Prop :=
  ∀ b, b < binCount → ∃ l, Linked s (s.heads b) l ∧ BackLinked s 0 l ∧ l.Nodup ∧ ∀ a, a ∈ l ↔ F b a

/-- No address is in two bins. -/
def Disj (F : Nat → Nat → Prop) : Prop := ∀ b b' a, F b a → F b' a → b = b'

theorem FreeLists.iff {s : State} {F G : Nat → Nat → Prop} (h : FreeLists s F)
    (hfg : ∀ b a, b < binCount → (F b a ↔ G b a)) : FreeLists s G := by
  intro b hb
  obtain ⟨l, h1, h2, h3, h4⟩ := h b hb
  exact ⟨l, h1, h2, h3, fun a => (h4 a).trans (hfg b a hb)⟩

theorem FreeLists.congr {s t : State} {F : Nat → Nat → Prop} (h : FreeLists s F) (hh : t.heads = s.heads)
    (hn : ∀ x, (t.hdr x).next = (s.hdr x).next) (hp : ∀ x, (t.hdr x).prevL = (s.hdr x).prevL) :
    FreeLists t F := by
  intro b hb
  obtain ⟨l, h1, h2, h3, h4⟩ := h b hb
  exact ⟨l, by rw [hh]; exact h1.congr (fun x _ => hn x), h2.congr (fun x _ => hp x), h3, h4⟩

theorem FreeLists.ne_zero {s : State} {F : Nat → Nat → Prop} (h : FreeLists s F) {b a : Nat}
    (hb : b < binCount) (ha : F b a) : a ≠ 0 := by
  obtain ⟨l, h1, -, -, h4⟩ := h b hb
  exact h1.ne_zero a ((h4 a).mpr ha)

theorem BitsOk.heads_congr {sec : Nat → Nat} {pri : Nat} {hs hs' : Nat → Nat} (h : BitsOk sec pri hs)
    (he : ∀ b, b < binCount → (hs b ≠ 0 ↔ hs' b ≠ 0)) : BitsOk sec pri hs' :=
  ⟨fun b hb => (h.1 b hb).trans (he b hb), h.2.1, h.2.2.1, h.2.2.2⟩

/-- **Popping the head `C` of a bin** removes `C` from the lists and keeps the bitmap right. -/
theorem pop_ok {s : State} {F : Nat → Nat → Prop} {bin C : Nat} (h : FreeLists s F) (hd : Disj F)
    (hbits : BitsOk s.secondary s.primary s.heads) (hbin : bin < binCount) (hC : s.heads bin = C)
    (hC0 : C ≠ 0) :
    FreeLists (unregisterFirst s C bin) (fun b a => F b a ∧ a ≠ C) ∧
      BitsOk (unregisterFirst s C bin).secondary (unregisterFirst s C bin).primary
        (unregisterFirst s C bin).heads := by
  obtain ⟨l, hl, hbl, hnd, hex⟩ := h bin hbin
  obtain ⟨rest, rfl⟩ : ∃ rest, l = C :: rest := by
    cases l with
    | nil => exact absurd ((hl.head).mpr rfl) (by rw [hC]; exact hC0)
    | cons x xs => exact ⟨xs, by rw [← hl.1, hC]⟩
  have hFC : F bin C := (hex C).mp List.mem_cons_self
  obtain ⟨u1, u2, u3, u4, u5, -, -⟩ := unregisterFirst_list hl hbl hnd
  refine ⟨fun b hb => ?_, ?_⟩
  · by_cases hbb : b = bin
    · subst hbb
      refine ⟨rest, u1, u2, (List.nodup_cons.mp hnd).2, fun a => ⟨fun ha => ⟨(hex a).mp
        (List.mem_cons_of_mem _ ha), fun h => (List.nodup_cons.mp hnd).1 (h ▸ ha)⟩, fun ⟨ha, hne⟩ => ?_⟩⟩
      rcases List.mem_cons.mp ((hex a).mpr ha) with h | h
      · exact absurd h hne
      · exact h
    · obtain ⟨l', hl', hbl', hnd', hex'⟩ := h b hb
      refine ⟨l', by rw [u5 b hbb]; exact hl'.congr (fun x _ => u3 x), hbl'.congr (fun x hx => u4 x ?_), hnd',
        fun a => ⟨fun ha => ⟨(hex' a).mp ha, fun hac => hbb (hd _ _ _ ((hex' a).mp ha) (hac ▸ hFC))⟩,
          fun ha => (hex' a).mpr ha.1⟩⟩
      intro hxn
      have hx0 : x ≠ 0 := hl'.ne_zero x hx
      obtain ⟨-, -, hl3⟩ := hl
      cases rest with
      | nil => exact hx0 (by rw [hxn]; exact hl3)
      | cons y ys =>
        have hy : y = x := by rw [hxn]; exact hl3.1.symm
        exact hbb (hd _ _ _ ((hex' x).mp hx) (hy ▸ (hex y).mp (List.mem_cons_of_mem _ List.mem_cons_self)))
  · unfold unregisterFirst
    dsimp only
    split
    · rename_i hn
      have := unsetBit_ok (s := s) (hs := upd s.heads bin (s.hdr C).next) hbin hbits
        (fun b' hb' => upd_ne _ _ hb') (by rw [upd_self, hn])
      exact this
    · rename_i hn
      refine BitsOk.heads_congr hbits (fun b hb => ?_)
      show s.heads b ≠ 0 ↔ upd s.heads bin (s.hdr C).next b ≠ 0
      by_cases hbb : b = bin
      · subst hbb; rw [upd_self, hC]; exact ⟨fun _ => hn, fun _ => hC0⟩
      · rw [upd_ne _ _ hbb]

theorem register_bits {s : State} {n prev size : Nat} (hsz : size ≠ 0) :
    (register s n prev size).1.secondary = (setBit s (binDown size)).secondary ∧
      (register s n prev size).1.primary = (setBit s (binDown size)).primary := by
  unfold register
  simp only [hsz, ↓reduceIte]
  split <;> exact ⟨rfl, rfl⟩

/-- **Pushing a chunk `n` that no bin holds** adds it to its bin and keeps the bitmap right. -/
theorem push_ok {s : State} {F : Nat → Nat → Prop} {n prev size : Nat} (h : FreeLists s F) (hd : Disj F)
    (hbits : BitsOk s.secondary s.primary s.heads) (hsz : size ≠ 0) (hB : binDown size < binCount)
    (hn0 : n ≠ 0) (hn : ∀ b, ¬ F b n) :
    FreeLists (register s n prev size).1 (fun b a => F b a ∨ (b = binDown size ∧ a = n)) ∧
      BitsOk (register s n prev size).1.secondary (register s n prev size).1.primary
        (register s n prev size).1.heads := by
  obtain ⟨l, hl, hbl, hnd, hex⟩ := h _ hB
  have hnl : n ∉ l := fun h => hn _ ((hex n).mp h)
  obtain ⟨r1, r2, r3, r4, -, -, r7, -, -, -⟩ := register_list (prev := prev) hsz hn0 hl hbl hnd hnl
  refine ⟨fun b hb => ?_, ?_⟩
  · by_cases hbb : b = binDown size
    · subst hbb
      refine ⟨n :: l, r1, r2, List.nodup_cons.mpr ⟨hnl, hnd⟩, fun a => ?_⟩
      simp only [List.mem_cons, hex, true_and]
      exact ⟨fun h => h.elim Or.inr Or.inl, fun h => h.elim Or.inr Or.inl⟩
    · obtain ⟨l', hl', hbl', hnd', hex'⟩ := h b hb
      have hxn : ∀ x ∈ l', x ≠ n := fun x hx hxn => hn b (hxn ▸ (hex' x).mp hx)
      refine ⟨l', by rw [r7 b hbb]; exact hl'.congr (fun x hx => r3 x (hxn x hx)),
        hbl'.congr (fun x hx => r4 x (hxn x hx) ?_), hnd', fun a => ?_⟩
      · intro hxh
        have hx0 : x ≠ 0 := hl'.ne_zero x hx
        obtain ⟨y, ys, hy⟩ : ∃ y ys, l = y :: ys := by
          cases l with
          | nil => exact absurd ((hl.head).mpr rfl) (by rw [← hxh]; exact hx0)
          | cons y ys => exact ⟨y, ys, rfl⟩
        subst hy
        have : y = x := by rw [hxh]; exact hl.1.symm
        exact hbb (hd _ _ _ ((hex' x).mp hx) ((hex x).mp (this ▸ List.mem_cons_self)))
      · rw [hex' a]
        exact ⟨Or.inl, fun h => h.elim id (fun h => absurd h.1 hbb)⟩
  · obtain ⟨e1, e2⟩ := register_bits (s := s) (n := n) (prev := prev) hsz
    rw [e1, e2]
    refine setBit_ok hB hbits (fun b' hb' => r7 b' hb') ?_
    rw [r1.1]; exact hn0

end Picoalloc
