import Services.Picoalloc.Invariant

/-!
# The free lists under the operations' writes

A bin's list depends only on its head and its nodes' `next` fields (`Linked`), and its back links
only on their `prevL` fields (`BackLinked`). `unregisterFirst` pops a list's head; `register` pushes
a chunk that no list holds.
-/

namespace Picoalloc

theorem upd_self {β : Type} (f : Nat → β) (a : Nat) (b : β) : upd f a b a = b := by simp [upd]
theorem upd_ne {β : Type} (f : Nat → β) {a x : Nat} (b : β) (h : x ≠ a) : upd f a b x = f x := by
  simp [upd, h]

theorem Linked.congr {s s' : State} {a : Nat} {l : List Nat} (h : Linked s a l)
    (hn : ∀ x ∈ l, (s'.hdr x).next = (s.hdr x).next) : Linked s' a l := by
  induction l generalizing a with
  | nil => exact h
  | cons x xs ih =>
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨h1, h2, ?_⟩
    rw [hn x (by simp)]
    exact ih h3 (fun y hy => hn y (by simp [hy]))

theorem BackLinked.congr {s s' : State} {p : Nat} {l : List Nat} (h : BackLinked s p l)
    (hp : ∀ x ∈ l, (s'.hdr x).prevL = (s.hdr x).prevL) : BackLinked s' p l := by
  induction l generalizing p with
  | nil => trivial
  | cons x xs ih =>
    obtain ⟨h1, h2⟩ := h
    exact ⟨(hp x (by simp)).trans h1, ih h2 (fun y hy => hp y (by simp [hy]))⟩

/-- The list linked from a head is unique. -/
theorem Linked.unique {s : State} {a : Nat} {l l' : List Nat} (h : Linked s a l) (h' : Linked s a l') :
    l = l' := by
  induction l generalizing a l' with
  | nil =>
    cases l' with
    | nil => rfl
    | cons y ys => obtain ⟨h1, h2, _⟩ := h'; simp [Linked] at h; omega
  | cons x xs ih =>
    cases l' with
    | nil => obtain ⟨h1, h2, _⟩ := h; simp [Linked] at h'; omega
    | cons y ys =>
      obtain ⟨h1, _, h3⟩ := h
      obtain ⟨h1', _, h3'⟩ := h'
      subst h1; subst h1'
      rw [ih h3 h3']

theorem Linked.ne_zero {s : State} {a : Nat} {l : List Nat} (h : Linked s a l) : ∀ x ∈ l, x ≠ 0 := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨_, h2, h3⟩ := h
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact h2
    · exact ih h3 y hy

theorem Linked.head {s : State} {a : Nat} {l : List Nat} (h : Linked s a l) :
    (a = 0 ↔ l = []) := by
  cases l with
  | nil => simp [Linked] at h; simp [h]
  | cons x xs => obtain ⟨h1, h2, _⟩ := h; simp [h1, h2]

/-- A `setHdr` that keeps `next` keeps every list. -/
theorem setHdr_next {s : State} {a : Nat} {f : Hdr → Hdr} (hf : ∀ h, (f h).next = h.next) (x : Nat) :
    ((setHdr s a f).hdr x).next = (s.hdr x).next := by
  unfold setHdr
  by_cases hx : x = a
  · subst hx; simp [upd_self, hf]
  · simp [upd_ne _ _ hx]

theorem setHdr_prevL {s : State} {a : Nat} {f : Hdr → Hdr} (hf : ∀ h, (f h).prevL = h.prevL) (x : Nat) :
    ((setHdr s a f).hdr x).prevL = (s.hdr x).prevL := by
  unfold setHdr
  by_cases hx : x = a
  · subst hx; simp [upd_self, hf]
  · simp [upd_ne _ _ hx]

theorem setHdr_other {s : State} {a x : Nat} {f : Hdr → Hdr} (hx : x ≠ a) :
    (setHdr s a f).hdr x = s.hdr x := by
  unfold setHdr; simp [upd_ne _ _ hx]

theorem setHdr_self {s : State} {a : Nat} {f : Hdr → Hdr} : (setHdr s a f).hdr a = f (s.hdr a) := by
  unfold setHdr; simp [upd_self]

@[simp] theorem setHdr_heads {s : State} {a : Nat} {f : Hdr → Hdr} : (setHdr s a f).heads = s.heads := rfl
@[simp] theorem setHdr_base {s : State} {a : Nat} {f : Hdr → Hdr} : (setHdr s a f).base = s.base := rfl
@[simp] theorem setHdr_allocated {s : State} {a : Nat} {f : Hdr → Hdr} :
    (setHdr s a f).allocated = s.allocated := rfl
@[simp] theorem setHdr_primary {s : State} {a : Nat} {f : Hdr → Hdr} : (setHdr s a f).primary = s.primary := rfl
@[simp] theorem setHdr_secondary {s : State} {a : Nat} {f : Hdr → Hdr} :
    (setHdr s a f).secondary = s.secondary := rfl

/-- **Popping a list's head**: after `unregisterFirst`, the bin's list is the rest, back-linked
    from 0, and every node's `next` is unchanged. -/
theorem unregisterFirst_list {s : State} {c bin : Nat} {rest : List Nat}
    (hl : Linked s (s.heads bin) (c :: rest)) (hb : BackLinked s 0 (c :: rest)) (hnd : (c :: rest).Nodup) :
    let s' := unregisterFirst s c bin
    Linked s' (s'.heads bin) rest ∧ BackLinked s' 0 rest ∧ (∀ x, (s'.hdr x).next = (s.hdr x).next) ∧
      (∀ x, x ≠ (s.hdr c).next → (s'.hdr x).prevL = (s.hdr x).prevL) ∧
      (∀ b, b ≠ bin → s'.heads b = s.heads b) ∧ s'.base = s.base ∧ s'.allocated = s.allocated := by
  obtain ⟨h1, h2, h3⟩ := hl
  obtain ⟨_, hb2⟩ := hb
  unfold unregisterFirst
  dsimp only
  split
  · rename_i hn
    rw [hn] at h3
    have : rest = [] := by
      cases rest with
      | nil => rfl
      | cons y ys => exact absurd h3.1.symm h3.2.1
    subst this
    refine ⟨?_, trivial, fun x => rfl, fun x _ => rfl, fun b hb => ?_, rfl, rfl⟩
    · simp only [Linked]; unfold unsetBit; simp [upd_self, hn]
    · unfold unsetBit; simp [upd_ne _ _ hb]
  · rename_i hn
    have hnext : ∀ x, ((setHdr { s with heads := upd s.heads bin (s.hdr c).next } (s.hdr c).next
        fun h => { h with prevL := 0 }).hdr x).next = (s.hdr x).next := fun x =>
      setHdr_next (f := fun h => { h with prevL := 0 }) (fun _ => rfl) x
    refine ⟨?_, ?_, hnext, fun x hx => setHdr_prevL' hx, fun b hb => by simp [upd_ne _ _ hb], rfl, rfl⟩
    · simp only [setHdr_heads, upd_self]
      exact h3.congr (fun x _ => hnext x)
    · cases rest with
      | nil => trivial
      | cons y ys =>
        obtain ⟨hy1, _, _⟩ := h3
        obtain ⟨_, hb3⟩ := hb2
        have hnd' : (y :: ys).Nodup := (List.nodup_cons.mp hnd).2
        refine ⟨?_, ?_⟩
        · rw [← hy1, setHdr_self]
        · refine hb3.congr (fun x hx => ?_)
          have : x ≠ y := fun h => (List.nodup_cons.mp hnd').1 (h ▸ hx)
          exact setHdr_prevL' (by rw [hy1]; exact this)
where
  setHdr_prevL' {s : State} {a x : Nat} {f : Hdr → Hdr} (hx : x ≠ a) :
      ((setHdr s a f).hdr x).prevL = (s.hdr x).prevL := by rw [setHdr_other hx]

theorem setBit_heads {s : State} {b : Nat} : (setBit s b).heads = s.heads := rfl
theorem setBit_hdr {s : State} {b : Nat} : (setBit s b).hdr = s.hdr := rfl
theorem unsetBit_heads {s : State} {b : Nat} : (unsetBit s b).heads = s.heads := rfl
theorem unsetBit_hdr {s : State} {b : Nat} : (unsetBit s b).hdr = s.hdr := rfl

/-- **Pushing a fresh chunk**: `register` of a nonempty chunk `n` that the bin's list `l` does not
    hold makes the list `n :: l`, back-linked from 0, and changes no other node's `next`, no other
    `prevL` but the old head's, no other header's `prev` or `size`, and no other bin's head. -/
theorem register_list {s : State} {n prev size : Nat} {l : List Nat} (hsz : size ≠ 0) (hn0 : n ≠ 0)
    (hl : Linked s (s.heads (binDown size)) l) (hb : BackLinked s 0 l) (hnd : l.Nodup) (hn : n ∉ l) :
    let s' := (register s n prev size).1
    Linked s' (s'.heads (binDown size)) (n :: l) ∧ BackLinked s' 0 (n :: l) ∧
      (∀ x, x ≠ n → (s'.hdr x).next = (s.hdr x).next) ∧
      (∀ x, x ≠ n → x ≠ s.heads (binDown size) → (s'.hdr x).prevL = (s.hdr x).prevL) ∧
      (∀ x, x ≠ n → (s'.hdr x).prev = (s.hdr x).prev ∧ (s'.hdr x).size = (s.hdr x).size) ∧
      s'.hdr n = ⟨prev, sizeWord size false, s.heads (binDown size), 0⟩ ∧
      (∀ b, b ≠ binDown size → s'.heads b = s.heads b) ∧ s'.base = s.base ∧ s'.allocated = s.allocated ∧
      (register s n prev size).2 = size := by
  unfold register
  simp only [hsz, ↓reduceIte]
  -- the state before the bitmap
  generalize hs1 : setHdr { s with heads := upd s.heads (binDown size) n } n
    (fun _ => ⟨prev, sizeWord size false, s.heads (binDown size), 0⟩) = s1
  have h1n : s1.hdr n = ⟨prev, sizeWord size false, s.heads (binDown size), 0⟩ := by rw [← hs1, setHdr_self]
  have h1x : ∀ x, x ≠ n → s1.hdr x = s.hdr x := fun x hx => by rw [← hs1, setHdr_other hx]
  have h1h : s1.heads = upd s.heads (binDown size) n := by rw [← hs1]; rfl
  by_cases h0 : s.heads (binDown size) = 0
  · simp only [h0, ↓reduceIte] at h1n ⊢
    have hl0 : l = [] := (hl.head).mp h0
    subst hl0
    refine ⟨⟨by rw [setBit_heads, h1h, upd_self], hn0, by rw [setBit_hdr, h1n]; rfl⟩,
      ⟨by rw [setBit_hdr, h1n], trivial⟩, fun x hx => by rw [setBit_hdr, h1x x hx],
      fun x hx _ => by rw [setBit_hdr, h1x x hx], fun x hx => by rw [setBit_hdr, h1x x hx]; simp,
      by rw [setBit_hdr, h1n], fun b hb => by rw [setBit_heads, h1h, upd_ne _ _ hb], ?_, ?_, trivial⟩
    · rw [← hs1]; rfl
    · rw [← hs1]; rfl
  · simp only [h0, ↓reduceIte]
    obtain ⟨x0, xs, rfl⟩ : ∃ x0 xs, l = x0 :: xs := by
      cases l with
      | nil => exact absurd ((hl.head).mpr rfl) h0
      | cons x0 xs => exact ⟨x0, xs, rfl⟩
    obtain ⟨hx1, hx2, hx3⟩ := hl
    have hxn : x0 ≠ n := fun h => hn (h ▸ List.mem_cons_self)
    generalize hs2 : setHdr s1 (s.heads (binDown size)) (fun h => { h with prevL := n }) = s2
    have h2x : ∀ x, x ≠ s.heads (binDown size) → s2.hdr x = s1.hdr x := fun x hx => by rw [← hs2, setHdr_other hx]
    have h2h : (s2.hdr (s.heads (binDown size))) = { s1.hdr (s.heads (binDown size)) with prevL := n } := by
      rw [← hs2, setHdr_self]
    have h2n : s2.hdr n = ⟨prev, sizeWord size false, s.heads (binDown size), 0⟩ := by
      rw [h2x n (by rw [hx1]; exact hxn.symm), h1n]
    have hnx : ∀ x, x ≠ n → (s2.hdr x).next = (s.hdr x).next := fun x hx => by
      by_cases hh : x = s.heads (binDown size)
      · rw [hh, h2h, h1x _ (by rw [hx1]; exact hxn)]
      · rw [h2x x hh, h1x x hx]
    refine ⟨⟨by rw [setBit_heads, ← hs2, setHdr_heads, h1h, upd_self], hn0, ?_⟩, ⟨?_, ?_⟩, fun x hx => ?_,
      fun x hx hh => ?_, fun x hx => ?_, by rw [setBit_hdr, h2n], fun b hb => ?_, ?_, ?_, trivial⟩
    · show Linked (setBit s2 (binDown size)) (s2.hdr n).next (x0 :: xs)
      rw [h2n]
      refine ⟨hx1, hx2, ?_⟩
      show Linked (setBit s2 (binDown size)) (s2.hdr x0).next xs
      rw [hnx x0 hxn]
      exact hx3.congr (fun y hy => hnx y (fun h => hn (h ▸ List.mem_cons_of_mem _ hy)))
    · show (s2.hdr n).prevL = 0
      rw [h2n]
    · obtain ⟨_, hb2⟩ := hb
      refine ⟨?_, hb2.congr (fun y hy => ?_)⟩
      · show (s2.hdr x0).prevL = n
        rw [← hx1, h2h]
      · have hy0 : y ≠ x0 := fun h => (List.nodup_cons.mp hnd).1 (h ▸ hy)
        have hyn : y ≠ n := fun h => hn (h ▸ List.mem_cons_of_mem _ hy)
        show (s2.hdr y).prevL = (s.hdr y).prevL
        rw [h2x y (by rw [hx1]; exact hy0), h1x y hyn]
    · rw [setBit_hdr]; exact hnx x hx
    · rw [setBit_hdr, h2x x hh, h1x x hx]
    · by_cases hh : x = s.heads (binDown size)
      · rw [setBit_hdr, hh, h2h, h1x _ (by rw [hx1]; exact hxn)]; simp
      · rw [setBit_hdr, h2x x hh, h1x x hx]; simp
    · rw [setBit_heads, ← hs2, setHdr_heads, h1h, upd_ne _ _ hb]
    · rw [← hs2, ← hs1]; rfl
    · rw [← hs2, ← hs1]; rfl

end Picoalloc
