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

theorem Linked.of_append {s : State} {a x : Nat} {l1 l2 : List Nat} (h : Linked s a (l1 ++ x :: l2)) :
    Linked s (s.hdr x).next l2 := by
  induction l1 generalizing a with
  | nil => exact h.2.2
  | cons z zs ih => exact ih h.2.2

theorem BackLinked.of_append {s : State} {p y x : Nat} {l1 l2 : List Nat}
    (h : BackLinked s p (l1 ++ y :: x :: l2)) : (s.hdr x).prevL = y := by
  induction l1 generalizing p with
  | nil => exact h.2.1
  | cons z zs ih => exact ih h.2

/-- Unlinking `x`, the node after `y`: `y`'s `next` skips it. -/
theorem Linked.remove {s s' : State} {a y x : Nat} {l1 l2 : List Nat}
    (h : Linked s a (l1 ++ y :: x :: l2)) (hnd : (l1 ++ y :: x :: l2).Nodup)
    (hn : ∀ z, z ≠ y → (s'.hdr z).next = (s.hdr z).next) (hy : (s'.hdr y).next = (s.hdr x).next) :
    Linked s' a (l1 ++ y :: l2) := by
  induction l1 generalizing a with
  | nil =>
    obtain ⟨h1, h2, -, -, h5⟩ := h
    refine ⟨h1, h2, ?_⟩
    show Linked s' (s'.hdr y).next l2
    rw [hy]
    have hy2 : y ∉ x :: l2 := (List.nodup_cons.mp hnd).1
    exact h5.congr (fun z hz => hn z (fun e => hy2 (e ▸ List.mem_cons_of_mem _ hz)))
  | cons z zs ih =>
    obtain ⟨h1, h2, h3⟩ := h
    have hz : z ∉ zs ++ y :: x :: l2 := (List.nodup_cons.mp hnd).1
    have hzy : z ≠ y := fun e => hz (e ▸ List.mem_append_right _ List.mem_cons_self)
    refine ⟨h1, h2, ?_⟩
    show Linked s' (s'.hdr z).next (zs ++ y :: l2)
    rw [hn z hzy]
    exact ih h3 (List.nodup_cons.mp hnd).2

/-- Unlinking `x`, the node after `y`: the node after `x` points back to `y`. -/
theorem BackLinked.remove {s s' : State} {p y x : Nat} {l1 l2 : List Nat}
    (h : BackLinked s p (l1 ++ y :: x :: l2)) (hnd : (l1 ++ y :: x :: l2).Nodup)
    (hp : ∀ z, z ∉ l2.head? → (s'.hdr z).prevL = (s.hdr z).prevL)
    (hw : ∀ w ∈ l2.head?, (s'.hdr w).prevL = y) :
    BackLinked s' p (l1 ++ y :: l2) := by
  induction l1 generalizing p with
  | nil =>
    obtain ⟨h1, -, h3⟩ := h
    have hy2 : y ∉ x :: l2 := (List.nodup_cons.mp hnd).1
    have hnd2 : l2.Nodup := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2
    refine ⟨(hp y (fun e => hy2 (List.mem_cons_of_mem _ (List.mem_of_mem_head? e)))).trans h1, ?_⟩
    show BackLinked s' y l2
    cases l2 with
    | nil => trivial
    | cons w ws =>
      obtain ⟨-, h4⟩ := h3
      refine ⟨hw w rfl, h4.congr (fun z hz => hp z ?_)⟩
      intro e
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at e
      subst e
      exact (List.nodup_cons.mp hnd2).1 hz
  | cons z zs ih =>
    obtain ⟨h1, h2⟩ := h
    have hz : z ∉ zs ++ y :: x :: l2 := (List.nodup_cons.mp hnd).1
    refine ⟨(hp z (fun e => hz (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_of_mem_head? e)))))).trans h1, ih h2 (List.nodup_cons.mp hnd).2⟩

/-- `unregister` keeps every header's `prev` and `size`. -/
theorem unregister_hdr {s : State} {x bin z : Nat} :
    ((unregister s x bin).hdr z).prev = (s.hdr z).prev ∧ ((unregister s x bin).hdr z).size = (s.hdr z).size := by
  have ps : ∀ (t : State) (a : Nat) (f : Hdr → Hdr), (∀ h, (f h).prev = h.prev ∧ (f h).size = h.size) →
      ∀ z, ((setHdr t a f).hdr z).prev = (t.hdr z).prev ∧ ((setHdr t a f).hdr z).size = (t.hdr z).size := by
    intro t a f hf z
    by_cases hz : z = a
    · subst hz; rw [setHdr_self]; exact hf _
    · rw [setHdr_other hz]; exact ⟨rfl, rfl⟩
  unfold unregister unregisterFirst
  dsimp only
  split
  · split
    · exact ⟨rfl, rfl⟩
    · refine ps _ _ _ ?_ z; intro; exact ⟨rfl, rfl⟩
  · split
    · refine ps _ _ _ ?_ z; intro; exact ⟨rfl, rfl⟩
    · have q1 := ps s (s.hdr x).prevL (fun h => { h with next := (s.hdr x).next }) (fun _ => ⟨rfl, rfl⟩) z
      have q2 := ps (setHdr s (s.hdr x).prevL fun h => { h with next := (s.hdr x).next }) (s.hdr x).next
        (fun h => { h with prevL := (s.hdr x).prevL }) (fun _ => ⟨rfl, rfl⟩) z
      rw [q2.1, q2.2]; exact q1

@[simp] theorem unregister_base {s : State} {x bin : Nat} : (unregister s x bin).base = s.base := by
  unfold unregister unregisterFirst unsetBit; dsimp only; split
  · split <;> rfl
  · split <;> rfl

@[simp] theorem unregister_allocated {s : State} {x bin : Nat} : (unregister s x bin).allocated = s.allocated := by
  unfold unregister unregisterFirst unsetBit; dsimp only; split
  · split <;> rfl
  · split <;> rfl

/-- **Unlinking a free chunk `x` of a bin**, anywhere in its list, removes `x` from the lists and
    keeps the bitmap right. -/
theorem remove_ok {s : State} {F : Nat → Nat → Prop} {bin x : Nat} (h : FreeLists s F) (hd : Disj F)
    (hbits : BitsOk s.secondary s.primary s.heads) (hbin : bin < binCount) (hx : F bin x) :
    FreeLists (unregister s x bin) (fun b a => F b a ∧ a ≠ x) ∧
      BitsOk (unregister s x bin).secondary (unregister s x bin).primary (unregister s x bin).heads := by
  unfold unregister
  split
  · rename_i hh
    exact pop_ok h hd hbits hbin hh (h.ne_zero hbin hx)
  · rename_i hh
    obtain ⟨l, hl, hbl, hnd, hex⟩ := h bin hbin
    obtain ⟨A, l2, hA⟩ := List.append_of_mem ((hex x).mpr hx)
    rcases List.eq_nil_or_concat A with hA0 | ⟨l1, y, hA1⟩
    · subst hA0; subst hA
      exact absurd hl.1 hh
    · subst hA1
      rw [List.concat_eq_append, List.append_assoc, List.singleton_append] at hA
      subst hA
      have hpx : (s.hdr x).prevL = y := hbl.of_append
      have hlx : Linked s (s.hdr x).next l2 := Linked.of_append (l1 := l1 ++ [y]) (by rw [List.append_assoc]; exact hl)
      have hy0 : y ≠ 0 := hl.ne_zero y (List.mem_append_right _ List.mem_cons_self)
      have hnd' := hnd
      rw [List.nodup_append] at hnd'
      obtain ⟨-, hnd2, hdis⟩ := hnd'
      have hyl2 : y ∉ x :: l2 := (List.nodup_cons.mp hnd2).1
      have hxl2 : x ∉ l2 := (List.nodup_cons.mp (List.nodup_cons.mp hnd2).2).1
      have hnxy : (s.hdr x).next ≠ y := by
        intro e
        cases l2 with
        | nil => exact hy0 (e ▸ hlx)
        | cons w ws => exact hyl2 (List.mem_cons_of_mem _ (e ▸ hlx.1 ▸ List.mem_cons_self))
      have hFy : F bin y := (hex y).mp (List.mem_append_right _ List.mem_cons_self)
      have hnxl : ∀ w ∈ l2.head?, w = (s.hdr x).next := by
        intro w hw
        cases l2 with
        | nil => simp at hw
        | cons v vs => simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hw; rw [← hw, hlx.1]
      dsimp only
      rw [hpx]
      generalize hnx : (s.hdr x).next = nx at hlx hnxy hnxl
      -- the new headers
      have key : ∀ (t : State), t.heads = s.heads → t.secondary = s.secondary → t.primary = s.primary →
          (∀ z, z ≠ y → (t.hdr z).next = (s.hdr z).next) → (t.hdr y).next = nx →
          (∀ z, z ∉ l2.head? → (t.hdr z).prevL = (s.hdr z).prevL) → (∀ w ∈ l2.head?, (t.hdr w).prevL = y) →
          FreeLists t (fun b a => F b a ∧ a ≠ x) ∧ BitsOk t.secondary t.primary t.heads := by
        intro t th tsec tpri tn ty tp tw
        refine ⟨fun b hb => ?_, by rw [th, tsec, tpri]; exact hbits⟩
        by_cases hbb : b = bin
        · subst hbb
          refine ⟨l1 ++ y :: l2, by rw [th]; exact hl.remove hnd tn (by rw [ty, hnx]), hbl.remove hnd tp tw, ?_,
            fun a => ?_⟩
          · rw [List.nodup_append] at hnd ⊢
            obtain ⟨n1, n2, n3⟩ := hnd
            refine ⟨n1, List.nodup_cons.mpr ⟨fun e => hyl2 (List.mem_cons_of_mem _ e),
              (List.nodup_cons.mp (List.nodup_cons.mp n2).2).2⟩, fun a ha b hb => n3 a ha b ?_⟩
            rcases List.mem_cons.mp hb with rfl | hb
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hb)
          · show a ∈ l1 ++ y :: l2 ↔ F _ a ∧ a ≠ x
            rw [← hex a]
            constructor
            · intro ha
              refine ⟨?_, fun e => ?_⟩
              · rcases List.mem_append.mp ha with ha | ha
                · exact List.mem_append_left _ ha
                · rcases List.mem_cons.mp ha with rfl | ha
                  · exact List.mem_append_right _ List.mem_cons_self
                  · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ha))
              · subst e
                rcases List.mem_append.mp ha with ha | ha
                · exact hdis a ha a (List.mem_cons_of_mem _ List.mem_cons_self) rfl
                · rcases List.mem_cons.mp ha with e | ha
                  · exact hyl2 (e ▸ List.mem_cons_self)
                  · exact hxl2 ha
            · rintro ⟨ha, hne⟩
              rcases List.mem_append.mp ha with ha | ha
              · exact List.mem_append_left _ ha
              · rcases List.mem_cons.mp ha with rfl | ha
                · exact List.mem_append_right _ List.mem_cons_self
                · rcases List.mem_cons.mp ha with rfl | ha
                  · exact absurd rfl hne
                  · exact List.mem_append_right _ (List.mem_cons_of_mem _ ha)
        · obtain ⟨l', hl', hbl', hnd', hex'⟩ := h b hb
          have hnot : ∀ z ∈ l', z ∉ l1 ++ y :: x :: l2 := fun z hz hz' =>
            hbb (hd _ _ _ ((hex' z).mp hz) ((hex z).mp hz'))
          refine ⟨l', by rw [th]; exact hl'.congr (fun z hz => tn z (fun e => hnot z hz (e ▸
            List.mem_append_right _ List.mem_cons_self))), hbl'.congr (fun z hz => tp z (fun e => hnot z hz
            (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_of_mem_head? e)))))),
            hnd', fun a => ?_⟩
          rw [hex' a]
          exact ⟨fun ha => ⟨ha, fun e => hbb (hd _ _ _ ha (e ▸ hx))⟩, fun ha => ha.1⟩
      split
      · rename_i h0
        refine key _ rfl rfl rfl (fun z hz => setHdr_other' hz) (by rw [setHdr_self]) (fun z _ => setHdr_prevL
          (f := fun h => { h with next := nx }) (fun _ => rfl) z) (fun w hw => ?_)
        exact absurd ((hnxl w hw).trans h0) (hlx.ne_zero w (List.mem_of_mem_head? hw))
      · rename_i h0
        refine key _ rfl rfl rfl (fun z hz => ?_) ?_ (fun z hz => ?_) (fun w hw => ?_)
        · rw [setHdr_next (f := fun h => { h with prevL := y }) (fun _ => rfl)]; exact setHdr_other' hz
        · rw [setHdr_next (f := fun h => { h with prevL := y }) (fun _ => rfl), setHdr_self]
        · have : z ≠ nx := by
            intro e; subst e
            cases l2 with
            | nil => exact h0 hlx
            | cons v vs => exact hz (by rw [← hlx.1]; rfl)
          rw [setHdr_other this, setHdr_prevL (f := fun h => { h with next := nx }) (fun _ => rfl)]
        · rw [hnxl w hw, setHdr_self]
where
  setHdr_other' {s : State} {a x : Nat} {f : Hdr → Hdr} (hx : x ≠ a) :
      ((setHdr s a f).hdr x).next = (s.hdr x).next := by rw [setHdr_other hx]

end Picoalloc
