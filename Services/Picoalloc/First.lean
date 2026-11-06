import Services.Picoalloc.Init

/-!
# The first chunk's `prev`

`init` writes 0 as the first chunk's `prev`, and no operation writes another value there: the
merged or split chunk at the base keeps the `prev` it had. `FirstOk` says so; the binary's loads of
`prev` are sign-extending, and agree with the model's for this value.
-/

namespace Picoalloc

/-- The first chunk records no predecessor. -/
def FirstOk (s : State) : Prop := (s.hdr s.base).prev = 0

theorem mergePrev_prev {s s1 : State} {X n pv M sz1 pv' : Nat} (hm : mergePrev s X n pv = (s1, M, sz1, pv'))
    (hpv : (s.hdr X).prev = pv) :
    pv' = (s.hdr M).prev ∧ (∀ z, (s1.hdr z).prev = (s.hdr z).prev) ∧ s1.base = s.base ∧ n ≤ sz1 := by
  unfold mergePrev at hm
  split at hm
  · dsimp only at hm
    split at hm
    · simp only [Prod.mk.injEq] at hm; obtain ⟨rfl, rfl, rfl, rfl⟩ := hm
      exact ⟨rfl, fun z => unregister_hdr.1, unregister_base, Nat.le_add_right _ _⟩
    · simp only [Prod.mk.injEq] at hm; obtain ⟨rfl, rfl, rfl, rfl⟩ := hm
      exact ⟨hpv.symm, fun _ => rfl, rfl, Nat.le_refl _⟩
  · simp only [Prod.mk.injEq] at hm; obtain ⟨rfl, rfl, rfl, rfl⟩ := hm
    exact ⟨hpv.symm, fun _ => rfl, rfl, Nat.le_refl _⟩

theorem mergeNext_prev {s s2 : State} {M sz1 T total : Nat} (hn : mergeNext s M sz1 T = (s2, total)) :
    (∀ z, (s2.hdr z).prev = (s.hdr z).prev) ∧ s2.base = s.base ∧ sz1 ≤ total := by
  unfold mergeNext at hn
  split at hn
  · split at hn
    · simp only [Prod.mk.injEq] at hn; obtain ⟨rfl, rfl⟩ := hn
      exact ⟨fun z => unregister_hdr.1, unregister_base, Nat.le_add_right _ _⟩
    · simp only [Prod.mk.injEq] at hn; obtain ⟨rfl, rfl⟩ := hn; exact ⟨fun _ => rfl, rfl, Nat.le_refl _⟩
  · simp only [Prod.mk.injEq] at hn; obtain ⟨rfl, rfl⟩ := hn; exact ⟨fun _ => rfl, rfl, Nat.le_refl _⟩

theorem freeFinal_base {s : State} {M pv total T : Nat} : (freeFinal s M pv total T).base = s.base := by
  unfold freeFinal; split <;> simp

/-- `freeFinal` at M ≥ the base writes the base's `prev` only as M's, with `pv`. -/
theorem freeFinal_first {s : State} {M pv total T : Nat} (ht : total ≠ 0) (hM : s.base ≤ M) :
    ((freeFinal s M pv total T).hdr s.base).prev = if s.base = M then pv else (s.hdr s.base).prev := by
  have hreg : ((register s M pv total).1.hdr s.base).prev = if s.base = M then pv else (s.hdr s.base).prev := by
    split
    · rename_i h; rw [h]; exact register_prev_self ht
    · rename_i h; exact (register_hdr_other h).1
  unfold freeFinal
  split
  · rw [setHdr_prev_get, if_neg (by omega)]; exact hreg
  · exact hreg

theorem free_first_aux {s s2 : State} {M pv total T : Nat} (h0 : FirstOk s) (hpv : pv = (s.hdr M).prev)
    (hp2 : ∀ z, (s2.hdr z).prev = (s.hdr z).prev) (hb2 : s2.base = s.base) (ht : total ≠ 0) (hM : s.base ≤ M) :
    ((freeFinal s2 M pv total T).hdr (freeFinal s2 M pv total T).base).prev = 0 := by
  rw [freeFinal_base, freeFinal_first ht (by rw [hb2]; exact hM), hb2]
  split
  · rename_i h; rw [hpv, ← h]; exact h0
  · rw [hp2]; exact h0

theorem free_first {s : State} {ptr n : Nat} {pre post : List Chunk} (hwf : WF s) (h0 : FirstOk s)
    (hcs : chunks s = pre ++ ⟨ptr - 32, n, true⟩ :: post) : FirstOk (free s ptr) := by
  obtain ⟨-, -, -, htiles, -, hprev, -, -⟩ := hwf
  unfold TilesOk at htiles
  unfold PrevsOk at hprev
  rw [hcs] at htiles hprev
  have hXl := htiles.mem_lt _ (List.mem_append_right _ List.mem_cons_self)
  simp only at hXl
  have hn : wordSize (s.hdr (ptr - 32)).size = n := by
    rw [chunks_hdr ⟨ptr - 32, n, true⟩ (by rw [hcs]; exact List.mem_append_right _ List.mem_cons_self),
      wordSize_sizeWord]
  unfold FirstOk
  rw [free_eq]
  generalize s.top = T
  rw [hn]
  generalize hX : ptr - 32 = X at *
  generalize hm : mergePrev s X n (s.hdr X).prev = m
  generalize hq : mergeNext m.1 m.2.1 m.2.2.1 T = q
  obtain ⟨hpv, hp1, hb1, hsz1⟩ := mergePrev_prev (hm.trans (rfl : m = (m.1, m.2.1, m.2.2.1, m.2.2.2))) rfl
  obtain ⟨s2, total⟩ := q
  obtain ⟨hp2, hb2, hst⟩ := mergeNext_prev hq
  have hMb : s.base ≤ m.2.1 := by
    obtain ⟨s1, M, sz1, pv⟩ := m
    show s.base ≤ M
    unfold mergePrev at hm
    split at hm
    · dsimp only at hm
      split at hm
      · simp only [Prod.mk.injEq] at hm; obtain ⟨-, rfl, -, -⟩ := hm
        rename_i hXb _
        rcases List.eq_nil_or_concat pre with h | ⟨pre1, d, h⟩
        · subst h; exact absurd htiles.1 hXb
        · rw [List.concat_eq_append] at h; subst h
          have hd : (s.hdr X).prev = d.size := (PrevOk.append.mp hprev).2.2 d (by simp) ⟨X, n, true⟩ rfl
          have hda := (Tiles.around (pre := pre1) (C := d.addr) (S := d.size) (u := d.used)
            (post := ⟨X, n, true⟩ :: post) (by
              have e : pre1 ++ [d] ++ ⟨X, n, true⟩ :: post =
                  pre1 ++ ⟨d.addr, d.size, d.used⟩ :: ⟨X, n, true⟩ :: post := by simp
              rw [← e]; exact htiles)).2.1 ⟨X, n, true⟩ rfl
          simp only at hda
          have := htiles.mem_lt d (by simp)
          rw [hd]; omega
      · simp only [Prod.mk.injEq] at hm; obtain ⟨-, rfl, -, -⟩ := hm; omega
    · simp only [Prod.mk.injEq] at hm; obtain ⟨-, rfl, -, -⟩ := hm; omega
  have ht : total ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hXl.2.2 hsz1) hst)
  exact free_first_aux h0 hpv (fun z => (hp2 z).trans (hp1 z)) (hb2.trans hb1) ht hMb


theorem allocPost_first {s1 : State} {bin r S C T : Nat} (hC : s1.heads bin = C)
    (hA : s1.base + 32 * ((C - s1.base) / 32) = C) (hS : r + 1 ≤ S) (hCb : s1.base ≤ C)
    (h0 : (s1.hdr s1.base).prev = 0) :
    ((allocPost s1 bin r S T).hdr (allocPost s1 bin r S T).base).prev = 0 := by
  rw [allocPost_base, allocPost_prev hC hA hS, if_neg (by omega), if_neg (by omega)]
  exact h0

theorem alloc_first {grow : Grow} {hb r p : Nat} {s s' : State} (hwf : WF s) (h0 : FirstOk s)
    (h : alloc grow hb 1 r s = some (p, s')) : FirstOk s' := by
  rw [alloc_one hwf.1] at h
  obtain ⟨bin, a1, hbin, hmax, hS, -, -, -, rfl⟩ := alloc1_eq h
  obtain ⟨-, -, -, -, -, hCb, hCal⟩ := bin_chunk hwf hmax hbin
  exact allocPost_first (s1 := { s with allocated := a1 }) rfl
    (show s.base + 32 * ((s.heads bin - s.base) / 32) = s.heads bin by omega) hS hCb h0

end Picoalloc
