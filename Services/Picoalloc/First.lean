import Services.Picoalloc.Init

/-!
# The first chunk's `prev`

`init` writes 0 as the first chunk's `prev`, and no operation writes another value there: the
merged or split chunk at the base keeps the `prev` it had, and `shrink` and `growInplace` write
headers only above the chunk they resize. `FirstOk` says so, for `init`, `alloc`, `free` and
`realloc`; the binary's loads of `prev` are sign-extending, and agree with the model's for this
value.
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


theorem init_first {grow : Grow} {hb : Nat} {s s' : State} (hs0 : s.base = 0)
    (h : init grow hb s = some s') : FirstOk s' := by
  unfold init at h
  simp only [hs0, ne_eq, not_true_eq_false, ↓reduceIte] at h
  split at h
  · simp at h
  simp only [Option.some.injEq] at h
  subst h
  unfold FirstOk
  simp [setHdr, setBit, upd]
theorem setHdr_size_prev {s : State} {a z w : Nat} :
    ((setHdr s a (fun h => { h with size := w })).hdr z).prev = (s.hdr z).prev := by
  by_cases hz : z = a
  · subst hz; rw [setHdr_self]
  · rw [setHdr_other hz]

/-- `freeFinal` at M leaves the `prev` of headers below M. -/
theorem freeFinal_other {s : State} {z M pv total T : Nat} (hM : z < M) :
    ((freeFinal s M pv total T).hdr z).prev = (s.hdr z).prev := by
  unfold freeFinal
  split
  · rw [setHdr_prev_get, if_neg (by omega)]; exact (register_hdr_other (by omega)).1
  · exact (register_hdr_other (by omega)).1

theorem mergeNext_base {s : State} {M sz1 T : Nat} : (mergeNext s M sz1 T).1.base = s.base := by
  generalize hq : mergeNext s M sz1 T = q
  obtain ⟨s2, total⟩ := q
  exact (mergeNext_prev hq).2.1

theorem shrink_base {s : State} {ptr newReq : Nat} : (shrink s ptr newReq).base = s.base := by
  unfold shrink
  dsimp only
  split
  · rfl
  · rw [freeFinal_base, mergeNext_base, setHdr_base]

theorem shrink_first {s : State} {ptr newReq : Nat} (h0 : FirstOk s) (hX : s.base ≤ ptr - 32) :
    FirstOk (shrink s ptr newReq) := by
  unfold FirstOk
  rw [shrink_base]
  unfold shrink
  generalize ptr - 32 = X at *
  dsimp only
  split
  · exact h0
  rw [setHdr_base, show s.base + 32 * maxSize = s.top from rfl]
  generalize s.top = T
  generalize hq : mergeNext (setHdr s X (fun h => { h with size := sizeWord (newReq + 1) true })) X
    (wordSize (s.hdr X).size) T = q
  obtain ⟨s2, total⟩ := q
  obtain ⟨hp2, -, -⟩ := mergeNext_prev hq
  rw [freeFinal_other (by omega), hp2, setHdr_size_prev]
  exact h0

theorem growInplace_first {grow : Grow} {s s' : State} {ptr newReq : Nat} (h0 : FirstOk s)
    (hX : s.base ≤ ptr - 32) (h : growInplace grow s ptr newReq = some s') : FirstOk s' := by
  unfold growInplace at h
  generalize ptr - 32 = X at *
  simp only at h
  split at h
  · simp only [Option.pure_def, Option.some.injEq] at h; subst h; exact h0
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · simp at h
  generalize hE : (X + 32 * (newReq + 1) - s.base) / 32 + _ = E at h
  obtain ⟨sa, sah, sabase, rfl⟩ : ∃ sa : State, sa.hdr = s.hdr ∧ sa.base = s.base ∧
      s' = freeFinal (setHdr (unregister sa (X + 32 * wordSize (s.hdr X).size)
        (binDown (wordSize (s.hdr (X + 32 * wordSize (s.hdr X).size)).size))) X
        (fun h => { h with size := sizeWord (newReq + 1) true })) (X + 32 * (newReq + 1)) (newReq + 1)
        (wordSize (s.hdr X).size + wordSize (s.hdr (X + 32 * wordSize (s.hdr X).size)).size - (newReq + 1))
        (s.base + 32 * maxSize) := by
    by_cases hlt : s.allocated < E
    · by_cases hg : grow s.base E = true
      · simp only [hlt, hg, ↓reduceIte, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        exact ⟨{ s with allocated := E }, rfl, rfl, h.symm⟩
      · simp [hlt, hg] at h
    · simp only [hlt, ↓reduceIte, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at h
      exact ⟨s, rfl, rfl, h.symm⟩
  unfold FirstOk
  rw [freeFinal_base, setHdr_base, unregister_base, sabase,
    freeFinal_other (by omega), setHdr_size_prev,
    unregister_hdr.1, sah]
  exact h0
/-- **`realloc` keeps the first chunk's `prev` at 0**, for the data address of an allocated chunk
    and alignment one unit. -/
theorem realloc_first {grow : Grow} {hb : Nat} {s s' : State} {ptr newReq p : Nat} {cp : Bool} (hwf : WF s)
    (h0 : FirstOk s) (hptr : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (h : realloc grow hb s ptr 1 newReq = some (p, s', cp)) : FirstOk s' := by
  obtain ⟨c, hc, h1, h2⟩ := hptr
  have hX : s.base ≤ ptr - 32 := by
    have ht := hwf.2.2.2.1
    unfold TilesOk at ht
    have := (ht.mem_lt c hc).1
    omega
  unfold realloc at h
  by_cases e1 : newReq = usable s ptr
  · simp only [e1, ↓reduceIte, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h; exact h0
  by_cases e2 : newReq = 0
  · simp only [e1, e2, ↓reduceIte, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    obtain ⟨pre, post, hcs⟩ := List.append_of_mem hc
    have hc' : c = ⟨ptr - 32, c.size, true⟩ := by
      cases c; simp only at h1 h2 ⊢; subst h2; simp only [Chunk.mk.injEq, and_true]; omega
    rw [hc'] at hcs
    exact free_first hwf h0 hcs
  by_cases e3 : newReq < usable s ptr
  · simp only [e1, e2, e3, ↓reduceIte, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h; exact shrink_first h0 hX
  simp only [e1, e2, e3, ↓reduceIte] at h
  cases hg : growInplace grow s ptr newReq with
  | some s2 =>
    simp only [hg, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    exact growInplace_first h0 hX hg
  | none =>
    simp only [hg] at h
    cases ha : alloc grow hb 1 newReq s with
    | none => simp [ha] at h
    | some r =>
      obtain ⟨p1, s1⟩ := r
      simp only [ha, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      have hw1 := alloc_wf hwf ha
      have hf1 := alloc_first hwf h0 ha
      obtain ⟨pre', post', S, h1', -, h2'⟩ := alloc_chunks hwf ha
      obtain ⟨pre, post, hcs⟩ := List.append_of_mem hc
      have hc' : c = ⟨ptr - 32, c.size, true⟩ := by
        cases c; simp only at h1 h2 ⊢; subst h2; simp only [Chunk.mk.injEq, and_true]; omega
      rw [hc'] at hcs
      have hm : (⟨ptr - 32, c.size, true⟩ : Chunk) ∈ pre' ++ ⟨p1 - 32, S, false⟩ :: post' := by
        rw [← h1', hcs]; exact List.mem_append_right _ List.mem_cons_self
      have hm1 : (⟨ptr - 32, c.size, true⟩ : Chunk) ∈ chunks s1 := by
        rw [h2']
        rcases List.mem_append.mp hm with hm | hm
        · exact List.mem_append_left _ hm
        · rcases List.mem_cons.mp hm with hm | hm
          · simp at hm
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _ hm))
      obtain ⟨pre1, post1, hcs1⟩ := List.append_of_mem hm1
      exact free_first hw1 hf1 hcs1

end Picoalloc
