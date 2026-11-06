import Services.Picoalloc.Alloc

/-!
# `free`

`free` in three steps (`Model.lean`): merging with a free previous chunk (`mergePrev`), with a free
next chunk (`mergeNext`), and registering the merged chunk (`freeFinal`). Each step is stated on
the chunk list: the merges take the freed chunk's free neighbours into it, and the last step makes
the merged chunk free.
-/

namespace Picoalloc

theorem Coalesced.append {xs ys : List Chunk} :
    Coalesced (xs ++ ys) ↔ Coalesced xs ∧ Coalesced ys ∧
      (∀ x ∈ xs.getLast?, ∀ y ∈ ys.head?, (x.used || y.used) = true) := by
  induction xs with
  | nil => simp [Coalesced]
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases ys with
      | nil => simp [Coalesced]
      | cons y ys => simp [Coalesced, And.comm]
    | cons x' xs' =>
      simp only [List.cons_append, Coalesced] at ih ⊢
      rw [ih]
      simp only [List.getLast?_cons_cons]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h1, h2⟩, h3, h4⟩
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨h1, h2, h3, h4⟩

/-- **Merging two adjacent chunks** keeps a tiling. -/
theorem Tiles.merge {a limit : Nat} {pre post : List Chunk} {c d : Chunk} {u : Bool}
    (h : Tiles a limit (pre ++ c :: d :: post)) :
    Tiles a limit (pre ++ ⟨c.addr, c.size + d.size, u⟩ :: post) := by
  obtain ⟨m, h1, h2⟩ := Tiles.append.mp h
  obtain ⟨h3, h4, h5, h6, h7⟩ := h2
  refine Tiles.append.mpr ⟨m, h1, ?_⟩
  show c.addr = m ∧ 0 < c.size + d.size ∧ Tiles (m + 32 * (c.size + d.size)) limit post
  refine ⟨h3, by omega, ?_⟩
  rw [show m + 32 * (c.size + d.size) = m + 32 * c.size + 32 * d.size by omega]
  exact h7

/-- The free chunks of a chunk list, by bin and address. -/
def Fof (cs : List Chunk) (b a : Nat) : Prop := ∃ c ∈ cs, c.addr = a ∧ c.used = false ∧ binDown c.size = b

theorem Fof_disj {a0 T : Nat} {cs cs' : List Chunk} (h : Tiles a0 T cs) (hsub : ∀ c ∈ cs', c ∈ cs) :
    Disj (Fof cs') := by
  rintro b b' a ⟨c, hc, h1, -, h3⟩ ⟨d, hd, h1', -, h3'⟩
  have := h.addr_inj c (hsub c hc) d (hsub d hd) (h1.trans h1'.symm)
  subst this; rw [← h3, ← h3']

theorem Fof_skip {A B : List Chunk} {c : Chunk} (hc : c.used = true) (b a : Nat) :
    Fof (A ++ c :: B) b a ↔ Fof (A ++ B) b a := by
  constructor
  · rintro ⟨e, he, h1, h2, h3⟩
    rcases List.mem_append.mp he with he | he
    · exact ⟨e, List.mem_append_left _ he, h1, h2, h3⟩
    · rcases List.mem_cons.mp he with rfl | he
      · rw [hc] at h2; exact absurd h2 (by decide)
      · exact ⟨e, List.mem_append_right _ he, h1, h2, h3⟩
  · rintro ⟨e, he, h1, h2, h3⟩
    rcases List.mem_append.mp he with he | he
    · exact ⟨e, List.mem_append_left _ he, h1, h2, h3⟩
    · exact ⟨e, List.mem_append_right _ (List.mem_cons_of_mem _ he), h1, h2, h3⟩

theorem Fof_remove {A B : List Chunk} {d : Chunk} (hne : ∀ e ∈ A ++ B, e.addr ≠ d.addr) (b a : Nat) :
    (Fof (A ++ d :: B) b a ∧ a ≠ d.addr) ↔ Fof (A ++ B) b a := by
  constructor
  · rintro ⟨⟨e, he, h1, h2, h3⟩, hn⟩
    rcases List.mem_append.mp he with he | he
    · exact ⟨e, List.mem_append_left _ he, h1, h2, h3⟩
    · rcases List.mem_cons.mp he with rfl | he
      · exact absurd h1.symm hn
      · exact ⟨e, List.mem_append_right _ he, h1, h2, h3⟩
  · rintro ⟨e, he, h1, h2, h3⟩
    refine ⟨?_, fun h => hne e he (h1.trans h)⟩
    rcases List.mem_append.mp he with he | he
    · exact ⟨e, List.mem_append_left _ he, h1, h2, h3⟩
    · exact ⟨e, List.mem_append_right _ (List.mem_cons_of_mem _ he), h1, h2, h3⟩

/-- In a tiling, the chunks other than `d` lie at other addresses. -/
theorem Tiles.others {a T : Nat} {A B : List Chunk} {d : Chunk} (h : Tiles a T (A ++ d :: B)) :
    ∀ e ∈ A ++ B, e.addr ≠ d.addr := by
  intro e he
  obtain ⟨m, h1, h2, h3, h4⟩ := Tiles.append.mp h
  rcases List.mem_append.mp he with he | he
  · have hA : ∀ x ∈ A, x.addr + 32 * x.size ≤ m := fun x hx => (h1.mem_lt x hx).2.1
    have := hA e he
    have := (h1.mem_lt e he).2.2
    omega
  · have := (h4.mem_lt e he).1
    omega

/-- **`free`'s merge with the previous chunk**: the freed chunk `X` takes in the chunk before it
    if that one is free. -/
theorem mergePrev_ok {s s1 : State} {T X n M sz1 pv : Nat} {pre post : List Chunk}
    (htl : Tiles s.base T (pre ++ ⟨X, n, true⟩ :: post))
    (hprev : PrevOk s (pre ++ ⟨X, n, true⟩ :: post))
    (henc : ∀ c ∈ pre ++ ⟨X, n, true⟩ :: post, (s.hdr c.addr).size = sizeWord c.size c.used)
    (hcoal : Coalesced (pre ++ ⟨X, n, true⟩ :: post))
    (hF : FreeLists s (Fof (pre ++ ⟨X, n, true⟩ :: post))) (hbits : BitsOk s.secondary s.primary s.heads)
    (hm : mergePrev s X n (s.hdr X).prev = (s1, M, sz1, pv)) :
    ∃ pre0 L, pre = pre0 ++ L ∧ (∀ c ∈ L, c.used = false) ∧
      Tiles s.base T (pre0 ++ ⟨M, sz1, true⟩ :: post) ∧ M + 32 * sz1 = X + 32 * n ∧
      (∀ c ∈ pre0.getLast?, c.used = true ∧ pv = c.size) ∧
      FreeLists s1 (Fof (pre0 ++ post)) ∧ BitsOk s1.secondary s1.primary s1.heads ∧
      (∀ z, (s1.hdr z).prev = (s.hdr z).prev ∧ (s1.hdr z).size = (s.hdr z).size) ∧
      s1.base = s.base ∧ s1.allocated = s.allocated ∧ (M = X ∨ ∃ c ∈ pre, c.addr = M) := by
  unfold mergePrev at hm
  rcases List.eq_nil_or_concat pre with h0 | ⟨pre1, d, hd⟩
  · subst h0
    have hX : X = s.base := htl.1
    rw [if_neg (fun h => h hX)] at hm
    simp only [Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hm
    exact ⟨[], [], rfl, by simp, htl, rfl, by simp, hF.iff (fun b a _ => Fof_skip rfl b a), hbits,
      fun _ => ⟨rfl, rfl⟩, rfl, rfl, Or.inl rfl⟩
  · rw [List.concat_eq_append] at hd
    subst hd
    have hcs : pre1 ++ [d] ++ ⟨X, n, true⟩ :: post = pre1 ++ d :: ⟨X, n, true⟩ :: post := by simp
    have htl0 := htl
    rw [hcs] at htl hprev henc hcoal hF
    obtain ⟨m0, -, hd1, hd2, hX1, hX2, -⟩ := Tiles.append.mp htl
    simp only at hX1
    have hdb := (htl.mem_lt d (List.mem_append_right _ List.mem_cons_self)).1
    have hXb : X ≠ s.base := by
      omega
    have hpX : (s.hdr X).prev = d.size := ((PrevOk.append.mp hprev).2.1).1
    have hdenc := henc d (List.mem_append_right _ List.mem_cons_self)
    have hpc : X - 32 * d.size = d.addr := by omega
    rw [if_pos hXb] at hm
    dsimp only at hm
    rw [hpX, hpc, hdenc, wordUsed_sizeWord, wordSize_sizeWord] at hm
    cases hu : d.used
    · rw [hu] at hm
      simp only [Bool.not_false, ↓reduceIte, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hm
      have hlast := (Coalesced.around hu hcoal).2
      have hplink := (PrevOk.append.mp hprev).2.2
      obtain ⟨r1, r2⟩ := remove_ok (bin := binDown d.size) (x := d.addr) hF (Fof_disj htl (fun _ h => h)) hbits
        (toBin_lt false (Nat.min_le_right _ _)) ⟨d, List.mem_append_right _ List.mem_cons_self, rfl, hu, rfl⟩
      have hm' := htl.merge (u := true)
      rw [Nat.add_comm d.size n] at hm'
      refine ⟨pre1, [d], rfl, by simp [hu], hm', by omega,
        fun c hc => ⟨hlast c hc, hplink c hc d rfl⟩, r1.iff (fun b a _ => ?_), r2, fun z => unregister_hdr,
        unregister_base, unregister_allocated, Or.inr ⟨d, by simp, rfl⟩⟩
      have hne := htl.others (A := pre1) (B := ⟨X, n, true⟩ :: post)
      exact (Fof_remove hne b a).trans (Fof_skip rfl b a)
    · rw [hu] at hm
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hm
      refine ⟨pre1 ++ [d], [], by simp, by simp, htl0, rfl, by simp [hu], ?_, hbits, fun _ => ⟨rfl, rfl⟩,
        rfl, rfl, Or.inl rfl⟩
      rw [← hcs] at hF
      exact hF.iff (fun b a _ => Fof_skip rfl b a)

/-- **`free`'s merge with the next chunk**: the merged chunk takes in the chunk after it if that one
    is free. -/
theorem mergeNext_ok {s1 s2 : State} {B T M sz1 total : Nat} {pre0 post : List Chunk}
    (htl : Tiles B T (pre0 ++ ⟨M, sz1, true⟩ :: post))
    (henc : ∀ c ∈ post, (s1.hdr c.addr).size = sizeWord c.size c.used)
    (hcoal : Coalesced post)
    (hF : FreeLists s1 (Fof (pre0 ++ post))) (hbits : BitsOk s1.secondary s1.primary s1.heads)
    (hn : mergeNext s1 M sz1 T = (s2, total)) :
    ∃ R post0, post = R ++ post0 ∧ (∀ c ∈ R, c.used = false) ∧
      Tiles B T (pre0 ++ ⟨M, total, true⟩ :: post0) ∧ (∀ c ∈ post0.head?, c.used = true) ∧
      FreeLists s2 (Fof (pre0 ++ post0)) ∧ BitsOk s2.secondary s2.primary s2.heads ∧
      (∀ z, (s2.hdr z).prev = (s1.hdr z).prev ∧ (s2.hdr z).size = (s1.hdr z).size) ∧
      s2.base = s1.base ∧ s2.allocated = s1.allocated ∧ sz1 ≤ total := by
  unfold mergeNext at hn
  obtain ⟨m0, -, hM1, hM2, hrest⟩ := Tiles.append.mp htl
  simp only at hM1 hM2 hrest
  subst hM1
  cases post with
  | nil =>
    have hT : M + 32 * sz1 = T := hrest
    rw [if_neg (by omega)] at hn
    simp only [Prod.mk.injEq] at hn
    obtain ⟨rfl, rfl⟩ := hn
    exact ⟨[], [], rfl, by simp, htl, by simp, hF, hbits, fun _ => ⟨rfl, rfl⟩, rfl, rfl, Nat.le_refl _⟩
  | cons e post' =>
    obtain ⟨he1, he2, he3⟩ := hrest
    have heT := (he3.le)
    rw [← he1, if_pos (by omega), henc e List.mem_cons_self, wordUsed_sizeWord, wordSize_sizeWord] at hn
    cases hu : e.used
    · rw [hu] at hn
      simp only [Bool.not_false, ↓reduceIte, Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      have hhead := (Coalesced.around (pre := []) hu hcoal).1
      have hsub : ∀ c ∈ pre0 ++ e :: post', c ∈ pre0 ++ ⟨M, sz1, true⟩ :: e :: post' := by
        intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · exact List.mem_append_left _ hc
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ hc)
      obtain ⟨r1, r2⟩ := remove_ok (bin := binDown e.size) (x := e.addr) hF (Fof_disj htl hsub)
        hbits (toBin_lt false (Nat.min_le_right _ _)) ⟨e, List.mem_append_right _ List.mem_cons_self, rfl, hu, rfl⟩
      have hm' := htl.merge (u := true)
      refine ⟨[e], post', rfl, by simp [hu], hm', hhead, r1.iff (fun b a _ => ?_), r2, fun z => unregister_hdr,
        unregister_base, unregister_allocated, Nat.le_add_right _ _⟩
      have hne : ∀ c ∈ pre0 ++ post', c.addr ≠ e.addr := by
        have h2 := htl
        rw [show pre0 ++ ⟨M, sz1, true⟩ :: e :: post' = (pre0 ++ [⟨M, sz1, true⟩]) ++ e :: post' by simp] at h2
        intro c hc
        refine h2.others c ?_
        rcases List.mem_append.mp hc with hc | hc
        · exact List.mem_append_left _ (List.mem_append_left _ hc)
        · exact List.mem_append_right _ hc
      exact Fof_remove hne b a
    · rw [hu] at hn
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      exact ⟨[], e :: post', rfl, by simp, htl, by simp [hu], hF, hbits, fun _ => ⟨rfl, rfl⟩, rfl, rfl,
        Nat.le_refl _⟩

theorem Fof_insert {A B : List Chunk} {c : Chunk} (b a : Nat) :
    Fof (A ++ c :: B) b a ↔ Fof (A ++ B) b a ∨ (c.used = false ∧ b = binDown c.size ∧ a = c.addr) := by
  constructor
  · rintro ⟨e, he, h1, h2, h3⟩
    rcases List.mem_append.mp he with he | he
    · exact Or.inl ⟨e, List.mem_append_left _ he, h1, h2, h3⟩
    · rcases List.mem_cons.mp he with rfl | he
      · exact Or.inr ⟨h2, h3.symm, h1.symm⟩
      · exact Or.inl ⟨e, List.mem_append_right _ he, h1, h2, h3⟩
  · rintro (⟨e, he, h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · rcases List.mem_append.mp he with he | he
      · exact ⟨e, List.mem_append_left _ he, h1, h2, h3⟩
      · exact ⟨e, List.mem_append_right _ (List.mem_cons_of_mem _ he), h1, h2, h3⟩
    · exact ⟨c, List.mem_append_right _ List.mem_cons_self, h3.symm, h1, h2.symm⟩

/-- **`free`'s last step**: the merged chunk `M` of `total` units is registered free, and the next
    chunk records its size. -/
theorem freeFinal_facts {s2 : State} {M pv total T : Nat} {F : Nat → Nat → Prop}
    (htot : total ≠ 0) (hM0 : M ≠ 0) (hF : FreeLists s2 F) (hd : Disj F)
    (hbits : BitsOk s2.secondary s2.primary s2.heads) (hM : ∀ b, ¬ F b M) :
    FreeLists (freeFinal s2 M pv total T) (fun b a => F b a ∨ (b = binDown total ∧ a = M)) ∧
      BitsOk (freeFinal s2 M pv total T).secondary (freeFinal s2 M pv total T).primary
        (freeFinal s2 M pv total T).heads ∧
      (∀ x, ((freeFinal s2 M pv total T).hdr x).size = if x = M then sizeWord total false else (s2.hdr x).size) ∧
      (∀ x, ((freeFinal s2 M pv total T).hdr x).prev =
        if x = M then pv else if x = M + 32 * total ∧ M + 32 * total < T then total else (s2.hdr x).prev) ∧
      (freeFinal s2 M pv total T).base = s2.base ∧ (freeFinal s2 M pv total T).allocated = s2.allocated := by
  obtain ⟨p1, p2⟩ := push_ok (prev := pv) hF hd hbits htot (toBin_lt false (Nat.min_le_right _ _)) hM0 hM
  have hsz : ∀ x, ((register s2 M pv total).1.hdr x).size = if x = M then sizeWord total false else (s2.hdr x).size := by
    intro x
    by_cases hx : x = M
    · subst hx; rw [register_size_self htot, if_pos rfl]
    · rw [(register_hdr_other hx).2.1, if_neg hx]
  have hpv : ∀ x, ((register s2 M pv total).1.hdr x).prev = if x = M then pv else (s2.hdr x).prev := by
    intro x
    by_cases hx : x = M
    · subst hx; rw [register_prev_self htot, if_pos rfl]
    · rw [(register_hdr_other hx).1, if_neg hx]
  have hne : M + 32 * total ≠ M := by omega
  have h2 : (register s2 M pv total).2 = total := by rw [register_snd, if_neg htot]
  unfold freeFinal
  rw [h2]
  split
  · rename_i hlt
    refine ⟨p1.congr rfl (setHdr_next (f := fun h => { h with prev := total }) (fun _ => rfl))
      (setHdr_prevL (f := fun h => { h with prev := total }) (fun _ => rfl)), p2,
      fun x => by rw [setHdr_prev_size, hsz], fun x => ?_, by simp, by simp⟩
    rw [setHdr_prev_get, hpv]
    by_cases hx : x = M
    · subst hx; simp; omega
    · by_cases hx2 : x = M + 32 * total
      · simp [hx, hx2, hlt]; omega
      · simp [hx, hx2]
  · rename_i hlt
    refine ⟨p1, p2, hsz, fun x => ?_, by simp, by simp⟩
    rw [hpv]
    by_cases hx : x = M
    · simp [hx]
    · simp [hx, hlt]

theorem free_eq (s : State) (ptr : Nat) : free s ptr =
    freeFinal (mergeNext (mergePrev s (ptr - 32) (wordSize (s.hdr (ptr - 32)).size) (s.hdr (ptr - 32)).prev).1
        (mergePrev s (ptr - 32) (wordSize (s.hdr (ptr - 32)).size) (s.hdr (ptr - 32)).prev).2.1
        (mergePrev s (ptr - 32) (wordSize (s.hdr (ptr - 32)).size) (s.hdr (ptr - 32)).prev).2.2.1 s.top).1
      (mergePrev s (ptr - 32) (wordSize (s.hdr (ptr - 32)).size) (s.hdr (ptr - 32)).prev).2.1
      (mergePrev s (ptr - 32) (wordSize (s.hdr (ptr - 32)).size) (s.hdr (ptr - 32)).prev).2.2.2
      (mergeNext (mergePrev s (ptr - 32) (wordSize (s.hdr (ptr - 32)).size) (s.hdr (ptr - 32)).prev).1
        (mergePrev s (ptr - 32) (wordSize (s.hdr (ptr - 32)).size) (s.hdr (ptr - 32)).prev).2.1
        (mergePrev s (ptr - 32) (wordSize (s.hdr (ptr - 32)).size) (s.hdr (ptr - 32)).prev).2.2.1 s.top).2
      s.top := rfl

/-- **`free` on the chunk list, and the invariant**: the freed chunk merges with its free
    neighbours into one free chunk, every other chunk is as it was, and the heap stays
    well-formed. -/
theorem free_ok {s : State} {ptr n : Nat} {pre post : List Chunk} (hwf : WF s)
    (hcs : chunks s = pre ++ ⟨ptr - 32, n, true⟩ :: post) :
    ∃ pre0 L R post0 M total, pre = pre0 ++ L ∧ post = R ++ post0 ∧ (∀ c ∈ L ++ R, c.used = false) ∧
      chunks (free s ptr) = pre0 ++ ⟨M, total, false⟩ :: post0 ∧ WF (free s ptr) ∧
      M = (mergePrev s (ptr - 32) (wordSize (s.hdr (ptr - 32)).size) (s.hdr (ptr - 32)).prev).2.1 := by
  have hwf' := hwf
  obtain ⟨hb0, hbal, hfit, htiles, hcoal, hprev, hlists, hspace⟩ := hwf'
  unfold TilesOk at htiles
  unfold CoalOk at hcoal
  unfold PrevsOk at hprev
  unfold ListsOk' at hlists
  unfold SpaceOk at hspace
  have henc := @chunks_hdr s
  rw [hcs] at htiles hcoal hprev hlists hspace henc
  rw [free_eq]
  generalize hX : ptr - 32 = X at *
  have hn : wordSize (s.hdr X).size = n := by
    rw [henc ⟨X, n, true⟩ (List.mem_append_right _ List.mem_cons_self), wordSize_sizeWord]
  rw [hn]
  rcases hm : mergePrev s X n (s.hdr X).prev with ⟨s1, M, sz1, pv⟩
  dsimp only
  rcases hn2 : mergeNext s1 M sz1 s.top with ⟨s2, total⟩
  dsimp only
  have hF0 : FreeLists s (Fof (pre ++ ⟨X, n, true⟩ :: post)) := fun b hb => hlists.lists b hb
  have hbits : BitsOk s.secondary s.primary s.heads := ⟨hlists.bits, hlists.prim, hlists.words, hlists.primW⟩
  obtain ⟨pre0, L, hpre, hLf, htl1, -, hlast, hF1, hb1, hps1, hbase1, halloc1, hMw⟩ :=
    mergePrev_ok htiles hprev henc hcoal hF0 hbits hm
  have hcX : Coalesced (⟨X, n, true⟩ :: post) := (Coalesced.append.mp hcoal).2.1
  have hcp : Coalesced post := ((Coalesced.append (xs := [⟨X, n, true⟩]) (ys := post)).mp hcX).2.1
  have henc' : ∀ c ∈ post, (s1.hdr c.addr).size = sizeWord c.size c.used := fun c hc => by
    rw [(hps1 _).2]; exact henc c (List.mem_append_right _ (List.mem_cons_of_mem _ hc))
  obtain ⟨R, post0, hpost, hRf, htl2, hhead, hF2, hb2, hps2, hbase2, halloc2, -⟩ :=
    mergeNext_ok htl1 henc' hcp hF1 hb1 hn2
  subst hpre hpost
  -- the merged chunk's place
  obtain ⟨hpa, hph, hpp, hpt⟩ := Tiles.around htl2
  have hMm := htl2.mem_lt ⟨M, total, true⟩ (List.mem_append_right _ List.mem_cons_self)
  simp only at hMm
  have hM0 : M ≠ 0 := by omega
  have hpre0 : ∀ d ∈ pre0, d.addr < M := fun d hd => by
    have := hpa d hd
    have := (htl2.mem_lt d (List.mem_append_left _ hd)).2.2
    omega
  have hMnot : ∀ b, ¬ Fof (pre0 ++ post0) b M := by
    rintro b ⟨c, hc, h1, -, -⟩
    exact htl2.others c hc h1
  have hsub : ∀ c ∈ pre0 ++ post0, c ∈ pre0 ++ ⟨M, total, true⟩ :: post0 := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact List.mem_append_left _ hc
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hc)
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := freeFinal_facts (M := M) (total := total) (pv := pv) (T := s.top) (by omega) hM0 hF2
    (Fof_disj htl2 hsub) hb2 hMnot
  generalize freeFinal s2 M pv total s.top = s' at f1 f2 f3 f4 f5 f6 ⊢
  -- the old chunk list, around the merged one
  have hcs2 : pre0 ++ L ++ ⟨X, n, true⟩ :: (R ++ post0) = pre0 ++ ((L ++ ⟨X, n, true⟩ :: R) ++ post0) := by simp
  rw [hcs2] at hcoal hprev hspace henc
  have memPre : ∀ c ∈ pre0, c ∈ pre0 ++ ((L ++ ⟨X, n, true⟩ :: R) ++ post0) :=
    fun c hc => List.mem_append_left _ hc
  have memPost : ∀ c ∈ post0, c ∈ pre0 ++ ((L ++ ⟨X, n, true⟩ :: R) ++ post0) :=
    fun c hc => List.mem_append_right _ (List.mem_append_right _ hc)
  have hsize0 : ∀ c ∈ pre0 ++ post0, (s2.hdr c.addr).size = sizeWord c.size c.used := by
    intro c hc
    rw [(hps2 _).2, (hps1 _).2]
    rcases List.mem_append.mp hc with hc | hc
    · exact henc c (memPre c hc)
    · exact henc c (memPost c hc)
  have hbase' : s'.base = s.base := by rw [f5, hbase2, hbase1]
  have halloc' : s'.allocated = s.allocated := by rw [f6, halloc2, halloc1]
  have htop' : s'.top = s.top := by unfold State.top; rw [hbase']
  have hchunks : chunks s' = pre0 ++ ⟨M, total, false⟩ :: post0 := by
    apply chunks_eq
    · rw [hbase', htop']; exact htl2.relabel
    · intro c hc
      rw [f3]
      rcases List.mem_append.mp hc with hc' | hc'
      · rw [if_neg (Nat.ne_of_lt (hpre0 c hc'))]
        exact hsize0 c (List.mem_append_left _ hc')
      · rcases List.mem_cons.mp hc' with rfl | hc'
        · rw [if_pos rfl]
        · rw [if_neg (htl2.others c (List.mem_append_right _ hc'))]
          exact hsize0 c (List.mem_append_right _ hc')
  have hprevs : ∀ x, (s'.hdr x).prev =
      if x = M then pv else if x = M + 32 * total ∧ M + 32 * total < s.top then total else (s.hdr x).prev := by
    intro x; rw [f4, (hps2 _).1, (hps1 _).1]
  refine ⟨pre0, L, R, post0, M, total, rfl, rfl, fun c hc => ?_, hchunks, ?_, rfl⟩
  · rcases List.mem_append.mp hc with hc | hc
    · exact hLf c hc
    · exact hRf c hc
  refine ⟨by rw [hbase']; exact hb0, by rw [hbase']; exact hbal, by rw [htop']; exact hfit, ?_, ?_, ?_, ?_, ?_⟩
  · -- tiling
    unfold TilesOk; rw [hchunks, hbase', htop']; exact htl2.relabel
  · -- coalesced
    unfold CoalOk; rw [hchunks]
    obtain ⟨c1, c2, -⟩ := Coalesced.append.mp hcoal
    have c3 := (Coalesced.append.mp c2).2.1
    refine Coalesced.append.mpr ⟨c1, (Coalesced.append (xs := [⟨M, total, false⟩])).mpr ⟨trivial, c3, ?_⟩, ?_⟩
    · intro x _ y hy; rw [hhead y hy]; simp
    · intro x hx _ _; rw [(hlast x hx).1]; simp
  · -- prev links
    unfold PrevsOk; rw [hchunks]
    obtain ⟨p1, p2, -⟩ := PrevOk.append.mp hprev
    have p3 := (PrevOk.append.mp p2).2.1
    refine PrevOk.append.mpr ⟨p1.congr (fun d hd => ?_), (PrevOk.append (xs := [⟨M, total, false⟩])).mpr
      ⟨trivial, p3.congr (fun d hd => ?_), fun x hx y hy => ?_⟩, fun x hx y hy => ?_⟩
    · have := hpre0 d (List.mem_of_mem_tail hd)
      rw [hprevs, if_neg (by omega), if_neg (by omega)]
    · have := hpt d hd
      rw [hprevs, if_neg (by omega), if_neg (by omega)]
    · simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hx
      subst hx
      have h1 := hph y hy
      have h2 := (hpp y (by cases post0 <;> simp_all)).2
      rw [hprevs, if_neg (by omega), if_pos ⟨h1, by omega⟩]
    · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      rw [hprevs, if_pos rfl]
      exact (hlast x hx).2
  · -- free lists
    unfold ListsOk'; rw [hchunks]
    obtain ⟨b1, b2, b3, b4⟩ := f2
    have hL : FreeLists s' (Fof (pre0 ++ ⟨M, total, false⟩ :: post0)) :=
      f1.iff (fun b a _ => by rw [Fof_insert]; simp only [true_and])
    exact ⟨fun b hb => hL b hb, b1, b2, b3, b4⟩
  · -- space
    unfold SpaceOk; rw [hchunks, hbase', halloc']
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hspace c (memPre c hc)
    · rcases List.mem_cons.mp hc with rfl | hc
      · refine ⟨fun h => by simp at h, ?_⟩
        rcases hMw with rfl | ⟨c', hc', rfl⟩
        · exact (hspace ⟨_, n, true⟩ (List.mem_append_right _ (List.mem_append_left _
            (List.mem_append_right _ List.mem_cons_self)))).2
        · rcases List.mem_append.mp hc' with hc' | hc'
          · exact (hspace c' (memPre c' hc')).2
          · exact (hspace c' (List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ hc')))).2
      · exact hspace c (memPost c hc)

/-- **`free` keeps the heap well-formed**, for the data address of an allocated chunk. -/
theorem free_wf {s : State} {ptr : Nat} (hwf : WF s)
    (h : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) : WF (free s ptr) := by
  obtain ⟨c, hc, h1, h2⟩ := h
  obtain ⟨pre, post, hcs⟩ := List.append_of_mem hc
  have hc' : c = ⟨ptr - 32, c.size, true⟩ := by
    cases c; simp only at h1 h2 ⊢; subst h2; simp only [Chunk.mk.injEq, and_true]; omega
  rw [hc'] at hcs
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hw, -⟩ := free_ok hwf hcs
  exact hw

end Picoalloc
