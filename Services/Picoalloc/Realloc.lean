import Services.Picoalloc.Free

/-!
# `realloc`

`shrink` keeps the front of the chunk and frees the rest, merged with a free next chunk;
`growInplace` takes in a free next chunk, the rest of which stays free; otherwise `realloc` is an
`alloc` and a `free`. Each keeps the heap invariant (`realloc_wf`).
-/

namespace Picoalloc

/-- Projections of a chunk literal, as rewrites (the kernel can be slow to see these by
    unfolding when a field is arithmetic). -/
theorem Chunk.addr_mk' (a n : Nat) (u : Bool) : Chunk.addr ⟨a, n, u⟩ = a := rfl
theorem Chunk.size_mk' (a n : Nat) (u : Bool) : Chunk.size ⟨a, n, u⟩ = n := rfl

/-- **Splitting off a free tail**: in a state `s2` where the allocated chunk `X` of `total` units now
    records `k < total` units and the lists hold the other free chunks, `freeFinal` frees the
    rest; the heap is well-formed with allocated space `A`. -/
theorem splitTail_ok {s s2 : State} {X k total A : Nat} {pre post0 : List Chunk}
    (hb0 : s.base ≠ 0) (hbal : s.base % 32 = 0) (hfit : s.top < 2 ^ 32)
    (htl2 : Tiles s.base s.top (pre ++ ⟨X, total, true⟩ :: post0)) (hk0 : 0 < k) (hkt : k < total)
    (hF2 : FreeLists s2 (Fof (pre ++ post0))) (hb2 : BitsOk s2.secondary s2.primary s2.heads)
    (hsz2 : ∀ x, (s2.hdr x).size = if x = X then sizeWord k true else (s.hdr x).size)
    (hpv2 : ∀ x, (s2.hdr x).prev = (s.hdr x).prev)
    (hbase2 : s2.base = s.base) (halloc2 : s2.allocated = A)
    (henc : ∀ c ∈ pre ++ post0, (s.hdr c.addr).size = sizeWord c.size c.used)
    (hcpre : Coalesced pre) (hcpost : Coalesced post0) (hhead : ∀ c ∈ post0.head?, c.used = true)
    (hppre : PrevOk s pre) (hppost : PrevOk s post0) (hlink : ∀ x ∈ pre.getLast?, (s.hdr X).prev = x.size)
    (hsp : ∀ c ∈ pre ++ post0, (c.used = true → c.addr + 32 * c.size ≤ s.base + 32 * A) ∧
      c.addr + 32 ≤ s.base + 32 * A)
    (hXsp : X + 32 * k + 32 ≤ s.base + 32 * A) :
    chunks (freeFinal s2 (X + 32 * k) k (total - k) s.top) =
        pre ++ ⟨X, k, true⟩ :: ⟨X + 32 * k, total - k, false⟩ :: post0 ∧
      WF (freeFinal s2 (X + 32 * k) k (total - k) s.top) := by
  have htl3 := Tiles.split (k := k) (v := true) (w := false) hk0 hkt htl2
  obtain ⟨hpa, -, hpp2, hpt2⟩ := Tiles.around htl2
  have hXm := htl2.mem_lt ⟨X, total, true⟩ (List.mem_append_right _ List.mem_cons_self)
  simp only at hXm
  have hpreX : ∀ d ∈ pre, d.addr < X := fun d hd => by
    have := hpa d hd
    have := (htl2.mem_lt d (List.mem_append_left _ hd)).2.2
    omega
  have hsub : ∀ c ∈ pre ++ post0, c ∈ pre ++ ⟨X, total, true⟩ :: post0 := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact List.mem_append_left _ hc
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hc)
  have hMnot : ∀ b, ¬ Fof (pre ++ post0) b (X + 32 * k) := by
    rintro b ⟨c, hc, h1, -, -⟩
    rcases List.mem_append.mp hc with hc | hc
    · have := hpreX c hc; omega
    · have := (hpp2 c hc).1; omega
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := freeFinal_facts (M := X + 32 * k) (total := total - k) (pv := k)
    (T := s.top) (by omega) (by omega) hF2 (Fof_disj htl2 hsub) hb2 hMnot
  generalize freeFinal s2 (X + 32 * k) k (total - k) s.top = s' at f1 f2 f3 f4 f5 f6 ⊢
  have hbase' : s'.base = s.base := by rw [f5, hbase2]
  have halloc' : s'.allocated = A := by rw [f6, halloc2]
  have htop' : s'.top = s.top := by unfold State.top; rw [hbase']
  have hsizes : ∀ x, (s'.hdr x).size = if x = X + 32 * k then sizeWord (total - k) false
      else if x = X then sizeWord k true else (s.hdr x).size := by
    intro x
    rw [f3, hsz2]
  have hprevs : ∀ x, (s'.hdr x).prev = if x = X + 32 * k then k
      else if x = X + 32 * k + 32 * (total - k) ∧ X + 32 * k + 32 * (total - k) < s.top then total - k
      else (s.hdr x).prev := by
    intro x; rw [f4, hpv2]
  have hchunks : chunks s' = pre ++ ⟨X, k, true⟩ :: ⟨X + 32 * k, total - k, false⟩ :: post0 := by
    apply chunks_eq
    · rw [hbase', htop']; exact htl3
    · intro c hc
      rw [hsizes]
      rcases List.mem_append.mp hc with hc' | hc'
      · have := hpreX c hc'
        rw [if_neg (by omega), if_neg (by omega)]
        exact henc c (List.mem_append_left _ hc')
      · rcases List.mem_cons.mp hc' with rfl | hc'
        · rw [if_neg (show X ≠ X + 32 * k by omega), if_pos rfl]
        · rcases List.mem_cons.mp hc' with rfl | hc'
          · rw [if_pos rfl]
          · have := (hpp2 c hc').1
            rw [if_neg (by omega), if_neg (by omega)]
            exact henc c (List.mem_append_right _ hc')
  refine ⟨hchunks, by rw [hbase']; exact hb0, by rw [hbase']; exact hbal, by rw [htop']; exact hfit,
    ?_, ?_, ?_, ?_, ?_⟩
  · unfold TilesOk; rw [hchunks, hbase', htop']; exact htl3
  · -- coalesced
    unfold CoalOk; rw [hchunks]
    have c4 : Coalesced (⟨X + 32 * k, total - k, false⟩ :: post0) :=
      (Coalesced.append (xs := [⟨X + 32 * k, total - k, false⟩])).mpr
        ⟨trivial, hcpost, fun x _ y hy => by rw [hhead y hy]; simp⟩
    refine Coalesced.append.mpr ⟨hcpre, (Coalesced.append (xs := [⟨X, k, true⟩])).mpr ⟨trivial, c4, ?_⟩, ?_⟩
    · intro x hx _ _
      simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hx
      subst hx; simp
    · intro _ _ y hy
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy; simp
  · -- prev links
    unfold PrevsOk; rw [hchunks]
    have p4 : PrevOk s' (⟨X + 32 * k, total - k, false⟩ :: post0) :=
      (PrevOk.append (xs := [⟨X + 32 * k, total - k, false⟩])).mpr ⟨trivial, hppost.congr (fun d hd => ?_),
        fun x hx y hy => ?_⟩
    · refine PrevOk.append.mpr ⟨hppre.congr (fun d hd => ?_), ⟨?_, p4⟩, fun x hx y hy => ?_⟩
      · have := hpreX d (List.mem_of_mem_tail hd)
        rw [hprevs, if_neg (by omega), if_neg (by omega)]
      · show (s'.hdr (Chunk.addr ⟨X + 32 * k, total - k, false⟩)).prev = Chunk.size ⟨X, k, true⟩
        rw [Chunk.addr_mk', Chunk.size_mk', hprevs, if_pos rfl]
      · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
        subst hy
        have := hpreX x (List.mem_of_getLast? hx)
        rw [Chunk.addr_mk', hprevs, if_neg (show X ≠ X + 32 * k by omega), if_neg (by omega)]
        exact hlink x hx
    · have := hpt2 d hd
      rw [hprevs, if_neg (by omega), if_neg (by omega)]
    · simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hx
      subst hx
      have h1 := (hpp2 y (List.mem_of_mem_head? hy))
      have h2 : y.addr = X + 32 * total := by
        cases post0 with
        | nil => simp at hy
        | cons e es =>
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
          subst hy
          obtain ⟨m, -, hXm', -, he, -⟩ := Tiles.append.mp htl2
          simp only at he hXm'
          omega
      rw [Chunk.size_mk', hprevs, if_neg (by omega), if_pos ⟨by omega, by omega⟩]
  · -- free lists
    unfold ListsOk'; rw [hchunks]
    obtain ⟨b1, b2, b3, b4⟩ := f2
    have hL : FreeLists s' (Fof (pre ++ ⟨X, k, true⟩ :: ⟨X + 32 * k, total - k, false⟩ :: post0)) :=
      f1.iff (fun b a _ => by rw [Fof_skip rfl, Fof_insert]; simp only [true_and])
    exact ⟨fun b hb => hL b hb, b1, b2, b3, b4⟩
  · -- space
    unfold SpaceOk; rw [hchunks, hbase', halloc']
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hsp c (List.mem_append_left _ hc)
    · rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨fun _ => by simp only; omega, by simp only; omega⟩
      · rcases List.mem_cons.mp hc with rfl | hc
        · exact ⟨fun h => by simp at h, by simp only; omega⟩
        · exact hsp c (List.mem_append_right _ hc)

/-- **`shrink` on the chunk list, and the invariant**: the chunk keeps `newReq + 1` units, and the
    rest, merged with a free next chunk, becomes one free chunk; the heap stays well-formed. -/
theorem shrink_ok {s : State} {ptr newReq cur : Nat} {pre post : List Chunk} (hwf : WF s)
    (hcs : chunks s = pre ++ ⟨ptr - 32, cur, true⟩ :: post) (hlt : newReq + 1 < cur) :
    ∃ R post0 rest, post = R ++ post0 ∧ (∀ c ∈ R, c.used = false) ∧
      chunks (shrink s ptr newReq) =
        pre ++ ⟨ptr - 32, newReq + 1, true⟩ :: ⟨ptr - 32 + 32 * (newReq + 1), rest, false⟩ :: post0 ∧
      WF (shrink s ptr newReq) := by
  have hwf' := hwf
  obtain ⟨hb0, hbal, hfit, htiles, hcoal, hprev, hlists, hspace⟩ := hwf'
  unfold TilesOk at htiles
  unfold CoalOk at hcoal
  unfold PrevsOk at hprev
  unfold ListsOk' at hlists
  unfold SpaceOk at hspace
  have henc := @chunks_hdr s
  rw [hcs] at htiles hcoal hprev hlists hspace henc
  generalize hX : ptr - 32 = X at *
  generalize hk : newReq + 1 = k at *
  have hcur : wordSize (s.hdr X).size = cur := by
    rw [henc ⟨X, cur, true⟩ (List.mem_append_right _ List.mem_cons_self), wordSize_sizeWord]
  unfold shrink
  simp only [hX, hk]
  rw [hcur, if_neg (by omega), setHdr_base, show s.base + 32 * maxSize = s.top from rfl]
  generalize hs0 : setHdr s X (fun h => { h with size := sizeWord k true }) = s0
  have h0x : ∀ z, z ≠ X → s0.hdr z = s.hdr z := fun z hz => by rw [← hs0, setHdr_other hz]
  have h0X : s0.hdr X = { s.hdr X with size := sizeWord k true } := by rw [← hs0, setHdr_self]
  have h0prev : ∀ z, (s0.hdr z).prev = (s.hdr z).prev := fun z => by
    by_cases hz : z = X
    · subst hz; rw [h0X]
    · rw [h0x z hz]
  rcases hn : mergeNext s0 X cur s.top with ⟨s2, total⟩
  dsimp only
  -- where things lie
  obtain ⟨hpa, -, hpp, -⟩ := Tiles.around htiles
  have hXm := htiles.mem_lt ⟨X, cur, true⟩ (List.mem_append_right _ List.mem_cons_self)
  simp only at hXm
  have hpreX : ∀ d ∈ pre, d.addr < X := fun d hd => by
    have := hpa d hd
    have := (htiles.mem_lt d (List.mem_append_left _ hd)).2.2
    omega
  have hF0 : FreeLists s (Fof (pre ++ ⟨X, cur, true⟩ :: post)) := fun b hb => hlists.lists b hb
  have hbits : BitsOk s.secondary s.primary s.heads := ⟨hlists.bits, hlists.prim, hlists.words, hlists.primW⟩
  have hF0' : FreeLists s0 (Fof (pre ++ post)) :=
    (hF0.congr (by rw [← hs0]; rfl) (fun z => by rw [← hs0]; exact setHdr_next (f := fun h => { h with size := sizeWord k true }) (fun _ => rfl) z)
      (fun z => by rw [← hs0]; exact setHdr_prevL (f := fun h => { h with size := sizeWord k true }) (fun _ => rfl) z)).iff (fun b a _ => Fof_skip rfl b a)
  have hb0' : BitsOk s0.secondary s0.primary s0.heads := by rw [← hs0]; exact hbits
  have henc' : ∀ c ∈ post, (s0.hdr c.addr).size = sizeWord c.size c.used := fun c hc => by
    have := (hpp c hc).1
    rw [h0x _ (by omega)]
    exact henc c (List.mem_append_right _ (List.mem_cons_of_mem _ hc))
  have hcX : Coalesced (⟨X, cur, true⟩ :: post) := (Coalesced.append.mp hcoal).2.1
  have hcp : Coalesced post := ((Coalesced.append (xs := [⟨X, cur, true⟩]) (ys := post)).mp hcX).2.1
  obtain ⟨R, post0, hpost, hRf, htl2, hhead, hF2, hb2, hps2, hbase2, halloc2, hcurt⟩ :=
    mergeNext_ok htiles henc' hcp hF0' hb0' hn
  subst hpost
  obtain ⟨c1, c2, -⟩ := Coalesced.append.mp hcoal
  have c3 : Coalesced post0 := ((Coalesced.append (xs := ⟨X, cur, true⟩ :: R)).mp c2).2.1
  obtain ⟨p1, p2, plink⟩ := PrevOk.append.mp hprev
  have p3 : PrevOk s post0 := ((PrevOk.append (xs := ⟨X, cur, true⟩ :: R)).mp p2).2.1
  have memPre : ∀ c ∈ pre, c ∈ pre ++ ⟨X, cur, true⟩ :: (R ++ post0) := fun c hc => List.mem_append_left _ hc
  have memPost : ∀ c ∈ post0, c ∈ pre ++ ⟨X, cur, true⟩ :: (R ++ post0) :=
    fun c hc => List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _ hc))
  have memBoth : ∀ c ∈ pre ++ post0, c ∈ pre ++ ⟨X, cur, true⟩ :: (R ++ post0) := fun c hc => by
    rcases List.mem_append.mp hc with hc | hc
    · exact memPre c hc
    · exact memPost c hc
  have hXs := hspace ⟨X, cur, true⟩ (List.mem_append_right _ List.mem_cons_self)
  simp only [forall_const] at hXs
  obtain ⟨hch, hw⟩ := splitTail_ok (s2 := s2) (k := k) (A := s.allocated) hb0 hbal hfit htl2 (by omega)
    (by omega) hF2 hb2
    (fun x => by
      rw [(hps2 x).2]
      by_cases h2 : x = X
      · subst h2; rw [if_pos rfl, h0X]
      · rw [if_neg h2, h0x x h2])
    (fun x => by rw [(hps2 x).1, h0prev])
    (by rw [hbase2, ← hs0]; rfl) (by rw [halloc2, ← hs0]; rfl)
    (fun c hc => henc c (memBoth c hc)) c1 c3 hhead p1 p3 (fun x hx => plink x hx _ rfl)
    (fun c hc => hspace c (memBoth c hc)) (by omega)
  exact ⟨R, post0, total - k, rfl, hRf, hch, hw⟩

/-- **No free tail**: in a state `s2` where the allocated chunk `X` of `total` units records its size
    and the lists hold the other free chunks, setting the next chunk's `prev` gives a well-formed
    heap with allocated space `A`. -/
theorem exactTail_ok {s s2 : State} {X total A : Nat} {pre post0 : List Chunk}
    (hb0 : s.base ≠ 0) (hbal : s.base % 32 = 0) (hfit : s.top < 2 ^ 32)
    (htl2 : Tiles s.base s.top (pre ++ ⟨X, total, true⟩ :: post0))
    (hF2 : FreeLists s2 (Fof (pre ++ post0))) (hb2 : BitsOk s2.secondary s2.primary s2.heads)
    (hsz2 : ∀ x, (s2.hdr x).size = if x = X then sizeWord total true else (s.hdr x).size)
    (hpv2 : ∀ x, (s2.hdr x).prev = (s.hdr x).prev)
    (hbase2 : s2.base = s.base) (halloc2 : s2.allocated = A)
    (henc : ∀ c ∈ pre ++ post0, (s.hdr c.addr).size = sizeWord c.size c.used)
    (hcpre : Coalesced pre) (hcpost : Coalesced post0)
    (hppre : PrevOk s pre) (hppost : PrevOk s post0) (hlink : ∀ x ∈ pre.getLast?, (s.hdr X).prev = x.size)
    (hsp : ∀ c ∈ pre ++ post0, (c.used = true → c.addr + 32 * c.size ≤ s.base + 32 * A) ∧
      c.addr + 32 ≤ s.base + 32 * A)
    (hXsp : X + 32 * total ≤ s.base + 32 * A) :
    chunks (if X + 32 * total < s.top then setHdr s2 (X + 32 * total) (fun h => { h with prev := total }) else s2) =
        pre ++ ⟨X, total, true⟩ :: post0 ∧
      WF (if X + 32 * total < s.top then setHdr s2 (X + 32 * total) (fun h => { h with prev := total }) else s2) := by
  obtain ⟨hpa, hph, hpp2, hpt2⟩ := Tiles.around htl2
  have hXm := htl2.mem_lt ⟨X, total, true⟩ (List.mem_append_right _ List.mem_cons_self)
  simp only at hXm
  have hpreX : ∀ d ∈ pre, d.addr < X := fun d hd => by
    have := hpa d hd
    have := (htl2.mem_lt d (List.mem_append_left _ hd)).2.2
    omega
  have key : ∀ t : State, t.heads = s2.heads → t.secondary = s2.secondary → t.primary = s2.primary →
      t.base = s2.base → t.allocated = s2.allocated →
      (∀ x, (t.hdr x).next = (s2.hdr x).next ∧ (t.hdr x).prevL = (s2.hdr x).prevL ∧
        (t.hdr x).size = (s2.hdr x).size) →
      (∀ x, (t.hdr x).prev = if x = X + 32 * total ∧ X + 32 * total < s.top then total else (s.hdr x).prev) →
      chunks t = pre ++ ⟨X, total, true⟩ :: post0 ∧ WF t := by
    intro t th tsec tpri tbase talloc thdr tprev
    have hbase' : t.base = s.base := by rw [tbase, hbase2]
    have htop' : t.top = s.top := by unfold State.top; rw [hbase']
    have hchunks : chunks t = pre ++ ⟨X, total, true⟩ :: post0 := by
      apply chunks_eq
      · rw [hbase', htop']; exact htl2
      · intro c hc
        rw [(thdr _).2.2, hsz2]
        rcases List.mem_append.mp hc with hc' | hc'
        · have := hpreX c hc'
          rw [if_neg (by omega)]
          exact henc c (List.mem_append_left _ hc')
        · rcases List.mem_cons.mp hc' with rfl | hc'
          · rw [if_pos rfl]
          · have := (hpp2 c hc').1
            rw [if_neg (by omega)]
            exact henc c (List.mem_append_right _ hc')
    refine ⟨hchunks, by rw [hbase']; exact hb0, by rw [hbase']; exact hbal, by rw [htop']; exact hfit,
      ?_, ?_, ?_, ?_, ?_⟩
    · unfold TilesOk; rw [hchunks, hbase', htop']; exact htl2
    · unfold CoalOk; rw [hchunks]
      refine Coalesced.append.mpr ⟨hcpre, (Coalesced.append (xs := [⟨X, total, true⟩])).mpr
        ⟨trivial, hcpost, fun x hx _ _ => ?_⟩, fun _ _ y hy => ?_⟩
      · simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hx
        subst hx; simp
      · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
        subst hy; simp
    · unfold PrevsOk; rw [hchunks]
      refine PrevOk.append.mpr ⟨hppre.congr (fun d hd => ?_), (PrevOk.append (xs := [⟨X, total, true⟩])).mpr
        ⟨trivial, hppost.congr (fun d hd => ?_), fun x hx y hy => ?_⟩, fun x hx y hy => ?_⟩
      · have := hpreX d (List.mem_of_mem_tail hd)
        rw [tprev, if_neg (by omega)]
      · have := hpt2 d hd
        rw [tprev, if_neg (by omega)]
      · simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hx
        subst hx
        have h1 := hph y hy
        have h2 := (hpp2 y (List.mem_of_mem_head? hy)).2
        rw [Chunk.size_mk', tprev, if_pos ⟨by omega, by omega⟩]
      · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
        subst hy
        rw [Chunk.addr_mk', tprev, if_neg (by omega)]
        exact hlink x hx
    · unfold ListsOk'; rw [hchunks]
      have hL : FreeLists t (Fof (pre ++ ⟨X, total, true⟩ :: post0)) :=
        (hF2.congr th (fun x => (thdr x).1) (fun x => (thdr x).2.1)).iff (fun b a _ => (Fof_skip rfl b a).symm)
      obtain ⟨b1, b2, b3, b4⟩ := hb2
      exact ⟨fun b hb => hL b hb, by rw [tsec, th]; exact b1, by rw [tpri, tsec]; exact b2,
        by rw [tsec]; exact b3, by rw [tpri]; exact b4⟩
    · unfold SpaceOk; rw [hchunks, hbase', talloc, halloc2]
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact hsp c (List.mem_append_left _ hc)
      · rcases List.mem_cons.mp hc with rfl | hc
        · exact ⟨fun _ => by simp only; omega, by simp only; omega⟩
        · exact hsp c (List.mem_append_right _ hc)
  split
  · rename_i hlt
    refine key _ rfl rfl rfl rfl rfl (fun x => ⟨setHdr_next (f := fun h => { h with prev := total }) (fun _ => rfl) x,
      setHdr_prevL (f := fun h => { h with prev := total }) (fun _ => rfl) x, setHdr_prev_size⟩) (fun x => ?_)
    rw [setHdr_prev_get, hpv2]
    by_cases hx : x = X + 32 * total
    · simp [hx, hlt]
    · simp [hx]
  · rename_i hlt
    refine key _ rfl rfl rfl rfl rfl (fun x => ⟨rfl, rfl, rfl⟩) (fun x => ?_)
    rw [hpv2]; simp [hlt]

theorem freeFinal_zero {s : State} {c p T : Nat} :
    freeFinal s c p 0 T = if c < T then setHdr s c (fun h => { h with prev := p }) else s := by
  unfold freeFinal; simp [register_zero]

/-- **`growInplace` on the chunk list, and the invariant**: the chunk is unchanged, or it grows into
    its free successor, the rest of which, if any, stays free; the heap stays well-formed. -/
theorem growInplace_ok {grow : Grow} {s s' : State} {ptr newReq cur : Nat} {pre post : List Chunk}
    (hwf : WF s) (hcs : chunks s = pre ++ ⟨ptr - 32, cur, true⟩ :: post)
    (h : growInplace grow s ptr newReq = some s') :
    WF s' ∧ (s' = s ∨ ∃ e post' rest, post = e :: post' ∧ e.used = false ∧ (∀ c ∈ rest, c.used = false) ∧
      chunks s' = pre ++ ⟨ptr - 32, newReq + 1, true⟩ :: (rest ++ post')) := by
  have hwf' := hwf
  obtain ⟨hb0, hbal, hfit, htiles, hcoal, hprev, hlists, hspace⟩ := hwf'
  unfold TilesOk at htiles
  unfold CoalOk at hcoal
  unfold PrevsOk at hprev
  unfold ListsOk' at hlists
  unfold SpaceOk at hspace
  have henc := @chunks_hdr s
  rw [hcs] at htiles hcoal hprev hlists hspace henc
  generalize hX : ptr - 32 = X at *
  generalize hk : newReq + 1 = k at *
  have hcur : wordSize (s.hdr X).size = cur := by
    rw [henc ⟨X, cur, true⟩ (List.mem_append_right _ List.mem_cons_self), wordSize_sizeWord]
  unfold growInplace at h
  simp only [hX, hk, hcur] at h
  split at h
  · simp only [Option.pure_def, Option.some.injEq] at h
    subst h; exact ⟨hwf, Or.inl rfl⟩
  rename_i hck
  split at h
  · simp at h
  rename_i hT
  split at h
  · simp at h
  rename_i hu
  split at h
  · simp at h
  rename_i hav
  have hT' : s.base + 32 * maxSize = s.top := rfl
  rw [hT'] at hT h
  obtain ⟨m, -, hXm, -, hrest⟩ := Tiles.append.mp htiles
  simp only at hXm hrest
  subst hXm
  have hXal := htiles.aligned ⟨X, cur, true⟩ (List.mem_append_right _ List.mem_cons_self)
  simp only at hXal
  cases post with
  | nil =>
    have : X + 32 * cur = s.top := hrest
    omega
  | cons e post' =>
  obtain ⟨he1, he2, -⟩ := hrest
  have hee := henc e (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))
  rw [← he1, hee, wordUsed_sizeWord] at hu
  rw [← he1, hee, wordSize_sizeWord] at hav h
  have heu : e.used = false := by simpa using hu
  generalize hE : (X + 32 * k - s.base) / 32 + (if cur + e.size - k = 0 then 0 else 1) = E at h
  obtain ⟨sa, sah, saheads, sasec, sapri, sabase, saA1, saA2, rfl⟩ : ∃ sa : State, sa.hdr = s.hdr ∧
      sa.heads = s.heads ∧ sa.secondary = s.secondary ∧ sa.primary = s.primary ∧ sa.base = s.base ∧
      s.allocated ≤ sa.allocated ∧ E ≤ sa.allocated ∧
      s' = freeFinal (setHdr (unregister sa e.addr (binDown e.size)) X
        (fun h => { h with size := sizeWord k true })) (X + 32 * k) k (cur + e.size - k) s.top := by
    by_cases hlt : s.allocated < E
    · by_cases hg : grow s.base E = true
      · simp only [hlt, hg, ↓reduceIte, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        exact ⟨{ s with allocated := E }, rfl, rfl, rfl, rfl, rfl, Nat.le_of_lt hlt, Nat.le_refl _, h.symm⟩
      · simp [hlt, hg] at h
    · simp only [hlt, ↓reduceIte, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at h
      exact ⟨s, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, by omega, h.symm⟩
  -- the lists
  have hF0 : FreeLists s (Fof (pre ++ ⟨X, cur, true⟩ :: e :: post')) := fun b hb => hlists.lists b hb
  have hbits : BitsOk s.secondary s.primary s.heads := ⟨hlists.bits, hlists.prim, hlists.words, hlists.primW⟩
  have hFa : FreeLists sa (Fof (pre ++ ⟨X, cur, true⟩ :: e :: post')) :=
    hF0.congr saheads (fun x => by rw [sah]) (fun x => by rw [sah])
  have hba : BitsOk sa.secondary sa.primary sa.heads := by rw [sasec, sapri, saheads]; exact hbits
  obtain ⟨r1, r2⟩ := remove_ok (bin := binDown e.size) (x := e.addr) hFa (Fof_disj htiles (fun _ h => h)) hba
    (toBin_lt false (Nat.min_le_right _ _))
    ⟨e, List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl, heu, rfl⟩
  generalize hs1 : unregister sa e.addr (binDown e.size) = s1 at r1 r2 ⊢
  have hl : pre ++ ⟨X, cur, true⟩ :: e :: post' = (pre ++ [⟨X, cur, true⟩]) ++ e :: post' := by simp
  have htiles' := htiles
  rw [hl] at htiles'
  have hF2 : FreeLists (setHdr s1 X (fun h => { h with size := sizeWord k true })) (Fof (pre ++ post')) :=
    ((FreeLists.congr (t := setHdr s1 X (fun h => { h with size := sizeWord k true })) r1 rfl (setHdr_next (f := fun h => { h with size := sizeWord k true }) (fun _ => rfl))
      (setHdr_prevL (f := fun h => { h with size := sizeWord k true }) (fun _ => rfl)))).iff (fun b a _ => by
        rw [hl, Fof_remove htiles'.others, show (pre ++ [⟨X, cur, true⟩]) ++ post' = pre ++ ⟨X, cur, true⟩ :: post'
          by simp, Fof_skip rfl])
  have hsz2 : ∀ x, ((setHdr s1 X (fun h => { h with size := sizeWord k true })).hdr x).size =
      if x = X then sizeWord k true else (s.hdr x).size := by
    intro x
    by_cases hx : x = X
    · subst hx; rw [setHdr_self, if_pos rfl]
    · rw [setHdr_other hx, if_neg hx, ← hs1, unregister_hdr.2, sah]
  have hpv2 : ∀ x, ((setHdr s1 X (fun h => { h with size := sizeWord k true })).hdr x).prev = (s.hdr x).prev := by
    intro x
    by_cases hx : x = X
    · subst hx; rw [setHdr_self]; show (s1.hdr x).prev = _; rw [← hs1, unregister_hdr.1, sah]
    · rw [setHdr_other hx, ← hs1, unregister_hdr.1, sah]
  have hbase2 : (setHdr s1 X (fun h => { h with size := sizeWord k true })).base = s.base := by
    rw [setHdr_base, ← hs1, unregister_base, sabase]
  have halloc2 : (setHdr s1 X (fun h => { h with size := sizeWord k true })).allocated = sa.allocated := by
    rw [setHdr_allocated, ← hs1, unregister_allocated]
  have htlm : Tiles s.base s.top (pre ++ ⟨X, cur + e.size, true⟩ :: post') := htiles.merge
  -- the neighbours
  obtain ⟨c1, c2, -⟩ := Coalesced.append.mp hcoal
  have c2' : Coalesced (e :: post') := ((Coalesced.append (xs := [⟨X, cur, true⟩])).mp c2).2.1
  have c3 : Coalesced post' := ((Coalesced.append (xs := [e])).mp c2').2.1
  have hhead := (Coalesced.around (pre := []) heu c2').1
  obtain ⟨p1, p2, plink⟩ := PrevOk.append.mp hprev
  have p3 : PrevOk s post' := ((PrevOk.append (xs := [⟨X, cur, true⟩, e])).mp p2).2.1
  have memBoth : ∀ c ∈ pre ++ post', c ∈ pre ++ ⟨X, cur, true⟩ :: e :: post' := fun c hc => by
    rcases List.mem_append.mp hc with hc | hc
    · exact List.mem_append_left _ hc
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc))
  have hsp : ∀ c ∈ pre ++ post', (c.used = true → c.addr + 32 * c.size ≤ s.base + 32 * sa.allocated) ∧
      c.addr + 32 ≤ s.base + 32 * sa.allocated := fun c hc => by
    obtain ⟨h1, h2⟩ := hspace c (memBoth c hc)
    exact ⟨fun hu => by have := h1 hu; omega, by omega⟩
  by_cases hr : cur + e.size - k = 0
  · rw [hr, freeFinal_zero]
    rw [hr] at hE
    have hkt : cur + e.size = k := by omega
    rw [hkt] at htlm
    obtain ⟨hch, hw⟩ := exactTail_ok hb0 hbal hfit htlm hF2 r2 hsz2 hpv2 hbase2 halloc2
      (fun c hc => henc c (memBoth c hc)) c1 c3 p1 p3 (fun x hx => plink x hx _ rfl) hsp (by omega)
    exact ⟨hw, Or.inr ⟨e, post', [], rfl, heu, by simp, hch⟩⟩
  · rw [if_neg hr] at hE
    obtain ⟨hch, hw⟩ := splitTail_ok hb0 hbal hfit htlm (by omega) (by omega) hF2 r2 hsz2 hpv2 hbase2 halloc2
      (fun c hc => henc c (memBoth c hc)) c1 c3 hhead p1 p3 (fun x hx => plink x hx _ rfl) hsp (by omega)
    exact ⟨hw, Or.inr ⟨e, post', [⟨X + 32 * k, cur + e.size - k, false⟩], rfl, heu, by simp, hch⟩⟩

/-- **`realloc` keeps the heap well-formed**, for the data address of an allocated chunk and
    alignment one unit. -/
theorem realloc_wf {grow : Grow} {hb : Nat} {s s' : State} {ptr newReq p : Nat} {cp : Bool} (hwf : WF s)
    (hptr : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (h : realloc grow hb s ptr 1 newReq = some (p, s', cp)) : WF s' := by
  obtain ⟨c, hc, h1, h2⟩ := hptr
  obtain ⟨pre, post, hcs⟩ := List.append_of_mem hc
  have hc' : c = ⟨ptr - 32, c.size, true⟩ := by
    cases c; simp only at h1 h2 ⊢; subst h2; simp only [Chunk.mk.injEq, and_true]; omega
  rw [hc'] at hcs
  have hcur : wordSize (s.hdr (ptr - 32)).size = c.size := by
    have := chunks_hdr c hc
    rw [show c.addr = ptr - 32 by omega, h2] at this
    rw [this, wordSize_sizeWord]
  unfold realloc usable at h
  rw [hcur] at h
  by_cases e1 : newReq = c.size - 1
  · simp only [e1, ↓reduceIte, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h; exact hwf
  by_cases e2 : newReq = 0
  · simp only [e1, e2, ↓reduceIte, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    exact free_wf hwf ⟨c, hc, h1, h2⟩
  by_cases e3 : newReq < c.size - 1
  · simp only [e1, e2, e3, ↓reduceIte, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    obtain ⟨-, -, -, -, -, -, hw⟩ := shrink_ok (cur := c.size) (newReq := newReq) hwf hcs (by omega)
    exact hw
  simp only [e1, e2, e3, ↓reduceIte] at h
  cases hg : growInplace grow s ptr newReq with
  | some s2 =>
    simp only [hg, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    exact (growInplace_ok hwf hcs hg).1
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
      obtain ⟨pre', post', S, h1', -, h2'⟩ := alloc_chunks hwf ha
      refine free_wf hw1 ⟨⟨ptr - 32, c.size, true⟩, ?_, by simp only; omega, rfl⟩
      have hm : (⟨ptr - 32, c.size, true⟩ : Chunk) ∈ pre' ++ ⟨p1 - 32, S, false⟩ :: post' := by
        rw [← h1', hcs]; exact List.mem_append_right _ List.mem_cons_self
      rw [h2']
      rcases List.mem_append.mp hm with hm | hm
      · exact List.mem_append_left _ hm
      · rcases List.mem_cons.mp hm with hm | hm
        · simp at hm
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _ hm))

end Picoalloc
