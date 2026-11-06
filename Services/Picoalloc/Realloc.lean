import Services.Picoalloc.Free

/-!
# `realloc`

`shrink` keeps the front of the chunk and frees the rest, merged with a free next chunk.
-/

namespace Picoalloc

/-- Projections of a chunk literal, as rewrites (the kernel can be slow to see these by
    unfolding when a field is arithmetic). -/
theorem Chunk.addr_mk' (a n : Nat) (u : Bool) : Chunk.addr ⟨a, n, u⟩ = a := rfl
theorem Chunk.size_mk' (a n : Nat) (u : Bool) : Chunk.size ⟨a, n, u⟩ = n := rfl

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
  have htl3 := Tiles.split (k := k) (v := true) (w := false) (by omega) (by omega) htl2
  obtain ⟨-, -, hpp2, hpt2⟩ := Tiles.around htl2
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
  have hbase' : s'.base = s.base := by rw [f5, hbase2, ← hs0]; rfl
  have halloc' : s'.allocated = s.allocated := by rw [f6, halloc2, ← hs0]; rfl
  have htop' : s'.top = s.top := by unfold State.top; rw [hbase']
  -- the old list around X
  have memPre : ∀ c ∈ pre, c ∈ pre ++ ⟨X, cur, true⟩ :: (R ++ post0) := fun c hc => List.mem_append_left _ hc
  have memPost : ∀ c ∈ post0, c ∈ pre ++ ⟨X, cur, true⟩ :: (R ++ post0) :=
    fun c hc => List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _ hc))
  have hsizes : ∀ x, (s'.hdr x).size = if x = X + 32 * k then sizeWord (total - k) false
      else if x = X then sizeWord k true else (s.hdr x).size := by
    intro x
    rw [f3, (hps2 _).2]
    by_cases h1 : x = X + 32 * k
    · rw [if_pos h1, if_pos h1]
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : x = X
      · subst h2; rw [if_pos rfl, h0X]
      · rw [if_neg h2, h0x x h2]
  have hprevs : ∀ x, (s'.hdr x).prev = if x = X + 32 * k then k
      else if x = X + 32 * k + 32 * (total - k) ∧ X + 32 * k + 32 * (total - k) < s.top then total - k
      else (s.hdr x).prev := by
    intro x; rw [f4, (hps2 _).1, h0prev]
  have hchunks : chunks s' = pre ++ ⟨X, k, true⟩ :: ⟨X + 32 * k, total - k, false⟩ :: post0 := by
    apply chunks_eq
    · rw [hbase', htop']; exact htl3
    · intro c hc
      rw [hsizes]
      rcases List.mem_append.mp hc with hc' | hc'
      · have := hpreX c hc'
        rw [if_neg (by omega), if_neg (by omega)]
        exact henc c (memPre c hc')
      · rcases List.mem_cons.mp hc' with rfl | hc'
        · rw [if_neg (show X ≠ X + 32 * k by omega), if_pos rfl]
        · rcases List.mem_cons.mp hc' with rfl | hc'
          · rw [if_pos rfl]
          · have := (hpp2 c hc').1
            rw [if_neg (by omega), if_neg (by omega)]
            exact henc c (memPost c hc')
  refine ⟨R, post0, total - k, rfl, hRf, hchunks, ?_⟩
  refine ⟨by rw [hbase']; exact hb0, by rw [hbase']; exact hbal, by rw [htop']; exact hfit, ?_, ?_, ?_, ?_, ?_⟩
  · unfold TilesOk; rw [hchunks, hbase', htop']; exact htl3
  · -- coalesced
    unfold CoalOk; rw [hchunks]
    obtain ⟨c1, c2, -⟩ := Coalesced.append.mp hcoal
    have c3 : Coalesced post0 := ((Coalesced.append (xs := ⟨X, cur, true⟩ :: R)).mp c2).2.1
    have c4 : Coalesced (⟨X + 32 * k, total - k, false⟩ :: post0) :=
      (Coalesced.append (xs := [⟨X + 32 * k, total - k, false⟩])).mpr
        ⟨trivial, c3, fun x _ y hy => by rw [hhead y hy]; simp⟩
    refine Coalesced.append.mpr ⟨c1, (Coalesced.append (xs := [⟨X, k, true⟩])).mpr ⟨trivial, c4, ?_⟩, ?_⟩
    · intro x hx _ _
      simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hx
      subst hx; simp
    · intro _ _ y hy
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy; simp
  · -- prev links
    unfold PrevsOk; rw [hchunks]
    obtain ⟨p1, p2, plink⟩ := PrevOk.append.mp hprev
    have p3 : PrevOk s post0 := ((PrevOk.append (xs := ⟨X, cur, true⟩ :: R)).mp p2).2.1
    have p4 : PrevOk s' (⟨X + 32 * k, total - k, false⟩ :: post0) :=
      (PrevOk.append (xs := [⟨X + 32 * k, total - k, false⟩])).mpr ⟨trivial, p3.congr (fun d hd => ?_),
        fun x hx y hy => ?_⟩
    · refine PrevOk.append.mpr ⟨p1.congr (fun d hd => ?_), ⟨?_, p4⟩, fun x hx y hy => ?_⟩
      · have := hpreX d (List.mem_of_mem_tail hd)
        rw [hprevs, if_neg (by omega), if_neg (by omega)]
      · show (s'.hdr (Chunk.addr ⟨X + 32 * k, total - k, false⟩)).prev = Chunk.size ⟨X, k, true⟩
        rw [Chunk.addr_mk', Chunk.size_mk', hprevs, if_pos rfl]
      · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
        subst hy
        have := hpreX x (List.mem_of_getLast? hx)
        rw [Chunk.addr_mk', hprevs, if_neg (show X ≠ X + 32 * k by omega), if_neg (by omega)]
        exact plink x hx _ rfl
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
    have hXs := hspace ⟨X, cur, true⟩ (List.mem_append_right _ List.mem_cons_self)
    simp only [forall_const] at hXs
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hspace c (memPre c hc)
    · rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨fun _ => by simp only; omega, by simp only; omega⟩
      · rcases List.mem_cons.mp hc with rfl | hc
        · exact ⟨fun h => by simp at h, by simp only; omega⟩
        · exact hspace c (memPost c hc)

end Picoalloc
