import Services.Bootstrap.Alloc.AllocImpl

/-!
# The binary's `alloc` on a well-formed heap

The facts `alloc_impl` takes about the heap, from the invariant: the binary's `alloc_impl` does
what the model's `alloc` does, alignment one unit, when the heap is in use and need not grow.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- The bins' heads once the head C of `bin` has left it. -/
theorem unregister_heads_head {s : State} {C bin b : Nat} (hc : s.heads bin = C) :
    (unregister s C bin).heads b = if b = bin then (s.hdr C).next else s.heads b := by
  unfold unregister unregisterFirst
  rw [if_pos hc]
  dsimp only
  split
  · rw [unsetBit_heads]; simp [upd]
  · rw [setHdr_heads]; simp [upd]

/-- **The binary's `alloc_impl` on a well-formed heap**: from memory holding a well-formed `s`, an
    allocation of `req` units at alignment one unit that the model makes without growing the heap,
    the binary returns its address and leaves memory holding the model's result, itself
    well-formed. -/
theorem alloc_refines {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    {grow : Grow} {hb : Nat} (s s' : State) (sp req ptr : Nat) (hwf : WF s) (hrep : Rep μ s)
    (h : alloc grow hb 1 req s = some (ptr, s')) (hng : s'.allocated = s.allocated)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat 1)
    (h9 : ω[9] = UInt64.ofNat req) (h10 : ω[10] = UInt64.ofNat 0)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hal : s.allocated < 2147483648)
    (hfo : FirstOk s) (hw : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 41177 ω μ x 41423 ω' μ' x 400 ∧ Rep μ' s' ∧ WF s' ∧
      ω'[7] = UInt64.ofNat ptr ∧ ω'[0] = ω[0] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[1] = ω[1] ∧
      (∀ a, μ'.writable a = true) ∧ (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) := by
  have hwf' : WF s' := alloc_wf hwf h
  rw [alloc_one hwf.1] at h
  obtain ⟨bin, a1, hbin, hmax, hS, ha1, hend, hp, rfl⟩ := alloc1_eq h
  rw [allocPost_allocated] at hng
  simp only at hng
  subst hng
  have es : ({ s with allocated := s.allocated } : State) = s := rfl
  rw [es] at hwf' ⊢
  obtain ⟨pre, post, hcs, hcs'⟩ := allocPost_chunks (a1 := s.allocated) hwf hmax hbin hS
  rw [es] at hcs'
  obtain ⟨hbc, hne, -, hbS, -, hCb, hCal⟩ := bin_chunk hwf hmax hbin
  generalize hC : s.heads bin = C at *
  generalize hSd : wordSize (s.hdr C).size = S at *
  have hpC : ptr = C + 32 := by rw [hp]; omega
  subst hpC
  have hwf0 := hwf
  obtain ⟨-, hbal, hfit, htiles, hcoal, hprev, hlists, hspace⟩ := hwf0
  unfold TilesOk at htiles
  unfold PrevsOk at hprev
  unfold ListsOk' at hlists
  have henc := @chunks_hdr s
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  rw [hcs] at htiles hprev hlists henc
  rw [htop] at htiles
  have hbits : BitsOk s.secondary s.primary s.heads := ⟨hlists.bits, hlists.prim, hlists.words, hlists.primW⟩
  have hF0 : FreeLists s (Fof (pre ++ ⟨C, S, false⟩ :: post)) := fun b hb => hlists.lists b hb
  generalize hH : HA (pre ++ ⟨C, S, false⟩ :: post) = H
  generalize hF : FA (pre ++ ⟨C, S, false⟩ :: post) = F
  have mkH : ∀ c ∈ pre ++ ⟨C, S, false⟩ :: post, H c.addr := fun c hc => hH ▸ ⟨c, hc, rfl⟩
  have mkF : ∀ c ∈ pre ++ ⟨C, S, false⟩ :: post, c.used = false → F c.addr := fun c hc hu => hF ▸ ⟨c, hc, rfl, hu⟩
  have unH : ∀ a, H a → ∃ c ∈ pre ++ ⟨C, S, false⟩ :: post, c.addr = a := fun a h => by rw [← hH] at h; exact h
  have unF : ∀ a, F a → ∃ c ∈ pre ++ ⟨C, S, false⟩ :: post, c.addr = a ∧ c.used = false := fun a h => by
    rw [← hF] at h; exact h
  have unHF : ∀ a, H a ∨ F a → ∃ c ∈ pre ++ ⟨C, S, false⟩ :: post, c.addr = a := by
    rintro a (h | h)
    · exact unH a h
    · obtain ⟨c, hc, h1, -⟩ := unF a h; exact ⟨c, hc, h1⟩
  have hHF : ∀ a, H a ∨ F a → Al s.base a := by
    intro a h
    obtain ⟨c, hc, rfl⟩ := unHF a h
    have := htiles.aligned c hc; have := htiles.mem_lt c hc; unfold Al; omega
  have hrep' : RepAt μ s H F :=
    ⟨hrep.heads, hrep.sec, hrep.pri, hrep.base, hrep.alloc,
      fun a h => by obtain ⟨c, hc, rfl⟩ := unH a h; exact hrep.prev c (hcs ▸ hc),
      fun a h => by obtain ⟨c, hc, rfl⟩ := unH a h; exact hrep.size c (hcs ▸ hc),
      fun a h => by obtain ⟨c, hc, rfl, hu⟩ := unF a h; exact hrep.next c (hcs ▸ hc) hu,
      fun a h => by obtain ⟨c, hc, rfl, hu⟩ := unF a h; exact hrep.prevL c (hcs ▸ hc) hu⟩
  have hCm : (⟨C, S, false⟩ : Chunk) ∈ pre ++ ⟨C, S, false⟩ :: post := List.mem_append_right _ List.mem_cons_self
  have hCl := htiles.mem_lt _ hCm
  simp only at hCl
  obtain ⟨hpa, hpost1, hpp, -⟩ := Tiles.around htiles
  have hFC : F C := mkF _ hCm rfl
  have hHC : H C := mkH _ hCm
  have hnx : (s.hdr C).next ≠ 0 → F (s.hdr C).next := fun h0 => by
    obtain ⟨c, hc, h1, h2⟩ := (member_facts hF0 hbc ⟨⟨C, S, false⟩, hCm, rfl, rfl, hbS⟩).1 h0
    rw [← h1]; exact mkF c hc h2
  have hpv : (s.hdr C).prev < 2147483648 := by
    by_cases hCb' : C = s.base
    · rw [hCb']; unfold FirstOk at hfo; omega
    · rcases List.eq_nil_or_concat pre with hp0 | ⟨pre1, d, hp0⟩
      · subst hp0; exact absurd htiles.1 hCb'
      · rw [List.concat_eq_append] at hp0; subst hp0
        have hd : (s.hdr C).prev = d.size := (PrevOk.append.mp hprev).2.2 d (by simp) ⟨C, S, false⟩ rfl
        have := htiles.mem_lt d (by simp)
        rw [hd]; omega
  have hNdis : S - req - 1 ≠ 0 → ∀ a, H a ∨ F a → a + 32 ≤ C + 32 * (req + 1) ∨ C + 32 * (req + 1) + 32 ≤ a := by
    intro hr a ha
    obtain ⟨c, hc, rfl⟩ := unHF a ha
    have hcl := htiles.mem_lt c hc
    rcases List.mem_append.mp hc with h | h
    · have := hpa c h; omega
    · rcases List.mem_cons.mp h with h | h
      · subst h; simp only; omega
      · have := (hpp c h).1; omega
  have hNold : S - req - 1 ≠ 0 →
      (registerAlloc (unregister s C bin) C (s.hdr C).prev (req + 1)).heads (binDown (S - req - 1)) ≠ 0 →
      F ((registerAlloc (unregister s C bin) C (s.hdr C).prev (req + 1)).heads (binDown (S - req - 1))) := by
    intro _ h0
    rw [show (registerAlloc (unregister s C bin) C (s.hdr C).prev (req + 1)).heads = (unregister s C bin).heads
      from rfl, unregister_heads_head hC] at h0 ⊢
    split
    · rename_i hb; rw [if_pos hb] at h0; exact hnx h0
    · rename_i hb; rw [if_neg hb] at h0
      rcases heads_ok (b := binDown (S - req - 1)) hF0 (toBin_lt false (Nat.min_le_right _ _)) with h | ⟨c, hc, h1, h2⟩
      · exact absurd h h0
      · rw [← h1]; exact mkF c hc h2
  have hFin : C + 32 * S < s.base + 1073741824 → H (C + 32 * S) := by
    intro hlt
    cases hpo : post with
    | nil =>
      rw [hpo] at htiles
      obtain ⟨m, -, hm1, -, hm3⟩ := Tiles.append.mp htiles
      simp only [Tiles] at hm1 hm3; omega
    | cons e es =>
      have := hpost1 e (by rw [hpo]; rfl)
      rw [← this]; exact mkH e (List.mem_append_right _ (List.mem_cons_of_mem _ (by rw [hpo]; exact List.mem_cons_self)))
  have hm' : req + 1 ≤ 33554432 := by rw [← maxSize_val]; exact hmax
  obtain ⟨ω', μ', run, rep', e7, e0, e5, e6, e1, ww, stk⟩ := alloc_impl (p := p) (P := P) (R := R) x ω μ s H F sp req
    bin C hrep' hbits h1 h7 h8 h9 h10 hsp hsp1 hb0 hbT hm' hbin (by unfold binCount at hbc; omega) hC hFC hHC hHF
    hnx hpv (by rw [hSd]; exact hS) (by rw [hSd]; omega) hal (by rw [hSd]; exact hend)
    (by rw [hSd]; exact hNdis) (by rw [hSd]; exact hNold) (by rw [hSd]; exact hFin) hw
  rw [hSd] at rep'
  refine ⟨ω', μ', run, ?_, hwf', e7, e0, e5, e6, e1, ww, stk⟩
  rw [show s.base + 32 * maxSize = s.base + 1073741824 by rw [maxSize_val]]
  rw [htop] at hcs'
  generalize hN : C + 32 * (req + 1) = N at rep'
  have cls : ∀ c ∈ chunks (allocPost s bin req S (s.base + 1073741824)),
      (c ∈ pre ++ ⟨C, S, false⟩ :: post ∧ c ≠ ⟨C, S, false⟩) ∨ c = ⟨C, req + 1, true⟩ ∨
      (S - req - 1 ≠ 0 ∧ c = ⟨N, S - req - 1, false⟩) := by
    intro c hc
    rw [hcs'] at hc
    rcases List.mem_append.mp hc with h | h
    · refine Or.inl ⟨List.mem_append_left _ h, fun e => ?_⟩
      subst e; have := hpa _ h; simp only at this; omega
    · rcases List.mem_cons.mp h with h | h
      · exact Or.inr (Or.inl h)
      · rcases List.mem_append.mp h with h | h
        · unfold remChunk at h
          split at h
          · simp at h
          · rename_i hr; simp only [List.mem_singleton] at h
            exact Or.inr (Or.inr ⟨hr, by rw [h, hN]⟩)
        · refine Or.inl ⟨List.mem_append_right _ (List.mem_cons_of_mem _ h), fun e => ?_⟩
          subst e; have := (hpp _ h).1; simp only at this; omega
  have cls' : ∀ c ∈ chunks (allocPost s bin req S (s.base + 1073741824)),
      (c ∈ pre ++ ⟨C, S, false⟩ :: post) ∨ (c.addr = C ∧ c.used = true) ∨
      (S - req - 1 ≠ 0 ∧ c.addr = N) := by
    intro c hc
    rcases cls c hc with ⟨h, -⟩ | h | ⟨hr, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨by rw [h], by rw [h]⟩)
    · exact Or.inr (Or.inr ⟨hr, by rw [h]⟩)
  have es2 : State.mk s.allocated s.base s.primary s.secondary s.heads s.hdr = s := rfl
  rw [es2]
  refine ⟨rep'.heads, rep'.sec, rep'.pri, rep'.base, rep'.alloc, fun c hc => ?_, fun c hc => ?_,
    fun c hc hu => ?_, fun c hc hu => ?_⟩
  · rcases cls' c hc with h | ⟨h, -⟩ | ⟨hr, h⟩
    · exact rep'.prev _ (Or.inl (mkH c h))
    · rw [h]; exact rep'.prev _ (Or.inl hHC)
    · rw [h]; exact rep'.prev _ (Or.inr ⟨hr, rfl⟩)
  · rcases cls' c hc with h | ⟨h, -⟩ | ⟨hr, h⟩
    · exact rep'.size _ (Or.inl (mkH c h))
    · rw [h]; exact rep'.size _ (Or.inl hHC)
    · rw [h]; exact rep'.size _ (Or.inr ⟨hr, rfl⟩)
  · rcases cls' c hc with h | ⟨-, h⟩ | ⟨hr, h⟩
    · exact rep'.next _ (Or.inl (mkF c h hu))
    · rw [h] at hu; exact absurd hu (by decide)
    · rw [h]; exact rep'.next _ (Or.inr ⟨hr, rfl⟩)
  · rcases cls' c hc with h | ⟨-, h⟩ | ⟨hr, h⟩
    · exact rep'.prevL _ (Or.inl (mkF c h hu))
    · rw [h] at hu; exact absurd hu (by decide)
    · rw [h]; exact rep'.prevL _ (Or.inr ⟨hr, rfl⟩)
end Services.Bootstrap.Alloc
