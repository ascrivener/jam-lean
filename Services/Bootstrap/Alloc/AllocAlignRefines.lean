import Services.Bootstrap.Alloc.AllocAlignImpl

/-!
# The binary's `alloc` with any alignment, on a well-formed heap

The facts `alloc_impl_align` takes about the heap, from the invariant: the binary's `alloc_impl`
does what the model's `alloc` does with an alignment of `2^k` units, when the heap is in use and
need not grow (`alloc_refines_align`); and so does the wrapper `alloc` (40494), given an alignment
of `al` octets with `(al + 31) / 32 = 2^k` (`alloc_wrap_refines_align`).
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- The heads of a bin's list, with the members' predicate: 0 or a member. -/
theorem heads_mem {t : State} {G : Nat → Nat → Prop} {b : Nat} (h : FreeLists t G) (hb : b < binCount)
    (h0 : t.heads b ≠ 0) : G b (t.heads b) := by
  obtain ⟨l, hl, -, -, hex⟩ := h b hb
  cases l with
  | nil => exact absurd ((hl.head).mpr rfl) h0
  | cons y ys => rw [hl.1]; exact (hex y).mp List.mem_cons_self

/-- **The binary's `alloc_impl` on a well-formed heap, with an alignment of `2^k` units**: from
    memory holding a well-formed `s`, an allocation of `req` units that the model makes without
    growing the heap, the binary returns its address and leaves memory holding the model's result,
    itself well-formed. -/
theorem alloc_refines_align {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    {grow : Grow} {hb : Nat} (s s' : State) (sp req k ptr : Nat) (hwf : WF s) (hrep : Rep μ s)
    (h : alloc grow hb (2 ^ k) req s = some (ptr, s')) (hng : s'.allocated = s.allocated)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat (2 ^ k))
    (h9 : ω[9] = UInt64.ofNat req) (h10 : ω[10] = UInt64.ofNat 0)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hal : s.allocated < 2147483648)
    (hfo : FirstOk s) {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hSTk : S0 + 152 ≤ sp ∧ sp ≤ S1)
    (hHT : s.base + 32 * s.allocated ≤ HT) (hw : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 41177 ω μ x 41423 ω' μ' x 500 ∧ Rep μ' s' ∧ WF s' ∧
      ω'[7] = UInt64.ofNat ptr ∧ ω'[0] = ω[0] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[1] = ω[1] ∧
      (∀ a, μ'.writable a = μ.writable a) ∧ (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) := by
  have hwf' : WF s' := alloc_wf_align hwf h
  obtain ⟨bin, a1, ha, -, hbin, hmax, hS, ha1, hend, hp, rfl⟩ := alloc_align_eq hwf.1 h
  rw [allocPostL_allocated] at hng
  simp only at hng
  subst hng
  have es : ({ s with allocated := s.allocated } : State) = s := rfl
  rw [es] at hwf' ⊢
  have hbin' : (findFirst s (binUp (req + 2 ^ k - 1 + 1))).or (findFirst s (binDown (req + 2 ^ k - 1 + 1))) =
      some bin := by rw [Nat.sub_add_cancel (by omega)]; exact hbin
  obtain ⟨hbc, hne, -, hbS, ⟨pre, post, hcs⟩, hCb, hCal⟩ := bin_chunk hwf (by omega) hbin'
  have hl1 := (leftOf_spec (base := s.base) (C := s.heads bin) ha).1
  have hwf0 := hwf
  obtain ⟨-, hbal, hfit, htiles, hcoal, hprev, hlists, hspace⟩ := hwf0
  unfold TilesOk at htiles
  have hA0 : s.base + 32 * ((s.heads bin - s.base) / 32) = s.heads bin := by omega
  have hcs' := allocPostL_chunks (a1 := s.allocated) (r := req) (lhs := leftOf s.base (s.heads bin) (2 ^ k)) hcs
    (by rw [← hcs]; exact htiles) rfl hA0 (by omega)
  rw [es] at hcs'
  generalize hC : s.heads bin = C at *
  generalize hl : leftOf s.base C (2 ^ k) = lhs at *
  generalize hSd : wordSize (s.hdr C).size = S at *
  have hpC : ptr = C + 32 * lhs + 32 := by rw [hp]; omega
  subst hpC
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
  have hHFT : ∀ a, H a ∨ F a → a + 32 ≤ HT := by
    intro a h
    obtain ⟨c, hc, rfl⟩ := unHF a h
    unfold SpaceOk at hspace; have := (hspace c (hcs ▸ hc)).2; omega
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
  have hFbin : Fof (pre ++ ⟨C, S, false⟩ :: post) bin C := ⟨⟨C, S, false⟩, hCm, rfl, rfl, hbS⟩
  have hnx : (s.hdr C).next ≠ 0 → F (s.hdr C).next := fun h0 => by
    obtain ⟨c, hc, h1, h2⟩ := (member_facts hF0 hbc hFbin).1 h0
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
  -- the bins after the chunk's unlink
  have hpop := (pop_ok hF0 (Fof_disj htiles (fun c hc => hc)) hbits hbc hC (by omega)).1
  have hu : unregister s C bin = unregisterFirst s C bin := by unfold unregister; rw [if_pos hC]
  have hLold : lhs ≠ 0 → (unregister s C bin).heads (binDown lhs) ≠ 0 →
      F ((unregister s C bin).heads (binDown lhs)) ∧ (unregister s C bin).heads (binDown lhs) ≠ C := by
    intro _ h0
    rw [hu] at h0 ⊢
    obtain ⟨⟨c, hc, h1, h2, -⟩, h3⟩ := heads_mem (b := binDown lhs) hpop (toBin_lt false (Nat.min_le_right _ _)) h0
    exact ⟨by rw [← h1]; exact mkF c hc h2, h3⟩
  have hN0 : C + 32 * lhs + 32 * (req + 1) + 32 * (S - lhs - req - 1) = C + 32 * S := by omega
  have hNdis : S - lhs - req - 1 ≠ 0 → ∀ a, H a ∨ F a →
      a + 32 ≤ C + 32 * lhs + 32 * (req + 1) ∨ C + 32 * lhs + 32 * (req + 1) + 32 ≤ a := by
    intro hr a ha
    obtain ⟨c, hc, rfl⟩ := unHF a ha
    have hcl := htiles.mem_lt c hc
    rcases List.mem_append.mp hc with h | h
    · have := hpa c h; omega
    · rcases List.mem_cons.mp h with h | h
      · subst h; simp only; omega
      · have := (hpp c h).1; omega
  have hNold : S - lhs - req - 1 ≠ 0 →
      (registerAlloc (register (unregister s C bin) C (s.hdr C).prev lhs).1 (C + 32 * lhs)
        (register (unregister s C bin) C (s.hdr C).prev lhs).2 (req + 1)).heads (binDown (S - lhs - req - 1)) ≠ 0 →
      F ((registerAlloc (register (unregister s C bin) C (s.hdr C).prev lhs).1 (C + 32 * lhs)
        (register (unregister s C bin) C (s.hdr C).prev lhs).2 (req + 1)).heads (binDown (S - lhs - req - 1))) := by
    intro _ h0
    rw [registerAlloc_heads] at h0 ⊢
    by_cases hl0 : lhs = 0
    · rw [hl0, register_zero] at h0 ⊢
      rw [unregister_heads_head hC] at h0 ⊢
      split
      · rename_i hb; rw [if_pos hb] at h0; exact hnx h0
      · rename_i hb; rw [if_neg hb] at h0
        rcases heads_ok (b := binDown (S - 0 - req - 1)) hF0 (toBin_lt false (Nat.min_le_right _ _)) with h | ⟨c, hc, h1, h2⟩
        · exact absurd h h0
        · rw [← h1]; exact mkF c hc h2
    · rw [register_heads hl0] at h0 ⊢
      split
      · exact hFC
      · rename_i hb'; rw [if_neg hb'] at h0
        rw [unregister_heads_head hC] at h0 ⊢
        split
        · rename_i hb; rw [if_pos hb] at h0; exact hnx h0
        · rename_i hb; rw [if_neg hb] at h0
          rcases heads_ok (b := binDown (S - lhs - req - 1)) hF0 (toBin_lt false (Nat.min_le_right _ _)) with h | ⟨c, hc, h1, h2⟩
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
  have hm' : req + 2 ^ k ≤ 33554432 := by rw [← maxSize_val]; exact hmax
  obtain ⟨ω', μ', run, rep', e7, e0, e5, e6, e1, ww, stk⟩ := alloc_impl_align (p := p) (P := P) (R := R) x ω μ s H F
    sp req k bin C lhs hrep' hbits h1 h7 h8 h9 h10 hsp hsp1 hb0 hbT hm' hbin (by unfold binCount at hbc; omega) hC hFC
    hHC hHF hnx hpv hl (by rw [hSd]; exact hS) (by rw [hSd]; omega) hal (by rw [hSd]; exact hend)
    hLold (by rw [hSd]; exact hNdis) (by rw [hSd]; exact hNold) (by rw [hSd]; exact hFin) hHTs hSTk hHFT hHT hw
  rw [hSd] at rep'
  refine ⟨ω', μ', run, ?_, hwf', e7, e0, e5, e6, e1, ww, stk⟩
  rw [show s.base + 32 * maxSize = s.base + 1073741824 by rw [maxSize_val]]
  rw [htop] at hcs'
  generalize hA : C + 32 * lhs = A at rep' hcs'
  generalize hN : A + 32 * (req + 1) = N at rep'
  have cls : ∀ c ∈ chunks (allocPostL s bin req S lhs (s.base + 1073741824)),
      (H c.addr ∧ (c.used = false → F c.addr)) ∨ (c.addr = A ∧ c.used = true) ∨
      (S - lhs - req - 1 ≠ 0 ∧ c.addr = N) := by
    intro c hc
    rw [hcs'] at hc
    rcases List.mem_append.mp hc with h | h
    · rcases List.mem_append.mp h with h | h
      · have hm : c ∈ pre ++ ⟨C, S, false⟩ :: post := List.mem_append_left _ h
        exact Or.inl ⟨mkH c hm, mkF c hm⟩
      · unfold leftChunk at h
        split at h
        · simp at h
        · simp only [List.mem_singleton] at h
          subst h
          exact Or.inl ⟨hHC, fun _ => hFC⟩
    · rcases List.mem_cons.mp h with h | h
      · subst h; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · rcases List.mem_append.mp h with h | h
        · unfold remChunk at h
          split at h
          · simp at h
          · rename_i hr; simp only [List.mem_singleton] at h
            subst h
            exact Or.inr (Or.inr ⟨by omega, by simp only; omega⟩)
        · have hm : c ∈ pre ++ ⟨C, S, false⟩ :: post := List.mem_append_right _ (List.mem_cons_of_mem _ h)
          exact Or.inl ⟨mkH c hm, mkF c hm⟩
  have es2 : State.mk s.allocated s.base s.primary s.secondary s.heads s.hdr = s := rfl
  rw [es2]
  refine ⟨rep'.heads, rep'.sec, rep'.pri, rep'.base, rep'.alloc, fun c hc => ?_, fun c hc => ?_,
    fun c hc hu => ?_, fun c hc hu => ?_⟩
  · rcases cls c hc with ⟨h, -⟩ | ⟨h, -⟩ | ⟨hr, h⟩
    · exact rep'.prev _ (Or.inl (Or.inl h))
    · rw [h]; exact rep'.prev _ (Or.inl (Or.inr rfl))
    · rw [h]; exact rep'.prev _ (Or.inr ⟨hr, rfl⟩)
  · rcases cls c hc with ⟨h, -⟩ | ⟨h, -⟩ | ⟨hr, h⟩
    · exact rep'.size _ (Or.inl (Or.inl h))
    · rw [h]; exact rep'.size _ (Or.inl (Or.inr rfl))
    · rw [h]; exact rep'.size _ (Or.inr ⟨hr, rfl⟩)
  · rcases cls c hc with ⟨-, h⟩ | ⟨-, h⟩ | ⟨hr, h⟩
    · exact rep'.next _ (Or.inl (h hu))
    · rw [h] at hu; exact absurd hu (by decide)
    · rw [h]; exact rep'.next _ (Or.inr ⟨hr, rfl⟩)
  · rcases cls c hc with ⟨-, h⟩ | ⟨-, h⟩ | ⟨hr, h⟩
    · exact rep'.prevL _ (Or.inl (h hu))
    · rw [h] at hu; exact absurd hu (by decide)
    · rw [h]; exact rep'.prevL _ (Or.inr ⟨hr, rfl⟩)

/-- **The binary's `alloc` refines the model's `alloc` with any alignment**: from memory holding a
    well-formed `s`, the lock byte clear, ω₇ = `size` and ω₈ = `al` octets with `(al + 31) / 32 = 2^k`
    units, when the model allocates the `⌈size/32⌉` units at alignment `2^k` without growing the
    heap, `alloc` (40494) reaches its return (the `jumpInd` at 40611) with the model's address in
    ω₇, memory holding the model's result, the lock byte clear again, the caller's ω₀, ω₁, ω₅, ω₆
    restored and the stack from sp up untouched. -/
theorem alloc_wrap_refines_align {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    {grow : Grow} {hb : Nat} (s s' : State) (sp size al k ptr : Nat) (hwf : WF s) (hrep : Rep μ s)
    (h : alloc grow hb (2 ^ k) ((size + 31) / 32) s = some (ptr, s')) (hng : s'.allocated = s.allocated)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat size) (h8 : ω[8] = UInt64.ofNat al)
    (hal : (al + 31) / 32 = 2 ^ k) (hk : k < 31) (hs : size + 31 < 68719476736)
    (hsp : 2147483816 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0) {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT)
    (hSTk : S0 + 168 ≤ sp ∧ sp ≤ S1) (hHT : s.base + 32 * s.allocated ≤ HT) (hw : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 40494 ω μ x 40611 ω' μ' x 540 ∧ Rep μ' s' ∧ WF s' ∧
      ω'[7] = UInt64.ofNat ptr ∧ rdN μ' 206848 1 = 0 ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have hK : 2 ^ k < 2147483648 :=
    Nat.lt_of_lt_of_le (Nat.pow_lt_pow_right (by decide) hk) (by decide)
  obtain ⟨ω1, μ1, r1, a1, a7, a8, a9, a10, a0, a5, -, st8, st16, fr1, ww1, g1⟩ :=
    al_lock_align (p := p) (P := P) (R := R) x ω μ sp size al (2 ^ k) h1 h7 h8 hal hK hs (by omega) hsp1 hl
      (by omega) ⟨by omega, by omega⟩ hw
  have rep1 : Rep μ1 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 =>
    fr1 a (by omega) (Or.inl (by omega)) (Or.inr (by unfold A0 at ha1; omega)) ha3
  obtain ⟨ω2, μ2, r2, rep2, wf2, e7, e0, e5, e6, e1, ww2, stk2⟩ :=
    alloc_refines_align (p := p) (P := P) (R := R) x ω1 μ1 s s' (sp - 16) _ k ptr hwf rep1 h hng a1 a7 a8 a9 a10
      (by omega) (by omega) hb0 hbT hA hfo hHTs ⟨by omega, by omega⟩ hHT (hw.of_eq ww1)
  have rj := al_ret_jump (p := p) (P := P) (R := R) x ω2 μ2 (by rw [e0, a0])
  obtain ⟨ω3, μ3, r3, c0, c5, c1, cl, fr3, ww3, g3⟩ :=
    al_unlock (p := p) (P := P) (R := R) x ω2 μ2 (sp - 16) (by rw [e1, a1]) (by rw [e5, a5]) (by omega) (by omega)
      (by omega) ⟨by omega, by omega⟩ ((hw.of_eq ww1).of_eq ww2)
  have hb' : s'.base = s.base := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, rfl⟩ := alloc_align_eq hwf.1 h; rw [allocPostL_base]
  refine ⟨ω3, μ3, (((r1.trans r2).trans rj).trans r3).mono (by omega),
    rep2.congr_lock wf2 (by rw [hb']; exact hb0) (by rw [hb']; exact hbT)
      (fun a ha1 ha2 ha3 => fr3 a (by omega) (by omega)), wf2,
    by rw [fget g3 7 (by decide) (by decide)]; exact e7, cl, fun a => (ww3 a).trans ((ww2 a).trans (ww1 a)),
    fun a ha1 ha2 => ((fr3 a ha1 (by omega)).trans (stk2 a ha1 (by omega))).trans
      (fr1 a ha1 (Or.inr ha2) (Or.inr (by omega)) (Or.inr (by omega))), ?_, ?_, ?_, ?_⟩
  · rw [c0, rdN_frame (μ := μ1) fun j hj => stk2 _ (by omega) (by omega), show sp - 16 + 8 = sp - 8 by omega]
    unfold rdN; rw [st8, Num.decodeLE_encodeLE]
    rw [Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]
  · rw [c1, h1]; congr 1; omega
  · rw [c5, rdN_frame (μ := μ1) fun j hj => stk2 _ (by omega) (by omega)]
    unfold rdN; rw [st16, Num.decodeLE_encodeLE]
    rw [Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]
  · rw [fget g3 6 (by decide) (by decide), e6, fget g1 6 (by decide) (by decide)]

/-- The wrapper's alignment `al` octets, for `al ≤ 32 · 2^k` above `32 · 2^(k−1)`: `2^k` units. -/
example : (64 + 31) / 32 = 2 ^ 1 ∧ (33 + 31) / 32 = 2 ^ 1 ∧ (32 + 31) / 32 = 2 ^ 0 := by decide

end Services.Bootstrap.Alloc
