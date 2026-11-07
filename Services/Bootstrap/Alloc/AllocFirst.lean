import Services.Bootstrap.Alloc.AllocWrapGrow

/-!
# The binary's `alloc` on the allocator's first use

`alloc_impl`'s entry, from 41221 (where the in-use path and the path through `initialize` meet), …
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code JAM

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **41221 … 41425**: the bins of `req + 1`, the search, and the chosen chunk C (memory untouched). -/
theorem alloc_entry221 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (sp req bin C w : Nat) (hbits : BitsOk s.secondary s.primary s.heads)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat 1)
    (h9 : ω[9] = UInt64.ofNat req) (h12 : ω[12] = UInt64.ofNat 1) (hf : rdN μ (sp + 120) 8 = 204984)
    (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296)
    (hp : rdN μ 206832 8 = s.primary) (hs : ∀ q, q < 38 → rdN μ (q * 8 + 204984 + 1544) 8 = s.secondary q)
    (hm : req + 1 ≤ 33554432)
    (hbin : (findFirst s (binUp (req + 1))).or (findFirst s (binDown (req + 1))) = some bin)
    (hC : rdN μ (196792 + 4 * bin) 4 = C) (hw : rdN μ (C + 4) 4 = w) (hC1 : C + 8 < 2147483648)
    (hS : req + 1 ≤ w / 2) (hwr : ∀ a, μ.writable a = true) :
    ∃ ω', FreeStepsH p R 41221 ω μ x 41425 ω' μ x 110 ∧ ∃ q b, q * 64 + b = bin ∧ q < 38 ∧ b < 64 ∧
      ω'[1] = UInt64.ofNat sp ∧ ω'[10] = UInt64.ofNat C ∧ ω'[11] = UInt64.ofNat (w / 2) ∧
      ω'[5] = UInt64.ofNat (196792 + 4 * bin) ∧ ω'[2] = UInt64.ofNat b ∧ ω'[6] = UInt64.ofNat q ∧
      ω'[3] = UInt64.ofNat 204984 ∧ ω'[8] = UInt64.ofNat 1 ∧ ω'[9] = UInt64.ofNat req ∧
      ω'[4] = UInt64.ofNat (req + 1) ∧ ω'[12] = UInt64.ofNat (req + 1) ∧ ω'[7] = UInt64.ofNat 196792 ∧
      ∀ j : Fin 13, j.val ∉ [0, 2, 3, 4, 5, 6, 10, 11, 12] → ω'[j] = ω[j] := by
  have hr1 : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hwr a)
  obtain ⟨ω2, r3, b0, b2, b4, b12, g3⟩ := al_bins (p := p) (P := P) (R := R) x ω μ req h9 h8 h12 hm
  have hbU : binUp (req + 1) < 2432 := toBin_lt true (Nat.min_le_right _ _)
  have hbD : binDown (req + 1) < 2432 := toBin_lt false (Nat.min_le_right _ _)
  have c7 : ω2[7] = UInt64.ofNat 196792 := by rw [fget g3 7 (by decide) (by decide)]; exact h7
  have c1 : ω2[1] = UInt64.ofNat sp := by rw [fget g3 1 (by decide) (by decide)]; exact h1
  have fu := find_up (p := p) (P := P) (R := R) x ω2 μ s sp _ hbits c1 b2 c7 (by omega) hf hp hs hbU hr1
  -- the search ends at 41378 with the bin as word q, bit b
  obtain ⟨ω4, q, b, r45, hqb, hq, hb', d6, d2, d3, fr4⟩ : ∃ ω4 q b, FreeStepsH p R 41297 ω2 μ x 41378 ω4 μ x 60 ∧
      q * 64 + b = bin ∧ q < 38 ∧ b < 64 ∧ ω4[6] = UInt64.ofNat q ∧ ω4[2] = UInt64.ofNat b ∧
      ω4[3] = UInt64.ofNat 204984 ∧ ∀ j : Fin 13, j.val ∉ [2, 3, 5, 6, 10, 11] → ω4[j] = ω2[j] := by
    cases hu : findFirst s (binUp (req + 1)) with
    | some bin' =>
      have : bin' = bin := by rw [hu] at hbin; exact Option.some.inj hbin
      subst this
      obtain ⟨ω4, q, b, r, e1, e2, e3, e4, e5, e6, -, e8⟩ := fu.1 _ hu
      exact ⟨ω4, q, b, r.mono (by omega), e1, e2, e3, e4, e5, e6, e8⟩
    | none =>
      rw [hu, Option.none_or] at hbin
      obtain ⟨ω3, r, e5, e3, e8⟩ := fu.2 hu
      obtain ⟨ω4, q, b, r', f1, f2, f3, f4, f5, f6⟩ := (find_down (p := p) (P := P) (R := R) x ω3 μ s _ hbits
        (by rw [fget e8 0 (by decide) (by decide)]; exact b0) e5 e3 hs hbD hr1).1 _ hbin
      exact ⟨ω4, q, b, (r.trans r').mono (by omega), f1, f2, f3, f4, f5,
        by rw [fget f6 3 (by decide) (by decide)]; exact e3,
        frame_trans f6 e8 (fun j hj => by simp at hj ⊢; omega) (fun j hj => by simp at hj ⊢; omega)⟩
  have k7 : ω4[7] = UInt64.ofNat 196792 := by rw [fget fr4 7 (by decide) (by decide)]; exact c7
  have k12 : ω4[12] = UInt64.ofNat (req + 1) := by rw [fget fr4 12 (by decide) (by decide)]; exact b12
  have hC' : rdN μ (196792 + 4 * (q * 64 + b)) 4 = C := by rw [hqb]; exact hC
  have hw' : rdN μ (C + 4) 4 = w := hw
  obtain ⟨ω5, r5, e10, e11, e5, g5⟩ := al_pick (p := p) (P := P) (R := R) x ω4 μ q b C w (w / 2 * 0 + (req + 1))
    d6 d2 k7 (by simpa using k12) hq hb' hC' hw' (by omega) (by omega) hr1
  have hw64 : w / 2 < 18446744073709551616 := by
    have := rdN_lt μ (C + 4) 4; rw [hw] at this; omega
  have r6 := al_size_ok (p := p) (P := P) (R := R) x ω5 μ (w / 2) (req + 1) e11
    (by rw [fget g5 12 (by decide) (by decide)]; exact k12) hS hw64
  have fr : ∀ j : Fin 13, j.val ∉ [0, 2, 3, 4, 5, 6, 10, 11, 12] → ω5[j] = ω[j] :=
    frame_trans g5 (frame_trans (l := [0, 2, 3, 4, 5, 6, 10, 11, 12]) fr4 g3 (fun j hj => by simp at hj ⊢; omega) (fun j hj => by simp at hj ⊢; omega))
      (fun j hj => by simp at hj ⊢; omega) (fun j hj => by simp at hj ⊢; omega)
  refine ⟨ω5, ((r3.trans r45).trans (r5.trans r6)).mono (by omega), q, b, hqb, hq, hb',
    by rw [fget fr 1 (by decide) (by decide)]; exact h1, e10, e11, by rw [e5, hqb],
    by rw [fget g5 2 (by decide) (by decide)]; exact d2, by rw [fget g5 6 (by decide) (by decide)]; exact d6,
    by rw [fget g5 3 (by decide) (by decide)]; exact d3,
    by rw [fget fr 8 (by decide) (by decide)]; exact h8,
    by rw [fget fr 9 (by decide) (by decide)]; exact h9,
    by rw [fget g5 4 (by decide) (by decide), fget fr4 4 (by decide) (by decide)]; exact b4,
    by rw [fget g5 12 (by decide) (by decide)]; exact k12,
    by rw [fget g5 7 (by decide) (by decide)]; exact k7, fr⟩


/-- **41221 … 41423**, the heap grown: `alloc_impl_grow` from where its two entries meet. -/
theorem alloc_impl_grow221 {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (x : RefineCtx) (ω : Regs)
    (μ : Memory)
    (s : State) (H F : Nat → Prop) (sp req bin C : Nat) (hrep : RepAt μ s H F)
    (hbits : BitsOk s.secondary s.primary s.heads)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat 1)
    (h9 : ω[9] = UInt64.ofNat req) (h12 : ω[12] = UInt64.ofNat 1)
    (h120 : rdN μ (sp + 120) 8 = 204984) (h112 : rdN μ (sp + 112) 8 = 0)
    (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648)
    (hm : req + 1 ≤ 33554432)
    (hbin : (findFirst s (binUp (req + 1))).or (findFirst s (binDown (req + 1))) = some bin) (hbn : bin < 2432)
    (hcb : s.heads bin = C) (hFC : F C) (hHC : H C) (hHF : ∀ a, H a ∨ F a → Al s.base a)
    (hnx : (s.hdr C).next ≠ 0 → F (s.hdr C).next) (hpv : (s.hdr C).prev < 2147483648)
    (hS : req + 1 ≤ wordSize (s.hdr C).size) (hCend : C + 32 * wordSize (s.hdr C).size ≤ s.base + 1073741824)
    (hal : s.allocated < 2147483648)
    (E : Nat) (hE : (C - s.base) / 32 + 1 + req + (if wordSize (s.hdr C).size - req - 1 = 0 then 0 else 1) = E)
    (hgr : s.allocated < E) (pa pb : Nat) (hbd : heapBounds env.code = (pa, pb)) (hab : pa ≤ pb)
    (hbs : pb < 4294967296) (hR : pagesOf (s.base + 32 * E) ≤ pb)
    (hNdis : wordSize (s.hdr C).size - req - 1 ≠ 0 → ∀ a, H a ∨ F a →
      a + 32 ≤ C + 32 * (req + 1) ∨ C + 32 * (req + 1) + 32 ≤ a)
    (hNold : wordSize (s.hdr C).size - req - 1 ≠ 0 →
      (registerAlloc (unregister { s with allocated := E } C bin) C (s.hdr C).prev (req + 1)).heads (binDown (wordSize (s.hdr C).size - req - 1))
        ≠ 0 →
      F ((registerAlloc (unregister { s with allocated := E } C bin) C (s.hdr C).prev (req + 1)).heads
        (binDown (wordSize (s.hdr C).size - req - 1))))
    (hFin : C + 32 * wordSize (s.hdr C).size < s.base + 1073741824 → H (C + 32 * wordSize (s.hdr C).size))
    (hwr : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (refineContract env) 41221 ω μ x 41423 ω' μ' x 500 ∧
      RepAt μ' (allocPost { s with allocated := E } bin req (wordSize (s.hdr C).size) (s.base + 1073741824))
        (fun a => H a ∨ (wordSize (s.hdr C).size - req - 1 ≠ 0 ∧ a = C + 32 * (req + 1)))
        (fun a => F a ∨ (wordSize (s.hdr C).size - req - 1 ≠ 0 ∧ a = C + 32 * (req + 1))) ∧
      ω'[7] = UInt64.ofNat (C + 32) ∧ ω'[0] = UInt64.ofNat (rdN μ (sp + 144) 8) ∧
      ω'[5] = UInt64.ofNat (rdN μ (sp + 136) 8) ∧ ω'[6] = UInt64.ofNat (rdN μ (sp + 128) 8) ∧
      ω'[1] = UInt64.ofNat (sp + 152) ∧
      (∀ a, μ'.writable a = true) ∧ (∀ a, a < 4294967296 → sp + 152 ≤ a → μ'.read a = μ.read a) := by
  have hAC := hHF C (Or.inr hFC)
  unfold Al at hAC
  have hHFl : ∀ a, H a ∨ F a → a + 16 < 2147483648 := fun a ha => by have := hHF a ha; unfold Al at this; omega
  generalize hSd : wordSize (s.hdr C).size = S at *
  have hsz := hrep.size C hHC
  have hwS : (s.hdr C).size / 2 = S := by rw [← hSd]; rfl
  have hsec : ∀ q, q < 38 → rdN μ (q * 8 + 204984 + 1544) 8 = s.secondary q := fun q hq => by
    have := hrep.sec q hq; unfold A0 at this; rw [show q * 8 + 204984 + 1544 = 196792 + 9736 + 8 * q by omega]
    exact this
  have hheads : rdN μ (196792 + 4 * bin) 4 = C := by
    have := hrep.heads bin hbn; unfold A0 at this; rw [this, hcb]
  have hpri : rdN μ 206832 8 = s.primary := by have := hrep.pri; unfold A0 at this; exact this
  obtain ⟨ω1, r1, q, b, hqb, hq, hb, a1, a10, a11, a5, a2, a6, a3, a8, a9, a4, a12, a7, g1⟩ :=
    alloc_entry221 (p := p) (P := P) (R := refineContract env) x ω μ s sp req bin C (s.hdr C).size hbits h1 h7 h8 h9
      h12 h120 hsp hsp1 hpri hsec hm hbin hheads hsz (by omega) (by omega) hwr
  rw [hwS] at a11
  obtain ⟨ω2, μ2, r2, rep2, b1, b8, b0, m96, m48, m80, m72, m104, m88, m120, ww2, fr2, g2⟩ := alloc_mid_grow (p := p)
    (P := P) env x ω1 μ s H F sp req bin q b C S hrep hcb hqb hq hb hFC hHC hHF hnx hb0 hbT hpv hS
    (by omega) hCend hal E hE hgr pa pb hbd hab hbs hR a1 a10 a11 a5 a2 a6 a3 a8 a9 h120
    (by omega) (by omega) hwr
  generalize hpvd : (s.hdr C).prev = pv at *
  generalize ht2 : unregister { s with allocated := E } C bin = t2 at *
  have e2b : t2.base = s.base := by rw [← ht2, unregister_base]

  have hCa : (C - s.base) % 32 = 0 := hAC.2.1
  obtain ⟨ω3, μ3, r3, rep3, c3, c12, c8, c2, c1, ww3, fr3⟩ := alloc_end1 (p := p) (P := P) (R := refineContract env) x ω2 μ2 t2 H F
    sp req C pv (S - req - 1) rep2 hHC (by rw [e2b]; exact hHF) (by rw [e2b]; exact hb0)
    (by rw [e2b]; exact hbT) (by rw [e2b]; exact hCa) (by rw [e2b]; omega) hpv (by omega) (by omega)
    (by rw [e2b]; omega) hNdis hNold b1 (by rw [e2b]; exact b8) b0
    (by rw [fget g2 4 (by decide) (by decide)]; exact a4) (by rw [fget g2 9 (by decide) (by decide)]; exact a9)
    (by rw [fget g2 7 (by decide) (by decide)]; exact a7) (by rw [e2b]; exact m96) m48 _ m80
    (by rw [e2b]; exact m72) m104 m88 m120 (by omega) (by omega) ww2
  generalize ht3 : register (registerAlloc t2 C pv (req + 1)) (C + 32 * (req + 1)) (req + 1) (S - req - 1) = rr at *
  have e3b : rr.1.base = s.base := by rw [← ht3, register_base, registerAlloc_base, e2b]
  have k112 : rdN μ3 (sp + 112) 8 = 0 := by
    rw [show rdN μ3 (sp + 112) 8 = rdN μ (sp + 112) 8 from rdN_frame fun j hj =>
      (fr3 _ (by omega) (by omega)).trans (fr2 _ (by omega) (by omega) (by omega))]
    exact h112
  have k120 : rdN μ3 (sp + 120) 8 = 204984 := by
    rw [← m120]; exact rdN_frame fun j hj => fr3 _ (by omega) (by omega)
  have hS32 : C + 32 * (req + 1) + 32 * (S - req - 1) = C + 32 * S := by omega
  obtain ⟨ω4, μ4, r4, rep4, d7, d0, d5, d6, d1, ww4, fr4, -⟩ := alloc_end2 (p := p) (P := P) (R := refineContract env) x ω3 μ3 rr.1
    (fun a => H a ∨ (S - req - 1 ≠ 0 ∧ a = C + 32 * (req + 1)))
    (fun a => F a ∨ (S - req - 1 ≠ 0 ∧ a = C + 32 * (req + 1))) sp (C + 32 * (req + 1)) (S - req - 1) rr.2
    (C + 32) rep3
    (fun a ha => by
      rw [e3b]
      rcases ha with (h | ⟨h0, rfl⟩) | (h | ⟨h0, rfl⟩)
      · exact hHF a (Or.inl h)
      · unfold Al; omega
      · exact hHF a (Or.inr h)
      · unfold Al; omega)
    (by rw [e3b]; exact hb0) (by rw [e3b]; exact hbT)
    (fun h => Or.inl (by rw [hS32]; exact hFin (by rw [e3b, hS32] at h; exact h)))
    (by rw [e3b, hS32]; exact hCend) (by omega) c1 c12 c8 c3 c2 k120 k112
    (by rw [← ht3]; unfold register; split <;> simp <;> omega) (by omega) (by omega) (by omega) ww3
  have tr : ∀ a, sp + 128 ≤ a → a + 8 ≤ sp + 152 → rdN μ3 a 8 = rdN μ a 8 := fun a h h' =>
    rdN_frame fun j hj => (fr3 _ (by omega) (by omega)).trans (fr2 _ (by omega) (by omega) (by omega))
  refine ⟨ω4, μ4, (((r1.trans r2).trans r3).trans r4).mono (by omega), ?_, d7, ?_, ?_, ?_, ?_, ww4,
    fun a h h' => (fr4 a h (by omega)).trans ((fr3 a h (by omega)).trans (fr2 a h (by omega) (by omega)))⟩
  · rw [allocPost_eq (s := { s with allocated := E }) hcb (show s.base ≤ C by omega) hCa]
    dsimp only
    rw [hpvd, ht2, ht3]
    rw [e3b] at rep4
    exact rep4
  · rw [d0, tr _ (by omega) (by omega)]
  · rw [d5, tr _ (by omega) (by omega)]
  · rw [d6, tr _ (by omega) (by omega)]
  · exact d1

end Services.Bootstrap.Alloc
