import Services.Bootstrap.Alloc.AllocWrapGrow
import Services.Bootstrap.Alloc.AllocInit

/-!
# The binary's `alloc` on the allocator's first use

`alloc_impl` meets its in-use path again at 41221 after the first-use path through `initialize`.
From there, `alloc_refines_grow221` repeats `alloc_refines_grow` with ω₀, ω₅ and ω₆ restored from
the prologue's frame.

`alloc_init_path` covers 41177 … 41221 with the heap base 0. That is the prologue, then
`initialize` (the host grows the heap to its bound; one free chunk is set up at 206880), then the
return. `init_rep` turns `initialize`'s writes into the model's `init`.

The first allocation always grows the heap (`first_grows`). `alloc_refines_first` and its locked
wrapper `alloc_wrap_refines_first` take a zeroed allocator in memory to the model's state after
`alloc (growTo pb) 206880 1 req` (alignment 1).
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
    (hS : req + 1 ≤ w / 2) {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1)
    (hCT : 196608 ≤ C ∧ C + 16 ≤ HT) (hwr : WrAt μ HT S0 S1) :
    ∃ ω', FreeStepsH p R 41221 ω μ x 41425 ω' μ x 110 ∧ ∃ q b, q * 64 + b = bin ∧ q < 38 ∧ b < 64 ∧
      ω'[1] = UInt64.ofNat sp ∧ ω'[10] = UInt64.ofNat C ∧ ω'[11] = UInt64.ofNat (w / 2) ∧
      ω'[5] = UInt64.ofNat (196792 + 4 * bin) ∧ ω'[2] = UInt64.ofNat b ∧ ω'[6] = UInt64.ofNat q ∧
      ω'[3] = UInt64.ofNat 204984 ∧ ω'[8] = UInt64.ofNat 1 ∧ ω'[9] = UInt64.ofNat req ∧
      ω'[4] = UInt64.ofNat (req + 1) ∧ ω'[12] = UInt64.ofNat (req + 1) ∧ ω'[7] = UInt64.ofNat 196792 ∧
      ∀ j : Fin 13, j.val ∉ [0, 2, 3, 4, 5, 6, 10, 11, 12] → ω'[j] = ω[j] := by
  have hr1 := hwr.rd
  obtain ⟨ω2, r3, b0, b2, b4, b12, g3⟩ := al_bins (p := p) (P := P) (R := R) x ω μ req h9 h8 h12 hm
  have hbU : binUp (req + 1) < 2432 := toBin_lt true (Nat.min_le_right _ _)
  have hbD : binDown (req + 1) < 2432 := toBin_lt false (Nat.min_le_right _ _)
  have c7 : ω2[7] = UInt64.ofNat 196792 := by rw [fget g3 7 (by decide) (by decide)]; exact h7
  have c1 : ω2[1] = UInt64.ofNat sp := by rw [fget g3 1 (by decide) (by decide)]; exact h1
  have fu := find_up (p := p) (P := P) (R := R) x ω2 μ s sp _ hbits c1 b2 c7 (by omega) hf hp hs hbU hHTs hSTk hr1
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
        (by rw [fget e8 0 (by decide) (by decide)]; exact b0) e5 e3 hs hbD hHTs hr1).1 _ hbin
      exact ⟨ω4, q, b, (r.trans r').mono (by omega), f1, f2, f3, f4, f5,
        by rw [fget f6 3 (by decide) (by decide)]; exact e3,
        frame_trans f6 e8 (fun j hj => by simp at hj ⊢; omega) (fun j hj => by simp at hj ⊢; omega)⟩
  have k7 : ω4[7] = UInt64.ofNat 196792 := by rw [fget fr4 7 (by decide) (by decide)]; exact c7
  have k12 : ω4[12] = UInt64.ofNat (req + 1) := by rw [fget fr4 12 (by decide) (by decide)]; exact b12
  have hC' : rdN μ (196792 + 4 * (q * 64 + b)) 4 = C := by rw [hqb]; exact hC
  have hw' : rdN μ (C + 4) 4 = w := hw
  obtain ⟨ω5, r5, e10, e11, e5, g5⟩ := al_pick (p := p) (P := P) (R := R) x ω4 μ q b C w (w / 2 * 0 + (req + 1))
    d6 d2 k7 (by simpa using k12) hq hb' hC' hw' (by omega) (by omega) hHTs hCT hr1
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


/-- **41221 … 41423**, the heap grown: `alloc_impl_grow` from where its two entries meet.
    Under `refineContractK cap`: the `grow_heap` call may cost up to `cap`. -/
theorem alloc_impl_grow221K {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (cap : Nat) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs)
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
    (hgr : s.allocated < E) (pb h : Nat) (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ h) (hhb : h ≤ pb)
    (hbs : pb < 4294967296) (hR : pagesOf (s.base + 32 * E) ≤ pb)
    (hcost : 275 + 121 * (growTop (pagesOf (s.base + 32 * E)) h pb - h) ≤ cap)
    (hNdis : wordSize (s.hdr C).size - req - 1 ≠ 0 → ∀ a, H a ∨ F a →
      a + 32 ≤ C + 32 * (req + 1) ∨ C + 32 * (req + 1) + 32 ≤ a)
    (hNold : wordSize (s.hdr C).size - req - 1 ≠ 0 →
      (registerAlloc (unregister { s with allocated := E } C bin) C (s.hdr C).prev (req + 1)).heads (binDown (wordSize (s.hdr C).size - req - 1))
        ≠ 0 →
      F ((registerAlloc (unregister { s with allocated := E } C bin) C (s.hdr C).prev (req + 1)).heads
        (binDown (wordSize (s.hdr C).size - req - 1))))
    (hFin : C + 32 * wordSize (s.hdr C).size < s.base + 1073741824 → H (C + 32 * wordSize (s.hdr C).size))
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * h) (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1) (hSb : 4096 * pb ≤ S0)
    (hp : HeapPages μ 48 pb h) (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true)
    (hHFT : ∀ a, H a ∨ F a → a + 32 ≤ 4096 * h) :
    ∃ ω' μ', FreeStepsH p (refineContractK cap env) 41221 ω μ x 41423 ω' μ' x 500 ∧
      RepAt μ' (allocPost { s with allocated := E } bin req (wordSize (s.hdr C).size) (s.base + 1073741824))
        (fun a => H a ∨ (wordSize (s.hdr C).size - req - 1 ≠ 0 ∧ a = C + 32 * (req + 1)))
        (fun a => F a ∨ (wordSize (s.hdr C).size - req - 1 ≠ 0 ∧ a = C + 32 * (req + 1))) ∧
      ω'[7] = UInt64.ofNat (C + 32) ∧ ω'[0] = UInt64.ofNat (rdN μ (sp + 144) 8) ∧
      ω'[5] = UInt64.ofNat (rdN μ (sp + 136) 8) ∧ ω'[6] = UInt64.ofNat (rdN μ (sp + 128) 8) ∧
      ω'[1] = UInt64.ofNat (sp + 152) ∧
      HeapPages μ' 48 pb (growTop (pagesOf (s.base + 32 * E)) h pb) ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → sp + 152 ≤ a → μ'.read a = μ.read a) := by
  have hwr := HeapPages.wrAt hp hhb hst
  obtain ⟨hRt, ht1, ht2⟩ := growTop_ge (h := h) hR
  have hpE := pagesOf_ge (s.base + 32 * E)
  generalize hT : growTop (pagesOf (s.base + 32 * E)) h pb = t at *
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
    alloc_entry221 (p := p) (P := P) (R := refineContractK cap env) x ω μ s sp req bin C (s.hdr C).size hbits h1 h7 h8 h9
      h12 h120 hsp hsp1 hpri hsec hm hbin hheads hsz (by omega) (by omega) hHTs hSTk ⟨by omega, by have := hHFT C (Or.inr hFC); omega⟩ hwr
  rw [hwS] at a11
  obtain ⟨ω2, μ2, r2, rep2, b1, b8, b0, m96, m48, m80, m72, m104, m88, m120, hp2, hst2, fr2, g2⟩ := alloc_mid_growK (p := p)
    (P := P) (S0 := S0) (S1 := S1) env cap hcap x ω1 μ s H F sp req bin q b C S hrep hcb hqb hq hb hFC hHC hHF hnx hb0 hbT hpv hS
    (by omega) hCend hal E hE hgr pb h hbd h48 hhb hbs hR (by rw [hT]; exact hcost) a1 a10 a11 a5 a2 a6 a3 a8 a9 h120
    (by omega) (by omega) hHTs hSTk hSb hp hst hHFT
  rw [hT] at hp2
  have hw2 := HeapPages.wrAt hp2 (by omega) hst2
  have hHFT2 : ∀ a, H a ∨ F a → a + 32 ≤ 4096 * t := fun a ha => by have := hHFT a ha; omega
  generalize hpvd : (s.hdr C).prev = pv at *
  generalize ht2 : unregister { s with allocated := E } C bin = t2 at *
  have e2b : t2.base = s.base := by rw [← ht2, unregister_base]

  have hCa : (C - s.base) % 32 = 0 := hAC.2.1
  obtain ⟨ω3, μ3, r3, rep3, c3, c12, c8, c2, c1, ww3, fr3⟩ := alloc_end1 (p := p) (P := P) (R := refineContractK cap env) x ω2 μ2 t2 H F
    sp req C pv (S - req - 1) rep2 hHC (by rw [e2b]; exact hHF) (by rw [e2b]; exact hb0)
    (by rw [e2b]; exact hbT) (by rw [e2b]; exact hCa) (by rw [e2b]; omega) hpv (by omega) (by omega)
    (by rw [e2b]; omega) hNdis hNold b1 (by rw [e2b]; exact b8) b0
    (by rw [fget g2 4 (by decide) (by decide)]; exact a4) (by rw [fget g2 9 (by decide) (by decide)]; exact a9)
    (by rw [fget g2 7 (by decide) (by decide)]; exact a7) (by rw [e2b]; exact m96) m48 _ m80
    (by rw [e2b]; exact m72) m104 m88 m120 (by omega) (by omega) (by omega) hSTk hHFT2
    (fun h0 => by have h' := hE; rw [if_neg h0] at h'; omega) hw2
  generalize ht3 : register (registerAlloc t2 C pv (req + 1)) (C + 32 * (req + 1)) (req + 1) (S - req - 1) = rr at *
  have e3b : rr.1.base = s.base := by rw [← ht3, register_base, registerAlloc_base, e2b]
  have k112 : rdN μ3 (sp + 112) 8 = 0 := by
    rw [show rdN μ3 (sp + 112) 8 = rdN μ (sp + 112) 8 from rdN_frame fun j hj =>
      (fr3 _ (by omega) (by omega)).trans (fr2 _ (by omega) (by omega) (by omega))]
    exact h112
  have k120 : rdN μ3 (sp + 120) 8 = 204984 := by
    rw [← m120]; exact rdN_frame fun j hj => fr3 _ (by omega) (by omega)
  have hS32 : C + 32 * (req + 1) + 32 * (S - req - 1) = C + 32 * S := by omega
  obtain ⟨ω4, μ4, r4, rep4, d7, d0, d5, d6, d1, ww4, fr4, -⟩ := alloc_end2 (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 rr.1
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
    (by rw [← ht3]; unfold register; split <;> simp <;> omega) (by omega) (by omega) (by omega) (by omega) hSTk
    (fun a ha => by
      rcases ha with (h' | ⟨h0, rfl⟩) | (h' | ⟨h0, rfl⟩)
      · exact hHFT2 a (Or.inl h')
      · have h'' := hE; rw [if_neg h0] at h''; omega
      · exact hHFT2 a (Or.inr h')
      · have h'' := hE; rw [if_neg h0] at h''; omega)
    (hw2.of_eq ww3)
  have tr : ∀ a, sp + 128 ≤ a → a + 8 ≤ sp + 152 → rdN μ3 a 8 = rdN μ a 8 := fun a h h' =>
    rdN_frame fun j hj => (fr3 _ (by omega) (by omega)).trans (fr2 _ (by omega) (by omega) (by omega))
  refine ⟨ω4, μ4, (((r1.trans r2).trans r3).trans r4).mono (by omega), ?_, d7, ?_, ?_, ?_, ?_,
    HeapPages.of_eq hp2 (fun a => (ww4 a).trans (ww3 a)), fun a h1 h2 => by rw [ww4, ww3]; exact hst2 a h1 h2,
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

/-- `alloc_impl_grow221K` at `hostCostMax`, the cap of `refineContract`: at most 14 pages a
    `grow_heap` call. -/
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
    (hgr : s.allocated < E) (pb h : Nat) (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ h) (hhb : h ≤ pb)
    (hbs : pb < 4294967296) (hR : pagesOf (s.base + 32 * E) ≤ pb)
    (hcost : growTop (pagesOf (s.base + 32 * E)) h pb ≤ h + 14)
    (hNdis : wordSize (s.hdr C).size - req - 1 ≠ 0 → ∀ a, H a ∨ F a →
      a + 32 ≤ C + 32 * (req + 1) ∨ C + 32 * (req + 1) + 32 ≤ a)
    (hNold : wordSize (s.hdr C).size - req - 1 ≠ 0 →
      (registerAlloc (unregister { s with allocated := E } C bin) C (s.hdr C).prev (req + 1)).heads (binDown (wordSize (s.hdr C).size - req - 1))
        ≠ 0 →
      F ((registerAlloc (unregister { s with allocated := E } C bin) C (s.hdr C).prev (req + 1)).heads
        (binDown (wordSize (s.hdr C).size - req - 1))))
    (hFin : C + 32 * wordSize (s.hdr C).size < s.base + 1073741824 → H (C + 32 * wordSize (s.hdr C).size))
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * h) (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1) (hSb : 4096 * pb ≤ S0)
    (hp : HeapPages μ 48 pb h) (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true)
    (hHFT : ∀ a, H a ∨ F a → a + 32 ≤ 4096 * h) :
    ∃ ω' μ', FreeStepsH p (refineContract env) 41221 ω μ x 41423 ω' μ' x 500 ∧
      RepAt μ' (allocPost { s with allocated := E } bin req (wordSize (s.hdr C).size) (s.base + 1073741824))
        (fun a => H a ∨ (wordSize (s.hdr C).size - req - 1 ≠ 0 ∧ a = C + 32 * (req + 1)))
        (fun a => F a ∨ (wordSize (s.hdr C).size - req - 1 ≠ 0 ∧ a = C + 32 * (req + 1))) ∧
      ω'[7] = UInt64.ofNat (C + 32) ∧ ω'[0] = UInt64.ofNat (rdN μ (sp + 144) 8) ∧
      ω'[5] = UInt64.ofNat (rdN μ (sp + 136) 8) ∧ ω'[6] = UInt64.ofNat (rdN μ (sp + 128) 8) ∧
      ω'[1] = UInt64.ofNat (sp + 152) ∧
      HeapPages μ' 48 pb (growTop (pagesOf (s.base + 32 * E)) h pb) ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → sp + 152 ≤ a → μ'.read a = μ.read a) :=
  alloc_impl_grow221K (p := p) (P := P) (S0 := S0) (S1 := S1) env hostCostMax (by decide) x ω μ s H
    F sp req bin C hrep hbits h1 h7 h8 h9 h12 h120 h112 hsp hsp1 hb0 hbT hm hbin hbn hcb hFC hHC
    hHF hnx hpv hS hCend hal E hE hgr pb h hbd h48 hhb hbs hR (by unfold hostCostMax; omega) hNdis
    hNold hFin hHTs hSTk hSb hp hst hHFT

/-- **The binary's `alloc` from 41221, the heap grown, refines the model's `alloc`**: as
    `alloc_refines_grow`, with ω₀, ω₅ and ω₆ restored from the frame `alloc_impl`'s prologue saved.
    Under `refineContractK cap`: the `grow_heap` call may cost up to `cap`. -/
theorem alloc_refines_grow221K {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (cap : Nat) (hcap : cap < 18446744073709551616) (x : RefineCtx)
    (ω : Regs) (μ : Memory) {hb : Nat} (s s' : State) (sp req ptr pb ph : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h : alloc (growTo pb) hb 1 req s = some (ptr, s')) (hgrown : s'.allocated ≠ s.allocated)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat 1)
    (h9 : ω[9] = UInt64.ofNat req) (h12 : ω[12] = UInt64.ofNat 1)
    (h120 : rdN μ (sp + 120) 8 = 204984) (h112 : rdN μ (sp + 112) 8 = 0)
    (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hal : s.allocated < 2147483648)
    (hfo : FirstOk s) (hcost : 275 + 121 * (pagesOf (s.base + 32 * s'.allocated) - ph) ≤ cap)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1) (hSb : 4096 * pb ≤ S0)
    (hp : HeapPages μ 48 pb ph) (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true)
    (hHT : s.base + 32 * s.allocated ≤ 4096 * ph) :
    ∃ ω' μ', FreeStepsH p (refineContractK cap env) 41221 ω μ x 41423 ω' μ' x 500 ∧ Rep μ' s' ∧ WF s' ∧
      ω'[7] = UInt64.ofNat ptr ∧ ω'[0] = UInt64.ofNat (rdN μ (sp + 144) 8) ∧
      ω'[5] = UInt64.ofNat (rdN μ (sp + 136) 8) ∧ ω'[6] = UInt64.ofNat (rdN μ (sp + 128) 8) ∧
      ω'[1] = UInt64.ofNat (sp + 152) ∧
      (∃ h', HeapPages μ' 48 pb h' ∧ s'.base + 32 * s'.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → sp + 152 ≤ a → μ'.read a = μ.read a) := by
  have hwf' : WF s' := alloc_wf hwf h
  rw [alloc_one hwf.1] at h
  obtain ⟨bin, hbin, hmax, hS, hlt, hgr, hp', rfl⟩ := alloc1_grown h hgrown
  simp only [allocPost_allocated] at hcost
  have hR : pagesOf (s.base + 32 * ((s.heads bin - s.base) / 32 + 1 + req +
      (if wordSize (s.hdr (s.heads bin)).size - req - 1 = 0 then 0 else 1))) ≤ pb := of_decide_eq_true hgr
  clear hgr hgrown
  generalize hEd : (s.heads bin - s.base) / 32 + 1 + req +
      (if wordSize (s.hdr (s.heads bin)).size - req - 1 = 0 then 0 else 1) = E at *
  obtain ⟨pre, post, hcs, hcs'⟩ := allocPost_chunks (a1 := E) hwf hmax hbin hS
  obtain ⟨hbc, hne, -, hbS, -, hCb, hCal⟩ := bin_chunk hwf hmax hbin
  generalize hC : s.heads bin = C at *
  generalize hSd : wordSize (s.hdr C).size = S at *
  have hpC : ptr = C + 32 := by rw [hp']; omega
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
  have hHFT : ∀ a, H a ∨ F a → a + 32 ≤ 4096 * ph := by
    intro a ha
    obtain ⟨c, hc, rfl⟩ := unHF a ha
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
      (registerAlloc (unregister { s with allocated := E } C bin) C (s.hdr C).prev (req + 1)).heads
        (binDown (S - req - 1)) ≠ 0 →
      F ((registerAlloc (unregister { s with allocated := E } C bin) C (s.hdr C).prev (req + 1)).heads
        (binDown (S - req - 1))) := by
    intro _ h0
    rw [show (registerAlloc (unregister { s with allocated := E } C bin) C (s.hdr C).prev (req + 1)).heads =
      (unregister { s with allocated := E } C bin).heads from rfl,
      unregister_heads_head (s := { s with allocated := E }) hC] at h0 ⊢
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
  obtain ⟨hRt, ht1, ht2⟩ := growTop_ge (h := ph) hR
  have hpE := pagesOf_ge (s.base + 32 * E)
  obtain ⟨ω', μ', run, rep', e7, e0, e5, e6, e1, hpg, hstg, stk⟩ := alloc_impl_grow221K (p := p) (P := P) env cap hcap x ω μ s H F sp req
    bin C hrep' hbits h1 h7 h8 h9 h12 h120 h112 hsp hsp1 hb0 hbT hm' hbin (by unfold binCount at hbc; omega) hC hFC hHC hHF
    hnx hpv (by rw [hSd]; exact hS) (by rw [hSd]; omega) hal E (by rw [hSd]; exact hEd) hlt pb ph hbd h48 hhb hbs hR
    (by unfold growTop; split <;> omega)
    (by rw [hSd]; exact hNdis) (by rw [hSd]; exact hNold) (by rw [hSd]; exact hFin) hHTs hSTk hSb hp hst hHFT
  rw [hSd] at rep'
  refine ⟨ω', μ', run, ?_, hwf', e7, e0, e5, e6, e1,
    ⟨_, hpg, by rw [allocPost_base, allocPost_allocated]; show s.base + 32 * E ≤ _; omega, ht1,
      by unfold growTop; split <;> omega⟩, hstg, stk⟩
  rw [show s.base + 32 * maxSize = s.base + 1073741824 by rw [maxSize_val]]
  rw [htop] at hcs'
  generalize hN : C + 32 * (req + 1) = N at rep'
  have cls : ∀ c ∈ chunks (allocPost { s with allocated := E } bin req S (s.base + 1073741824)),
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
  have cls' : ∀ c ∈ chunks (allocPost { s with allocated := E } bin req S (s.base + 1073741824)),
      (c ∈ pre ++ ⟨C, S, false⟩ :: post) ∨ (c.addr = C ∧ c.used = true) ∨
      (S - req - 1 ≠ 0 ∧ c.addr = N) := by
    intro c hc
    rcases cls c hc with ⟨h, -⟩ | h | ⟨hr, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨by rw [h], by rw [h]⟩)
    · exact Or.inr (Or.inr ⟨hr, by rw [h]⟩)
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

/-- `alloc_refines_grow221K` at `hostCostMax`, the cap of `refineContract`: at most 14 pages a
    `grow_heap` call. -/
theorem alloc_refines_grow221 {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (x : RefineCtx)
    (ω : Regs) (μ : Memory) {hb : Nat} (s s' : State) (sp req ptr pb ph : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h : alloc (growTo pb) hb 1 req s = some (ptr, s')) (hgrown : s'.allocated ≠ s.allocated)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat 1)
    (h9 : ω[9] = UInt64.ofNat req) (h12 : ω[12] = UInt64.ofNat 1)
    (h120 : rdN μ (sp + 120) 8 = 204984) (h112 : rdN μ (sp + 112) 8 = 0)
    (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hal : s.allocated < 2147483648)
    (hfo : FirstOk s) (hcost : pagesOf (s.base + 32 * s'.allocated) ≤ ph + 14)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1) (hSb : 4096 * pb ≤ S0)
    (hp : HeapPages μ 48 pb ph) (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true)
    (hHT : s.base + 32 * s.allocated ≤ 4096 * ph) :
    ∃ ω' μ', FreeStepsH p (refineContract env) 41221 ω μ x 41423 ω' μ' x 500 ∧ Rep μ' s' ∧ WF s' ∧
      ω'[7] = UInt64.ofNat ptr ∧ ω'[0] = UInt64.ofNat (rdN μ (sp + 144) 8) ∧
      ω'[5] = UInt64.ofNat (rdN μ (sp + 136) 8) ∧ ω'[6] = UInt64.ofNat (rdN μ (sp + 128) 8) ∧
      ω'[1] = UInt64.ofNat (sp + 152) ∧
      (∃ h', HeapPages μ' 48 pb h' ∧ s'.base + 32 * s'.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → sp + 152 ≤ a → μ'.read a = μ.read a) :=
  alloc_refines_grow221K (p := p) (P := P) (hb := hb) (S0 := S0) (S1 := S1)
    env hostCostMax (by decide) x ω μ s s' sp req ptr pb ph hwf hrep hbd h48 hhb hbs h hgrown h1 h7
    h8 h9 h12 h120 h112 hsp hsp1 hb0 hbT hal hfo (by unfold hostCostMax; omega) hHTs hSTk hSb hp
    hst hHT

/-- **41177 … 41221 on first use** (heap base 0): the prologue, the call to `initialize` (the host
    grows the heap to its bound `pb` pages, at least the 51 that `initialize` needs), its writes,
    and the return to the bins with the saved ω₇, ω₈ and ω₉ restored.
    Under `refineContractK cap`, for any cap covering the call's 275. -/
theorem alloc_init_pathK {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (cap : Nat) (hcap : cap < 18446744073709551616) (h275 : 275 ≤ cap) (x : RefineCtx)
    (ω : Regs) (μ : Memory) (sp req pb ph : Nat) (hbd : heapBounds env.code = (48, pb)) (h51 : 51 ≤ ph)
    (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat 1)
    (h9 : ω[9] = UInt64.ofNat req) (h10 : ω[10] = UInt64.ofNat 0)
    (hsp : 2147483832 ≤ sp) (hsp1 : sp < 4294967296)
    (hb : rdN μ 206520 8 = 0) {S0 S1 : Nat} (hSTk : S0 + 184 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0)
    (hp : HeapPages μ 48 pb ph) (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (refineContractK cap env) 41177 ω μ x 41221 ω' μ' x 80 ∧
      ω'[1] = UInt64.ofNat (sp - 152) ∧ ω'[7] = UInt64.ofNat 196792 ∧ ω'[8] = UInt64.ofNat 1 ∧
      ω'[9] = UInt64.ofNat req ∧ ω'[12] = UInt64.ofNat 1 ∧
      rdN μ' (sp - 152 + 120) 8 = 204984 ∧ rdN μ' (sp - 152 + 112) 8 = 0 ∧
      UInt64.ofNat (rdN μ' (sp - 152 + 144) 8) = ω[0] ∧ UInt64.ofNat (rdN μ' (sp - 152 + 136) 8) = ω[5] ∧
      UInt64.ofNat (rdN μ' (sp - 152 + 128) 8) = ω[6] ∧
      rdN μ' 206516 4 = 206880 ∧ rdN μ' 206520 8 = 206880 ∧ rdN μ' 206824 8 = rdN μ 206824 8 ||| 2 ^ 63 ∧
      rdN μ' 206832 8 = rdN μ 206832 8 ||| 2 ^ 37 ∧ rdN μ' 206840 4 = 1 ∧ rdN μ' 206880 4 = 0 ∧
      rdN μ' 206884 4 = sizeWord 33554432 false ∧ rdN μ' 206888 4 = 0 ∧ rdN μ' 206892 4 = 0 ∧
      (∀ a, a < 4294967296 → (a < 206516 ∨ 206528 ≤ a) → (a < 206824 ∨ 206844 ≤ a) →
        (a < 206880 ∨ 206896 ≤ a) → (a < sp - 184 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      HeapPages μ' 48 pb ph ∧ (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) := by
  have hwr := HeapPages.wrAt hp hhb hst
  have hT : growTop 51 ph pb = ph := by unfold growTop; rw [if_pos (Or.inl h51)]
  have dec : ∀ v : UInt64, UInt64.ofNat (Num.decodeLE (Num.encodeLE 8 v.toNat)) = v := fun v => by
    rw [Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]
  obtain ⟨ω1, μ1, r1, a1, a11, a12, s0, s5, s6, s10, s32, fr1, ww1, g1⟩ :=
    al_pro (p := p) (P := P) (R := refineContractK cap env) x ω μ sp 0 0 h1 h7 (by rw [h8]) (by decide)
      (by omega) hsp1 hb (by omega) ⟨by omega, by omega⟩ hwr
  have r2 := al_br_init (p := p) (P := P) (R := refineContractK cap env) x ω1 μ1 a11
  obtain ⟨ω3, μ3, r3, c0, c5, c7, m48, m104, fr3, ww3, g3⟩ :=
    ai_call (p := p) (P := P) (R := refineContractK cap env) x ω1 μ1 (sp - 152) a1 (by omega) (by omega) (by omega) ⟨by omega, by omega⟩
      (hwr.of_eq ww1)
  obtain ⟨ω4, μ4, r4, d1, d5, d6, d7, n8, n16, n24, n32, fr4, ww4, g4⟩ :=
    ii_pre (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (sp - 152)
      (by rw [fget g3 1 (by decide) (by decide)]; exact a1) (by omega) (by omega) (by omega) ⟨by omega, by omega⟩
      ((hwr.of_eq ww1).of_eq ww3)
  have hp4 := HeapPages.of_eq hp (fun a => (ww4 a).trans ((ww3 a).trans (ww1 a)))
  have hst4 : ∀ a, S0 ≤ a → a < S1 → μ4.writable a = true := fun a h1 h2 => by
    rw [ww4, ww3, ww1]; exact hst a h1 h2
  have r5 := ii_callK (p := p) (P := P) env cap hcap x ω4 μ4 pb ph hbd hp4 (by omega) hhb hbs d7 (by rw [hT]; omega)
  rw [hT] at r5
  have hp5 := HeapPages.grow hp4 (Nat.le_refl ph)
  have hst5 := stack_setPages hst4 (t := ph) (by omega)
  have hw5 := HeapPages.wrAt hp5 hhb hst5
  have q7 : ω3[7] = UInt64.ofNat 196792 := by
    rw [c7, fget g1 7 (by decide) (by decide)]; exact h7
  obtain ⟨ω6, μ6, r6, w1, w2, w3, w4, w5, w6, w7, w8, w9, e7, e0, e5, e6, e1, fr6, ww6, g6⟩ :=
    ii_post (p := p) (P := P) (R := refineContractK cap env) x (setR7 ω4 ph) (μ4.setPages 48 (ph - 48) (some .write))
      (sp - 152 - 32) ph _ _
      (by rw [setR7_other (by decide) (by decide)]; exact d1) setR7_self
      (by rw [setR7_other (by decide) (by decide)]; exact d6)
      (by rw [setR7_other (by decide) (by decide)]; exact d5)
      (by unfold rdN; rw [Memory.readN_setPages, n32, q7]; rfl) h51 (by omega) rfl rfl (by omega) (by omega) (by omega)
      ⟨by omega, by omega⟩ hw5
  -- reads of μ₆ above the stack pointer, back to μ₃ and μ₁
  have tr3 : ∀ q, sp - 152 ≤ q → q + 8 ≤ sp → rdN μ6 q 8 = rdN μ3 q 8 := fun q h h' =>
    rdN_frame fun j hj => by
      rw [fr6 _ (by omega) (by omega) (by omega) (by omega), Memory.read_setPages,
        fr4 _ (by omega) (Or.inr (by omega))]
  have tr : ∀ q, sp - 152 ≤ q → q + 8 ≤ sp → q + 8 ≤ sp - 152 + 48 ∨ sp - 152 + 56 ≤ q →
      q + 8 ≤ sp - 152 + 104 ∨ sp - 152 + 112 ≤ q → rdN μ6 q 8 = rdN μ1 q 8 := fun q h h' h2 h3 =>
    (tr3 q h h').trans (rdN_frame fun j hj => fr3 _ (by omega) (by omega) (by omega))
  have k0 : ω6[0] = UInt64.ofNat 1998 := by
    rw [e0, show sp - 152 - 32 + 24 = sp - 152 - 8 by omega]; unfold rdN
    rw [Memory.readN_setPages, n8, c0]; rfl
  have r7 := ii_ret (p := p) (P := P) (R := refineContractK cap env) x ω6 μ6 k0
  obtain ⟨ω8, r8, b8, b9, b7, b11, g8⟩ := ai_back (p := p) (P := P) (R := refineContractK cap env) x ω6 μ6 (sp - 152)
    (by rw [e1, show sp - 152 - 32 + 32 = sp - 152 by omega]) e7 (by omega)
    (by omega) ⟨by omega, by omega⟩ (hw5.of_eq ww6).rd
  have rd3 : ∀ q, sp - 152 ≤ q → q + 8 ≤ sp → ∀ v : UInt64, μ3.readN q 8 = Num.encodeLE 8 v.toNat →
      UInt64.ofNat (rdN μ6 q 8) = v := fun q h h' v hv => by
    rw [tr3 q h h']; unfold rdN; rw [hv]; exact dec v
  have rd1 : ∀ q, sp - 152 ≤ q → q + 8 ≤ sp → (q + 8 ≤ sp - 152 + 48 ∨ sp - 152 + 56 ≤ q) →
      (q + 8 ≤ sp - 152 + 104 ∨ sp - 152 + 112 ≤ q) → ∀ v : UInt64, μ1.readN q 8 = Num.encodeLE 8 v.toNat →
      UInt64.ofNat (rdN μ6 q 8) = v := fun q h h' h2 h3 v hv => by
    rw [tr q h h' h2 h3]; unfold rdN; rw [hv]; exact dec v
  have stat : ∀ a, a < 2147483648 → μ4.read a = μ.read a := fun a ha => by
    rw [fr4 _ (by omega) (Or.inl (by omega)), fr3 _ (by omega) (by omega) (by omega),
      fr1 _ (by omega) (Or.inl (by omega))]
  have st8 : ∀ q, q + 8 ≤ 2147483648 → rdN (μ4.setPages 48 (ph - 48) (some .write)) q 8 = rdN μ q 8 :=
    fun q hq => rdN_frame fun j hj => by rw [Memory.read_setPages]; exact stat _ (by omega)
  refine ⟨ω8, μ6, ((((((r1.trans r2).trans r3).trans r4).trans r5).trans r6).trans (r7.trans r8)).mono (by omega),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, w1, w2, by rw [w3, st8 _ (by omega)], by rw [w4, st8 _ (by omega)],
    w5, w6, w7, w8, w9, fun a ha s1 s2 s3 s4 => ?_, HeapPages.of_eq hp5 ww6,
    fun a h1 h2 => by rw [ww6]; exact hst5 a h1 h2⟩
  · rw [fget g8 1 (by decide) (by decide), e1, show sp - 152 - 32 + 32 = sp - 152 by omega]
  · rw [b7]
    have := rd3 (sp - 152 + 48) (by omega) (by omega) _ m48
    rw [this, ← c7]; exact q7
  · rw [b8]
    have := rd3 (sp - 152 + 104) (by omega) (by omega) _ m104
    rw [this, fget g1 8 (by decide) (by decide)]; exact h8
  · rw [b9, e5, show sp - 152 - 32 + 16 = sp - 152 - 16 by omega]; unfold rdN
    rw [Memory.readN_setPages, n16, dec, c5, fget g1 9 (by decide) (by decide)]; exact h9
  · rw [fget g8 12 (by decide) (by decide), fget g6 12 (by decide) (by decide),
      setR7_other (by decide) (by decide), fget g4 12 (by decide) (by decide),
      fget g3 12 (by decide) (by decide)]; exact a12
  · rw [tr _ (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega)),
      show sp - 152 + 120 = sp - 32 by omega]; exact s32
  · have := rd1 (sp - 152 + 112) (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega)) _
      (by rw [show sp - 152 + 112 = sp - 40 by omega]; exact s10)
    rw [h10] at this
    have hl := rdN_lt64 μ6 (sp - 152 + 112)
    have := congrArg UInt64.toNat this
    rw [UInt64.toNat_ofNat', UInt64.toNat_ofNat'] at this
    simpa [Nat.mod_eq_of_lt hl] using this
  · exact rd1 _ (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega)) _
      (by rw [show sp - 152 + 144 = sp - 8 by omega]; exact s0)
  · exact rd1 _ (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega)) _
      (by rw [show sp - 152 + 136 = sp - 16 by omega]; exact s5)
  · exact rd1 _ (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega)) _
      (by rw [show sp - 152 + 128 = sp - 24 by omega]; exact s6)
  · rw [fr6 _ ha s1 s2 s3, Memory.read_setPages]
    rcases s4 with s4 | s4
    · by_cases hl : a < sp - 152 - 32
      · rw [fr4 _ ha (Or.inl hl)]
        by_cases hm : a < sp - 152
        · rw [fr3 _ ha (by omega) (by omega), fr1 _ ha (Or.inl hm)]
        · omega
      · omega
    · rw [fr4 _ ha (Or.inr (by omega)), fr3 _ ha (by omega) (by omega), fr1 _ ha (Or.inr s4)]

/-- `alloc_init_pathK` at `hostCostMax`, the cap of `refineContract`. -/
theorem alloc_init_path {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (x : RefineCtx)
    (ω : Regs) (μ : Memory) (sp req pb ph : Nat) (hbd : heapBounds env.code = (48, pb)) (h51 : 51 ≤ ph)
    (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat 1)
    (h9 : ω[9] = UInt64.ofNat req) (h10 : ω[10] = UInt64.ofNat 0)
    (hsp : 2147483832 ≤ sp) (hsp1 : sp < 4294967296)
    (hb : rdN μ 206520 8 = 0) {S0 S1 : Nat} (hSTk : S0 + 184 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0)
    (hp : HeapPages μ 48 pb ph) (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (refineContract env) 41177 ω μ x 41221 ω' μ' x 80 ∧
      ω'[1] = UInt64.ofNat (sp - 152) ∧ ω'[7] = UInt64.ofNat 196792 ∧ ω'[8] = UInt64.ofNat 1 ∧
      ω'[9] = UInt64.ofNat req ∧ ω'[12] = UInt64.ofNat 1 ∧
      rdN μ' (sp - 152 + 120) 8 = 204984 ∧ rdN μ' (sp - 152 + 112) 8 = 0 ∧
      UInt64.ofNat (rdN μ' (sp - 152 + 144) 8) = ω[0] ∧ UInt64.ofNat (rdN μ' (sp - 152 + 136) 8) = ω[5] ∧
      UInt64.ofNat (rdN μ' (sp - 152 + 128) 8) = ω[6] ∧
      rdN μ' 206516 4 = 206880 ∧ rdN μ' 206520 8 = 206880 ∧ rdN μ' 206824 8 = rdN μ 206824 8 ||| 2 ^ 63 ∧
      rdN μ' 206832 8 = rdN μ 206832 8 ||| 2 ^ 37 ∧ rdN μ' 206840 4 = 1 ∧ rdN μ' 206880 4 = 0 ∧
      rdN μ' 206884 4 = sizeWord 33554432 false ∧ rdN μ' 206888 4 = 0 ∧ rdN μ' 206892 4 = 0 ∧
      (∀ a, a < 4294967296 → (a < 206516 ∨ 206528 ≤ a) → (a < 206824 ∨ 206844 ≤ a) →
        (a < 206880 ∨ 206896 ≤ a) → (a < sp - 184 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      HeapPages μ' 48 pb ph ∧ (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) :=
  alloc_init_pathK (p := p) (P := P) (S0 := S0) (S1 := S1) env hostCostMax (by decide) (by decide)
    x ω μ sp req pb ph hbd h51 hhb hbs h1 h7 h8 h9 h10 hsp hsp1 hb hSTk hSb hp hst

/-- `init`'s result on a zeroed allocator: the heap base and one unit allocated, after the heap grew
    to cover it. -/
theorem init_fields {grow : Grow} {hb : Nat} {s s' : State} (hs0 : s.base = 0) (h : init grow hb s = some s') :
    s'.base = hb ∧ s'.allocated = 1 ∧ grow hb 1 = true := by
  unfold init at h
  simp only [hs0, ne_eq, not_true_eq_false, ↓reduceIte] at h
  split at h
  · simp at h
  · rename_i hg
    simp only [Option.some.injEq] at h
    refine ⟨by rw [← h]; rfl, by rw [← h]; rfl, by simpa using hg⟩

/-- The first `alloc` after `init` grows the heap: the one free chunk starts at the base, so the
    allocation ends at least two units past it, beyond the one unit `init` allocated. -/
theorem first_grows {grow : Grow} {r p : Nat} {s s' : State} (hwf : WF s) (c0 : Nat)
    (hch : chunks s = [⟨c0, maxSize, false⟩]) (h1 : s.allocated = 1) (h : alloc1 grow r s = some (p, s')) :
    s'.allocated ≠ s.allocated := by
  obtain ⟨bin, a1, hbin, hmax, hS, hA, hE, -, rfl⟩ := alloc1_eq h
  obtain ⟨-, -, -, -, ⟨pre, post, hcs⟩, -, -⟩ := bin_chunk hwf hmax hbin
  rw [hch] at hcs
  have hx : wordSize (s.hdr (s.heads bin)).size = maxSize := by
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, Chunk.mk.injEq] at hcs
      exact hcs.1.2.1.symm
    | cons y ys => simp at hcs
  rw [allocPost_allocated, h1]
  show a1 ≠ 1
  rw [hx, maxSize_val] at hE
  split at hE <;> omega

/-- **The binary's `alloc` on the allocator's first use refines the model's `alloc`**: from a
    zeroed allocator in memory (heap base 0, no free chunks), `alloc_impl` runs `initialize`, which
    has the host grow the heap to its bound `pb` pages and sets up one free chunk at 206880, then
    allocates from it, growing the heap again; memory then holds the model's state after
    `alloc (growTo pb) 206880 1 req` (GP v0.8.0 Appendix B, the `grow_heap` host call).
    Under `refineContractK cap`: the `grow_heap` call may cost up to `cap`. -/
theorem alloc_refines_firstK {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (cap : Nat) (hcap : cap < 18446744073709551616) (x : RefineCtx)
    (ω : Regs) (μ : Memory) (s s' : State) (sp req ptr pb ph : Nat)
    (hrep : RepAt μ s (fun _ => False) (fun _ => False)) (hs0 : s.base = 0) (hheads : ∀ b, s.heads b = 0)
    (hsec : ∀ q, s.secondary q = 0) (hpri : s.primary = 0)
    (hbd : heapBounds env.code = (48, pb)) (h51 : 51 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h : alloc (growTo pb) 206880 1 req s = some (ptr, s'))
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat 1)
    (h9 : ω[9] = UInt64.ofNat req) (h10 : ω[10] = UInt64.ofNat 0)
    (hsp : 2147483832 ≤ sp) (hsp1 : sp < 4294967296) (hcost : 275 + 121 * (pagesOf (206880 + 32 * s'.allocated) - ph) ≤ cap)
    {S0 S1 : Nat} (hSTk : S0 + 184 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (refineContractK cap env) 41177 ω μ x 41423 ω' μ' x 580 ∧ Rep μ' s' ∧ WF s' ∧
      ω'[7] = UInt64.ofNat ptr ∧ ω'[0] = ω[0] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[1] = ω[1] ∧
      (∃ h', HeapPages μ' 48 pb h' ∧ s'.base + 32 * s'.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧ (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) := by
  cases hi : init (growTo pb) 206880 s with
  | none => unfold alloc at h; simp [hi] at h
  | some s0 =>
  obtain ⟨e_base, e_alloc, -⟩ := init_fields hs0 hi
  obtain ⟨hch, hwf0⟩ := init_wf (by decide) (by decide) (by rw [maxSize_val]; decide) hs0 hheads hsec hpri hi
  have hfo := init_first hs0 hi
  rw [alloc_after_init hi hwf0.1] at h
  have hgrown : s'.allocated ≠ s0.allocated := by
    rw [alloc_one hwf0.1] at h; exact first_grows hwf0 _ hch e_alloc h
  have hb : rdN μ 206520 8 = 0 := by have := hrep.base; unfold A0 at this; rw [this, hs0]
  obtain ⟨ω1, μ1, r1, a1, a7, a8, a9, a12, m120, m112, m144, m136, m128, w1, w2, w3, w4, w5, w6, w7, w8, w9,
      fr1, hp1, hst1⟩ := alloc_init_pathK (p := p) (P := P) env cap hcap (by omega) x ω μ sp req pb ph hbd h51 hhb hbs h1 h7 h8 h9 h10
    hsp hsp1 hb hSTk hSb hp hst
  have rep0 := init_rep hrep hs0 hi w1 w2 w3 w4 w5 w6 w7 w8 w9
    (fun a ha s1 s2 s3 => fr1 a (by omega) s1 s2 s3 (Or.inl (by omega)))
  have rep1 : Rep μ1 s0 :=
    ⟨rep0.heads, rep0.sec, rep0.pri, rep0.base, rep0.alloc,
      fun c hc => rep0.prev _ (by rw [hch, List.mem_singleton] at hc; subst hc; rfl),
      fun c hc => rep0.size _ (by rw [hch, List.mem_singleton] at hc; subst hc; rfl),
      fun c hc _ => rep0.next _ (by rw [hch, List.mem_singleton] at hc; subst hc; rfl),
      fun c hc _ => rep0.prevL _ (by rw [hch, List.mem_singleton] at hc; subst hc; rfl)⟩
  obtain ⟨ω2, μ2, r2, rep2, wf2, c7, c0, c5, c6, c1, hh', hst2, fr2⟩ := alloc_refines_grow221K (p := p) (P := P)
    (S0 := S0) (S1 := S1) env cap hcap x
    ω1 μ1 s0 s' (sp - 152) req ptr pb ph hwf0 rep1 hbd (by omega) hhb hbs h hgrown a1 a7 a8 a9 a12 m120 m112
    (by omega) (by omega) (by omega) (by rw [e_base]; omega) (by rw [e_alloc]; omega) hfo
    (by rw [e_base]; exact hcost) (by omega) ⟨by omega, by omega⟩ hSb hp1 hst1 (by rw [e_base, e_alloc]; omega)
  refine ⟨ω2, μ2, (r1.trans r2).mono (by omega), rep2, wf2, c7, by rw [c0, m144], by rw [c5, m136],
    by rw [c6, m128], by rw [c1, h1, show sp - 152 + 152 = sp by omega], hh', hst2, fun a ha hs => ?_⟩
  rw [fr2 a ha (by omega), fr1 a ha (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr hs)]

/-- `alloc_refines_firstK` at `hostCostMax`, the cap of `refineContract`: at most 14 pages a
    `grow_heap` call. -/
theorem alloc_refines_first {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (x : RefineCtx)
    (ω : Regs) (μ : Memory) (s s' : State) (sp req ptr pb ph : Nat)
    (hrep : RepAt μ s (fun _ => False) (fun _ => False)) (hs0 : s.base = 0) (hheads : ∀ b, s.heads b = 0)
    (hsec : ∀ q, s.secondary q = 0) (hpri : s.primary = 0)
    (hbd : heapBounds env.code = (48, pb)) (h51 : 51 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h : alloc (growTo pb) 206880 1 req s = some (ptr, s'))
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat 1)
    (h9 : ω[9] = UInt64.ofNat req) (h10 : ω[10] = UInt64.ofNat 0)
    (hsp : 2147483832 ≤ sp) (hsp1 : sp < 4294967296) (hcost : pagesOf (206880 + 32 * s'.allocated) ≤ ph + 14)
    {S0 S1 : Nat} (hSTk : S0 + 184 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (refineContract env) 41177 ω μ x 41423 ω' μ' x 580 ∧ Rep μ' s' ∧ WF s' ∧
      ω'[7] = UInt64.ofNat ptr ∧ ω'[0] = ω[0] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[1] = ω[1] ∧
      (∃ h', HeapPages μ' 48 pb h' ∧ s'.base + 32 * s'.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧ (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) :=
  alloc_refines_firstK (p := p) (P := P) (S0 := S0) (S1 := S1) env hostCostMax (by decide) x ω μ s
    s' sp req ptr pb ph hrep hs0 hheads hsec hpri hbd h51 hhb hbs h h1 h7 h8 h9 h10 hsp hsp1
    (by unfold hostCostMax; omega) hSTk hSb hp hst

/-- The allocator's fields (`RepAt` with no headers) survive writes outside them. -/
theorem RepAt.congr_fields {μ μ' : Memory} {t : State} (h : RepAt μ t (fun _ => False) (fun _ => False))
    (wf : ∀ b, A0 ≤ b → b < 206848 → μ'.read b = μ.read b) : RepAt μ' t (fun _ => False) (fun _ => False) := by
  refine ⟨fun b hb => ?_, fun q hq => ?_, ?_, ?_, ?_, fun b hb => hb.elim, fun b hb => hb.elim,
    fun b hb => hb.elim, fun b hb => hb.elim⟩
  · rw [← h.heads b hb]; unfold binCount at hb
    exact rdN_frame fun j hj => wf _ (by unfold A0; omega) (by unfold A0; omega)
  · rw [← h.sec q hq]; exact rdN_frame fun j hj => wf _ (by unfold A0; omega) (by unfold A0; omega)
  · rw [← h.pri]; exact rdN_frame fun j hj => wf _ (by unfold A0; omega) (by unfold A0; omega)
  · rw [← h.base]; exact rdN_frame fun j hj => wf _ (by unfold A0; omega) (by unfold A0; omega)
  · rw [← h.alloc]; exact rdN_frame fun j hj => wf _ (by unfold A0; omega) (by unfold A0; omega)

/-- After the first `alloc`, the heap base is 206880. -/
theorem alloc_first_base {grow : Grow} {r p : Nat} {s s' : State} (hs0 : s.base = 0)
    (h : alloc grow 206880 1 r s = some (p, s')) : s'.base = 206880 := by
  cases hi : init grow 206880 s with
  | none => unfold alloc at h; simp [hi] at h
  | some s0 =>
    obtain ⟨e_base, -, -⟩ := init_fields hs0 hi
    have hne : s0.base ≠ 0 := by rw [e_base]; decide
    rw [alloc_after_init hi hne, alloc_one hne] at h
    obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := alloc1_eq h
    rw [allocPost_base]; exact e_base

/-- **`alloc` (40494 … 40611) on the allocator's first use refines the model's `alloc`**: under the
    lock, `alloc_impl` initialises the allocator and allocates `⌈size / 32⌉` units (alignment 1);
    memory then holds the model's state, the lock is released, and ω₀, ω₁, ω₅ and ω₆ are restored.
    Under `refineContractK cap`: the `grow_heap` call may cost up to `cap`. -/
theorem alloc_wrap_refines_firstK {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (cap : Nat) (hcap : cap < 18446744073709551616)
    (x : RefineCtx) (ω : Regs) (μ : Memory) (s s' : State) (sp size al ptr pb ph : Nat)
    (hrep : RepAt μ s (fun _ => False) (fun _ => False)) (hs0 : s.base = 0) (hheads : ∀ b, s.heads b = 0)
    (hsec : ∀ q, s.secondary q = 0) (hpri : s.primary = 0)
    (hbd : heapBounds env.code = (48, pb)) (h51 : 51 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h : alloc (growTo pb) 206880 1 ((size + 31) / 32) s = some (ptr, s'))
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat size) (h8 : ω[8] = UInt64.ofNat al)
    (hal : 1 ≤ al) (hal1 : al ≤ 32) (hs : size + 31 < 68719476736)
    (hsp : 2147483848 ≤ sp) (hsp1 : sp < 4294967296)
    (hl : rdN μ 206848 1 = 0) (hcost : 275 + 121 * (pagesOf (206880 + 32 * s'.allocated) - ph) ≤ cap)
    {S0 S1 : Nat} (hSTk : S0 + 200 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (refineContractK cap env) 40494 ω μ x 40611 ω' μ' x 620 ∧ Rep μ' s' ∧ WF s' ∧
      ω'[7] = UInt64.ofNat ptr ∧ rdN μ' 206848 1 = 0 ∧
      (∃ h', HeapPages μ' 48 pb h' ∧ s'.base + 32 * s'.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have hw := HeapPages.wrAt hp hhb hst
  obtain ⟨ω1, μ1, r1, a1, a7, a8, a9, a10, a0, a5, -, st8, st16, fr1, ww1, g1⟩ :=
    al_lock (p := p) (P := P) (R := refineContractK cap env) (S0 := S0) (S1 := S1) x ω μ sp size al h1 h7 h8 hal hal1 hs (by omega) hsp1 hl (by omega) ⟨by omega, by omega⟩ hw
  have rep1 := hrep.congr_fields fun a ha1 ha2 =>
    fr1 a (by omega) (Or.inl (by omega)) (Or.inr (by unfold A0 at ha1; omega)) (Or.inl ha2)
  obtain ⟨ω2, μ2, r2, rep2, wf2, e7, e0, e5, e6, e1, ⟨h', hp2, hsp2, hh1, hh2⟩, hst2, stk2⟩ :=
    alloc_refines_firstK (p := p) (P := P) (S0 := S0) (S1 := S1) env cap hcap x ω1 μ1 s s' (sp - 16) _ ptr pb ph rep1 hs0
      hheads hsec hpri hbd h51 hhb hbs h a1 a7 a8 a9 a10 (by omega) (by omega) hcost ⟨by omega, by omega⟩ hSb
      (HeapPages.of_eq hp ww1) (fun a h1 h2 => by rw [ww1]; exact hst a h1 h2)
  have rj := al_ret_jump (p := p) (P := P) (R := refineContractK cap env) x ω2 μ2 (by rw [e0, a0])
  obtain ⟨ω3, μ3, r3, c0, c5, c1, cl, fr3, ww3, g3⟩ :=
    al_unlock (p := p) (P := P) (R := refineContractK cap env) (S0 := S0) (S1 := S1) x ω2 μ2 (sp - 16) (by rw [e1, a1]) (by rw [e5, a5]) (by omega) (by omega) (by omega)
      ⟨by omega, by omega⟩ (HeapPages.wrAt hp2 hh2 hst2)
  have hb' : s'.base = 206880 := alloc_first_base hs0 h
  refine ⟨ω3, μ3, (((r1.trans r2).trans rj).trans r3).mono (by omega),
    rep2.congr_lock wf2 (by rw [hb']; decide) (by rw [hb']; decide)
      (fun a ha1 ha2 ha3 => fr3 a (by omega) (by omega)), wf2,
    by rw [fget g3 7 (by decide) (by decide)]; exact e7, cl, ⟨h', HeapPages.of_eq hp2 ww3, hsp2, hh1, hh2⟩,
    fun a h1 h2 => by rw [ww3]; exact hst2 a h1 h2,
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

/-- `alloc_wrap_refines_firstK` at `hostCostMax`, the cap of `refineContract`: at most 14 pages a
    `grow_heap` call. -/
theorem alloc_wrap_refines_first {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (x : RefineCtx) (ω : Regs) (μ : Memory) (s s' : State) (sp size al ptr pb ph : Nat)
    (hrep : RepAt μ s (fun _ => False) (fun _ => False)) (hs0 : s.base = 0) (hheads : ∀ b, s.heads b = 0)
    (hsec : ∀ q, s.secondary q = 0) (hpri : s.primary = 0)
    (hbd : heapBounds env.code = (48, pb)) (h51 : 51 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h : alloc (growTo pb) 206880 1 ((size + 31) / 32) s = some (ptr, s'))
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat size) (h8 : ω[8] = UInt64.ofNat al)
    (hal : 1 ≤ al) (hal1 : al ≤ 32) (hs : size + 31 < 68719476736)
    (hsp : 2147483848 ≤ sp) (hsp1 : sp < 4294967296)
    (hl : rdN μ 206848 1 = 0) (hcost : pagesOf (206880 + 32 * s'.allocated) ≤ ph + 14)
    {S0 S1 : Nat} (hSTk : S0 + 200 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (refineContract env) 40494 ω μ x 40611 ω' μ' x 620 ∧ Rep μ' s' ∧ WF s' ∧
      ω'[7] = UInt64.ofNat ptr ∧ rdN μ' 206848 1 = 0 ∧
      (∃ h', HeapPages μ' 48 pb h' ∧ s'.base + 32 * s'.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] :=
  alloc_wrap_refines_firstK (p := p) (P := P) (S0 := S0) (S1 := S1) env hostCostMax (by decide) x ω
    μ s s' sp size al ptr pb ph hrep hs0 hheads hsec hpri hbd h51 hhb hbs h h1 h7 h8 hal hal1 hs
    hsp hsp1 hl (by unfold hostCostMax; omega) hSTk hSb hp hst

end Services.Bootstrap.Alloc
