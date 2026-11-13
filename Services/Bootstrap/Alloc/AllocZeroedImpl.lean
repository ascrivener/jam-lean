import Services.Bootstrap.Alloc.AllocZeroedTail
import Services.Bootstrap.Alloc.AllocImpl
import Services.Bootstrap.Alloc.AllocZeroedMemzero

/-!
# The binary's `alloc_impl` with the zero flag

Copies of `AllocImpl.lean`'s composition with the zero flag (ω₁₀ at the entry, stored at the frame
+ 112) generic: they end at the caller's return target, through `memzero` when the tail zeroes the
block. The flag-0 lemmas are unchanged.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- As `aw_hdr`, with ω₄ = 32·req (the block's data octets, `memzero`'s length in the zeroing tail).
    **41870 … 41910**: the allocated chunk M's header (`prev`, `req + 1` units, used); ω₂ the data,
    ω₈ the next chunk, ω₁₂ the space on the right. -/
theorem aw_hdrZ {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp M pv req A d rhs : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h2 : ω[2] = UInt64.ofNat M)
    (h0 : ω[0] = UInt64.ofNat pv) (h4 : ω[4] = UInt64.ofNat (req + 1)) (h9 : ω[9] = UInt64.ofNat req)
    (hA : rdN μ (sp + 80) 8 = A) (hd : rdN μ (sp + 72) 8 = d) (hrh : rdN μ (sp + 104) 8 = rhs)
    (hM : M + 32 * (req + 1) < 2147483648) (hpv : pv < 4294967296) (hrq : 2 * (req + 1) + 1 < 4294967296)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1)
    (hMT : 196608 ≤ M ∧ M + 8 ≤ HT) (hwr : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 41870 ω μ x 41910 ω' μ' x 14 ∧
      rdN μ' M 4 = pv ∧ rdN μ' (M + 4) 4 = sizeWord (req + 1) true ∧
      ω'[2] = UInt64.ofNat (M + 32) ∧ ω'[8] = UInt64.ofNat (M + 32 * (req + 1)) ∧ ω'[12] = UInt64.ofNat rhs ∧
      ω'[3] = UInt64.ofNat (req + 1) ∧ ω'[4] = UInt64.ofNat (32 * req) ∧
      (∀ a, a < 4294967296 → (a < M ∨ M + 8 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧ ∀ j : Fin 13, j.val ∉ [2, 3, 4, 6, 8, 10, 12] → ω'[j] = ω[j] := by
  have hr := hwr.rd
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h2, h0, h4, h9, hA, hd, hrh, hwr, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, by reg_frame⟩
    · rd_simp []; simp only [Nat.reducePow, Nat.reduceMul]; omega
    · rd_simp []; unfold sizeWord; simp only [Nat.reducePow, Nat.reduceMul, ↓reduceIte]; omega
    · reg_val
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, ↓reduceIte, PVM.getD_some', Nat.reduceEqDiff]; congr 1; omega
    · reg_val
    · reg_val
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, ↓reduceIte, PVM.getD_some', Nat.reduceEqDiff]; congr 1; omega
    · rd_simp []
    · rd_simp [hwr]

/-- As `alloc_end1`, with ω₄ = 32·req at the end (for the zeroing tail).
    **41726 … 42054**: the allocated chunk C's header (`registerAlloc`), and the `rhs` units after it,
    at N, registered free (`register`), the memory holding the result; ω₃ what `register` returns. -/
theorem alloc_end1Z {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (H F : Nat → Prop) (sp req C pv rhs : Nat) (hrep : RepAt μ s H F)
    (hHC : H C) (hHF : ∀ a, H a ∨ F a → Al s.base a) (hb0 : 206864 ≤ s.base)
    (hbT : s.base + 1073741824 < 2147483648) (hCa : (C - s.base) % 32 = 0) (hCb : s.base ≤ C)
    (hpv : pv < 2147483648) (hrq : req + 1 ≤ 33554432) (hrh : rhs ≤ 33554432)
    (hNe : C + 32 * (req + 1) + 32 * rhs ≤ s.base + 1073741824)
    (hNdis : rhs ≠ 0 → ∀ a, H a ∨ F a → a + 32 ≤ C + 32 * (req + 1) ∨ C + 32 * (req + 1) + 32 ≤ a)
    (hNold : rhs ≠ 0 → (registerAlloc s C pv (req + 1)).heads (binDown rhs) ≠ 0 →
      F ((registerAlloc s C pv (req + 1)).heads (binDown rhs)))
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat (32 * ((C - s.base) / 32)))
    (h0 : ω[0] = UInt64.ofNat 0) (h4 : ω[4] = UInt64.ofNat (req + 1)) (h9 : ω[9] = UInt64.ofNat req)
    (h7 : ω[7] = UInt64.ofNat 196792)
    (h96 : rdN μ (sp + 96) 8 = s.base) (h48 : rdN μ (sp + 48) 8 = pv) (A : Nat) (h80 : rdN μ (sp + 80) 8 = A)
    (h72 : rdN μ (sp + 72) 8 = (C - s.base) / 32 + 1) (h104 : rdN μ (sp + 104) 8 = rhs)
    (h88 : rdN μ (sp + 88) 8 = 204984) (h120 : rdN μ (sp + 120) 8 = 204984)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT)
    (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1) (hHFT : ∀ a, H a ∨ F a → a + 32 ≤ HT)
    (hNT : rhs ≠ 0 → C + 32 * (req + 1) + 32 ≤ HT) (hw : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 41726 ω μ x 42054 ω' μ' x 80 ∧
      RepAt μ' (register (registerAlloc s C pv (req + 1)) (C + 32 * (req + 1)) (req + 1) rhs).1
        (fun a => H a ∨ (rhs ≠ 0 ∧ a = C + 32 * (req + 1))) (fun a => F a ∨ (rhs ≠ 0 ∧ a = C + 32 * (req + 1))) ∧
      ω'[3] = UInt64.ofNat (register (registerAlloc s C pv (req + 1)) (C + 32 * (req + 1)) (req + 1) rhs).2 ∧
      ω'[12] = UInt64.ofNat rhs ∧ ω'[8] = UInt64.ofNat (C + 32 * (req + 1)) ∧ ω'[2] = UInt64.ofNat (C + 32) ∧
      ω'[1] = UInt64.ofNat sp ∧ ω'[4] = UInt64.ofNat (32 * req) ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      (∀ a, a < 4294967296 → 2147483648 ≤ a → μ'.read a = μ.read a) ∧
      HKeepG μ μ' (fun a => (H a ∨ F a) ∨ (rhs ≠ 0 ∧ a = C + 32 * (req + 1))) := by
  have hC : s.base + 32 * ((C - s.base) / 32) = C := by omega
  have hHFl : ∀ a, H a ∨ F a → 206864 ≤ a ∧ a + 16 < 2147483648 := fun a ha => by
    have := hHF a ha; unfold Al at this; omega
  have hAC := hHF C (Or.inl hHC)
  have hCT := hHFT C (Or.inl hHC)
  unfold Al at hAC
  obtain ⟨ω1, r1, a2, a0, g1⟩ := aw_left0 (p := p) (P := P) (R := R) x ω μ sp s.base ((C - s.base) / 32) pv h1 h8
    h0 h96 h48 (by omega) hsp hHTs hSTk hw.rd
  rw [hC] at a2
  obtain ⟨ω2, μ2, r2, m1, m2, b2, b8, b12, b3, b4, fr2, ww2, g2⟩ := aw_hdrZ (p := p) (P := P) (R := R) x ω1 μ sp C pv req
    A ((C - s.base) / 32 + 1) rhs (by rw [fget g1 1 (by decide) (by decide)]; exact h1) a2 a0
    (by rw [fget g1 4 (by decide) (by decide)]; exact h4) (by rw [fget g1 9 (by decide) (by decide)]; exact h9)
    h80 h72 h104 (by omega) (by omega) (by omega) hsp0 hsp hHTs hSTk ⟨by omega, by omega⟩ hw
  have rep2 : RepAt μ2 (registerAlloc s C pv (req + 1)) H F :=
    registerAlloc_rep hrep hHC m1 m2 (fun b h1 h2 => fr2 b (by omega) h2) (by omega) (fun b hb => by
      have := hHF b hb; unfold Al at this; omega)
  have k1 : ω2[1] = UInt64.ofNat sp := by
    rw [fget g2 1 (by decide) (by decide), fget g1 1 (by decide) (by decide)]; exact h1
  have tr2 : ∀ a, a < 4294967296 → 2147483648 ≤ a → μ2.read a = μ.read a := fun a h h' => fr2 a h (by omega)
  have st2 : ∀ a, sp + 32 ≤ a → a + 8 ≤ sp + 152 → rdN μ2 a 8 = rdN μ a 8 := fun a h h' =>
    rdN_frame fun j hj => tr2 _ (by omega) (by omega)
  by_cases hr0 : rhs = 0
  · subst hr0
    have r3 := ar_zero (p := p) (P := P) (R := R) x ω2 μ2 b12
    have e : register (registerAlloc s C pv (req + 1)) (C + 32 * (req + 1)) (req + 1) 0 =
        (registerAlloc s C pv (req + 1), req + 1) := by unfold register; simp
    have eH : (fun a => H a ∨ ((0 : Nat) ≠ 0 ∧ a = C + 32 * (req + 1))) = H := funext fun a => propext (by simp)
    have eF : (fun a => F a ∨ ((0 : Nat) ≠ 0 ∧ a = C + 32 * (req + 1))) = F := funext fun a => propext (by simp)
    rw [e, eH, eF]
    exact ⟨ω2, μ2, ((r1.trans r2).trans r3).mono (by omega), rep2, b3, b12, b8, b2, k1, b4, ww2, tr2,
      HKeepG.of_low fun a h1 h2 h3 => fr2 a (by omega) (by have := h3 C (Or.inl (Or.inl hHC)); omega)⟩
  · generalize hN : C + 32 * (req + 1) = N at *
    generalize hs3 : registerAlloc s C pv (req + 1) = s3 at *
    have hBin : binDown rhs < 2432 := toBin_lt false (Nat.min_le_right _ _)
    -- the bin of rhs, plus one, in ω₆
    obtain ⟨ω3, r3, c6, c12, g3⟩ : ∃ ω3, FreeStepsH p R 41910 ω2 μ2 x 41958 ω3 μ2 x 16 ∧
        ω3[6] = UInt64.ofNat (binDown rhs + 1) ∧ ω3[12] = UInt64.ofNat rhs ∧
        ∀ j : Fin 13, j.val ∉ [6, 9, 11, 12] → ω3[j] = ω2[j] := by
      by_cases hsm : rhs ≤ 127
      · obtain ⟨ω3, r, e6, g⟩ := ar_bin_small (p := p) (P := P) (R := R) x ω2 μ2 rhs b12 (by omega) hsm
        exact ⟨ω3, r.mono (by omega), e6, by rw [fget g 12 (by decide) (by decide)]; exact b12,
          fun j hj => g j (by simp at hj ⊢; omega)⟩
      · exact ar_bin_big (p := p) (P := P) (R := R) x ω2 μ2 sp rhs k1 b12 (by rw [st2 _ (by omega) (by omega)]; exact h104)
          (by omega) (by omega) hsp hHTs hSTk (hw.of_eq ww2).rd
    have hold := rep2.heads (binDown rhs) (by unfold binCount; omega)
    unfold A0 at hold
    generalize hO : s3.heads (binDown rhs) = old at hold hNold
    have hOF := hNold hr0
    have hOA : old ≠ 0 → Al s.base old := fun h => hHF _ (Or.inr (hOF h))
    have hNd := hNdis hr0
    obtain ⟨ω4, μ4, r4, w1, w2, w3, w4, w5, w6, w7, w8, wf, ww4, d3, -, d12, g4⟩ := ar_write (p := p) (P := P) (R := R)
      x ω3 μ2 sp (binDown rhs) N (req + 1) rhs old
      (by rw [fget g3 1 (by decide) (by decide)]; exact k1) c6 (by rw [fget g3 8 (by decide) (by decide)]; exact b8)
      (by rw [fget g3 3 (by decide) (by decide)]; exact b3) c12
      (by rw [fget g3 7 (by decide) (by decide), fget g2 7 (by decide) (by decide), fget g1 7 (by decide) (by decide)]
          exact h7)
      (by rw [st2 _ (by omega) (by omega)]; exact h88) (by rw [st2 _ (by omega) (by omega)]; exact h120)
      (by rw [st2 _ (by omega) (by omega)]; exact h104) hBin (by omega) (by omega) (by omega) (by omega)
      (by rw [show 196792 + binDown rhs * 4 = 196792 + 4 * binDown rhs by omega]; exact hold)
      (by by_cases h0 : old = 0
          · omega
          · have := hOA h0; unfold Al at this; omega)
      (fun h0 => by
        have := hOA h0; have h2 := hNd old (Or.inr (hOF h0)); unfold Al at this; omega)
      hsp0 hsp hHTs hSTk (by have := hNT hr0; omega)
      (fun h0 => by have := hHFT _ (Or.inr (hOF h0)); omega) (hw.of_eq ww2)
    have hNa : 206864 ≤ N := by omega
    have rep4 := register_rep (M := N) (pv := req + 1) (size := rhs) rep2 hr0 (by unfold binCount; omega)
      (by rw [hO]; intro e; subst e; have := hNd _ (Or.inr (hOF (by omega))); omega)
      (by rw [show binDown rhs * 4 + 196792 = 196792 + binDown rhs * 4 by omega]; exact w1) w2 w3
      (by rw [hO]; exact w4) w5 (by rw [hO]; exact w6)
      (by rw [show 204984 + binDown rhs / 64 * 8 + 1544 = binDown rhs / 64 * 8 + 204984 + 1544 by omega]; exact w7) w8
      (fun a h1 h2 h3 h4 h5 h6 => wf a h1 (by omega) h3 (by rw [hO] at h4; exact h4) (by omega) h6)
      hNa (by omega) (by rw [hO]; intro h0; have := hOA h0; unfold Al at this; omega)
      (fun a ha => by
        rw [hO]
        have hAa := hHF a ha; have hda := hNd a ha
        unfold Al at hAa
        refine ⟨by omega, by omega, by omega, ?_⟩
        by_cases h0 : old = 0
        · exact Or.inl h0
        · have := hOA h0; unfold Al at this; omega)
    have eH : (fun a => H a ∨ (rhs ≠ 0 ∧ a = N)) = (fun a => H a ∨ a = N) :=
      funext fun a => propext (by simp [hr0])
    have eF : (fun a => F a ∨ (rhs ≠ 0 ∧ a = N)) = (fun a => F a ∨ a = N) :=
      funext fun a => propext (by simp [hr0])
    have e2 : (register s3 N (req + 1) rhs).2 = rhs := by unfold register; simp [hr0]
    rw [eH, eF, e2]
    refine ⟨ω4, μ4, (((r1.trans r2).trans r3).trans r4).mono (by omega), rep4, d3, d12,
      by rw [fget g4 8 (by decide) (by decide), fget g3 8 (by decide) (by decide)]; exact b8,
      by rw [fget g4 2 (by decide) (by decide), fget g3 2 (by decide) (by decide)]; exact b2,
      by rw [fget g4 1 (by decide) (by decide), fget g3 1 (by decide) (by decide)]; exact k1,
      by rw [fget g4 4 (by decide) (by decide), fget g3 4 (by decide) (by decide)]; exact b4, fun a => (ww4 a).trans (ww2 a),
      fun a h h' => (wf a h (by omega) (by omega) (by
        by_cases h0 : old = 0
        · exact Or.inl h0
        · have := hOA h0; unfold Al at this; right; right; omega) (by omega) (by omega)).trans (tr2 a h h'),
      HKeepG.of_low fun a h1 h2 h3 => by
        have hN' := h3 N (Or.inr ⟨hr0, rfl⟩)
        have hC' := h3 C (Or.inl (Or.inl hHC))
        have ho : old = 0 ∨ a < old + 12 ∨ old + 16 ≤ a := by
          by_cases h0 : old = 0
          · exact Or.inl h0
          · have := h3 old (Or.inl (Or.inr (hOF h0))); right; omega
        rw [wf a (by omega) (by omega) (by omega) ho (by omega) (by omega), fr2 a (by omega) (by omega)]⟩

/-- The representation is kept by a write to a region D … D + n above the allocator's globals that
    meets no header (the zeroed block's data). -/
theorem RepAt.congr_off {μ μ' : Memory} {t : State} {H F : Nat → Prop} {D n : Nat} (h : RepAt μ t H F)
    (wf : ∀ b, b < 4294967296 → (b < D ∨ D + n ≤ b) → μ'.read b = μ.read b) (hD : 206864 ≤ D)
    (hHa : ∀ b, H b ∨ F b → b + 16 ≤ D ∨ D + n ≤ b) (hHl : ∀ b, H b ∨ F b → b + 16 < 4294967296) :
    RepAt μ' t H F := by
  refine ⟨fun b hb => ?_, fun q hq => ?_, ?_, ?_, ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_,
    fun b hb => ?_⟩
  · rw [← h.heads b hb]; unfold A0; unfold binCount at hb; exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · rw [← h.sec q hq]; unfold A0; exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · rw [← h.pri]; unfold A0; exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · rw [← h.base]; unfold A0; exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · rw [← h.alloc]; unfold A0; exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · have := hHa b (Or.inl hb); have := hHl b (Or.inl hb); rw [← h.prev b hb]; exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · have := hHa b (Or.inl hb); have := hHl b (Or.inl hb); rw [← h.size b hb]; exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · have := hHa b (Or.inr hb); have := hHl b (Or.inr hb); rw [← h.next b hb]; exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · have := hHa b (Or.inr hb); have := hHl b (Or.inr hb); rw [← h.prevL b hb]; exact rdN_frame fun j hj => wf _ (by omega) (by omega)

/-- **42054 … the caller's return target t**, the flag z generic: as `alloc_end2` (the final chunk F
    records `pv` if below the heap's end, the data address D returned in ω₇), and when ω₁₀ ∧ z ≠ 0 the
    block's 32·req data octets D … D + 32·req zeroed by `memzero`, which returns to t itself. The
    memory is kept off the headers and off the block's data. -/
theorem alloc_end2Z {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (t : State) (H F : Nat → Prop) (sp N rhs pv D req z ret tg : Nat) (hrep : RepAt μ t H F)
    (hHF : ∀ a, H a ∨ F a → Al t.base a) (hb0 : 206864 ≤ t.base) (hbT : t.base + 1073741824 < 2147483648)
    (hFin : N + 32 * rhs < t.base + 1073741824 → H (N + 32 * rhs))
    (hNe : N + 32 * rhs ≤ t.base + 1073741824) (hNa : 206864 ≤ N)
    (h1 : ω[1] = UInt64.ofNat sp) (h12 : ω[12] = UInt64.ofNat rhs) (h8 : ω[8] = UInt64.ofNat N)
    (h3 : ω[3] = UInt64.ofNat pv) (h2 : ω[2] = UInt64.ofNat D) (h4 : ω[4] = UInt64.ofNat (32 * req))
    (h120 : rdN μ (sp + 120) 8 = 204984) (hz : z < 18446744073709551616) (h112 : rdN μ (sp + 112) 8 = z)
    (h144 : rdN μ (sp + 144) 8 = ret) (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = tg) (hbt : P.isBlockStart tg = true)
    (hpv : pv < 4294967296) (hD8 : D % 8 = 0) (hDa : 206864 ≤ D) (hreq : 1 ≤ req)
    (hDT : D + 32 * req < 2147483648)
    (hDH : ∀ a, H a ∨ F a → a + 16 ≤ D ∨ D + 32 * req ≤ a)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT)
    (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1) (hHFT : ∀ a, H a ∨ F a → a + 32 ≤ HT) (hDHT : D + 32 * req ≤ HT)
    (hw : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 42054 ω μ x tg ω' μ' x (96 * req + 60) ∧
      RepAt μ' (if N + 32 * rhs < t.base + 1073741824 then
        setHdr t (N + 32 * rhs) (fun h => { h with prev := pv }) else t) H F ∧
      ω'[7] = UInt64.ofNat D ∧ ω'[0] = UInt64.ofNat ret ∧
      ω'[5] = UInt64.ofNat (rdN μ (sp + 136) 8) ∧ ω'[6] = UInt64.ofNat (rdN μ (sp + 128) 8) ∧
      ω'[1] = UInt64.ofNat (sp + 152) ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      (∀ a, a < 4294967296 → 2147483648 ≤ a → μ'.read a = μ.read a) ∧
      ∀ a, OffHdrG (fun a => H a ∨ F a) a → (a < D ∨ D + 32 * req ≤ a) → μ'.read a = μ.read a := by
  have hb4 : rdN μ 206520 4 = t.base := by
    rw [rdN_lo]; have := hrep.base; unfold A0 at this; rw [this]; omega
  have hr := hw.rd
  have hDl : D < 4294967296 := by omega
  have hwl : Exec.bitwise (· && ·) ω[10].toNat z < 18446744073709551616 := by
    rw [bitwise_and_land _ _ hz]
    exact Nat.lt_of_le_of_lt Nat.and_le_left (UInt64.toNat_lt _)
  have hHl : ∀ b, H b ∨ F b → b + 16 < 4294967296 := fun b hb => by have := hHF b hb; unfold Al at this; omega
  -- the block's data is writable
  have hwD : ∀ (μ1 : Memory), (∀ a, μ1.writable a = μ.writable a) →
      ∀ a, D ≤ a → a < D + 32 * req → μ1.writable a = true := fun μ1 e a h h' => by
    rw [e]; exact hw a (Or.inl ⟨by omega, by omega⟩)
  -- the zeroing: memzero on D … D + 32·req from 70133, returning to tg
  have mz : ∀ (ω1 : Regs) (μ1 : Memory), (∀ a, μ1.writable a = μ.writable a) →
      ω1[0] = UInt64.ofNat ret → ω1[7] = UInt64.ofNat D → ω1[8] = UInt64.ofNat 0 →
      ω1[9] = UInt64.ofNat (32 * req) →
      ∃ ω2 μ2, FreeStepsH p R 70133 ω1 μ1 x tg ω2 μ2 x (96 * req + 20) ∧
        ω2[0] = ω1[0] ∧ ω2[1] = ω1[1] ∧ ω2[5] = ω1[5] ∧ ω2[6] = ω1[6] ∧ ω2[7] = ω1[7] ∧
        (∀ a, a < 4294967296 → (a < D ∨ D + 32 * req ≤ a) → μ2.read a = μ1.read a) ∧
        (∀ a, μ2.writable a = μ1.writable a) := fun ω1 μ1 ww e0 e7 e8 e9 => by
    obtain ⟨ω2, μ2, r2, f0, f1, f5, f6, f7, -, fr2, -, ww2⟩ := MZ.memzero (p := p) (P := P) (R := R) x ω1 μ1 D
      (32 * req) ret tg hD8 ⟨by omega, by omega⟩ (by omega) e0 e7 e8 e9 hret hjt hbt (hwD μ1 ww)
    exact ⟨ω2, μ2, r2.mono (by omega), f0, f1, f5, f6, f7, fr2, ww2⟩
  by_cases hin : N + 32 * rhs < t.base + 1073741824
  · rw [if_pos hin]
    have hHF' := hFin hin
    have hAF := hHF _ (Or.inl hHF')
    unfold Al at hAF
    have hNT : 196608 ≤ N + 32 * rhs ∧ N + 32 * rhs + 4 ≤ HT := ⟨by omega, by have := hHFT _ (Or.inl hHF'); omega⟩
    by_cases hwz : Exec.bitwise (· && ·) ω[10].toNat z = 0
    · obtain ⟨ω1, μ1, r1, w1, e11, fr1, ww1, g1⟩ := an_tail_inZ0 (p := p) (P := P) (R := R) x ω μ sp N rhs pv t.base D
        h1 h12 h8 h3 h2 h120 z hz h112 hwz hb4 hbT hin hpv hDl hsp0 hsp hHTs hSTk hNT hw
      have rep1 : RepAt μ1 (setHdr t (N + 32 * rhs) (fun h => { h with prev := pv })) H F :=
        setPrev_rep hrep hHF' w1 fr1 (by omega) (fun b hb => by
          have := hHF b hb; unfold Al at this; omega)
      have tr : ∀ a, sp + 128 ≤ a → a + 8 ≤ sp + 152 → rdN μ1 a 8 = rdN μ a 8 := fun a h h' =>
        rdN_frame fun j hj => fr1 _ (by omega) (by omega)
      obtain ⟨ω2, r2, d7, d0, d5, d6, d1⟩ := an_retZ (p := p) (P := P) (R := R) x ω1 μ1 sp ret tg
        (by rw [fget g1 1 (by decide) (by decide)]; exact h1) (by rw [tr _ (by omega) (by omega)]; exact h144)
        hret hjt hbt hsp hHTs hSTk (hw.of_eq ww1).rd
      exact ⟨ω2, μ1, (r1.trans r2).mono (by omega), rep1, by rw [d7, e11], d0,
        by rw [d5, tr _ (by omega) (by omega)], by rw [d6, tr _ (by omega) (by omega)], d1, ww1,
        fun a h h' => fr1 a h (by omega), fun a ha _ => fr1 a (by have := ha.2.1; omega) (by
          have := ha.2.2 _ (Or.inl hHF'); omega)⟩
    · obtain ⟨ω1, μ1, r1, w1, e7, e8, e9, e0, e5, e6, e1, fr1, ww1⟩ := an_tail_inZ1 (p := p) (P := P) (R := R) x ω μ
        sp N rhs pv t.base D h1 h12 h8 h3 h2 h120 z hz h112 hwz hwl (32 * req) h4 (by omega) hb4 hbT hin hpv hDl
        hsp0 hsp hHTs hSTk hNT hw
      have rep1 : RepAt μ1 (setHdr t (N + 32 * rhs) (fun h => { h with prev := pv })) H F :=
        setPrev_rep hrep hHF' w1 fr1 (by omega) (fun b hb => by
          have := hHF b hb; unfold Al at this; omega)
      obtain ⟨ω2, μ2, r2, f0, f1, f5, f6, f7, fr2, ww2⟩ := mz ω1 μ1 ww1 (by rw [e0, h144]) e7 e8 e9
      refine ⟨ω2, μ2, (r1.trans r2).mono (by omega), rep1.congr_off fr2 hDa hDH hHl,
        by rw [f7, e7], by rw [f0, e0, h144], by rw [f5, e5], by rw [f6, e6], by rw [f1, e1],
        fun a => (ww2 a).trans (ww1 a), fun a h h' => (fr2 a h (Or.inr (by omega))).trans (fr1 a h (by omega)),
        fun a ha hd => (fr2 a (by have := ha.2.1; omega) hd).trans (fr1 a (by have := ha.2.1; omega) (by
          have := ha.2.2 _ (Or.inl hHF'); omega))⟩
  · rw [if_neg hin]
    by_cases hwz : Exec.bitwise (· && ·) ω[10].toNat z = 0
    · obtain ⟨ω1, r1, e11, g1⟩ := an_tail_endZ0 (p := p) (P := P) (R := R) x ω μ sp N rhs t.base D
        h1 h12 h8 h2 h120 z hz h112 hwz hb4 hbT (by omega) (by omega) hDl hsp hHTs hSTk hr
      obtain ⟨ω2, r2, d7, d0, d5, d6, d1⟩ := an_retZ (p := p) (P := P) (R := R) x ω1 μ sp ret tg
        (by rw [fget g1 1 (by decide) (by decide)]; exact h1) h144 hret hjt hbt hsp hHTs hSTk hr
      exact ⟨ω2, μ, (r1.trans r2).mono (by omega), hrep, by rw [d7, e11], d0, d5, d6, d1, fun _ => rfl,
        fun _ _ _ => rfl, fun _ _ _ => rfl⟩
    · obtain ⟨ω1, r1, e7, e8, e9, e0, e5, e6, e1⟩ := an_tail_endZ1 (p := p) (P := P) (R := R) x ω μ sp N rhs t.base D
        h1 h12 h8 h2 h120 z hz h112 hwz hwl (32 * req) h4 (by omega) hb4 hbT (by omega) (by omega) hDl hsp hHTs hSTk hr
      obtain ⟨ω2, μ2, r2, f0, f1, f5, f6, f7, fr2, ww2⟩ := mz ω1 μ (fun _ => rfl) (by rw [e0, h144]) e7 e8 e9
      exact ⟨ω2, μ2, (r1.trans r2).mono (by omega), hrep.congr_off fr2 hDa hDH hHl,
        by rw [f7, e7], by rw [f0, e0, h144], by rw [f5, e5], by rw [f6, e6], by rw [f1, e1], ww2,
        fun a h h' => fr2 a h (Or.inr (by omega)), fun a ha hd => fr2 a (by have := ha.2.1; omega) hd⟩

end Services.Bootstrap.Alloc
