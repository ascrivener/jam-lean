import Services.Bootstrap.Alloc.AllocZeroedTail
import Services.Bootstrap.Alloc.AllocImpl
import Services.Bootstrap.Alloc.AllocZeroedMemzero
import Services.Bootstrap.Alloc.AllocRefines

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

/-- **The heap frame off a block's data**: `HKeepG`, except in D … E (a block the zeroing tail may
    clear). -/
def HKeepGD (μ μ' : Memory) (G : Nat → Prop) (D E : Nat) : Prop :=
  ∀ a, OffHdrG G a → (a < D ∨ E ≤ a) → μ'.read a = μ.read a

theorem HKeepGD.mono {μ μ' : Memory} {G G' : Nat → Prop} {D E : Nat} (h : HKeepGD μ μ' G D E)
    (hG : ∀ b, G b → G' b ∨ b + 16 ≤ 196616 ∨ (196792 ≤ b ∧ b + 16 ≤ 206864)) : HKeepGD μ μ' G' D E :=
  fun a ⟨h1, h2, h3⟩ hd =>
    h a ⟨h1, h2, fun b hb => by rcases hG b hb with h | h; exact h3 b h; unfold Glob at h1; omega⟩ hd

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

/-- **The binary's `alloc_impl` with the zero flag z** (ω₁₀ at the entry), to the caller's return target
    tg (ω₀ = ret, an entry of **j**): as `alloc_impl`, the block's data possibly zeroed (when the
    flag and the tail's condition say so), the memory kept off the headers and off the block's data.
    `alloc_impl`'s statement: (alignment one unit, the heap in
    use, no growth, not zeroing): from the entry (41177) to its return (41423), memory holding s at
    the header addresses H/F comes to hold `allocPost s bin req S top`, and C + 32 is returned —
    given the facts about the heap the stages need, which the invariant provides. -/
theorem alloc_implZ {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (H F : Nat → Prop) (sp req bin C : Nat) (hrep : RepAt μ s H F)
    (hbits : BitsOk s.secondary s.primary s.heads)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat 1)
    (h9 : ω[9] = UInt64.ofNat req) (z : Nat) (hz : z < 18446744073709551616) (h10 : ω[10] = UInt64.ofNat z)
    (ret tg : Nat) (h0 : ω[0] = UInt64.ofNat ret) (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = tg) (hbt : P.isBlockStart tg = true)
    (hreq : 1 ≤ req) (hb8 : s.base % 8 = 0)
    (hCdis : ∀ a, H a ∨ F a → a ≠ C → a + 16 ≤ C ∨ C + 32 * wordSize (s.hdr C).size ≤ a)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648)
    (hm : req + 1 ≤ 33554432)
    (hbin : (findFirst s (binUp (req + 1))).or (findFirst s (binDown (req + 1))) = some bin) (hbn : bin < 2432)
    (hcb : s.heads bin = C) (hFC : F C) (hHC : H C) (hHF : ∀ a, H a ∨ F a → Al s.base a)
    (hnx : (s.hdr C).next ≠ 0 → F (s.hdr C).next) (hpv : (s.hdr C).prev < 2147483648)
    (hS : req + 1 ≤ wordSize (s.hdr C).size) (hCend : C + 32 * wordSize (s.hdr C).size ≤ s.base + 1073741824)
    (hal : s.allocated < 2147483648)
    (hend : (C - s.base) / 32 + 1 + req +
      (if wordSize (s.hdr C).size - req - 1 = 0 then 0 else 1) ≤ s.allocated)
    (hNdis : wordSize (s.hdr C).size - req - 1 ≠ 0 → ∀ a, H a ∨ F a →
      a + 32 ≤ C + 32 * (req + 1) ∨ C + 32 * (req + 1) + 32 ≤ a)
    (hNold : wordSize (s.hdr C).size - req - 1 ≠ 0 →
      (registerAlloc (unregister s C bin) C (s.hdr C).prev (req + 1)).heads (binDown (wordSize (s.hdr C).size - req - 1))
        ≠ 0 →
      F ((registerAlloc (unregister s C bin) C (s.hdr C).prev (req + 1)).heads
        (binDown (wordSize (s.hdr C).size - req - 1))))
    (hFin : C + 32 * wordSize (s.hdr C).size < s.base + 1073741824 → H (C + 32 * wordSize (s.hdr C).size))
    {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hSTk : S0 + 152 ≤ sp ∧ sp ≤ S1)
    (hHFT : ∀ a, H a ∨ F a → a + 32 ≤ HT) (hHT : s.base + 32 * s.allocated ≤ HT) (hwr : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 41177 ω μ x tg ω' μ' x (96 * req + 460) ∧
      RepAt μ' (allocPost s bin req (wordSize (s.hdr C).size) (s.base + 1073741824))
        (fun a => H a ∨ (wordSize (s.hdr C).size - req - 1 ≠ 0 ∧ a = C + 32 * (req + 1)))
        (fun a => F a ∨ (wordSize (s.hdr C).size - req - 1 ≠ 0 ∧ a = C + 32 * (req + 1))) ∧
      ω'[7] = UInt64.ofNat (C + 32) ∧ ω'[0] = ω[0] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[1] = ω[1] ∧
      (∀ a, μ'.writable a = μ.writable a) ∧ (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ∀ a, OffHdrG (fun a => (H a ∨ F a) ∨ (wordSize (s.hdr C).size - req - 1 ≠ 0 ∧ a = C + 32 * (req + 1))) a →
        (a < C + 32 ∨ C + 32 + 32 * req ≤ a) → μ'.read a = μ.read a := by
  have hAC := hHF C (Or.inr hFC)
  have hCT := hHFT C (Or.inr hFC)
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
  have hbase : rdN μ 206520 8 = s.base := by have := hrep.base; unfold A0 at this; exact this
  have hpri : rdN μ 206832 8 = s.primary := by have := hrep.pri; unfold A0 at this; exact this
  obtain ⟨ω1, μ1, r1, q, b, hqb, hq, hb, a1, a10, a11, a5, a2, a6, a3, a8, a9, a4, a12, a7, st0, st5, st6, st10,
      st32, sf1, ww1⟩ := alloc_entry (p := p) (P := P) (R := R) x ω μ s sp req bin C (s.hdr C).size hbits h1 h7 h8 h9
    hsp hsp1 hbase (by omega) hpri hsec hm hbin hheads hsz (by omega) (by omega) hHTs hSTk ⟨by omega, by omega⟩ hwr
  rw [hwS] at a11
  have rep1 : RepAt μ1 s H F := hrep.congr_low (fun a ha => sf1 a (by omega) (Or.inl (by omega))) hHFl
  obtain ⟨ω2, μ2, r2, rep2, b1, b8, b0, m96, m48, m80, m72, m104, m88, m120, ww2, fr2, hk2, g2⟩ := alloc_mid (p := p)
    (P := P) (R := R) x ω1 μ1 s H F (sp - 152) req bin q b C S rep1 hcb hqb hq hb hFC hHC hHF hnx hb0 hbT hpv hS
    (by omega) hCend hal hend a1 a10 a11 a5 a2 a6 a3 a8 a9 (by rw [show sp - 152 + 120 = sp - 32 by omega]; exact st32)
    (by omega) (by omega) hHTs ⟨by omega, by omega⟩ hHFT (hwr.of_eq ww1)
  generalize hpvd : (s.hdr C).prev = pv at *
  generalize ht2 : unregister s C bin = t2 at *
  have e2b : t2.base = s.base := by rw [← ht2, unregister_base]
  have e2a : t2.allocated = s.allocated := by rw [← ht2, unregister_allocated]
  have hCa : (C - s.base) % 32 = 0 := hAC.2.1
  obtain ⟨ω3, μ3, r3, rep3, c3, c12, c8, c2, c1, c4, ww3, fr3, hk3⟩ := alloc_end1Z (p := p) (P := P) (R := R) x ω2 μ2 t2 H F
    (sp - 152) req C pv (S - req - 1) rep2 hHC (by rw [e2b]; exact hHF) (by rw [e2b]; exact hb0)
    (by rw [e2b]; exact hbT) (by rw [e2b]; exact hCa) (by rw [e2b]; omega) hpv (by omega) (by omega)
    (by rw [e2b]; omega) hNdis hNold b1 (by rw [e2b]; exact b8) b0
    (by rw [fget g2 4 (by decide) (by decide)]; exact a4) (by rw [fget g2 9 (by decide) (by decide)]; exact a9)
    (by rw [fget g2 7 (by decide) (by decide)]; exact a7) (by rw [e2b]; exact m96) m48 _ m80
    (by rw [e2b]; exact m72) m104 m88 m120 (by omega) (by omega) hHTs ⟨by omega, by omega⟩ hHFT
    (fun h0 => by have h' := hend; rw [if_neg h0] at h'; omega) ((hwr.of_eq ww1).of_eq ww2)
  generalize ht3 : register (registerAlloc t2 C pv (req + 1)) (C + 32 * (req + 1)) (req + 1) (S - req - 1) = rr at *
  have e3b : rr.1.base = s.base := by rw [← ht3, register_base, registerAlloc_base, e2b]
  have k112 : rdN μ3 (sp - 152 + 112) 8 = z := by
    rw [show rdN μ3 (sp - 152 + 112) 8 = rdN μ1 (sp - 152 + 112) 8 from rdN_frame fun j hj =>
      (fr3 _ (by omega) (by omega)).trans (fr2 _ (by omega) (by omega) (by omega)),
      show sp - 152 + 112 = sp - 40 by omega]
    unfold rdN; rw [st10, h10, Num.decodeLE_encodeLE, UInt64.toNat_ofNat_of_lt' hz, Nat.mod_eq_of_lt hz]
  have k144 : rdN μ3 (sp - 152 + 144) 8 = ret := by
    rw [show rdN μ3 (sp - 152 + 144) 8 = rdN μ1 (sp - 152 + 144) 8 from rdN_frame fun j hj =>
      (fr3 _ (by omega) (by omega)).trans (fr2 _ (by omega) (by omega) (by omega)),
      show sp - 152 + 144 = sp - 8 by omega]
    unfold rdN; rw [st0, h0, Num.decodeLE_encodeLE]
    have : ret < 18446744073709551616 := by omega
    rw [UInt64.toNat_ofNat_of_lt' this, Nat.mod_eq_of_lt this]
  have hC8 : (C + 32) % 8 = 0 := by omega
  have k120 : rdN μ3 (sp - 152 + 120) 8 = 204984 := by
    rw [← m120]; exact rdN_frame fun j hj => fr3 _ (by omega) (by omega)
  have hS32 : C + 32 * (req + 1) + 32 * (S - req - 1) = C + 32 * S := by omega
  obtain ⟨ω4, μ4, r4, rep4, d7, d0, d5, d6, d1, ww4, fr4, hk4⟩ := alloc_end2Z (p := p) (P := P) (R := R) x ω3 μ3 rr.1
    (fun a => H a ∨ (S - req - 1 ≠ 0 ∧ a = C + 32 * (req + 1)))
    (fun a => F a ∨ (S - req - 1 ≠ 0 ∧ a = C + 32 * (req + 1))) (sp - 152) (C + 32 * (req + 1)) (S - req - 1) rr.2
    (C + 32) req z ret tg rep3
    (fun a ha => by
      rw [e3b]
      rcases ha with (h | ⟨h0, rfl⟩) | (h | ⟨h0, rfl⟩)
      · exact hHF a (Or.inl h)
      · unfold Al; omega
      · exact hHF a (Or.inr h)
      · unfold Al; omega)
    (by rw [e3b]; exact hb0) (by rw [e3b]; exact hbT)
    (fun h => Or.inl (by rw [hS32]; exact hFin (by rw [e3b, hS32] at h; exact h)))
    (by rw [e3b, hS32]; exact hCend) (by omega) c1 c12 c8 c3 c2 c4 k120 hz k112 k144 hret hjt hbt
    (by rw [← ht3]; unfold register; split <;> simp <;> omega) hC8 (by omega) hreq (by omega)
    (fun a ha => by
      rcases ha with (h | ⟨h0, rfl⟩) | (h | ⟨h0, rfl⟩)
      · by_cases e : a = C
        · subst e; omega
        · have := hCdis a (Or.inl h) e; omega
      · omega
      · by_cases e : a = C
        · subst e; omega
        · have := hCdis a (Or.inr h) e; omega
      · omega)
    (by omega) (by omega) hHTs ⟨by omega, by omega⟩
    (fun a ha => by
      rcases ha with (h | ⟨h0, rfl⟩) | (h | ⟨h0, rfl⟩)
      · exact hHFT a (Or.inl h)
      · have h' := hend; rw [if_neg h0] at h'; omega
      · exact hHFT a (Or.inr h)
      · have h' := hend; rw [if_neg h0] at h'; omega)
    (by have h' := hend; split at h' <;> omega)
    (((hwr.of_eq ww1).of_eq ww2).of_eq ww3)
  have tr : ∀ a, sp - 152 + 128 ≤ a → a + 8 ≤ sp → rdN μ3 a 8 = rdN μ1 a 8 := fun a h h' =>
    rdN_frame fun j hj => (fr3 _ (by omega) (by omega)).trans (fr2 _ (by omega) (by omega) (by omega))
  refine ⟨ω4, μ4, (((r1.trans r2).trans r3).trans r4).mono (by omega), ?_, d7, ?_, ?_, ?_, ?_,
    fun a => (ww4 a).trans ((ww3 a).trans ((ww2 a).trans (ww1 a))),
    fun a h h' => ((fr4 a h (by omega)).trans ((fr3 a h (by omega)).trans (fr2 a h (by omega) (by omega)))).trans
      (sf1 a h (Or.inr h')),
    fun a ha hd => (hk4 a ⟨ha.1, ha.2.1, fun b hb => ha.2.2 b (by
      rcases hb with (h | h) | (h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h)⟩ hd).trans ((((HKeepG.of_low fun a h1 h2 _ => sf1 a (by omega) (Or.inl (by omega))).trans
      (hk2.mono fun b hb => Or.inl (Or.inl hb))).trans hk3) a ha)⟩
  · rw [allocPost_eq hcb (by omega) hCa, hpvd, ht2, ht3]
    rw [e3b] at rep4
    exact rep4
  · rw [d0, h0]
  · rw [d5, tr _ (by omega) (by omega), show sp - 152 + 136 = sp - 16 by omega]
    unfold rdN; rw [st5, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]
  · rw [d6, tr _ (by omega) (by omega), show sp - 152 + 128 = sp - 24 by omega]
    unfold rdN; rw [st6, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]
  · rw [d1, h1]; congr 1; omega

/-- **`alloc_refines_hdr` with the zero flag z**, to the caller's return target tg: the heap frame
    off the new block's data (which the tail may zero). `alloc_refines_hdr`:: as `alloc_refines`, and in the heap only the
    allocator's fields and the headers of chunks of the result `s'` change (`HKeepG`): every
    allocated chunk of `s`, still a chunk of `s'`, keeps its data. -/
theorem alloc_refines_hdrZ {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    {grow : Grow} {hb : Nat} (s s' : State) (sp req ptr : Nat) (hwf : WF s) (hrep : Rep μ s)
    (h : alloc grow hb 1 req s = some (ptr, s')) (hng : s'.allocated = s.allocated)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat 1)
    (h9 : ω[9] = UInt64.ofNat req) (z : Nat) (hz : z < 18446744073709551616) (h10 : ω[10] = UInt64.ofNat z)
    (ret tg : Nat) (h0 : ω[0] = UInt64.ofNat ret) (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = tg) (hbt : P.isBlockStart tg = true) (hreq : 1 ≤ req)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hal : s.allocated < 2147483648)
    (hfo : FirstOk s) {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hSTk : S0 + 152 ≤ sp ∧ sp ≤ S1)
    (hHT : s.base + 32 * s.allocated ≤ HT) (hw : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 41177 ω μ x tg ω' μ' x (96 * req + 460) ∧ Rep μ' s' ∧ WF s' ∧
      ω'[7] = UInt64.ofNat ptr ∧ ω'[0] = ω[0] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[1] = ω[1] ∧
      (∀ a, μ'.writable a = μ.writable a) ∧ (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      HKeepGD μ μ' (fun a => ∃ c ∈ chunks s', c.addr = a) ptr (ptr + 32 * req) := by
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
  obtain ⟨ω', μ', run, rep', e7, e0, e5, e6, e1, ww, stk, hk⟩ := alloc_implZ (p := p) (P := P) (R := R) x ω μ s H F sp req
    bin C hrep' hbits h1 h7 h8 h9 z hz h10 ret tg h0 hret hjt hbt hreq (by have := hwf.2.1; omega)
    (fun a ha hne => by
      obtain ⟨c, hc, rfl⟩ := unHF a ha
      have hcl := htiles.mem_lt c hc
      rcases List.mem_append.mp hc with h | h
      · have := hpa c h; omega
      · rcases List.mem_cons.mp h with h | h
        · subst h; exact absurd rfl hne
        · have := (hpp c h).1; first | omega | (rw [hSd]; omega)) hsp hsp1 hb0 hbT hm' hbin (by unfold binCount at hbc; omega) hC hFC hHC hHF
    hnx hpv (by rw [hSd]; exact hS) (by rw [hSd]; omega) hal (by rw [hSd]; exact hend)
    (by rw [hSd]; exact hNdis) (by rw [hSd]; exact hNold) (by rw [hSd]; exact hFin) hHTs hSTk hHFT hHT hw
  rw [hSd] at rep'
  refine ⟨ω', μ', run, ?_, hwf', e7, e0, e5, e6, e1, ww, stk, ?_⟩
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
  rw [show s.base + 32 * maxSize = s.base + 1073741824 by rw [maxSize_val]]
  rw [htop] at hcs'
  rw [hSd] at hk
  refine HKeepGD.mono hk fun b hb => Or.inl ?_
  rw [hcs']
  rcases hb with hb | ⟨hr, rfl⟩
  · obtain ⟨c, hc, rfl⟩ := unHF b hb
    rcases List.mem_append.mp hc with h | h
    · exact ⟨c, List.mem_append_left _ h, rfl⟩
    · rcases List.mem_cons.mp h with h | h
      · subst h; exact ⟨_, List.mem_append_right _ List.mem_cons_self, rfl⟩
      · exact ⟨c, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _ h)), rfl⟩
  · refine ⟨⟨C + 32 * (req + 1), S - req - 1, false⟩,
      List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ ?_)), rfl⟩
    unfold remChunk; rw [if_neg hr]; exact List.mem_singleton_self _

end Services.Bootstrap.Alloc
