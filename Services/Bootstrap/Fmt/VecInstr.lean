import Services.Bootstrap.Fmt.VecInstrSteps
import Services.Bootstrap.Fmt.VecDebug

/-!
# `<Vec<Instruction> as fmt::Debug>::fmt` (29675), frame-only, plain options

`vi_loop`: the element loop (29717 … 29749), one `DebugList::entry` per 232-octet element, each
element formatted by `<&Instruction as Debug>` (26990) as a `RefOk` (at most 2000 octets, constant
2³¹: `RefOk.mono` lifts the arms' `instr<t>_ok`). `vec_instr_ok`: the whole function as an `ArgOk`
for the `Vec` at v. The text is not stated.
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- A `RefOk` holds for a larger M and C. -/
theorem RefOk.mono {p : ByteArray} {P : Program} {env : RefineHost.Env} {pb S0 S1 Z : Nat} {μA : Memory}
    {sA : State} {spA e a M C M' C' : Nat} (h : RefOk p P R env pb S0 S1 Z μA sA spA e a M C) (hM : M ≤ M')
    (hC : C ≤ C') : RefOk p P R env pb S0 S1 Z μA sA spA e a M' C' := by
  intro ω μ x s sp F W cap len ret t v5 v6 v H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hWA hF hn
    hv ra
  rcases h ω μ x s sp F W cap len ret t v5 v6 v H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hWA hF
      (by omega) hv ra with ⟨ω', μ', x', s', cap', n, hn', run, rest⟩ | hx
  · exact Or.inl ⟨ω', μ', x', s', cap', n, by omega, run.mono (by omega), rest⟩
  · exact Or.inr (hx.mono (by omega))

theorem vi_loop {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA T F W r0 v5 v6 Ze : Nat) (hZe : 600 ≤ Ze) (hS : S0 ≤ spA)
    (hT : S0 + Ze + 104 ≤ T ∧ T % 8 = 0 ∧ 2147483648 + Ze + 104 ≤ T ∧ T + 64 ≤ spA)
    (hW : T + 64 ≤ W ∧ W + 24 ≤ S1 ∧ W + 24 ≤ spA)
    (hF : T + 64 ≤ F ∧ F + 24 ≤ S1 ∧ (F + 24 ≤ W ∨ W + 24 ≤ F)) :
    ∀ m, 0 < m → ∀ (q h : Nat) (ω : Regs) (μ : Memory) (x : X) (s : State) (cap len : Nat),
    HeapCtx env pb S0 S1 μ s → s.base % 8 = 0 → Fmtr sA s μ F W cap len →
    Keeps pb spA (fun _ => False) sA μA μ s → DL μ (T + 16) F h → (h = 0 ∨ h = 1) →
    ω[1] = UInt64.ofNat T → ω[6] = UInt64.ofNat q → ω[5] = UInt64.ofNat (232 * m) →
    rdN μ T 8 = 75784 → rdN μ 75808 8 = 1264 →
    (∀ j, j < m → RefOk p P R env pb S0 S1 Ze μA sA spA 26990 (q + 232 * j) 2000 2147483648) →
    q + 232 * m < 4294967296 → len + 2002 * m < 134217728 →
    (∃ ω' μ' x' s' cap' n, n ≤ 2002 * m ∧
      FreeStepsH p R 29717 ω μ x 29752 ω' μ' x' (7 * n + 2 * (cap' - cap) + 2147490000 * m) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Fmtr sA s' μ' F W cap' (len + n) ∧ cap ≤ cap' ∧
      cap' ≤ max cap (max 8 (2 * (len + n))) ∧ DL μ' (T + 16) F 1 ∧
      Keeps pb T (vdE T W) sA μ μ' s' ∧ ω'[1] = UInt64.ofNat T) ∨
    Exhausts p R pb 29717 ω μ x (4294967296 + 2147510000 * m - 2 * cap) := by
  intro m
  induction m with
  | zero => intro h; exact absurd h (Nat.lt_irrefl 0)
  | succ k ih =>
  intro _ q h ω μ x s cap len H hba hf KA hd hh h1 h6 h5 rT rvt hel hqm hn
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  have hcap := hf.str.lt
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, s8, s32, fr1, rd1, wr1⟩ := vi_l (p := p) (P := P) (R := R)
    x ω μ T q ⟨by omega, by omega⟩ h1 h6 (by omega) rT (fun a h1 h2 => hst a (by omega) (by omega))
  have k1 : ∀ a, a < 4294967296 → ¬ (T + 8 ≤ a ∧ a < T + 40) → μ1.read a = μ.read a := fun a h1 h2 =>
    fr1 a h1 (by omega) (by omega)
  have H1 : HeapCtx env pb S0 S1 μ1 s := ctx_hi H (fun a ha => k1 a (by omega) (by omega)) wr1
  have K1 : Keeps pb T (vdE T W) sA μ μ1 s :=
    Keeps.of_frame (Z := fun a => T + 8 ≤ a ∧ a < T + 40) hf.str.base
      (fun a ha hz => k1 a ha hz) rd1 wr1 (fun a hz => hst a (by omega) (by omega))
      (fun a hz h => Or.inr hz) (fun a hz hg => by unfold Glob at hg; omega)
      (fun c hc hu a ha => by
        have := chunk_bounds H.wf (hf.str.base c hc hu)
        have := H.hbT
        unfold InData at ha; omega)
  have hf1 : Fmtr sA s μ1 F W cap len := hf.congr (fun j hj => k1 _ (by omega) (by omega))
    (fun j hj => k1 _ (by omega) (by omega)) (fun a h1 h2 => ⟨k1 a (by omega) (by omega), rd1 a⟩)
  have KA1 : Keeps pb spA (fun _ => False) sA μA μ1 s := by
    have := KA.trans' (K1.lift (sp' := spA) (by omega) (fun a h ha => by unfold vdE at h; omega))
    rwa [Nat.max_self] at this
  have hd1 : DL μ1 (T + 16) F h :=
    ⟨by rw [rdN_frame (fun j hj => fr1 _ (by omega) (by omega) (by omega))]; exact hd.fm,
      by rw [rdN_frame (fun j hj => fr1 _ (by omega) (by omega) (by omega))]; exact hd.ok,
      by rw [rdN_frame (fun j hj => fr1 _ (by omega) (by omega) (by omega))]; exact hd.has⟩
  have rvt1 : rdN μ1 (75784 + 24) 8 = 1264 := by
    rw [rdN_frame (fun j hj => k1 _ (by omega) (by omega))]; exact rvt
  rcases debug_entry (p := p) (P := P) (R := R) env pb S0 S1 Ze hZe HA HR μA sA spA 26990 q 2000 2147483648 1264
      (by simpa using hel 0 (by omega))
      x ω1 μ1 s T F W (T + 16) (T + 32) 75784 cap len 1386 29742 (232 * (k + 1)) q h H1 hba hf1 KA1 hd1 hh
      a0 (a1.trans h1) (a5.trans h5) (a6.trans h6) a7 a8 a9 ⟨by omega, by omega⟩ ⟨by decide, by decide⟩ rvt1
      (by decide) jte_631 bs_26990 s32 (by decide) jte_692 bs_29742 ⟨by omega, hT.2.1, by omega⟩
      ⟨by omega, by omega, by omega⟩ ⟨by omega, hW.2.1⟩ ⟨by omega, hF.2.1, hF.2.2⟩
      ⟨by omega, by omega, Or.inl (by omega), Or.inl (by omega)⟩ ⟨by omega, by omega, Or.inl (by omega)⟩
      (by omega) with
    ⟨ω2, μ2, x2, s2, cap2, n2, hn2, run2, H2, hb2, hf2, hc1, hc2, hd2, K2, b0, b1, b5, b6⟩ | hx
  · have K2' : Keeps pb T (vdE T W) sA μ1 μ2 s2 :=
      K2.mono (Nat.le_refl _) (fun a h => by unfold dlE at h; unfold vdE; omega)
    have K12 := K1.trans' K2'
    rw [Nat.max_self] at K12
    have hst2 : ∀ a, S0 ≤ a → a < S1 → μ2.writable a = true := H2.st
    have s8' : rdN μ2 (T + 8) 8 = q + 232 := by
      rw [rdN_frame (fun j hj => K2.hi _ (by omega) (by omega) (by unfold dlE; omega))]; exact s8
    obtain ⟨ω3, run3, c1, c5, c6⟩ := vi_n (p := p) (P := P) (R := R) x2 ω2 μ2 T (232 * (k + 1)) (q + 232)
      ⟨by omega, by omega⟩ b1 b5 ⟨by omega, by omega⟩ s8'
      (fun a h1 h2 => Memory.readable_of_writable (hst2 a (by omega) (by omega)))
    by_cases hk : k = 0
    · subst hk
      rw [if_pos (by omega)] at run3
      refine Or.inl ⟨ω3, μ2, x2, s2, cap2, n2, by omega, ((run1.trans run2).trans run3).mono (by omega), H2, hb2,
        hf2, hc1, hc2, hd2, K12, c1.trans b1⟩
    · rw [if_neg (by omega)] at run3
      have rT2 : rdN μ2 T 8 = 75784 := by
        rw [show T = T + 0 by rfl, rdN_frame (fun j hj => K12.hi _ (by omega) (by omega) (by unfold vdE; omega))]
        exact rT
      have rvt2 : rdN μ2 75808 8 = 1264 := by
        rw [rdN_frame (fun j hj => K12.ro _ (by omega) (Or.inl (by unfold pageSize; omega)) (H.ro _ (by omega)))]
        exact rvt
      have KA2 : Keeps pb spA (fun _ => False) sA μA μ2 s2 := by
        have := KA.trans' (K12.lift (sp' := spA) (by omega) (fun a h ha => by unfold vdE at h; omega))
        rwa [Nat.max_self] at this
      rcases ih (by omega) (q + 232) 1 ω3 μ2 x2 s2 cap2 (len + n2) H2 (hb2 ▸ hba) hf2 KA2 hd2 (Or.inr rfl)
          (c1.trans b1) c6 (by rw [c5]; congr 1) rT2 rvt2
          (fun j hj => by rw [show q + 232 + 232 * j = q + 232 * (j + 1) by omega]; exact hel (j + 1) (by omega))
          (by omega) (by omega) with
        ⟨ω4, μ4, x4, s4, cap4, n4, hn4, run4, H4, hb4, hf4, hc3, hc4, hd4, K4, d1⟩ | hx
      · have K := K12.trans' K4
        rw [Nat.max_self] at K
        refine Or.inl ⟨ω4, μ4, x4, s4, cap4, n2 + n4, by omega,
          (((run1.trans run2).trans run3).trans run4).mono (by omega), H4, hb4.trans hb2,
          by rwa [show len + (n2 + n4) = len + n2 + n4 by omega], by omega, ?_, hd4, K, d1⟩
        rw [show len + (n2 + n4) = len + n2 + n4 by omega]; omega
      · refine Or.inr ((Exhausts.pre ((run1.trans run2).trans run3) hx).mono ?_)
        have : cap2 ≤ max cap (max 8 (2 * (len + n2))) := hc2
        omega
  · exact Or.inr ((Exhausts.pre run1 hx).mono (by omega))


end Services.Bootstrap.Fmt
