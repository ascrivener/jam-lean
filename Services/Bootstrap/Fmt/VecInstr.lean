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


/-- **`<Vec<Instruction> as Debug>::fmt`** (29675, plain options) as an argument: the `Vec`
    (cap, ptr, len) at v (where `ValAt` puts it), its len elements of 232 octets at ptr, each formatted
    by 26990 as a `RefOk` with stack depth Ze. At most 2002 · len + 2 octets. It needs Ze + 168 octets
    of stack below the caller (Z) and the vtable's `fmt` word (75808: 1264). -/
theorem vec_instr_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 Z Ze : Nat) (hZ : Ze + 168 ≤ Z) (hZe : 600 ≤ Ze) (HA : AllocOk p R env pb S0 S1)
    (HR : ReallocOk p R env pb S0 S1) (μA : Memory) (sA : State) (spA v ptr len : Nat) (hS : S0 ≤ spA)
    (hv : ValAt μA sA spA S1 v 24) (rp : rdN μA (v + 8) 8 = ptr) (rl : rdN μA (v + 16) 8 = len)
    (hel : ∀ j, j < len → RefOk p P R env pb S0 S1 Ze μA sA spA 26990 (ptr + 232 * j) 2000 2147483648)
    (hpl : ptr + 232 * len < 4294967296) (hrvt : rdN μA 75808 8 = 1264) :
    ArgOk p P R env pb S0 S1 Z μA sA spA 29675 v (2002 * len + 2) (4294967296 + 2147510000 * len + 10000) := by
  intro ω μ x s sp F W cap len0 ret t v5 v6 H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hWA hF hn
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  obtain ⟨hrvec, hlvec⟩ := hv.readable (by decide) H hS hspA K
  have rp' : rdN μ (v + 8) 8 = ptr := by rw [hv.rdN H K (by omega)]; exact rp
  have rl' : rdN μ (v + 16) 8 = len := by rw [hv.rdN H K (by omega)]; exact rl
  have hptr : ptr < 18446744073709551616 := by omega
  have hlen : 232 * len < 18446744073709551616 := by omega
  -- 26807 … 26830
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, s56, s48, s40, fr1, rd1, wr1⟩ := vi_a (p := p) (P := P)
    (R := R) x ω μ sp v ptr len ret v5 v6 ⟨by omega, by omega⟩ h0 h1 h5 h6 h7
    ⟨by omega, hv5, hv6, by omega⟩ (by omega) rp' rl'
    (fun a h1 h2 => hrvec a (by omega) h2) (fun a h1 h2 => hst a (by omega) (by omega))
  have k1 : ∀ a, a < 4294967296 → (a < sp - 64 ∨ sp ≤ a) → μ1.read a = μ.read a := fr1
  have H1 : HeapCtx env pb S0 S1 μ1 s := ctx_hi H (fun a ha => k1 a (by omega) (Or.inl (by omega))) wr1
  have hf1 : Fmtr sA s μ1 F W cap len0 := hf.congr (fun j hj => k1 _ (by omega) (Or.inr (by omega)))
    (fun j hj => k1 _ (by omega) (Or.inr (by omega))) (fun a h1 h2 => ⟨k1 a (by omega) (Or.inl (by omega)), rd1 a⟩)
  have K1 : Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) sA μ μ1 s :=
    Keeps.of_frame (Z := fun a => sp - 64 ≤ a ∧ a < sp) hf.str.base
      (fun a ha hz => k1 a ha (by omega)) rd1 wr1 (fun a hz => hst a (by omega) (by omega))
      (fun a hz h => by omega) (fun a hz hg => by unfold Glob at hg; omega)
      (fun c hc hu a ha => by
        have := chunk_bounds H.wf (hf.str.base c hc hu)
        have := H.hbT
        unfold InData at ha; omega)
  have KA1 : Keeps pb spA (fun _ => False) sA μA μ1 s := by
    have := K.trans' (K1.lift (sp' := spA) hspA (fun a h ha => by omega))
    rwa [Nat.max_self] at this
  -- the list: "["
  rcases debug_list_new (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω1 μ1 sA s (sp - 64) F W (sp - 64 + 16)
      cap len0 1384 29702 len ptr H1 hba hf1 a0 a1 a5 a6 a7 (a8.trans h8) ⟨by omega, hptr⟩ (by decide) jte_691
      bs_29702 ⟨by omega, by omega, by omega⟩ ⟨by omega, hW.2⟩ ⟨by omega, hF.2.1, hF.2.2⟩
      ⟨by omega, by omega, Or.inl (by omega), Or.inl (by omega)⟩ (by omega) with
    ⟨ω2, μ2, x2, s2, cap2, run2, H2, hb2, hf2, hc1, hc2, hd2, K2, b0, b1, b5, b6⟩ | hx
  rotate_left
  · exact Or.inr ((Exhausts.pre run1 hx).mono (by omega))
  have hst2 : ∀ a, S0 ≤ a → a < S1 → μ2.writable a = true := H2.st
  have K2' : Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) sA μ1 μ2 s2 :=
    K2.lift (by omega) (fun a h ha => by unfold dlE at h; omega)
  have KA2 : Keeps pb spA (fun _ => False) sA μA μ2 s2 := by
    have := KA1.trans' (K2'.lift (sp' := spA) hspA (fun a h ha => by omega))
    rwa [Nat.max_self] at this
  have kT2 : ∀ a, sp - 64 + 40 ≤ a → a < sp → μ2.read a = μ1.read a := fun a h1 h2 =>
    K2.hi a (by omega) (by omega) (by unfold dlE; omega)
  -- the elements: from 29702 to 29752
  have mid : (∃ ω3 μ3 x3 s3 cap3 n3, n3 ≤ 2002 * len ∧
      FreeStepsH p R 29702 ω2 μ2 x2 29752 ω3 μ3 x3 (7 * n3 + 2 * (cap3 - cap2) + 2147490000 * len + 5) ∧
      HeapCtx env pb S0 S1 μ3 s3 ∧ s3.base = s2.base ∧ Fmtr sA s3 μ3 F W cap3 (len0 + 1 + n3) ∧ cap2 ≤ cap3 ∧
      cap3 ≤ max cap2 (max 8 (2 * (len0 + 1 + n3))) ∧ (∃ h, DL μ3 (sp - 64 + 16) F h) ∧
      Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) sA μ2 μ3 s3 ∧ ω3[1] = UInt64.ofNat (sp - 64) ∧
      (∀ a, sp - 64 + 40 ≤ a → a < sp → μ3.read a = μ2.read a)) ∨
      Exhausts p R pb 29702 ω2 μ2 x2 (4294967296 + 2147510000 * len - 2 * cap2 + 5) := by
    by_cases hl0 : len = 0
    · subst hl0
      have run3 := vi_b0 (p := p) (P := P) (R := R) x2 ω2 μ2 b5
      exact Or.inl ⟨ω2, μ2, x2, s2, cap2, 0, by omega, run3.mono (by omega), H2, rfl, hf2, Nat.le_refl _,
        by have := hf2.str.le; have := hf2.str.lt; omega, ⟨0, hd2⟩, (Keeps.refl _ _ _ _ _).rebase hf2.str.base, b1, fun _ _ _ => rfl⟩
    · obtain ⟨ω3, μ3, run3, c1, c5, c6, rT, fr3, rd3, wr3⟩ := vi_b (p := p) (P := P) (R := R) x2 ω2 μ2 (sp - 64) len
        ⟨by omega, by omega⟩ b1 b5 ⟨by omega, hlen⟩ (fun a h1 h2 => hst2 a (by omega) (by omega))
      have k3 : ∀ a, a < 4294967296 → (a < sp - 64 ∨ sp - 64 + 8 ≤ a) → μ3.read a = μ2.read a := fr3
      have H3 : HeapCtx env pb S0 S1 μ3 s2 := ctx_hi H2 (fun a ha => k3 a (by omega) (Or.inl (by omega))) wr3
      have K3 : Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) sA μ2 μ3 s2 :=
        Keeps.of_frame (Z := fun a => sp - 64 ≤ a ∧ a < sp - 64 + 8) hf2.str.base
          (fun a ha hz => k3 a ha (by omega)) rd3 wr3 (fun a hz => hst2 a (by omega) (by omega))
          (fun a hz h => by omega) (fun a hz hg => by unfold Glob at hg; omega)
          (fun c hc hu a ha => by
            have := chunk_bounds H2.wf (hf2.str.base c hc hu)
            have := H2.hbT
            unfold InData at ha; omega)
      have hf3 : Fmtr sA s2 μ3 F W cap2 (len0 + 1) := hf2.congr (fun j hj => k3 _ (by omega) (Or.inr (by omega)))
        (fun j hj => k3 _ (by omega) (Or.inr (by omega)))
        (fun a h1 h2 => ⟨k3 a (by omega) (Or.inl (by omega)), rd3 a⟩)
      have KA3 : Keeps pb spA (fun _ => False) sA μA μ3 s2 := by
        have := KA2.trans' (K3.lift (sp' := spA) hspA (fun a h ha => by omega))
        rwa [Nat.max_self] at this
      have hd3 : DL μ3 (sp - 64 + 16) F 0 :=
        ⟨by rw [rdN_frame (fun j hj => k3 _ (by omega) (Or.inr (by omega)))]; exact hd2.fm,
          by rw [rdN_frame (fun j hj => k3 _ (by omega) (Or.inr (by omega)))]; exact hd2.ok,
          by rw [rdN_frame (fun j hj => k3 _ (by omega) (Or.inr (by omega)))]; exact hd2.has⟩
      have rvt3 : rdN μ3 75808 8 = 1264 := by
        rw [rdN_frame (fun j hj => KA3.ro _ (by omega) (Or.inl (by unfold pageSize; omega))
          (by rw [← (KA3.access _ (Or.inl (by unfold pageSize; omega))).2]; exact H3.ro _ (by omega)))]
        exact hrvt
      rcases vi_loop (p := p) (P := P) (R := R) env pb S0 S1 HA HR μA sA spA (sp - 64) F W ret v5 v6 Ze hZe hS
          ⟨by omega, by omega, by omega, by omega⟩ ⟨by omega, hW.2, hWA⟩ ⟨by omega, hF.2.1, hF.2.2⟩ len (by omega)
          ptr 0 ω3 μ3 x2 s2 cap2 (len0 + 1) H3 (hb2 ▸ hba) hf3 KA3 hd3 (Or.inl rfl) (c1.trans b1) (c6.trans b6)
          c5 rT rvt3 hel hpl (by omega) with
        ⟨ω4, μ4, x4, s4, cap4, n4, hn4, run4, H4, hb4, hf4, hc3, hc4, hd4, K4, d1⟩ | hx
      · refine Or.inl ⟨ω4, μ4, x4, s4, cap4, n4, hn4, (run3.trans run4).mono (by omega), H4, hb4, hf4, hc3, hc4,
          ⟨1, hd4⟩, ?_, d1, fun a h1 h2 => ?_⟩
        · have := K3.trans' (K4.lift (sp' := sp) (by omega) (fun a h ha => by unfold vdE at h; omega))
          rwa [Nat.max_self] at this
        · rw [K4.hi a (by omega) (by omega) (by unfold vdE; omega), k3 a (by omega) (Or.inr (by omega))]
      · exact Or.inr ((Exhausts.pre run3 hx).mono (by omega))
  rcases mid with ⟨ω3, μ3, x3, s3, cap3, n3, hn3, run3, H3, hb3, hf3, hc3, hc4, ⟨hh, hd3⟩, K3, d1, kT3⟩ | hx
  rotate_left
  · refine Or.inr ((Exhausts.pre (run1.trans run2) hx).mono ?_)
    have : cap2 ≤ max cap (max 8 (2 * (len0 + 1))) := hc2
    have := hf2.str.lt
    omega
  obtain ⟨ω4, run4, e0, e1, e5, e6, e7⟩ := vi_e (p := p) (P := P) (R := R) x3 ω3 μ3 (sp - 64) ⟨by omega, by omega⟩ d1
  rcases debug_finish (p := p) (P := P) (R := R) env pb S0 S1 HA HR x3 ω4 μ3 sA s3 (sp - 64) F W (sp - 64 + 16)
      cap3 (len0 + 1 + n3) 1388 29762 (ω4[5].toNat) hh H3 (hb3 ▸ hb2 ▸ hba) hf3 hd3 e0 (e1.trans d1) (by simp) e7
      (UInt64.toNat_lt _) (by decide) jte_693 bs_29762 ⟨by omega, by omega, by omega⟩ ⟨by omega, hW.2⟩
      ⟨by omega, hF.2.1, hF.2.2⟩ ⟨by omega, by omega, Or.inl (by omega), Or.inl (by omega)⟩ (by omega) with
    ⟨ω5, μ5, x5, s5, cap5, run5, H5, hb5, hf5, hc5, hc6, K5, f0, f1, f5, f6, f7⟩ | hx
  rotate_left
  · refine Or.inr ((Exhausts.pre (((run1.trans run2).trans run3).trans run4) hx).mono ?_)
    have : cap2 ≤ max cap (max 8 (2 * (len0 + 1))) := hc2
    have := hf3.str.lt
    omega
  have hst5 : ∀ a, S0 ≤ a → a < S1 → μ5.writable a = true := H5.st
  have kk : ∀ o, 40 ≤ o → o + 8 ≤ 64 → rdN μ5 (sp - 64 + o) 8 = rdN μ1 (sp - 64 + o) 8 := fun o h1 h2 =>
    rdN_frame (fun j hj => by
      rw [K5.hi _ (by omega) (by omega) (by unfold dlE; omega), kT3 _ (by omega) (by omega),
        kT2 _ (by omega) (by omega)])
  obtain ⟨ω6, run6, g0, g1, g5, g6, g7⟩ := vi_r (p := p) (P := P) (R := R) x5 ω5 μ5 (sp - 64) ret t v5 v6
    ⟨by omega, by omega⟩ f1 ((kk 56 (by omega) (by omega)).trans s56) ((kk 48 (by omega) (by omega)).trans s48)
    ((kk 40 (by omega) (by omega)).trans s40) hret hjt hbt
    (fun a h1 h2 => Memory.readable_of_writable (hst5 a (by omega) (by omega)))
  have K := ((K1.trans' K2').trans' K3).trans'
    (K5.lift (sp' := sp) (by omega) (fun a h ha => by unfold dlE at h; omega))
  simp only [Nat.max_self] at K
  refine Or.inl ⟨ω6, μ5, x5, s5, cap5, 1 + n3 + 1, by omega,
    (((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).mono ?_, H5, hb5.trans (hb3.trans hb2),
    by rwa [show len0 + (1 + n3 + 1) = len0 + 1 + n3 + 1 by omega], by omega, ?_, K, g0,
    by rw [g1]; congr 1; omega, g5, g6, g7.trans f7⟩
  · omega
  · rw [show len0 + (1 + n3 + 1) = len0 + 1 + n3 + 1 by omega]
    have : cap2 ≤ max cap (max 8 (2 * (len0 + 1))) := hc2
    omega


end Services.Bootstrap.Fmt
