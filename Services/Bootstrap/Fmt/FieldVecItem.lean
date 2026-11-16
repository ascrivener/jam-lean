import Services.Bootstrap.Fmt.FieldVecItemSteps
import Services.Bootstrap.Fmt.FieldStruct1
import Services.Bootstrap.Fmt.VecInstr

/-!
# `<&Vec<Item> as fmt::Debug>::fmt` (26504), step 8

Generated from `FieldVecVec.lean` (26397, the same template) for 32-octet elements formatted by
36917 (`ref_item_36917_ok`). `vw_loop`, `ref_vecitem_core`, `ref_vecitem_26504_ok`. The field of
`Output` (37067); the text is the binary's own (GP v0.8.0 does not specify Debug output).
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

theorem vw_loop {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA T F W r0 v5 v6 Ze Me Ce : Nat) (hCe : 1073741824 ≤ Ce) (hZe : 600 ≤ Ze) (hS : S0 ≤ spA)
    (hT : S0 + Ze + 104 ≤ T ∧ T % 8 = 0 ∧ 2147483648 + Ze + 104 ≤ T ∧ T + 64 ≤ spA)
    (hW : T + 64 ≤ W ∧ W + 24 ≤ S1 ∧ W + 24 ≤ spA)
    (hF : T + 64 ≤ F ∧ F + 24 ≤ S1 ∧ (F + 24 ≤ W ∨ W + 24 ≤ F)) :
    ∀ m, 0 < m → ∀ (q h : Nat) (ω : Regs) (μ : Memory) (x : X) (s : State) (cap len : Nat),
    HeapCtx env pb S0 S1 μ s → s.base % 8 = 0 → Fmtr sA s μ F W cap len →
    Keeps pb spA (fun _ => False) sA μA μ s → DL μ (T + 16) F h → (h = 0 ∨ h = 1) →
    ω[1] = UInt64.ofNat T → ω[6] = UInt64.ofNat q → ω[5] = UInt64.ofNat (32 * m) →
    rdN μ T 8 = 75816 → rdN μ 75840 8 = 1746 →
    (∀ j, j < m → RefOk p P R env pb S0 S1 Ze μA sA spA 36917 (q + 32 * j) Me Ce) →
    q + 32 * m < 4294967296 → len + (Me + 2) * m < 134217728 →
    (∃ ω' μ' x' s' cap' n, n ≤ (Me + 2) * m ∧
      FreeStepsH p R 26548 ω μ x 26581 ω' μ' x' (7 * n + 2 * (cap' - cap) + (Ce + 6352) * m) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Fmtr sA s' μ' F W cap' (len + n) ∧ cap ≤ cap' ∧
      cap' ≤ max cap (max 8 (2 * (len + n))) ∧ DL μ' (T + 16) F 1 ∧
      Keeps pb T (vdE T W) sA μ μ' s' ∧ ω'[1] = UInt64.ofNat T) ∨
    Exhausts p R pb 26548 ω μ x (2147483648 + Ce + (Ce + 7 * Me + 26352) * m - 2 * cap) := by
  intro m
  induction m with
  | zero => intro h; exact absurd h (Nat.lt_irrefl 0)
  | succ k ih =>
  intro _ q h ω μ x s cap len H hba hf KA hd hh h1 h6 h5 rT rvt hel hqm hn
  have em1 : (Me + 2) * (k + 1) = (Me + 2) * k + (Me + 2) := Nat.mul_succ _ _
  have em2 : (Ce + 6352) * (k + 1) = (Ce + 6352) * k + (Ce + 6352) := Nat.mul_succ _ _
  have em3 : (Ce + 7 * Me + 26352) * (k + 1) = (Ce + 7 * Me + 26352) * k + (Ce + 7 * Me + 26352) := Nat.mul_succ _ _
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  have hcap := hf.str.lt
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, s8, s32, fr1, rd1, wr1⟩ := vw_l (p := p) (P := P) (R := R)
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
  have rvt1 : rdN μ1 (75816 + 24) 8 = 1746 := by
    rw [rdN_frame (fun j hj => k1 _ (by omega) (by omega))]; exact rvt
  rcases debug_entry (p := p) (P := P) (R := R) env pb S0 S1 Ze hZe HA HR μA sA spA 36917 q Me Ce 1746
      (by simpa using hel 0 (by omega))
      x ω1 μ1 s T F W (T + 16) (T + 32) 75816 cap len 1230 26572 (32 * (k + 1)) q h H1 hba hf1 KA1 hd1 hh
      a0 (a1.trans h1) (a5.trans h5) (a6.trans h6) a7 a8 a9 ⟨by omega, by omega⟩ ⟨by decide, by decide⟩ rvt1
      (by decide) jte_872 bs_36917 s32 (by decide) jte_614 bs_26572 ⟨by omega, hT.2.1, by omega⟩
      ⟨by omega, by omega, by omega⟩ ⟨by omega, hW.2.1⟩ ⟨by omega, hF.2.1, hF.2.2⟩
      ⟨by omega, by omega, Or.inl (by omega), Or.inl (by omega)⟩ ⟨by omega, by omega, Or.inl (by omega)⟩
      (by omega) with
    ⟨ω2, μ2, x2, s2, cap2, n2, hn2, run2, H2, hb2, hf2, hc1, hc2, hd2, K2, b0, b1, b5, b6⟩ | hx
  · have K2' : Keeps pb T (vdE T W) sA μ1 μ2 s2 :=
      K2.mono (Nat.le_refl _) (fun a h => by unfold dlE at h; unfold vdE; omega)
    have K12 := K1.trans' K2'
    rw [Nat.max_self] at K12
    have hst2 : ∀ a, S0 ≤ a → a < S1 → μ2.writable a = true := H2.st
    have s8' : rdN μ2 (T + 8) 8 = q + 32 := by
      rw [rdN_frame (fun j hj => K2.hi _ (by omega) (by omega) (by unfold dlE; omega))]; exact s8
    obtain ⟨ω3, run3, c1, c5, c6⟩ := vw_n (p := p) (P := P) (R := R) x2 ω2 μ2 T (32 * (k + 1)) (q + 32)
      ⟨by omega, by omega⟩ b1 b5 ⟨by omega, by omega⟩ s8'
      (fun a h1 h2 => Memory.readable_of_writable (hst2 a (by omega) (by omega)))
    by_cases hk : k = 0
    · subst hk
      rw [if_pos (by omega)] at run3
      refine Or.inl ⟨ω3, μ2, x2, s2, cap2, n2, by omega, ((run1.trans run2).trans run3).mono (by omega), H2, hb2,
        hf2, hc1, hc2, hd2, K12, c1.trans b1⟩
    · rw [if_neg (by omega)] at run3
      have rT2 : rdN μ2 T 8 = 75816 := by
        rw [show T = T + 0 by rfl, rdN_frame (fun j hj => K12.hi _ (by omega) (by omega) (by unfold vdE; omega))]
        exact rT
      have rvt2 : rdN μ2 75840 8 = 1746 := by
        rw [rdN_frame (fun j hj => K12.ro _ (by omega) (Or.inl (by unfold pageSize; omega)) (H.ro _ (by omega)))]
        exact rvt
      have KA2 : Keeps pb spA (fun _ => False) sA μA μ2 s2 := by
        have := KA.trans' (K12.lift (sp' := spA) (by omega) (fun a h ha => by unfold vdE at h; omega))
        rwa [Nat.max_self] at this
      rcases ih (by omega) (q + 32) 1 ω3 μ2 x2 s2 cap2 (len + n2) H2 (hb2 ▸ hba) hf2 KA2 hd2 (Or.inr rfl)
          (c1.trans b1) c6 (by rw [c5]; congr 1) rT2 rvt2
          (fun j hj => by rw [show q + 32 + 32 * j = q + 32 * (j + 1) by omega]; exact hel (j + 1) (by omega))
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



/-- **`<&Vec<T> as Debug>::fmt`** at 26504 (plain options) as a field (`RefOk`): the slot holds the
    address a of a `Vec` (cap, ptr, len) where `ValAt` puts it, whose len elements of 32 octets at ptr
    are each formatted by 36917 as a `RefOk` with stack depth Ze, at most Me octets and constant Ce.
    At most (Me + 2) · len + 2 octets. It needs Ze + 168 octets of stack below the caller (Z) and the
    vtable's `fmt` word (75840: 1746). -/
theorem ref_vecitem_core {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 Z Ze Me Ce : Nat) (hCe : 1073741824 ≤ Ce) (hZ : Ze + 168 ≤ Z) (hZe : 600 ≤ Ze) (HA : AllocOk p R env pb S0 S1)
    (HR : ReallocOk p R env pb S0 S1) (μA : Memory) (sA : State) (spA a ptr len : Nat) (hS : S0 ≤ spA)
    (hv : ValAt μA sA spA S1 a 24) (rp : rdN μA (a + 8) 8 = ptr) (rl : rdN μA (a + 16) 8 = len)
    (hel : ∀ j, j < len → RefOk p P R env pb S0 S1 Ze μA sA spA 36917 (ptr + 32 * j) Me Ce)
    (hpl : ptr + 32 * len < 4294967296) (hrvt : rdN μA 75840 8 = 1746) :
    RefOk p P R env pb S0 S1 Z μA sA spA 26504 a ((Me + 2) * len + 2)
      (2147483648 + Ce + (Ce + 7 * Me + 26352) * len + 10000) := by
  intro ω μ x s sp F W cap len0 ret t v5 v6 q H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hWA hF hn
    hq rq
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  obtain ⟨hrvec, hlvec⟩ := hv.readable (by decide) H hS hspA K
  have rp' : rdN μ (a + 8) 8 = ptr := by rw [hv.rdN H K (by omega)]; exact rp
  have rl' : rdN μ (a + 16) 8 = len := by rw [hv.rdN H K (by omega)]; exact rl
  have hptr : ptr < 18446744073709551616 := by omega
  have hlen : 32 * len < 18446744073709551616 := by omega
  have dX : (Ce + 7 * Me + 26352) * len = (Ce + 6352) * len + 7 * ((Me + 2) * len) + 19986 * len := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc]; omega
  -- 36917 … 26830
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, s56, s48, s40, fr1, rd1, wr1⟩ := vw_a (p := p) (P := P)
    (R := R) x ω μ sp q a ptr len ret v5 v6 ⟨by omega, by omega⟩ h0 h1 h5 h6 h7
    ⟨by omega, hv5, hv6, by omega, by omega⟩ hq.1 (by omega) rq rp' rl'
    (fun b h1 h2 => Memory.readable_of_writable (hst b (by omega) (by omega)))
    (fun b h1 h2 => hrvec b (by omega) h2) (fun b h1 h2 => hst b (by omega) (by omega))
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
      cap len0 1228 26534 len ptr H1 hba hf1 a0 a1 a5 a6 a7 (a8.trans h8) ⟨by omega, hptr⟩ (by decide) jte_613
      bs_26534 ⟨by omega, by omega, by omega⟩ ⟨by omega, hW.2⟩ ⟨by omega, hF.2.1, hF.2.2⟩
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
  -- the elements: from 26534 to 26581
  have mid : (∃ ω3 μ3 x3 s3 cap3 n3, n3 ≤ (Me + 2) * len ∧
      FreeStepsH p R 26534 ω2 μ2 x2 26581 ω3 μ3 x3 (7 * n3 + 2 * (cap3 - cap2) + (Ce + 6352) * len + 7) ∧
      HeapCtx env pb S0 S1 μ3 s3 ∧ s3.base = s2.base ∧ Fmtr sA s3 μ3 F W cap3 (len0 + 1 + n3) ∧ cap2 ≤ cap3 ∧
      cap3 ≤ max cap2 (max 8 (2 * (len0 + 1 + n3))) ∧ (∃ h, DL μ3 (sp - 64 + 16) F h) ∧
      Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) sA μ2 μ3 s3 ∧ ω3[1] = UInt64.ofNat (sp - 64) ∧
      (∀ a, sp - 64 + 40 ≤ a → a < sp → μ3.read a = μ2.read a)) ∨
      Exhausts p R pb 26534 ω2 μ2 x2 (2147483648 + Ce + (Ce + 7 * Me + 26352) * len - 2 * cap2 + 7) := by
    by_cases hl0 : len = 0
    · subst hl0
      have run3 := vw_b0 (p := p) (P := P) (R := R) x2 ω2 μ2 b5
      exact Or.inl ⟨ω2, μ2, x2, s2, cap2, 0, by omega, run3.mono (by omega), H2, rfl, hf2, Nat.le_refl _,
        by have := hf2.str.le; have := hf2.str.lt; omega, ⟨0, hd2⟩, (Keeps.refl _ _ _ _ _).rebase hf2.str.base, b1, fun _ _ _ => rfl⟩
    · obtain ⟨ω3, μ3, run3, c1, c5, c6, rT, fr3, rd3, wr3⟩ := vw_b (p := p) (P := P) (R := R) x2 ω2 μ2 (sp - 64) len
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
      have rvt3 : rdN μ3 75840 8 = 1746 := by
        rw [rdN_frame (fun j hj => KA3.ro _ (by omega) (Or.inl (by unfold pageSize; omega))
          (by rw [← (KA3.access _ (Or.inl (by unfold pageSize; omega))).2]; exact H3.ro _ (by omega)))]
        exact hrvt
      rcases vw_loop (p := p) (P := P) (R := R) env pb S0 S1 HA HR μA sA spA (sp - 64) F W ret v5 v6 Ze Me Ce hCe hZe hS
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
  obtain ⟨ω4, run4, e0, e1, e5, e6, e7⟩ := vw_e (p := p) (P := P) (R := R) x3 ω3 μ3 (sp - 64) ⟨by omega, by omega⟩ d1
  rcases debug_finish (p := p) (P := P) (R := R) env pb S0 S1 HA HR x3 ω4 μ3 sA s3 (sp - 64) F W (sp - 64 + 16)
      cap3 (len0 + 1 + n3) 1232 26591 (ω4[5].toNat) hh H3 (hb3 ▸ hb2 ▸ hba) hf3 hd3 e0 (e1.trans d1) (by simp) e7
      (UInt64.toNat_lt _) (by decide) jte_615 bs_26591 ⟨by omega, by omega, by omega⟩ ⟨by omega, hW.2⟩
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
  obtain ⟨ω6, run6, g0, g1, g5, g6, g7⟩ := vw_r (p := p) (P := P) (R := R) x5 ω5 μ5 (sp - 64) ret t v5 v6
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




/-- **`<&Vec<Item> as Debug>::fmt`** (26504, plain options) as a field (`RefOk`): the slot holds the
    address a of a `Vec` (cap, ptr, len) where `ValAt` puts it, whose len 32-octet `Item`s at ptr
    are where `ValAt` puts them. At most 178 · len + 2 octets. It needs 1128 octets of stack below the
    caller (Z) and the vtables' `fmt` words (75840: 1746, `&Item`; 76064: 1712; 76000: 1788). -/
theorem ref_vecitem_26504_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 Z : Nat) (hZ : 1128 ≤ Z) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA a ptr len : Nat) (hS : S0 ≤ spA)
    (hv : ValAt μA sA spA S1 a 24) (rp : rdN μA (a + 8) 8 = ptr) (rl : rdN μA (a + 16) 8 = len)
    (hel : ∀ j, j < len → ∀ i, i < 32 → ValAt μA sA spA S1 (ptr + 32 * j + i) 1)
    (hpl : ptr + 32 * len < 4294967296) (hvt : rdN μA 75840 8 = 1746) (hvk : rdN μA 76064 8 = 1712)
    (hrvt : rdN μA 76000 8 = 1788) :
    RefOk p P R env pb S0 S1 Z μA sA spA 26504 a (178 * len + 2) (5368983648 + 3221527584 * len + 10000) :=
  ref_vecitem_core env pb S0 S1 Z 960 176 3221500000 (by omega) (by omega) (by decide) HA HR
    μA sA spA a ptr len hS hv rp rl
    (fun j hj => ref_item_36917_ok env pb S0 S1 960 (Nat.le_refl _) HA HR μA sA spA (ptr + 32 * j) hS
      (hel j hj) hvk hrvt)
    hpl hvt
