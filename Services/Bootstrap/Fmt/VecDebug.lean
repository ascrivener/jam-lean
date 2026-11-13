import Services.Bootstrap.Fmt.VecDebugSteps
import Services.Bootstrap.Fmt.DebugList

/-!
# `<&Vec<u8> as fmt::Debug>::fmt` (26807), frame-only

`vd_loop`: the element loop (26848 … 26881), one `DebugList::entry` per octet, by induction on the
octets left. `vec_u8_ok`: the whole function as an `ArgOk`, for a reference v (where `ValAt` puts
it) to a `Vec<u8>` whose words and octets are where `ValAt` puts them: at most 5·len + 2 octets
(`[`, `]`, and per octet `", "` and at most 3 digits; the text is not stated).
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- What the element loop changes from T up: the `String`, and T + 8 … T + 40 (the next address,
    the `DebugList`, the slot). -/
def vdE (T W a : Nat) : Prop := (W ≤ a ∧ a < W + 24) ∨ (T + 8 ≤ a ∧ a < T + 40)

variable {X : Type} {R : HostRel X}

theorem vd_loop {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA T F W r0 v5 v6 : Nat) (hS : S0 ≤ spA)
    (hT : S0 + 704 ≤ T ∧ T % 8 = 0 ∧ 2147484352 ≤ T ∧ T + 64 ≤ spA)
    (hW : T + 64 ≤ W ∧ W + 24 ≤ S1 ∧ W + 24 ≤ spA)
    (hF : T + 64 ≤ F ∧ F + 24 ≤ S1 ∧ (F + 24 ≤ W ∨ W + 24 ≤ F)) :
    ∀ m, 0 < m → ∀ (q h : Nat) (ω : Regs) (μ : Memory) (x : X) (s : State) (cap len : Nat),
    HeapCtx env pb S0 S1 μ s → s.base % 8 = 0 → Fmtr sA s μ F W cap len →
    Keeps pb spA (fun _ => False) sA μA μ s → DL μ (T + 16) F h → (h = 0 ∨ h = 1) →
    ω[1] = UInt64.ofNat T → ω[5] = UInt64.ofNat q → ω[6] = UInt64.ofNat m →
    rdN μ T 8 = 75976 → rdN μ 76000 8 = 1788 →
    (∀ j, j < m → ValAt μA sA spA S1 (q + j) 1) → q + m < 4294967296 → len + 5 * m < 134217728 →
    (∃ ω' μ' x' s' cap' n, n ≤ 5 * m ∧
      FreeStepsH p R 26848 ω μ x 26881 ω' μ' x' (7 * n + 2 * (cap' - cap) + 4500 * m) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Fmtr sA s' μ' F W cap' (len + n) ∧ cap ≤ cap' ∧
      cap' ≤ max cap (max 8 (2 * (len + n))) ∧ DL μ' (T + 16) F 1 ∧
      Keeps pb T (vdE T W) sA μ μ' s' ∧ ω'[1] = UInt64.ofNat T) ∨
    Exhausts p R pb 26848 ω μ x (2684354560 + 4500 * m - 2 * cap) := by
  intro m
  induction m with
  | zero => intro h; exact absurd h (Nat.lt_irrefl 0)
  | succ k ih =>
  intro _ q h ω μ x s cap len H hba hf KA hd hh h1 h5 h6 rT rvt helts hqm hn
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  have hcap := hf.str.lt
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, s8, s32, fr1, rd1, wr1⟩ := vd_l (p := p) (P := P) (R := R)
    x ω μ T q ⟨by omega, by omega⟩ h1 h5 (by omega) rT (fun a h1 h2 => hst a (by omega) (by omega))
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
  have rvt1 : rdN μ1 (75976 + 24) 8 = 1788 := by
    rw [rdN_frame (fun j hj => k1 _ (by omega) (by omega))]; exact rvt
  rcases debug_entry (p := p) (P := P) (R := R) env pb S0 S1 600 (Nat.le_refl _) HA HR μA sA spA 37527 q 3 2300 1788
      (ref_u8_ok env pb S0 S1 HA HR μA sA spA q hS (by simpa using helts 0 (by omega)))
      x ω1 μ1 s T F W (T + 16) (T + 32) 75976 cap len 1254 26872 q (k + 1) h H1 hba hf1 KA1 hd1 hh
      a0 (a1.trans h1) (a5.trans h5) (a6.trans h6) a7 a8 a9 ⟨by omega, by omega⟩ ⟨by decide, by decide⟩ rvt1
      (by decide) jte_893 bs_37527 s32 (by decide) jte_626 bs_26872 ⟨by omega, hT.2.1, by omega⟩
      ⟨by omega, by omega, by omega⟩ ⟨by omega, hW.2.1⟩ ⟨by omega, hF.2.1, hF.2.2⟩
      ⟨by omega, by omega, Or.inl (by omega), Or.inl (by omega)⟩ ⟨by omega, by omega, Or.inl (by omega)⟩
      (by omega) with
    ⟨ω2, μ2, x2, s2, cap2, n2, hn2, run2, H2, hb2, hf2, hc1, hc2, hd2, K2, b0, b1, b5, b6⟩ | hx
  · have K2' : Keeps pb T (vdE T W) sA μ1 μ2 s2 :=
      K2.mono (Nat.le_refl _) (fun a h => by unfold dlE at h; unfold vdE; omega)
    have K12 := K1.trans' K2'
    rw [Nat.max_self] at K12
    have hst2 : ∀ a, S0 ≤ a → a < S1 → μ2.writable a = true := H2.st
    have s8' : rdN μ2 (T + 8) 8 = q + 1 := by
      rw [rdN_frame (fun j hj => K2.hi _ (by omega) (by omega) (by unfold dlE; omega))]; exact s8
    obtain ⟨ω3, run3, c1, c5, c6⟩ := vd_n (p := p) (P := P) (R := R) x2 ω2 μ2 T (k + 1) (q + 1)
      ⟨by omega, by omega⟩ b1 b6 ⟨by omega, by omega⟩ s8'
      (fun a h1 h2 => Memory.readable_of_writable (hst2 a (by omega) (by omega)))
    by_cases hk : k = 0
    · subst hk
      rw [if_pos (by omega)] at run3
      refine Or.inl ⟨ω3, μ2, x2, s2, cap2, n2, by omega, ((run1.trans run2).trans run3).mono (by omega), H2, hb2,
        hf2, hc1, hc2, hd2, K12, c1.trans b1⟩
    · rw [if_neg (by omega)] at run3
      have rT2 : rdN μ2 T 8 = 75976 := by
        rw [show T = T + 0 by rfl, rdN_frame (fun j hj => K12.hi _ (by omega) (by omega) (by unfold vdE; omega))]
        exact rT
      have rvt2 : rdN μ2 76000 8 = 1788 := by
        rw [rdN_frame (fun j hj => K12.ro _ (by omega) (Or.inl (by unfold pageSize; omega)) (H.ro _ (by omega)))]
        exact rvt
      have KA2 : Keeps pb spA (fun _ => False) sA μA μ2 s2 := by
        have := KA.trans' (K12.lift (sp' := spA) (by omega) (fun a h ha => by unfold vdE at h; omega))
        rwa [Nat.max_self] at this
      rcases ih (by omega) (q + 1) 1 ω3 μ2 x2 s2 cap2 (len + n2) H2 (hb2 ▸ hba) hf2 KA2 hd2 (Or.inr rfl)
          (c1.trans b1) c5 (by rw [c6]; congr 1) rT2 rvt2
          (fun j hj => by rw [show q + 1 + j = q + (j + 1) by omega]; exact helts (j + 1) (by omega))
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

/-- A value where `ValAt` puts it keeps its octets in every memory a run reaches keeping the
    caller's frame. -/
theorem ValAt.read {env : RefineHost.Env} {pb S0 S1 spA a n : Nat} {sA s : State} {μA μ : Memory}
    (h : ValAt μA sA spA S1 a n) (H : HeapCtx env pb S0 S1 μ s)
    (K : Keeps pb spA (fun _ => False) sA μA μ s) : ∀ j, j < n → μ.read (a + j) = μA.read (a + j) := by
  intro j hj
  have := H.hS1
  rcases h with ⟨h1, h2, -⟩ | ⟨c, hc, hu, hd⟩
  · exact K.hi _ (by omega) (by omega) id
  · exact K.data c hc hu _ (hd j hj)

/-- A word where `ValAt` puts it, read in a memory the run reaches. -/
theorem ValAt.rdN {env : RefineHost.Env} {pb S0 S1 spA a o n : Nat} {sA s : State} {μA μ : Memory}
    (h : ValAt μA sA spA S1 a n) (H : HeapCtx env pb S0 S1 μ s)
    (K : Keeps pb spA (fun _ => False) sA μA μ s) (ho : o + 8 ≤ n) : rdN μ (a + o) 8 = rdN μA (a + o) 8 :=
  rdN_frame (fun j hj => by rw [show a + o + j = a + (o + j) by omega]; exact h.read H K _ (by omega))

/-- The body of `vec_u8_ok`, for a reference at v whose word (the `Vec`'s address vec) is read in
    the memory the call starts from: readable there, above sp or below the heap's top. -/
theorem vec_u8_core {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 Z : Nat) (hZ : 768 ≤ Z) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA v vec ptr len : Nat) (hS : S0 ≤ spA)
    (hvec : ValAt μA sA spA S1 vec 24)
    (rp : rdN μA (vec + 8) 8 = ptr) (rl : rdN μA (vec + 16) 8 = len)
    (helts : ∀ j, j < len → ValAt μA sA spA S1 (ptr + j) 1) (hpl : ptr + len < 4294967296)
    (hrvt : rdN μA 76000 8 = 1788)
    (ω : Regs) (μ : Memory) (x : X) (s : State) (sp F W cap len0 ret t v5 v6 : Nat)
    (H : HeapCtx env pb S0 S1 μ s) (hba : s.base % 8 = 0) (K : Keeps pb spA (fun _ => False) sA μA μ s)
    (hf : Fmtr sA s μ F W cap len0)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat F)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hsp : S0 + Z ≤ sp ∧ sp % 8 = 0 ∧ 2147483648 + Z ≤ sp) (hspA : sp ≤ spA) (hW : sp ≤ W ∧ W + 24 ≤ S1)
    (hWA : W + 24 ≤ spA) (hF : sp ≤ F ∧ F + 24 ≤ S1 ∧ (F + 24 ≤ W ∨ W + 24 ≤ F))
    (hn : len0 + (5 * len + 2) < 134217728)
    (hrv : ∀ b, v ≤ b → b < v + 8 → μ.readable b = true)
    (hlv : (sp ≤ v ∧ v + 8 ≤ S1) ∨ v + 8 ≤ 2147483648) (rv' : rdN μ v 8 = vec) :
    (∃ ω' μ' x' s' cap' n, n ≤ 5 * len + 2 ∧
      FreeStepsH p R 26807 ω μ x t ω' μ' x' (7 * n + 2 * (cap' - cap) + (2147483648 + 4500 * len + 5000)) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Fmtr sA s' μ' F W cap' (len0 + n) ∧ cap ≤ cap' ∧
      cap' ≤ max cap (max 8 (2 * (len0 + n))) ∧
      Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) sA μ μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0) ∨
    Exhausts p R pb 26807 ω μ x (1073741824 + (2147483648 + 4500 * len + 5000)) := by
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  obtain ⟨hrvec, hlvec⟩ := hvec.readable (by decide) H hS hspA K
  have rp' : rdN μ (vec + 8) 8 = ptr := by rw [hvec.rdN H K (by omega)]; exact rp
  have rl' : rdN μ (vec + 16) 8 = len := by rw [hvec.rdN H K (by omega)]; exact rl
  have hptr : ptr < 18446744073709551616 := by omega
  have hlen : len < 18446744073709551616 := by omega
  -- 26807 … 26830
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, s56, s48, s40, fr1, rd1, wr1⟩ := vd_a (p := p) (P := P)
    (R := R) x ω μ sp v vec ptr len ret v5 v6 ⟨by omega, by omega⟩ h0 h1 h5 h6 h7
    ⟨by omega, hv5, hv6, by omega, by omega⟩ ⟨by omega, by omega⟩ rv' rp' rl' hrv
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
      cap len0 1252 26837 ptr len H1 hba hf1 a0 a1 a5 a6 a7 (a8.trans h8) ⟨hptr, hlen⟩ (by decide) jte_625
      bs_26837 ⟨by omega, by omega, by omega⟩ ⟨by omega, hW.2⟩ ⟨by omega, hF.2.1, hF.2.2⟩
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
  -- the elements: from 26837 to 26881
  have mid : (∃ ω3 μ3 x3 s3 cap3 n3, n3 ≤ 5 * len ∧
      FreeStepsH p R 26837 ω2 μ2 x2 26881 ω3 μ3 x3 (7 * n3 + 2 * (cap3 - cap2) + 4500 * len + 4) ∧
      HeapCtx env pb S0 S1 μ3 s3 ∧ s3.base = s2.base ∧ Fmtr sA s3 μ3 F W cap3 (len0 + 1 + n3) ∧ cap2 ≤ cap3 ∧
      cap3 ≤ max cap2 (max 8 (2 * (len0 + 1 + n3))) ∧ (∃ h, DL μ3 (sp - 64 + 16) F h) ∧
      Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) sA μ2 μ3 s3 ∧ ω3[1] = UInt64.ofNat (sp - 64) ∧
      (∀ a, sp - 64 + 40 ≤ a → a < sp → μ3.read a = μ2.read a)) ∨
      Exhausts p R pb 26837 ω2 μ2 x2 (2684354560 + 4500 * len - 2 * cap2 + 4) := by
    by_cases hl0 : len = 0
    · subst hl0
      have run3 := vd_b0 (p := p) (P := P) (R := R) x2 ω2 μ2 b6
      exact Or.inl ⟨ω2, μ2, x2, s2, cap2, 0, by omega, run3.mono (by omega), H2, rfl, hf2, Nat.le_refl _,
        by have := hf2.str.le; have := hf2.str.lt; omega, ⟨0, hd2⟩, (Keeps.refl _ _ _ _ _).rebase hf2.str.base, b1, fun _ _ _ => rfl⟩
    · obtain ⟨ω3, μ3, run3, c1, c5, c6, rT, fr3, rd3, wr3⟩ := vd_b (p := p) (P := P) (R := R) x2 ω2 μ2 (sp - 64) len
        ⟨by omega, by omega⟩ b1 b6 ⟨by omega, hlen⟩ (fun a h1 h2 => hst2 a (by omega) (by omega))
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
      have rvt3 : rdN μ3 76000 8 = 1788 := by
        rw [rdN_frame (fun j hj => KA3.ro _ (by omega) (Or.inl (by unfold pageSize; omega))
          (by rw [← (KA3.access _ (Or.inl (by unfold pageSize; omega))).2]; exact H3.ro _ (by omega)))]
        exact hrvt
      rcases vd_loop (p := p) (P := P) (R := R) env pb S0 S1 HA HR μA sA spA (sp - 64) F W ret v5 v6 hS
          ⟨by omega, by omega, by omega, by omega⟩ ⟨by omega, hW.2, hWA⟩ ⟨by omega, hF.2.1, hF.2.2⟩ len (by omega)
          ptr 0 ω3 μ3 x2 s2 cap2 (len0 + 1) H3 (hb2 ▸ hba) hf3 KA3 hd3 (Or.inl rfl) (c1.trans b1) (c5.trans b5)
          (c6.trans b6) rT rvt3 helts hpl (by omega) with
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
  obtain ⟨ω4, run4, e0, e1, e5, e6, e7⟩ := vd_e (p := p) (P := P) (R := R) x3 ω3 μ3 (sp - 64) ⟨by omega, by omega⟩ d1
  rcases debug_finish (p := p) (P := P) (R := R) env pb S0 S1 HA HR x3 ω4 μ3 sA s3 (sp - 64) F W (sp - 64 + 16)
      cap3 (len0 + 1 + n3) 1256 26891 (ω4[5].toNat) hh H3 (hb3 ▸ hb2 ▸ hba) hf3 hd3 e0 (e1.trans d1) (by simp) e7
      (UInt64.toNat_lt _) (by decide) jte_627 bs_26891 ⟨by omega, by omega, by omega⟩ ⟨by omega, hW.2⟩
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
  obtain ⟨ω6, run6, g0, g1, g5, g6, g7⟩ := vd_r (p := p) (P := P) (R := R) x5 ω5 μ5 (sp - 64) ret t v5 v6
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


/-- **`<&Vec<u8> as Debug>::fmt`** (26807, plain options) as an argument: a reference at v (where
    `ValAt` puts it) to a `Vec<u8>` (cap, ptr, len) whose words and len octets are where `ValAt`
    puts them; at most 5·len + 2 octets. It needs 768 octets of stack below the caller (Z). -/
theorem vec_u8_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 Z : Nat) (hZ : 768 ≤ Z) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA v vec ptr len : Nat) (hS : S0 ≤ spA)
    (hv : ValAt μA sA spA S1 v 8) (rv : rdN μA v 8 = vec) (hvec : ValAt μA sA spA S1 vec 24)
    (rp : rdN μA (vec + 8) 8 = ptr) (rl : rdN μA (vec + 16) 8 = len)
    (helts : ∀ j, j < len → ValAt μA sA spA S1 (ptr + j) 1) (hpl : ptr + len < 4294967296)
    (hrvt : rdN μA 76000 8 = 1788) :
    ArgOk p P R env pb S0 S1 Z μA sA spA 26807 v (5 * len + 2) (2147483648 + 4500 * len + 5000) := by
  intro ω μ x s sp F W cap len0 ret t v5 v6 H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hWA hF hn
  intro ω μ x s sp F W cap len0 ret t v5 v6 H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hWA hF hn
  obtain ⟨hrv, hlv⟩ := hv.readable (by decide) H hS hspA K
  exact vec_u8_core env pb S0 S1 Z hZ HA HR μA sA spA v vec ptr len hS hvec rp rl helts hpl hrvt ω μ x s sp F W
    cap len0 ret t v5 v6 H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hWA hF hn hrv hlv
    (by rw [show v = v + 0 by rfl, hv.rdN H K (by omega)]; exact rv)

/-- **`<&Vec<u8> as Debug>::fmt`** (26807, plain options) as an entry or field (`RefOk`): the slot
    holds the address a of a `Vec<u8>` (cap, ptr, len) whose words and len octets are where `ValAt`
    puts them; at most 5·len + 2 octets. -/
theorem ref_vec_u8_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 Z : Nat) (hZ : 768 ≤ Z) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA a ptr len : Nat) (hS : S0 ≤ spA)
    (hvec : ValAt μA sA spA S1 a 24)
    (rp : rdN μA (a + 8) 8 = ptr) (rl : rdN μA (a + 16) 8 = len)
    (helts : ∀ j, j < len → ValAt μA sA spA S1 (ptr + j) 1) (hpl : ptr + len < 4294967296)
    (hrvt : rdN μA 76000 8 = 1788) :
    RefOk p P R env pb S0 S1 Z μA sA spA 26807 a (5 * len + 2) (2147483648 + 4500 * len + 5000) := by
  intro ω μ x s sp F W cap len0 ret t v5 v6 v H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hWA hF hn
    hv ra
  have hst : ∀ b, S0 ≤ b → b < S1 → μ.writable b = true := H.st
  have := H.hS1
  exact vec_u8_core env pb S0 S1 Z hZ HA HR μA sA spA v a ptr len hS hvec rp rl helts hpl hrvt ω μ x s sp F W
    cap len0 ret t v5 v6 H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hWA hF hn
    (fun b h1 h2 => Memory.readable_of_writable (hst b (by omega) (by omega))) (Or.inl ⟨hv.1, hv.2.1⟩) ra

end Services.Bootstrap.Fmt
