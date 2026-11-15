import Services.Bootstrap.Fmt.U8x32Steps
import Services.Bootstrap.Fmt.DebugList

/-!
# `<&[u8; 32] as fmt::Debug>::fmt` (36529), frame-only

`a8_loop`: entries 1 … 30 (38042 … 38612), one `DebugList::entry` each, by induction on the
entries left. `ref_u8x32_ok`: the whole function as a field or entry passed through a slot
(`RefOk`), for 32 octets where `ValAt` puts them: at most 5·32 + 2 = 162 octets (`[`, `]`, and per
octet `", "` and at most 3 digits; the text is not stated).
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- What the entries change from T up: the `String`, and T … T + 24 (the `DebugList` and the
    slot). -/
def a8E (T W c : Nat) : Prop := (W ≤ c ∧ c < W + 24) ∨ (T ≤ c ∧ c < T + 24)

variable {X : Type} {R : HostRel X}

/-- Entries 31 − m … 30 (m ≤ 30), from 38042 + 19(30 − m) to 38612: the `DebugList` at T, the
    array at a, the vtable 75976 in ω₆. -/
theorem a8_loop {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA T F W a : Nat) (hS : S0 ≤ spA)
    (hT : S0 + 704 ≤ T ∧ T % 8 = 0 ∧ 2147484352 ≤ T ∧ T + 48 ≤ spA)
    (hW : T + 48 ≤ W ∧ W + 24 ≤ S1 ∧ W + 24 ≤ spA)
    (hF : T + 48 ≤ F ∧ F + 24 ≤ S1 ∧ (F + 24 ≤ W ∨ W + 24 ≤ F))
    (helts : ∀ j, j < 32 → ValAt μA sA spA S1 (a + j) 1) (ha : a + 32 < 4294967296) :
    ∀ m, m ≤ 30 → ∀ (ω : Regs) (μ : Memory) (x : X) (s : State) (cap len : Nat),
    HeapCtx env pb S0 S1 μ s → s.base % 8 = 0 → Fmtr sA s μ F W cap len →
    Keeps pb spA (fun _ => False) sA μA μ s → DL μ T F 1 →
    ω[1] = UInt64.ofNat T → ω[5] = UInt64.ofNat a → ω[6] = UInt64.ofNat 75976 →
    rdN μ 76000 8 = 1788 → len + 5 * m < 134217728 →
    (∃ ω' μ' x' s' cap' n, n ≤ 5 * m ∧
      FreeStepsH p R (38042 + 19 * (30 - m)) ω μ x 38612 ω' μ' x' (7 * n + 2 * (cap' - cap) + 4500 * m) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Fmtr sA s' μ' F W cap' (len + n) ∧ cap ≤ cap' ∧
      cap' ≤ max cap (max 8 (2 * (len + n))) ∧ DL μ' T F 1 ∧
      Keeps pb T (a8E T W) sA μ μ' s' ∧ ω'[1] = UInt64.ofNat T ∧ ω'[5] = UInt64.ofNat a ∧
      ω'[6] = UInt64.ofNat 75976) ∨
    Exhausts p R pb (38042 + 19 * (30 - m)) ω μ x (2684354560 + 4500 * m - 2 * cap) := by
  intro m
  induction m with
  | zero =>
    intro _ ω μ x s cap len H hba hf KA hd h1 h5 h6 rvt hn
    have := hf.str.le
    have := hf.str.lt
    exact Or.inl ⟨ω, μ, x, s, cap, 0, Nat.le_refl _, FreeStepsH.refl.mono (Nat.zero_le _), H, rfl, hf,
      Nat.le_refl _, by omega, hd, (Keeps.refl _ _ _ _ _).rebase hf.str.base, h1, h5, h6⟩
  | succ k ih =>
  intro hk ω μ x s cap len H hba hf KA hd h1 h5 h6 rvt hn
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst : ∀ c, S0 ≤ c → c < S1 → μ.writable c = true := H.st
  have hcap := hf.str.lt
  -- entry i = 30 − k
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, s16, fr1, rd1, wr1⟩ := a8_e (p := p) (P := P) (R := R)
    x ω μ (30 - k) T a ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ h1 h5 h6 (by omega)
    (fun c h1 h2 => hst c (by omega) (by omega))
  rw [show 38042 + 19 * (30 - k - 1) = 38042 + 19 * (30 - (k + 1)) by omega] at run1
  have k1 : ∀ c, c < 4294967296 → ¬ (T + 16 ≤ c ∧ c < T + 24) → μ1.read c = μ.read c := fun c h1 h2 =>
    fr1 c h1 (by omega)
  have H1 : HeapCtx env pb S0 S1 μ1 s := ctx_hi H (fun c hc => k1 c (by omega) (by omega)) wr1
  have K1 : Keeps pb T (a8E T W) sA μ μ1 s :=
    Keeps.of_frame (Z := fun c => T + 16 ≤ c ∧ c < T + 24) hf.str.base
      (fun c hc hz => k1 c hc hz) rd1 wr1 (fun c hz => hst c (by omega) (by omega))
      (fun c hz h => Or.inr ⟨by omega, by omega⟩) (fun c hz hg => by unfold Glob at hg; omega)
      (fun c hc hu b hb => by
        have := chunk_bounds H.wf (hf.str.base c hc hu)
        have := H.hbT
        unfold InData at hb; omega)
  have hf1 : Fmtr sA s μ1 F W cap len := hf.congr (fun j hj => k1 _ (by omega) (by omega))
    (fun j hj => k1 _ (by omega) (by omega)) (fun c h1 h2 => ⟨k1 c (by omega) (by omega), rd1 c⟩)
  have KA1 : Keeps pb spA (fun _ => False) sA μA μ1 s := by
    have := KA.trans' (K1.lift (sp' := spA) (by omega) (fun c h hc => by unfold a8E at h; omega))
    rwa [Nat.max_self] at this
  have hd1 : DL μ1 T F 1 :=
    ⟨by rw [show T = T + 0 by rfl, rdN_frame (fun j hj => k1 _ (by omega) (by omega))]; exact hd.fm,
      by rw [rdN_frame (fun j hj => k1 _ (by omega) (by omega))]; exact hd.ok,
      by rw [rdN_frame (fun j hj => k1 _ (by omega) (by omega))]; exact hd.has⟩
  have rvt1 : rdN μ1 (75976 + 24) 8 = 1788 := by
    rw [rdN_frame (fun j hj => k1 _ (by omega) (by omega))]; exact rvt
  obtain ⟨hjt, hbt⟩ := a8_jt (p := p) (P := P) (30 - k) (by omega)
  rcases debug_entry (p := p) (P := P) (R := R) env pb S0 S1 600 (Nat.le_refl _) HA HR μA sA spA 37527 (a + (30 - k))
      3 2300 1788
      (ref_u8_ok env pb S0 S1 HA HR μA sA spA (a + (30 - k)) hS (helts (30 - k) (by omega)))
      x ω1 μ1 s T F W T (T + 16) 75976 cap len (1820 + 2 * (30 - k)) (38042 + 19 * (30 - k)) a 75976 1 H1 hba hf1
      KA1 hd1 (Or.inr rfl) a0 (a1.trans h1) (a5.trans h5) (a6.trans h6) a7 a8 a9 ⟨by omega, by omega⟩
      ⟨by decide, by decide⟩ rvt1 (by decide) jte_893 bs_37527 s16 ⟨by omega, by omega, by omega⟩ hjt hbt
      ⟨by omega, hT.2.1, by omega⟩ ⟨by omega, by omega, by omega⟩ ⟨by omega, hW.2.1⟩ ⟨by omega, hF.2.1, hF.2.2⟩
      ⟨by omega, by omega, Or.inl (by omega), Or.inl (by omega)⟩ ⟨by omega, by omega, Or.inl (by omega)⟩
      (by omega) with
    ⟨ω2, μ2, x2, s2, cap2, n2, hn2, run2, H2, hb2, hf2, hc1, hc2, hd2, K2, b0, b1, b5, b6⟩ | hx
  · have K2' : Keeps pb T (a8E T W) sA μ1 μ2 s2 :=
      K2.mono (Nat.le_refl _) (fun c h => by unfold dlE at h; unfold a8E; omega)
    have K12 := K1.trans' K2'
    rw [Nat.max_self] at K12
    have rvt2 : rdN μ2 76000 8 = 1788 := by
      rw [rdN_frame (fun j hj => K12.ro _ (by omega) (Or.inl (by unfold pageSize; omega)) (H.ro _ (by omega)))]
      exact rvt
    have KA2 : Keeps pb spA (fun _ => False) sA μA μ2 s2 := by
      have := KA.trans' (K12.lift (sp' := spA) (by omega) (fun c h hc => by unfold a8E at h; omega))
      rwa [Nat.max_self] at this
    rcases ih (by omega) ω2 μ2 x2 s2 cap2 (len + n2) H2 (hb2 ▸ hba) hf2 KA2 hd2 b1 b5 b6 rvt2 (by omega) with
      ⟨ω4, μ4, x4, s4, cap4, n4, hn4, run4, H4, hb4, hf4, hc3, hc4, hd4, K4, d1, d5, d6⟩ | hx
    · have K := K12.trans' K4
      rw [Nat.max_self] at K
      refine Or.inl ⟨ω4, μ4, x4, s4, cap4, n2 + n4, by omega,
        ((run1.trans run2).trans run4).mono (by omega), H4, hb4.trans hb2,
        by rwa [show len + (n2 + n4) = len + n2 + n4 by omega], by omega, ?_, hd4, K, d1, d5, d6⟩
      rw [show len + (n2 + n4) = len + n2 + n4 by omega]; omega
    · refine Or.inr ((Exhausts.pre (run1.trans run2) hx).mono ?_)
      have : cap2 ≤ max cap (max 8 (2 * (len + n2))) := hc2
      omega
  · exact Or.inr ((Exhausts.pre run1 hx).mono (by omega))

/-- **`<&[u8; 32] as Debug>::fmt`** (36529, plain options) as a field or entry: the slot holds the
    address a of 32 octets where `ValAt` puts them; at most 162 octets. It needs 752 octets of stack
    below the caller (Z), and the vtable 75976's `fmt` word (76000: 1788, `<&u8 as Debug>`). -/
theorem ref_u8x32_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 Z : Nat) (hZ : 752 ≤ Z) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA a : Nat) (hS : S0 ≤ spA)
    (helts : ∀ j, j < 32 → ValAt μA sA spA S1 (a + j) 1) (hrvt : rdN μA 76000 8 = 1788) :
    RefOk p P R env pb S0 S1 Z μA sA spA 36529 a 162 2147632648 := by
  intro ω μ x s sp F W cap len0 ret t v5 v6 v H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hWA hF hn
    hv ra
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst : ∀ c, S0 ≤ c → c < S1 → μ.writable c = true := H.st
  have ha : a + 32 < 4294967296 := by
    obtain ⟨-, h⟩ := (helts 31 (by omega)).readable (by decide) H hS hspA K
    omega
  have ha64 : a < 18446744073709551616 := by omega
  -- 36529 … 38012
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, s40, s32, s24, fr1, rd1, wr1⟩ := a8_a (p := p) (P := P)
    (R := R) x ω μ sp v a ret v5 v6 ⟨by omega, by omega⟩ h0 h1 h5 h6 h7 ⟨by omega, hv5, hv6, by omega⟩ ra
    (fun c h1 h2 => Memory.readable_of_writable (hst c (by omega) (by omega)))
    (fun c h1 h2 => hst c (by omega) (by omega))
  have k1 : ∀ c, c < 4294967296 → (c < sp - 24 ∨ sp ≤ c) → μ1.read c = μ.read c := fr1
  have H1 : HeapCtx env pb S0 S1 μ1 s := ctx_hi H (fun c hc => k1 c (by omega) (Or.inl (by omega))) wr1
  have hf1 : Fmtr sA s μ1 F W cap len0 := hf.congr (fun j hj => k1 _ (by omega) (Or.inr (by omega)))
    (fun j hj => k1 _ (by omega) (Or.inr (by omega))) (fun c h1 h2 => ⟨k1 c (by omega) (Or.inl (by omega)), rd1 c⟩)
  have K1 : Keeps pb sp (fun c => W ≤ c ∧ c < W + 24) sA μ μ1 s :=
    Keeps.of_frame (Z := fun c => sp - 24 ≤ c ∧ c < sp) hf.str.base
      (fun c hc hz => k1 c hc (by omega)) rd1 wr1 (fun c hz => hst c (by omega) (by omega))
      (fun c hz h => by omega) (fun c hz hg => by unfold Glob at hg; omega)
      (fun c hc hu b hb => by
        have := chunk_bounds H.wf (hf.str.base c hc hu)
        have := H.hbT
        unfold InData at hb; omega)
  have KA1 : Keeps pb spA (fun _ => False) sA μA μ1 s := by
    have := K.trans' (K1.lift (sp' := spA) hspA (fun c h hc => by omega))
    rwa [Nat.max_self] at this
  -- the list: "["
  rcases debug_list_new (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω1 μ1 sA s (sp - 48) F W (sp - 48)
      cap len0 1818 38018 a v6 H1 hba hf1 a0 a1 a5 a6 a7 (a8.trans h8) ⟨ha64, hv6⟩ (by decide) jte_908
      bs_38018 ⟨by omega, by omega, by omega⟩ ⟨by omega, hW.2⟩ ⟨by omega, hF.2.1, hF.2.2⟩
      ⟨by omega, by omega, Or.inl (by omega), Or.inl (by omega)⟩ (by omega) with
    ⟨ω2, μ2, x2, s2, cap2, run2, H2, hb2, hf2, hc1, hc2, hd2, K2, b0, b1, b5, b6⟩ | hx
  rotate_left
  · exact Or.inr ((Exhausts.pre run1 hx).mono (by omega))
  have hst2 : ∀ c, S0 ≤ c → c < S1 → μ2.writable c = true := H2.st
  have K2' : Keeps pb sp (fun c => W ≤ c ∧ c < W + 24) sA μ1 μ2 s2 :=
    K2.lift (by omega) (fun c h hc => by unfold dlE at h; omega)
  have KA2 : Keeps pb spA (fun _ => False) sA μA μ2 s2 := by
    have := KA1.trans' (K2'.lift (sp' := spA) hspA (fun c h hc => by omega))
    rwa [Nat.max_self] at this
  have kT2 : ∀ c, sp - 48 + 24 ≤ c → c < sp → μ2.read c = μ1.read c := fun c h1 h2 =>
    K2.hi c (by omega) (by omega) (by unfold dlE; omega)
  have rvt2 : rdN μ2 76000 8 = 1788 := by
    rw [rdN_frame (fun j hj => KA2.ro _ (by omega) (Or.inl (by unfold pageSize; omega))
      (by rw [← (KA2.access _ (Or.inl (by unfold pageSize; omega))).2]; exact H2.ro _ (by omega)))]
    exact hrvt
  -- entry 0
  obtain ⟨ω3, μ3, run3, c0, c1, c5, c6, c7, c8, c9, s16, fr3, rd3, wr3⟩ := a8_e0 (p := p) (P := P) (R := R)
    x2 ω2 μ2 (sp - 48) a ⟨by omega, by omega⟩ b1 b5 ha64 (fun c h1 h2 => hst2 c (by omega) (by omega))
  have k3 : ∀ c, c < 4294967296 → ¬ (sp - 48 + 16 ≤ c ∧ c < sp - 48 + 24) → μ3.read c = μ2.read c :=
    fun c h1 h2 => fr3 c h1 (by omega)
  have H3 : HeapCtx env pb S0 S1 μ3 s2 := ctx_hi H2 (fun c hc => k3 c (by omega) (by omega)) wr3
  have K3 : Keeps pb (sp - 48) (a8E (sp - 48) W) sA μ2 μ3 s2 :=
    Keeps.of_frame (Z := fun c => sp - 48 + 16 ≤ c ∧ c < sp - 48 + 24) hf2.str.base
      (fun c hc hz => k3 c hc hz) rd3 wr3 (fun c hz => hst2 c (by omega) (by omega))
      (fun c hz h => Or.inr ⟨by omega, by omega⟩) (fun c hz hg => by unfold Glob at hg; omega)
      (fun c hc hu b hb => by
        have := chunk_bounds H2.wf (hf2.str.base c hc hu)
        have := H2.hbT
        unfold InData at hb; omega)
  have hf3 : Fmtr sA s2 μ3 F W cap2 (len0 + 1) := hf2.congr (fun j hj => k3 _ (by omega) (by omega))
    (fun j hj => k3 _ (by omega) (by omega)) (fun c h1 h2 => ⟨k3 c (by omega) (by omega), rd3 c⟩)
  have KA3 : Keeps pb spA (fun _ => False) sA μA μ3 s2 := by
    have := KA2.trans' (K3.lift (sp' := spA) (by omega) (fun c h hc => by unfold a8E at h; omega))
    rwa [Nat.max_self] at this
  have hd3 : DL μ3 (sp - 48) F 0 :=
    ⟨by rw [show sp - 48 = sp - 48 + 0 by rfl, rdN_frame (fun j hj => k3 _ (by omega) (by omega))]; exact hd2.fm,
      by rw [rdN_frame (fun j hj => k3 _ (by omega) (by omega))]; exact hd2.ok,
      by rw [rdN_frame (fun j hj => k3 _ (by omega) (by omega))]; exact hd2.has⟩
  have rvt3 : rdN μ3 (75976 + 24) 8 = 1788 := by
    rw [rdN_frame (fun j hj => k3 _ (by omega) (by omega))]; exact rvt2
  obtain ⟨hjt0, hbt0⟩ := a8_jt (p := p) (P := P) 0 (by omega)
  rcases debug_entry (p := p) (P := P) (R := R) env pb S0 S1 600 (Nat.le_refl _) HA HR μA sA spA 37527 (a + 0)
      3 2300 1788 (ref_u8_ok env pb S0 S1 HA HR μA sA spA (a + 0) hS (helts 0 (by omega)))
      x2 ω3 μ3 s2 (sp - 48) F W (sp - 48) (sp - 48 + 16) 75976 cap2 (len0 + 1) (1820 + 2 * 0) (38042 + 19 * 0)
      a 75976 0 H3 (hb2 ▸ hba) hf3 KA3 hd3 (Or.inl rfl) c0 (c1.trans b1) (c5.trans b5) c6 c7 c8 c9
      ⟨by omega, by omega⟩ ⟨by decide, by decide⟩ rvt3 (by decide) jte_893 bs_37527 s16
      ⟨by omega, by omega, by omega⟩ hjt0 hbt0 ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega⟩
      ⟨by omega, hW.2⟩ ⟨by omega, hF.2.1, hF.2.2⟩ ⟨by omega, by omega, Or.inl (by omega), Or.inl (by omega)⟩
      ⟨by omega, by omega, Or.inl (by omega)⟩ (by omega) with
    ⟨ω4, μ4, x4, s4, cap4, n4, hn4, run4, H4, hb4, hf4, hc3, hc4, hd4, K4, d0, d1, d5, d6⟩ | hx
  rotate_left
  · refine Or.inr ((Exhausts.pre ((run1.trans run2).trans run3) hx).mono ?_)
    have : cap2 ≤ max cap (max 8 (2 * (len0 + 1))) := hc2
    have := hf2.str.lt
    omega
  have K4' : Keeps pb (sp - 48) (a8E (sp - 48) W) sA μ3 μ4 s4 :=
    K4.mono (Nat.le_refl _) (fun c h => by unfold dlE at h; unfold a8E; omega)
  have KA4 : Keeps pb spA (fun _ => False) sA μA μ4 s4 := by
    have := KA3.trans' (K4'.lift (sp' := spA) (by omega) (fun c h hc => by unfold a8E at h; omega))
    rwa [Nat.max_self] at this
  have rvt4 : rdN μ4 76000 8 = 1788 := by
    rw [rdN_frame (fun j hj => KA4.ro _ (by omega) (Or.inl (by unfold pageSize; omega))
      (by rw [← (KA4.access _ (Or.inl (by unfold pageSize; omega))).2]; exact H4.ro _ (by omega)))]
    exact hrvt
  -- entries 1 … 30
  rcases a8_loop (p := p) (P := P) (R := R) env pb S0 S1 HA HR μA sA spA (sp - 48) F W a hS
      ⟨by omega, by omega, by omega, by omega⟩ ⟨by omega, hW.2, hWA⟩ ⟨by omega, hF.2.1, hF.2.2⟩ helts ha 30
      (Nat.le_refl _) ω4 μ4 x4 s4 cap4 (len0 + 1 + n4) H4 (hb4 ▸ hb2 ▸ hba) hf4 KA4 hd4
      d1 d5 d6 rvt4 (by omega) with
    ⟨ω5, μ5, x5, s5, cap5, n5, hn5, run5, H5, hb5, hf5, hc5, hc6, hd5, K5, e1, e5, e6⟩ | hx
  rotate_left
  · refine Or.inr ((Exhausts.pre (((run1.trans run2).trans run3).trans run4) hx).mono ?_)
    have : cap2 ≤ max cap (max 8 (2 * (len0 + 1))) := hc2
    have : cap4 ≤ max cap2 (max 8 (2 * (len0 + 1 + n4))) := hc4
    have := hf4.str.lt
    omega
  have hst5 : ∀ c, S0 ≤ c → c < S1 → μ5.writable c = true := H5.st
  -- entry 31
  obtain ⟨ω6, μ6, run6, f0, f1, f5, f6, f7, f8, f9, s16', fr6, rd6, wr6⟩ := a8_e31 (p := p) (P := P) (R := R)
    x5 ω5 μ5 (sp - 48) a ⟨by omega, by omega⟩ e1 e5 e6 (by omega) (fun c h1 h2 => hst5 c (by omega) (by omega))
  have k6 : ∀ c, c < 4294967296 → ¬ (sp - 48 + 16 ≤ c ∧ c < sp - 48 + 24) → μ6.read c = μ5.read c :=
    fun c h1 h2 => fr6 c h1 (by omega)
  have H6 : HeapCtx env pb S0 S1 μ6 s5 := ctx_hi H5 (fun c hc => k6 c (by omega) (by omega)) wr6
  have K6 : Keeps pb (sp - 48) (a8E (sp - 48) W) sA μ5 μ6 s5 :=
    Keeps.of_frame (Z := fun c => sp - 48 + 16 ≤ c ∧ c < sp - 48 + 24) hf5.str.base
      (fun c hc hz => k6 c hc hz) rd6 wr6 (fun c hz => hst5 c (by omega) (by omega))
      (fun c hz h => Or.inr ⟨by omega, by omega⟩) (fun c hz hg => by unfold Glob at hg; omega)
      (fun c hc hu b hb => by
        have := chunk_bounds H5.wf (hf5.str.base c hc hu)
        have := H5.hbT
        unfold InData at hb; omega)
  have hf6 : Fmtr sA s5 μ6 F W cap5 (len0 + 1 + n4 + n5) := hf5.congr (fun j hj => k6 _ (by omega) (by omega))
    (fun j hj => k6 _ (by omega) (by omega)) (fun c h1 h2 => ⟨k6 c (by omega) (by omega), rd6 c⟩)
  have K35 := ((K3.trans' K4').trans' K5).trans' K6
  simp only [Nat.max_self] at K35
  have KA6 : Keeps pb spA (fun _ => False) sA μA μ6 s5 := by
    have := KA2.trans' (K35.lift (sp' := spA) (by omega) (fun c h hc => by unfold a8E at h; omega))
    rwa [Nat.max_self] at this
  have hd6 : DL μ6 (sp - 48) F 1 :=
    ⟨by rw [show sp - 48 = sp - 48 + 0 by rfl, rdN_frame (fun j hj => k6 _ (by omega) (by omega))]; exact hd5.fm,
      by rw [rdN_frame (fun j hj => k6 _ (by omega) (by omega))]; exact hd5.ok,
      by rw [rdN_frame (fun j hj => k6 _ (by omega) (by omega))]; exact hd5.has⟩
  have rvt6 : rdN μ6 (75976 + 24) 8 = 1788 := by
    rw [rdN_frame (fun j hj => KA6.ro _ (by omega) (Or.inl (by unfold pageSize; omega))
      (by rw [← (KA6.access _ (Or.inl (by unfold pageSize; omega))).2]; exact H6.ro _ (by omega)))]
    exact hrvt
  rcases debug_entry (p := p) (P := P) (R := R) env pb S0 S1 600 (Nat.le_refl _) HA HR μA sA spA 37527 (a + 31)
      3 2300 1788 (ref_u8_ok env pb S0 S1 HA HR μA sA spA (a + 31) hS (helts 31 (by omega)))
      x5 ω6 μ6 s5 (sp - 48) F W (sp - 48) (sp - 48 + 16) 75976 cap5 (len0 + 1 + n4 + n5) 1882 38631
      (a + 31) 75976 1 H6 (hb5 ▸ hb4 ▸ hb2 ▸ hba) hf6 KA6 hd6 (Or.inr rfl) f0 (f1.trans e1) f5 (f6.trans e6) f7 f8 f9
      ⟨by omega, by omega⟩ ⟨by decide, by decide⟩ rvt6 (by decide) jte_893 bs_37527 s16'
      ⟨by omega, by omega, by omega⟩ jte_940 bs_38631 ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega⟩
      ⟨by omega, hW.2⟩ ⟨by omega, hF.2.1, hF.2.2⟩ ⟨by omega, by omega, Or.inl (by omega), Or.inl (by omega)⟩
      ⟨by omega, by omega, Or.inl (by omega)⟩ (by omega) with
    ⟨ω7, μ7, x7, s7, cap7, n7, hn7, run7, H7, hb7, hf7, hc7, hc8, hd7, K7, g0, g1, g5, g6⟩ | hx
  rotate_left
  · refine Or.inr ((Exhausts.pre (((((run1.trans run2).trans run3).trans run4).trans run5).trans run6) hx).mono ?_)
    have : cap2 ≤ max cap (max 8 (2 * (len0 + 1))) := hc2
    have : cap4 ≤ max cap2 (max 8 (2 * (len0 + 1 + n4))) := hc4
    have : cap5 ≤ max cap4 (max 8 (2 * (len0 + 1 + n4 + n5))) := hc6
    have := hf5.str.lt
    omega
  -- finish: "]"
  obtain ⟨ω8, run8, i0, i1, i5, i6, i7⟩ := a8_f (p := p) (P := P) (R := R) x7 ω7 μ7 (sp - 48) ⟨by omega, by omega⟩
    g1
  rcases debug_finish (p := p) (P := P) (R := R) env pb S0 S1 HA HR x7 ω8 μ7 sA s7 (sp - 48) F W (sp - 48)
      cap7 (len0 + 1 + n4 + n5 + n7) 1884 38639 (a + 31) 1 H7 (hb7 ▸ hb5 ▸ hb4 ▸ hb2 ▸ hba) hf7 hd7 i0
      (i1.trans g1) (i5.trans g5) i7 (by omega) (by decide) jte_941 bs_38639
      ⟨by omega, by omega, by omega⟩ ⟨by omega, hW.2⟩ ⟨by omega, hF.2.1, hF.2.2⟩
      ⟨by omega, by omega, Or.inl (by omega), Or.inl (by omega)⟩ (by omega) with
    ⟨ω9, μ9, x9, s9, cap9, run9, H9, hb9, hf9, hc9, hc10, K9, j0, j1, j5, j6, j7⟩ | hx
  rotate_left
  · refine Or.inr ((Exhausts.pre ((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans
      (run7.trans run8)) hx).mono ?_)
    have : cap2 ≤ max cap (max 8 (2 * (len0 + 1))) := hc2
    have : cap4 ≤ max cap2 (max 8 (2 * (len0 + 1 + n4))) := hc4
    have : cap5 ≤ max cap4 (max 8 (2 * (len0 + 1 + n4 + n5))) := hc6
    have : cap7 ≤ max cap5 (max 8 (2 * (len0 + 1 + n4 + n5 + n7))) := hc8
    have := hf7.str.lt
    omega
  have hst9 : ∀ c, S0 ≤ c → c < S1 → μ9.writable c = true := H9.st
  -- the saved words, T + 24 … T + 48, kept since 38012
  have K79 := K7.trans' K9
  simp only [Nat.max_self] at K79
  have kk : ∀ o, 24 ≤ o → o + 8 ≤ 48 → rdN μ9 (sp - 48 + o) 8 = rdN μ1 (sp - 48 + o) 8 := fun o h1 h2 =>
    rdN_frame (fun j hj => by
      rw [K79.hi _ (by omega) (by omega) (by unfold dlE; omega),
        K35.hi _ (by omega) (by omega) (by unfold a8E; omega), kT2 _ (by omega) (by omega)])
  obtain ⟨ω10, run10, l0, l1, l5, l6, l7⟩ := a8_r (p := p) (P := P) (R := R) x9 ω9 μ9 (sp - 48) ret t v5 v6
    ⟨by omega, by omega⟩ j1 ((kk 40 (by omega) (by omega)).trans s40) ((kk 32 (by omega) (by omega)).trans s32)
    ((kk 24 (by omega) (by omega)).trans s24) hret hjt hbt
    (fun c h1 h2 => Memory.readable_of_writable (hst9 c (by omega) (by omega)))
  have K := ((K1.trans' K2').trans' (K35.lift (sp' := sp) (by omega)
    (fun c h hc => by unfold a8E at h; omega))).trans'
    (K79.lift (sp' := sp) (by omega) (fun c h hc => by unfold dlE at h; omega))
  simp only [Nat.max_self] at K
  refine Or.inl ⟨ω10, μ9, x9, s9, cap9, 1 + n4 + n5 + n7 + 1, by omega,
    (((((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8).trans
      run9).trans run10).mono ?_, H9, hb9.trans (hb7.trans (hb5.trans (hb4.trans hb2))),
    by rwa [show len0 + (1 + n4 + n5 + n7 + 1) = len0 + 1 + n4 + n5 + n7 + 1 by omega], by omega, ?_, K, l0,
    by rw [l1]; congr 1; omega, l5, l6, l7.trans j7⟩
  · have : cap2 ≤ max cap (max 8 (2 * (len0 + 1))) := hc2
    omega
  · rw [show len0 + (1 + n4 + n5 + n7 + 1) = len0 + 1 + n4 + n5 + n7 + 1 by omega]
    have : cap2 ≤ max cap (max 8 (2 * (len0 + 1))) := hc2
    have : cap4 ≤ max cap2 (max 8 (2 * (len0 + 1 + n4))) := hc4
    have : cap5 ≤ max cap4 (max 8 (2 * (len0 + 1 + n4 + n5))) := hc6
    have : cap7 ≤ max cap5 (max 8 (2 * (len0 + 1 + n4 + n5 + n7))) := hc8
    have : cap9 ≤ max cap7 (max 8 (2 * (len0 + 1 + n4 + n5 + n7 + 1))) := hc10
    omega

end Services.Bootstrap.Fmt
