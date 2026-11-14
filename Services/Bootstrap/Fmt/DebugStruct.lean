import Services.Bootstrap.Fmt.DebugStructSteps
import Services.Bootstrap.Fmt.DebugTuple

/-!
# `DebugStruct::field` (65057), frame-only, plain options

`debug_field`: on a `DebugStruct` at D (laid out as a `DebugList`, `DL`) with h ∈ {0, 1} fields
written, a field named by nl octets of read-only data at nm, with ω₁₀ the address v of a slot
the value's address v (as `ArgOk` states it: the value itself, or a slot holding its address, see
`RefOk.toArgOk`) and ω₁₁ its `Debug` vtable vt (`fmt` resolving to e):
`" { "` (h = 0) or `", "`, the name, `": "`, the value. The struct then has a field. At most
nl + M + 5 octets; the text is not stated.
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- A `String` write's frame carried along: the words at T … T + 112 (W at or above T + 112). -/
theorem keepT112 {pb S0 S1 T W : Nat} {env : RefineHost.Env} {s₀ s' : State} {μ μ' : Memory}
    (K : Keeps pb T (fun a => W ≤ a ∧ a < W + 24) s₀ μ μ' s') (H : HeapCtx env pb S0 S1 μ' s')
    (hW : T + 112 ≤ W ∧ W < 4294967296) : ∀ o, o + 8 ≤ 112 → rdN μ' (T + o) 8 = rdN μ (T + o) 8 := fun o ho =>
  rdN_frame (fun j hj => K.hi _ (by omega) (by omega) (by omega))

/-- **A field reached through a slot** (`RefOk`): an `ArgOk` at the slot v, for a slot at or above
    spA holding the field's address a in the caller's memory. -/
theorem RefOk.toArgOk {p : ByteArray} {P : Program} {env : RefineHost.Env} {pb S0 S1 Z : Nat} {μA : Memory}
    {sA : State} {spA e a M C v : Nat} (h : RefOk p P R env pb S0 S1 Z μA sA spA e a M C)
    (hv : spA ≤ v ∧ v + 8 ≤ S1) (ra : rdN μA v 8 = a) : ArgOk p P R env pb S0 S1 Z μA sA spA e v M C := by
  intro ω μ x s sp F W cap len ret t v5 v6 H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hWA hF hn
  have := H.hS1
  exact h ω μ x s sp F W cap len ret t v5 v6 v H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hWA hF
    hn ⟨by omega, hv.2, Or.inr (by omega)⟩ (by rw [rdN_frame (fun j hj => K.hi _ (by omega) (by omega) id)]; exact ra)

/-- **`DebugStruct::field`** (65057, plain options). -/
theorem debug_field {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 Z : Nat) (hZ : 600 ≤ Z) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA e M C fn : Nat) (x : X) (ω : Regs) (μ : Memory) (s : State)
    (sp F W D nm nl v vt cap len ret t v5 v6 h : Nat) (hV : ArgOk p P R env pb S0 S1 Z μA sA spA e v M C)
    (H : HeapCtx env pb S0 S1 μ s) (hba : s.base % 8 = 0) (hf : Fmtr sA s μ F W cap len)
    (KA : Keeps pb spA (fun _ => False) sA μA μ s) (hd : DL μ D F h) (hh : h = 0 ∨ h = 1)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat D) (h8 : ω[8] = UInt64.ofNat nm)
    (h9 : ω[9] = UInt64.ofNat nl) (h10 : ω[10] = UInt64.ofNat v) (h11 : ω[11] = UInt64.ofNat vt)
    (hv5 : v5 < 18446744073709551616 ∧ v6 < 18446744073709551616)
    (hnm : 65536 ≤ nm ∧ nm + nl + 24 ≤ 77144)
    (hvt : 65536 ≤ vt ∧ vt + 32 ≤ 77144) (rfn : rdN μ (vt + 24) 8 = fn)
    (hfn : 0 < fn ∧ fn ≤ 2806 ∧ fn % 2 = 0) (hje : P.jumpTable.getD (fn / 2 - 1) 0 = e)
    (hbe : P.isBlockStart e = true)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hsp : S0 + Z + 112 ≤ sp ∧ sp % 8 = 0 ∧ 2147483648 + Z + 112 ≤ sp) (hA : sp ≤ spA ∧ W + 24 ≤ spA ∧ D + 24 ≤ spA)
    (hW : sp ≤ W ∧ W + 24 ≤ S1)
    (hF : sp ≤ F ∧ F + 24 ≤ S1 ∧ (F + 24 ≤ W ∨ W + 24 ≤ F))
    (hD : sp ≤ D ∧ D + 24 ≤ S1 ∧ (D + 24 ≤ W ∨ W + 24 ≤ D) ∧ (D + 24 ≤ F ∨ F + 24 ≤ D))
    (hvv : v < 18446744073709551616) (hn : len + nl + M + 5 < 134217728) :
    (∃ ω' μ' x' s' cap' n, n ≤ nl + M + 5 ∧
      FreeStepsH p R 65057 ω μ x t ω' μ' x' (7 * n + 2 * (cap' - cap) + C + 6200) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Fmtr sA s' μ' F W cap' (len + n) ∧ cap ≤ cap' ∧
      cap' ≤ max cap (max 8 (2 * (len + n))) ∧ DL μ' D F 1 ∧
      Keeps pb sp (dlE W D) sA μ μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat D) ∨
    Exhausts p R pb 65057 ω μ x (1610612736 + 7 * (nl + M) + C + 6400) := by
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  have hcap := hf.str.lt
  have hhl : h ≤ 1 := by omega
  -- the prefix
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, s104, s96, s88, s16, s24, s8, s0, fr1, rd1, wr1⟩ :=
    ds_a (p := p) (P := P) (R := R) x ω μ sp D F W nm nl v vt h ret v5 v6 ⟨by omega, by omega⟩ h0 h1 h5 h6 h7
      h8 h9 h10 h11 ⟨by omega, hv5.1, hv5.2, by omega, by omega, by omega, by omega, by omega, by omega⟩
      ⟨Or.inr hD.1, Or.inr hF.1⟩ hh hd.fm hd.ok hd.has hf.flags hf.buf hf.vt hf.vws
      (fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)))
      (fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)))
      (fun a h1 h2 => hf.vrd a (by omega) (by omega)) (fun a h1 h2 => hst a (by omega) (by omega))
  have k1 : ∀ a, a < 4294967296 → (a < sp - 112 ∨ sp ≤ a) → μ1.read a = μ.read a := fr1
  have H1 : HeapCtx env pb S0 S1 μ1 s := ctx_hi H (fun a ha => k1 a (by omega) (Or.inl (by omega))) wr1
  have K1 : Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) sA μ μ1 s :=
    Keeps.of_frame (Z := fun a => sp - 112 ≤ a ∧ a < sp) hf.str.base
      (fun a ha hz => k1 a ha (by omega)) rd1 wr1 (fun a hz => hst a (by omega) (by omega))
      (fun a hz h => by omega) (fun a hz hg => by unfold Glob at hg; omega)
      (fun c hc hu a ha => by
        have := chunk_bounds H.wf (hf.str.base c hc hu)
        have := H.hbT
        unfold InData at ha; omega)
  have hf1 : Fmtr sA s μ1 F W cap len := hf.congr (fun j hj => k1 _ (by omega) (Or.inr (by omega)))
    (fun j hj => k1 _ (by omega) (Or.inr (by omega))) (fun a h1 h2 => ⟨k1 a (by omega) (Or.inl (by omega)), rd1 a⟩)
  rcases write_str (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω1 μ1 sA s (sp - 112) W (72803 + 3 * h) (3 - h)
      cap len 2738 65148 D nm H1 hba hf1.str a0 a1 a5 a6 a7 a8 a9 ⟨by omega, by omega⟩ (by decide) jte_1368
      bs_65148 ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (Or.inl ⟨by omega, by omega⟩)
      (fun a h1 h2 => hf1.vrd a (by omega) (by omega)) with
    ⟨ω2, μ2, x2, s2, cap2, run2, H2, hb2, hs2, hc1, hc2, K2, b0, b1, b5, b6, b7⟩ | hx
  rotate_left
  · exact Or.inr ((Exhausts.pre run1 hx).mono (by omega))
  have kk2 := keepT112 K2 H2 ⟨by omega, by omega⟩
  have K12 := K1.trans' (K2.lift (sp' := sp) (by omega) (fun a h _ => h))
  rw [Nat.max_self] at K12
  have hf2 : Fmtr sA s2 μ2 F W cap2 (len + (3 - h)) :=
    Fmtr.of_keeps hf H K12 ⟨hF.1, by omega⟩ (fun a h1 h2 h => by omega) hs2
  have hst2 : ∀ a, S0 ≤ a → a < S1 → μ2.writable a = true := H2.st
  -- the name
  obtain ⟨ω3, run3, c0, c1, c5, c7, c8, c9⟩ := ds_b (p := p) (P := P) (R := R) x2 ω2 μ2 (sp - 112) D F W nm nl
    ⟨by omega, by omega⟩ b1 b5 b6 b7 ⟨by omega, by omega⟩ ((kk2 0 (by omega)).trans s0)
    ((kk2 8 (by omega)).trans s8) hf2.buf hf2.vt hf2.vws
    (fun a h1 h2 => Memory.readable_of_writable (hst2 a (by omega) (by omega)))
    (fun a h1 h2 => Memory.readable_of_writable (hst2 a (by omega) (by omega)))
    (fun a h1 h2 => hf2.vrd a (by omega) (by omega))
  rcases write_str (p := p) (P := P) (R := R) env pb S0 S1 HA HR x2 ω3 μ2 sA s2 (sp - 112) W nm nl cap2
      (len + (3 - h)) 2740 65179 D (ω3[6].toNat) H2 (hb2 ▸ hba) hf2.str c0 c1 c5 (by simp)
      c7 c8 c9 ⟨by omega, UInt64.toNat_lt _⟩ (by decide) jte_1369 bs_65179
      ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (Or.inl ⟨by omega, by omega⟩)
      (fun a h1 h2 => hf2.vrd a (by omega) (by omega)) with
    ⟨ω4, μ4, x4, s4, cap4, run4, H4, hb4, hs4, hc3, hc4, K4, d0, d1, d5, d6, d7⟩ | hx
  rotate_left
  · refine Or.inr ((Exhausts.pre ((run1.trans run2).trans run3) hx).mono ?_)
    have : cap2 ≤ max cap (max 8 (2 * (len + (3 - h)))) := hc2
    omega
  have kk4 := keepT112 K4 H4 ⟨by omega, by omega⟩
  have K14 := K12.trans' (K4.lift (sp' := sp) (by omega) (fun a h _ => h))
  rw [Nat.max_self] at K14
  have hf4 : Fmtr sA s4 μ4 F W cap4 (len + (3 - h) + nl) :=
    Fmtr.of_keeps hf H K14 ⟨hF.1, by omega⟩ (fun a h1 h2 h => by omega) hs4
  have hst4 : ∀ a, S0 ≤ a → a < S1 → μ4.writable a = true := H4.st
  have w14 : ∀ o, o + 8 ≤ 112 → rdN μ4 (sp - 112 + o) 8 = rdN μ1 (sp - 112 + o) 8 := fun o ho => by
    rw [kk4 o ho, kk2 o ho]
  -- ": "
  obtain ⟨ω5, run5, e0, e1, e5, e7, e8, e9⟩ := ds_c (p := p) (P := P) (R := R) x4 ω4 μ4 (sp - 112) D F W
    ⟨by omega, by omega⟩ d1 d5 d7 (by omega) ((w14 8 (by omega)).trans s8) hf4.buf hf4.vt hf4.vws
    (fun a h1 h2 => Memory.readable_of_writable (hst4 a (by omega) (by omega)))
    (fun a h1 h2 => Memory.readable_of_writable (hst4 a (by omega) (by omega)))
    (fun a h1 h2 => hf4.vrd a (by omega) (by omega))
  rcases write_str (p := p) (P := P) (R := R) env pb S0 S1 HA HR x4 ω5 μ4 sA s4 (sp - 112) W 72808 2 cap4
      (len + (3 - h) + nl) 2742 65214 D (ω5[6].toNat) H4 (hb4 ▸ hb2 ▸ hba) hf4.str e0 e1 e5
      (by simp) e7 e8 e9 ⟨by omega, UInt64.toNat_lt _⟩ (by decide) jte_1370 bs_65214
      ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (Or.inl ⟨by omega, by omega⟩)
      (fun a h1 h2 => hf4.vrd a (by omega) (by omega)) with
    ⟨ω6, μ6, x6, s6, cap6, run6, H6, hb6, hs6, hc5, hc6, K6, g0, g1, g5, g6, g7⟩ | hx
  rotate_left
  · refine Or.inr ((Exhausts.pre ((((run1.trans run2).trans run3).trans run4).trans run5) hx).mono ?_)
    have : cap2 ≤ max cap (max 8 (2 * (len + (3 - h)))) := hc2
    have : cap4 ≤ max cap2 (max 8 (2 * (len + (3 - h) + nl))) := hc4
    have := hs4.lt
    omega
  have kk6 := keepT112 K6 H6 ⟨by omega, by omega⟩
  have K16 := K14.trans' (K6.lift (sp' := sp) (by omega) (fun a h _ => h))
  rw [Nat.max_self] at K16
  have hf6 : Fmtr sA s6 μ6 F W cap6 (len + (3 - h) + nl + 2) :=
    Fmtr.of_keeps hf H K16 ⟨hF.1, by omega⟩ (fun a h1 h2 h => by omega) hs6
  have hst6 : ∀ a, S0 ≤ a → a < S1 → μ6.writable a = true := H6.st
  have w16 : ∀ o, o + 8 ≤ 112 → rdN μ6 (sp - 112 + o) 8 = rdN μ1 (sp - 112 + o) 8 := fun o ho => by
    rw [kk6 o ho, w14 o ho]
  have KA6 : Keeps pb spA (fun _ => False) sA μA μ6 s6 := by
    have := KA.trans' (K16.lift (sp' := spA) hA.1 (fun a h ha => by omega))
    rwa [Nat.max_self] at this
  have hro6 : ∀ a, a < 196608 → μ6.read a = μ.read a := fun a ha =>
    K16.ro a (by omega) (Or.inl (by unfold pageSize; omega)) (H.ro a ha)
  have rfn6 : rdN μ6 (vt + 24) 8 = fn := by rw [rdN_frame (fun j hj => hro6 _ (by omega))]; exact rfn
  -- the value
  obtain ⟨ω7, run7, i0, i1, i5, i7, i8⟩ := ds_d (p := p) (P := P) (R := R) x6 ω6 μ6 (sp - 112) D F v vt fn e
    ⟨by omega, by omega⟩ g1 g5 g7 (by omega) ((w16 8 (by omega)).trans s8) ((w16 16 (by omega)).trans s16)
    ((w16 24 (by omega)).trans s24) rfn6 hfn hje hbe
    (fun a h1 h2 => Memory.readable_of_writable (hst6 a (by omega) (by omega)))
    (fun a h1 h2 => hf6.vrd a (by omega) (by omega))
  rcases hV ω7 μ6 x6 s6 (sp - 112) F W cap6 (len + (3 - h) + nl + 2) 2744 65242 D (ω7[6].toNat) H6
      (hb6 ▸ hb4 ▸ hb2 ▸ hba) KA6 hf6 i0 i1 i5 (by simp) i7 i8 (by omega) (UInt64.toNat_lt _)
      (by decide) jte_1371 bs_65242 ⟨by omega, by omega, by omega⟩ (by omega) ⟨by omega, by omega⟩ hA.2.1
      ⟨by omega, hF.2.1, hF.2.2⟩ (by omega) with
    ⟨ω8, μ8, x8, s8, cap8, n8, hn8, run8, H8, hb8, hf8, hc7, hc8, K8, j0, j1, j5, j6, j7⟩ | hx
  rotate_left
  · refine Or.inr ((Exhausts.pre ((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7)
      hx).mono ?_)
    have : cap2 ≤ max cap (max 8 (2 * (len + (3 - h)))) := hc2
    have : cap4 ≤ max cap2 (max 8 (2 * (len + (3 - h) + nl))) := hc4
    have : cap6 ≤ max cap4 (max 8 (2 * (len + (3 - h) + nl + 2))) := hc6
    have := hs6.lt
    omega
  have kk8 := keepT112 K8 H8 ⟨by omega, by omega⟩
  have hst8 : ∀ a, S0 ≤ a → a < S1 → μ8.writable a = true := H8.st
  have w18 : ∀ o, o + 8 ≤ 112 → rdN μ8 (sp - 112 + o) 8 = rdN μ1 (sp - 112 + o) 8 := fun o ho => by
    rw [kk8 o ho, w16 o ho]
  -- the result and the return
  obtain ⟨ω9, μ9, run9, m0, m1, m5, m6, m7, mr, mh, fr9, rd9, wr9⟩ := ds_e (p := p) (P := P) (R := R) x8 ω8 μ8
    (sp - 112) D ret t v5 v6 0 ⟨by omega, by omega⟩ j1 j5 j7 (by omega) ⟨by omega, Or.inr (by omega)⟩
    ((w18 104 (by omega)).trans s104) ((w18 96 (by omega)).trans s96) ((w18 88 (by omega)).trans s88) hret hjt hbt
    (fun a h1 h2 => Memory.readable_of_writable (hst8 a (by omega) (by omega)))
    (fun a h1 h2 => hst8 a (by omega) (by omega))
  have K9 : Keeps pb sp (dlE W D) sA μ8 μ9 s8 :=
    Keeps.of_frame (Z := fun a => D + 8 ≤ a ∧ a < D + 10) hf8.str.base
      (fun a ha hz => fr9 a ha (by omega)) rd9 wr9 (fun a hz => hst8 a (by omega) (by omega))
      (fun a hz h => Or.inr ⟨by omega, by omega⟩) (fun a hz hg => by unfold Glob at hg; omega)
      (fun c hc hu a ha => by
        have := chunk_bounds H8.wf (hf8.str.base c hc hu)
        have := H8.hbT
        unfold InData at ha; omega)
  have H9 : HeapCtx env pb S0 S1 μ9 s8 := ctx_hi H8 (fun a ha => fr9 a (by omega) (Or.inl (by omega))) wr9
  have K := (((K16.mono (sp' := sp) (by omega) (fun a h => Or.inl h)).trans'
    (K8.lift (sp' := sp) (by omega) (fun a h _ => Or.inl h))).trans' K9)
  simp only [Nat.max_self] at K
  have hs9 : Str sA s8 μ9 W cap8 (len + (3 - h) + nl + 2 + n8) :=
    hf8.str.update (fun j hj => fr9 _ (by omega) (by omega))
      ((rdN_frame (fun j hj => fr9 _ (by omega) (by omega))).trans hf8.str.rl) hf8.str.le
  have hf9 : Fmtr sA s8 μ9 F W cap8 (len + (3 - h) + nl + 2 + n8) :=
    Fmtr.of_keeps hf8 H8 K9 ⟨hF.1, by omega⟩ (fun a h1 h2 h => by unfold dlE at h; omega) hs9
  have dF : rdN μ9 D 8 = F := by
    rw [show D = D + 0 by rfl, rdN_frame (fun j hj => fr9 _ (by omega) (by omega)),
      rdN_frame (fun j hj => K8.hi _ (by omega) (by omega) (by omega)),
      rdN_frame (fun j hj => K16.hi _ (by omega) (by omega) (by omega))]
    exact hd.fm
  refine Or.inl ⟨ω9, μ9, x8, s8, cap8, (3 - h) + nl + 2 + n8, by omega,
    (((((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8).trans
      run9)).mono ?_, H9, hb8.trans (hb6.trans (hb4.trans hb2)), ?_, by omega, ?_, ⟨dF, mr, mh⟩, K, m0,
    by rw [m1]; congr 1; omega, m5, m6, m7⟩
  · omega
  · rwa [show len + ((3 - h) + nl + 2 + n8) = len + (3 - h) + nl + 2 + n8 by omega]
  · rw [show len + ((3 - h) + nl + 2 + n8) = len + (3 - h) + nl + 2 + n8 by omega]
    have : cap2 ≤ max cap (max 8 (2 * (len + (3 - h)))) := hc2
    have : cap4 ≤ max cap2 (max 8 (2 * (len + (3 - h) + nl))) := hc4
    have : cap6 ≤ max cap4 (max 8 (2 * (len + (3 - h) + nl + 2))) := hc6
    omega

end Services.Bootstrap.Fmt
