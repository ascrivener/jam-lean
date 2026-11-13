import Services.Bootstrap.Fmt.DebugTupleSteps
import Services.Bootstrap.Fmt.DebugList

/-!
# `Formatter::debug_tuple_field1_finish` (62471), frame-only, plain options

`debug_tuple1`: `name(field)`: the name (nl > 0 octets of read-only data), `"("`, the field's
`Debug::fmt` (through its vtable, with a slot holding the field's address: `RefOk`), `")"`. Either
`Ok` with the `String` at most nl + M + 2 octets longer (the text not stated), the allocator's
context kept, and from sp up only the `String` changed; or a failed allocator call.
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- The flags octet of plain options is 0 (no `{:#?}`). -/
theorem Fmtr.flags {s₀ s : State} {μ : Memory} {F W cap len : Nat} (hf : Fmtr s₀ s μ F W cap len) :
    rdN μ (F + 18) 1 = 0 := by
  have e1 : rdN μ (F + 16) 4 = rdN μ (F + 16) 2 + 65536 * rdN μ (F + 18) 2 := by
    have := rdN_add μ (F + 16) 2 2; simpa [show F + 16 + 2 = F + 18 by omega] using this
  have e2 : rdN μ (F + 18) 2 = rdN μ (F + 18) 1 + 256 * rdN μ (F + 19) 1 := by
    have := rdN_add μ (F + 18) 1 1; simpa [show F + 18 + 1 = F + 19 by omega] using this
  have l1 : rdN μ (F + 16) 2 < 65536 := by simpa using rdN_lt μ (F + 16) 2
  have l2 : rdN μ (F + 18) 1 < 256 := by simpa using rdN_lt μ (F + 18) 1
  have := hf.opts
  omega

/-- A `String` write's frame (`Keeps` from T with only W changed), with the `Formatter` and the
    frame words at T … T + 128 other than those written, carried along. -/
theorem keepT {pb S0 S1 T W : Nat} {env : RefineHost.Env} {s₀ s s' : State} {μ μ' : Memory}
    (K : Keeps pb T (fun a => W ≤ a ∧ a < W + 24) s₀ μ μ' s') (H : HeapCtx env pb S0 S1 μ' s')
    (hW : T + 128 ≤ W) : ∀ o, o + 8 ≤ 128 → rdN μ' (T + o) 8 = rdN μ (T + o) 8 := fun o ho =>
  rdN_frame (fun j hj => K.hi _ (by omega) (by have := H.hS1; omega) (by omega))

theorem debug_tuple1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA e a M C fn : Nat) (hR : RefOk p P R env pb S0 S1 μA sA spA e a M C)
    (x : X) (ω : Regs) (μ : Memory) (s : State) (sp F W nm nl v vt cap len ret t v5 v6 : Nat)
    (H : HeapCtx env pb S0 S1 μ s) (hba : s.base % 8 = 0) (hf : Fmtr sA s μ F W cap len)
    (KA : Keeps pb spA (fun _ => False) sA μA μ s)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat F) (h8 : ω[8] = UInt64.ofNat nm)
    (h9 : ω[9] = UInt64.ofNat nl) (h10 : ω[10] = UInt64.ofNat v) (h11 : ω[11] = UInt64.ofNat vt)
    (hv5 : v5 < 18446744073709551616 ∧ v6 < 18446744073709551616)
    (hnm : 65536 ≤ nm ∧ nm + nl + 24 ≤ 196608 ∧ 0 < nl)
    (hvt : 65536 ≤ vt ∧ vt + 32 ≤ 77144) (rfn : rdN μ (vt + 24) 8 = fn)
    (hfn : 0 < fn ∧ fn ≤ 2806 ∧ fn % 2 = 0) (hje : P.jumpTable.getD (fn / 2 - 1) 0 = e)
    (hbe : P.isBlockStart e = true) (hslot : rdN μ v 8 = a)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hsp : S0 + 728 ≤ sp ∧ sp % 8 = 0 ∧ 2147484376 ≤ sp) (hA : sp ≤ spA ∧ W + 24 ≤ spA)
    (hW : sp ≤ W ∧ W + 24 ≤ S1)
    (hF : sp ≤ F ∧ F + 24 ≤ S1 ∧ (F + 24 ≤ W ∨ W + 24 ≤ F))
    (hv : sp ≤ v ∧ v + 8 ≤ S1 ∧ (v + 8 ≤ W ∨ W + 24 ≤ v)) (hn : len + nl + M + 2 < 134217728) :
    (∃ ω' μ' x' s' cap' n, n ≤ nl + M + 2 ∧
      FreeStepsH p R 62471 ω μ x t ω' μ' x' (7 * n + 2 * (cap' - cap) + C + 6100) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Fmtr sA s' μ' F W cap' (len + n) ∧ cap ≤ cap' ∧
      cap' ≤ max cap (max 8 (2 * (len + n))) ∧
      Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) sA μ μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0) ∨
    Exhausts p R pb 62471 ω μ x (1610612736 + 7 * (nl + M) + C + 6200) := by
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  have hcap := hf.str.lt
  -- the name
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, s120, s112, s104, s8, s24, s32, s40, fr1, rd1, wr1⟩ :=
    dt_a (p := p) (P := P) (R := R) x ω μ sp F W nm nl v vt ret v5 v6 ⟨by omega, by omega⟩ h0 h1 h5 h6 h7 h8 h9
      h10 h11 ⟨by omega, hv5.1, hv5.2, by omega, by omega, by omega, by omega, by omega⟩ (Or.inr hF.1) hf.buf hf.vt
      hf.vws (fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)))
      (fun a h1 h2 => hf.vrd a (by omega) (by omega)) (fun a h1 h2 => hst a (by omega) (by omega))
  have k1 : ∀ a, a < 4294967296 → (a < sp - 128 ∨ sp ≤ a) → μ1.read a = μ.read a := fr1
  have H1 : HeapCtx env pb S0 S1 μ1 s := ctx_hi H (fun a ha => k1 a (by omega) (Or.inl (by omega))) wr1
  have K1 : Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) sA μ μ1 s :=
    Keeps.of_frame (Z := fun a => sp - 128 ≤ a ∧ a < sp) hf.str.base
      (fun a ha hz => k1 a ha (by omega)) rd1 wr1 (fun a hz => hst a (by omega) (by omega))
      (fun a hz h => by omega) (fun a hz hg => by unfold Glob at hg; omega)
      (fun c hc hu a ha => by
        have := chunk_bounds H.wf (hf.str.base c hc hu)
        have := H.hbT
        unfold InData at ha; omega)
  have hf1 : Fmtr sA s μ1 F W cap len := hf.congr (fun j hj => k1 _ (by omega) (Or.inr (by omega)))
    (fun j hj => k1 _ (by omega) (Or.inr (by omega))) (fun a h1 h2 => ⟨k1 a (by omega) (Or.inl (by omega)), rd1 a⟩)
  rcases write_str (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω1 μ1 sA s (sp - 128) W nm nl cap len 2646
      62513 2596 F H1 hba hf1.str a0 a1 a5 a6 a7 a8 a9 ⟨by omega, by omega⟩ (by decide) jte_1322 bs_62513
      ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (Or.inl ⟨by omega, by omega⟩)
      (fun a h1 h2 => by rw [rd1]; exact hf.vrd a (by omega) (by omega)) with
    ⟨ω2, μ2, x2, s2, cap2, run2, H2, hb2, hs2, hc1, hc2, K2, b0, b1, b5, b6, b7⟩ | hx
  rotate_left
  · exact Or.inr ((Exhausts.pre run1 hx).mono (by omega))
  have kk2 := keepT K2 H2 (by omega)
  have K12 := K1.trans' (K2.lift (sp' := sp) (by omega) (fun a h _ => h))
  rw [Nat.max_self] at K12
  have hf2 : Fmtr sA s2 μ2 F W cap2 (len + nl) := Fmtr.of_keeps hf H K12 ⟨hF.1, by omega⟩ (fun a h1 h2 h => by omega) hs2
  have hst2 : ∀ a, S0 ≤ a → a < S1 → μ2.writable a = true := H2.st
  -- "("
  obtain ⟨ω3, μ3, run3, c0, c1, c5, c6, c7, c8, c9, sF, fr3, rd3, wr3⟩ := dt_b (p := p) (P := P) (R := R) x2 ω2 μ2
    (sp - 128) F W ⟨by omega, by omega⟩ b1 b5 b6 b7 ⟨by omega, Or.inr (by omega)⟩ hf2.flags
    ((kk2 40 (by omega)).trans s40) (fun a h1 h2 => Memory.readable_of_writable (hst2 a (by omega) (by omega)))
    (fun a h1 h2 => hst2 a (by omega) (by omega))
  have k3 : ∀ a, a < 4294967296 → (a < sp - 128 ∨ sp - 128 + 8 ≤ a) → μ3.read a = μ2.read a := fr3
  have H3 : HeapCtx env pb S0 S1 μ3 s2 := ctx_hi H2 (fun a ha => k3 a (by omega) (Or.inl (by omega))) wr3
  have hs3 : Str sA s2 μ3 W cap2 (len + nl) := (hf2.congr (fun j hj => k3 _ (by omega) (Or.inr (by omega)))
    (fun j hj => k3 _ (by omega) (Or.inr (by omega)))
    (fun a h1 h2 => ⟨k3 a (by omega) (Or.inl (by omega)), rd3 a⟩)).str
  have K3 : Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) sA μ2 μ3 s2 :=
    Keeps.of_frame (Z := fun a => sp - 128 ≤ a ∧ a < sp - 128 + 8) hf2.str.base
      (fun a ha hz => k3 a ha (by omega)) rd3 wr3 (fun a hz => hst2 a (by omega) (by omega))
      (fun a hz h => by omega) (fun a hz hg => by unfold Glob at hg; omega)
      (fun c hc hu a ha => by
        have := chunk_bounds H2.wf (hf2.str.base c hc hu)
        have := H2.hbT
        unfold InData at ha; omega)
  rcases write_str (p := p) (P := P) (R := R) env pb S0 S1 HA HR x2 ω3 μ3 sA s2 (sp - 128) W 72815 1 cap2 (len + nl)
      2648 62566 2596 F H3 (hb2 ▸ hba) hs3 c0 (c1.trans b1) (c5.trans b5) (c6.trans b6) c7 c8 c9
      ⟨by omega, by omega⟩ (by decide) jte_1323 bs_62566
      ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (Or.inl ⟨by omega, by omega⟩)
      (fun a h1 h2 => by rw [rd3, (K12.access a (Or.inl (by unfold pageSize; omega))).1]
                         exact hf.vrd a (by omega) (by omega)) with
    ⟨ω4, μ4, x4, s4, cap4, run4, H4, hb4, hs4, hc3, hc4, K4, d0, d1, d5, d6, d7⟩ | hx
  rotate_left
  · refine Or.inr ((Exhausts.pre ((run1.trans run2).trans run3) hx).mono ?_)
    have : cap2 ≤ max cap (max 8 (2 * (len + nl))) := hc2
    omega
  have kk4 := keepT K4 H4 (by omega)
  have hst4 : ∀ a, S0 ≤ a → a < S1 → μ4.writable a = true := H4.st
  have k3' : ∀ o, 8 ≤ o → o + 8 ≤ 128 → rdN μ3 (sp - 128 + o) 8 = rdN μ2 (sp - 128 + o) 8 := fun o h1 h2 =>
    rdN_frame (fun j hj => k3 _ (by omega) (Or.inr (by omega)))
  -- the frame words, from μ1 to μ4
  have w14 : ∀ o, 8 ≤ o → o + 8 ≤ 128 → rdN μ4 (sp - 128 + o) 8 = rdN μ1 (sp - 128 + o) 8 := fun o h1 h2 => by
    rw [kk4 o (by omega), k3' o h1 h2, kk2 o (by omega)]
  have K34 := K3.trans' (K4.lift (sp' := sp) (by omega) (fun a h _ => h))
  rw [Nat.max_self] at K34
  have K14 := K12.trans' K34
  rw [Nat.max_self] at K14
  have hf4 : Fmtr sA s4 μ4 F W cap4 (len + nl + 1) := Fmtr.of_keeps hf H K14 ⟨hF.1, by omega⟩ (fun a h1 h2 h => by omega) hs4
  have KA4 : Keeps pb spA (fun _ => False) sA μA μ4 s4 := by
    have := KA.trans' (K14.lift (sp' := spA) hA.1 (fun a h ha => by omega))
    rwa [Nat.max_self] at this
  have rF4 : rdN μ4 (sp - 128) 8 = F := by
    rw [show sp - 128 = sp - 128 + 0 by rfl, kk4 0 (by omega)]; exact sF
  have hro4 : ∀ a, a < 196608 → μ4.read a = μ.read a := fun a ha =>
    K14.ro a (by omega) (Or.inl (by unfold pageSize; omega)) (H.ro a ha)
  have rfn4 : rdN μ4 (vt + 24) 8 = fn := by rw [rdN_frame (fun j hj => hro4 _ (by omega))]; exact rfn
  -- the field
  obtain ⟨ω5, run5, e0, e1, e5, e6, e7, e8⟩ := dt_c (p := p) (P := P) (R := R) x4 ω4 μ4 (sp - 128) F v vt fn e
    ⟨by omega, by omega⟩ d1 d7 rF4 ((w14 24 (by omega) (by omega)).trans s24)
    ((w14 32 (by omega) (by omega)).trans s32) rfn4 (by omega) hfn hje hbe
    (fun a h1 h2 => Memory.readable_of_writable (hst4 a (by omega) (by omega)))
    (fun a h1 h2 => by rw [(K14.access a (Or.inl (by unfold pageSize; omega))).1]; exact hf.vrd a (by omega) (by omega))
  have hslot4 : rdN μ4 v 8 = a := by
    rw [rdN_frame (fun j hj => K14.hi _ (by omega) (by omega) (by omega))]; exact hslot
  rcases hR ω5 μ4 x4 s4 (sp - 128) F W cap4 (len + nl + 1) 2650 62588 F (ω5[6].toNat) v H4 (hb4 ▸ hb2 ▸ hba) KA4
      hf4 e0 (e1.trans d1) e5 (by simp) e7 e8 (by omega) (UInt64.toNat_lt _) (by decide) jte_1324 bs_62588
      ⟨by omega, by omega, by omega⟩ (by omega) ⟨by omega, by omega⟩ hA.2 ⟨by omega, hF.2.1, hF.2.2⟩ (by omega)
      ⟨by omega, hv.2.1, hv.2.2⟩ hslot4 with
    ⟨ω6, μ6, x6, s6, cap6, n6, hn6, run6, H6, hb6, hf6, hc5, hc6, K6, g0, g1, g5, g6, g7⟩ | hx
  rotate_left
  · refine Or.inr ((Exhausts.pre ((((run1.trans run2).trans run3).trans run4).trans run5) hx).mono ?_)
    have : cap2 ≤ max cap (max 8 (2 * (len + nl))) := hc2
    have : cap4 ≤ max cap2 (max 8 (2 * (len + nl + 1))) := hc4
    have := hs4.lt
    omega
  have kk6 := keepT K6 H6 (by omega)
  have hst6 : ∀ a, S0 ≤ a → a < S1 → μ6.writable a = true := H6.st
  -- ")"
  obtain ⟨ω7, run7, i0, i1, i5, i6, i7, i8, i9⟩ := dt_d (p := p) (P := P) (R := R) x6 ω6 μ6 (sp - 128) F W nl
    ⟨by omega, by omega⟩ g1 g5 g7 (by omega) ((kk6 8 (by omega)).trans ((w14 8 (by omega) (by omega)).trans s8))
    (by omega) hf6.buf hf6.vt hf6.vws (fun a h1 h2 => Memory.readable_of_writable (hst6 a (by omega) (by omega)))
    (fun a h1 h2 => Memory.readable_of_writable (hst6 a (by omega) (by omega)))
    (fun a h1 h2 => hf6.vrd a (by omega) (by omega))
  rcases write_str (p := p) (P := P) (R := R) env pb S0 S1 HA HR x6 ω7 μ6 sA s6 (sp - 128) W 72824 1 cap6
      (len + nl + 1 + n6) 2660 62801 F (ω5[6].toNat) H6 (hb6 ▸ hb4 ▸ hb2 ▸ hba) hf6.str i0 (i1.trans g1)
      (i5.trans g5) (i6.trans g6) i7 i8 i9 ⟨by omega, UInt64.toNat_lt _⟩ (by decide) jte_1329 bs_62801
      ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (Or.inl ⟨by omega, by omega⟩)
      (fun a h1 h2 => hf6.vrd a (by omega) (by omega)) with
    ⟨ω8, μ8, x8, s8, cap8, run8, H8, hb8, hs8, hc7, hc8, K8, j0, j1, j5, j6, j7⟩ | hx
  rotate_left
  · refine Or.inr ((Exhausts.pre ((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7)
      hx).mono ?_)
    have : cap2 ≤ max cap (max 8 (2 * (len + nl))) := hc2
    have : cap4 ≤ max cap2 (max 8 (2 * (len + nl + 1))) := hc4
    have := hs8.lt
    have := hf6.str.lt
    omega
  have kk8 := keepT K8 H8 (by omega)
  have hst8 : ∀ a, S0 ≤ a → a < S1 → μ8.writable a = true := H8.st
  have w18 : ∀ o, 8 ≤ o → o + 8 ≤ 128 → rdN μ8 (sp - 128 + o) 8 = rdN μ1 (sp - 128 + o) 8 := fun o h1 h2 => by
    rw [kk8 o (by omega), kk6 o (by omega), w14 o h1 h2]
  obtain ⟨ω9, run9, m0, m1, m5, m6, m7⟩ := dt_e (p := p) (P := P) (R := R) x8 ω8 μ8 (sp - 128) ret t v5 v6
    ⟨by omega, by omega⟩ j1 ((w18 120 (by omega) (by omega)).trans s120)
    ((w18 112 (by omega) (by omega)).trans s112) ((w18 104 (by omega) (by omega)).trans s104) hret hjt hbt
    (fun a h1 h2 => Memory.readable_of_writable (hst8 a (by omega) (by omega)))
  have K := (K14.trans' (K6.lift (sp' := sp) (by omega) (fun a h _ => h))).trans'
    (K8.lift (sp' := sp) (by omega) (fun a h _ => h))
  simp only [Nat.max_self] at K
  have hf8 : Fmtr sA s8 μ8 F W cap8 (len + nl + 1 + n6 + 1) :=
    Fmtr.of_keeps hf H K ⟨hF.1, by omega⟩ (fun a h1 h2 h => by omega) hs8
  refine Or.inl ⟨ω9, μ8, x8, s8, cap8, nl + n6 + 2, by omega,
    ((((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8).trans
      run9).mono ?_, H8, hb8.trans (hb6.trans (hb4.trans hb2)), ?_, by omega, ?_, K, m0,
    by rw [m1]; congr 1; omega, m5, m6, m7.trans j7⟩
  · omega
  · rwa [show len + (nl + n6 + 2) = len + nl + 1 + n6 + 1 by omega]
  · rw [show len + (nl + n6 + 2) = len + nl + 1 + n6 + 1 by omega]
    have : cap2 ≤ max cap (max 8 (2 * (len + nl))) := hc2
    have : cap4 ≤ max cap2 (max 8 (2 * (len + nl + 1))) := hc4
    omega

end Services.Bootstrap.Fmt
