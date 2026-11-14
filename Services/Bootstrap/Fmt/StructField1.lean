import Services.Bootstrap.Fmt.StructField1Steps
import Services.Bootstrap.Fmt.DebugStruct

/-!
# `Formatter::debug_struct_field1_finish` (62816), frame-only, plain options

`debug_struct1`: `name { field: value }`. The struct's name is nl > 0 octets of read-only data at
nm, the field's name fnl octets at fnm; the value is passed as v (`ArgOk` at v: the value, or a slot holding
its address, `RefOk.toArgOk`), with its `Debug` vtable vt on the caller's stack (the word at sp)
and its `fmt` resolving to e. At most nl + fnl + M + 7 octets; the text is not stated.
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **`Formatter::debug_struct_field1_finish`** (62816, plain options). -/
theorem debug_struct1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 Z : Nat) (hZ : 600 ≤ Z) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA e M C fn : Nat) (x : X) (ω : Regs) (μ : Memory) (s : State)
    (sp F W nm nl fnm fnl v vt cap len ret t v5 v6 : Nat)
    (hV : FieldOk p P R env pb S0 S1 Z μA sA spA e v M C μ sp W)
    (H : HeapCtx env pb S0 S1 μ s) (hba : s.base % 8 = 0) (hf : Fmtr sA s μ F W cap len)
    (KA : Keeps pb spA (fun _ => False) sA μA μ s)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat F) (h8 : ω[8] = UInt64.ofNat nm)
    (h9 : ω[9] = UInt64.ofNat nl) (h10 : ω[10] = UInt64.ofNat fnm) (h11 : ω[11] = UInt64.ofNat fnl)
    (h12 : ω[12] = UInt64.ofNat v)
    (hv5 : v5 < 18446744073709551616 ∧ v6 < 18446744073709551616)
    (hnm : 65536 ≤ nm ∧ nm + nl + 24 ≤ 77144) (hfnm : 65536 ≤ fnm ∧ fnm + fnl + 24 ≤ 77144)
    (rvt : rdN μ sp 8 = vt)
    (hvt : 65536 ≤ vt ∧ vt + 32 ≤ 77144) (rfn : rdN μ (vt + 24) 8 = fn)
    (hfn : 0 < fn ∧ fn ≤ 2806 ∧ fn % 2 = 0) (hje : P.jumpTable.getD (fn / 2 - 1) 0 = e)
    (hbe : P.isBlockStart e = true)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hsp : S0 + Z + 168 ≤ sp ∧ sp % 8 = 0 ∧ 2147483648 + Z + 168 ≤ sp) (hA : sp ≤ spA ∧ W + 24 ≤ spA)
    (hs8 : sp + 8 ≤ S1) (hW8 : sp + 8 ≤ W)
    (hW : sp ≤ W ∧ W + 24 ≤ S1)
    (hF : sp ≤ F ∧ F + 24 ≤ S1 ∧ (F + 24 ≤ W ∨ W + 24 ≤ F))
    (hvv : v < 18446744073709551616) (hn : len + nl + fnl + M + 7 < 134217728) :
    (∃ ω' μ' x' s' cap' n, n ≤ nl + fnl + M + 7 ∧
      FreeStepsH p R 62816 ω μ x t ω' μ' x' (7 * n + 2 * (cap' - cap) + C + 10400) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Fmtr sA s' μ' F W cap' (len + n) ∧ cap ≤ cap' ∧
      cap' ≤ max cap (max 8 (2 * (len + n))) ∧
      Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) sA μ μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0) ∨
    Exhausts p R pb 62816 ω μ x (2147483648 + 7 * (nl + fnl + M) + C + 10600) := by
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  have hcap := hf.str.lt
  -- the struct's name
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, s48, s40, s32, s8, s0, fr1, rd1, wr1⟩ :=
    sf1_a (p := p) (P := P) (R := R) x ω μ sp F W fnm fnl v ret v5 v6 ⟨by omega, by omega⟩ h0 h1 h5 h6 h7 h10 h11
      h12 ⟨by omega, hv5.1, hv5.2, by omega, by omega, by omega, by omega⟩ (Or.inr hF.1) hf.buf hf.vt hf.vws
      (fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)))
      (fun a h1 h2 => hf.vrd a (by omega) (by omega)) (fun a h1 h2 => hst a (by omega) (by omega))
  have k1 : ∀ a, a < 4294967296 → (a < sp - 56 ∨ sp ≤ a) → μ1.read a = μ.read a := fr1
  have H1 : HeapCtx env pb S0 S1 μ1 s := ctx_hi H (fun a ha => k1 a (by omega) (Or.inl (by omega))) wr1
  have K1 : Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) sA μ μ1 s :=
    Keeps.of_frame (Z := fun a => sp - 56 ≤ a ∧ a < sp) hf.str.base
      (fun a ha hz => k1 a ha (by omega)) rd1 wr1 (fun a hz => hst a (by omega) (by omega))
      (fun a hz h => by omega) (fun a hz hg => by unfold Glob at hg; omega)
      (fun c hc hu a ha => by
        have := chunk_bounds H.wf (hf.str.base c hc hu)
        have := H.hbT
        unfold InData at ha; omega)
  have hf1 : Fmtr sA s μ1 F W cap len := hf.congr (fun j hj => k1 _ (by omega) (Or.inr (by omega)))
    (fun j hj => k1 _ (by omega) (Or.inr (by omega))) (fun a h1 h2 => ⟨k1 a (by omega) (Or.inl (by omega)), rd1 a⟩)
  rcases write_str (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω1 μ1 sA s (sp - 56) W nm nl cap len 2662
      62850 fnm F H1 hba hf1.str a0 a1 a5 a6 a7 (a8.trans h8) (a9.trans h9) ⟨by omega, by omega⟩ (by decide)
      jte_1330 bs_62850 ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (Or.inl ⟨by omega, by omega⟩)
      (fun a h1 h2 => hf1.vrd a (by omega) (by omega)) with
    ⟨ω2, μ2, x2, s2, cap2, run2, H2, hb2, hs2, hc1, hc2, K2, b0, b1, b5, b6, b7⟩ | hx
  rotate_left
  · exact Or.inr ((Exhausts.pre run1 hx).mono (by omega))
  have kk2 : ∀ o, o + 8 ≤ 64 → rdN μ2 (sp - 56 + o) 8 = rdN μ1 (sp - 56 + o) 8 := fun o ho =>
    rdN_frame (fun j hj => K2.hi _ (by omega) (by omega) (by omega))
  have K12 := K1.trans' (K2.lift (sp' := sp) (by omega) (fun a h _ => h))
  rw [Nat.max_self] at K12
  have hf2 : Fmtr sA s2 μ2 F W cap2 (len + nl) :=
    Fmtr.of_keeps hf H K12 ⟨hF.1, by omega⟩ (fun a h1 h2 h => by omega) hs2
  have hst2 : ∀ a, S0 ≤ a → a < S1 → μ2.writable a = true := H2.st
  -- the DebugStruct at T + 16, then the field
  have rvt2 : rdN μ2 (sp - 56 + 56) 8 = vt := by
    rw [kk2 56 (by omega), show sp - 56 + 56 = sp by omega, rdN_frame (fun j hj => k1 _ (by omega) (Or.inr (by omega)))]
    exact rvt
  obtain ⟨ω3, μ3, run3, c0, c1, c5, c6, c7, c8, c9, c10, c11, dF, dr, dh, fr3, rd3, wr3⟩ := sf1_b (p := p) (P := P)
    (R := R) x2 ω2 μ2 (sp - 56) F fnm fnl v vt ⟨by omega, by omega⟩ b1 b5 b6 b7 ⟨by omega, by omega⟩
    ((kk2 0 (by omega)).trans s0) ((kk2 8 (by omega)).trans s8) rvt2
    (fun a h1 h2 => Memory.readable_of_writable (hst2 a (by omega) (by omega)))
    (fun a h1 h2 => hst2 a (by omega) (by omega))
  have k3 : ∀ a, a < 4294967296 → (a < sp - 56 + 16 ∨ sp - 56 + 26 ≤ a) → μ3.read a = μ2.read a := fr3
  have H3 : HeapCtx env pb S0 S1 μ3 s2 := ctx_hi H2 (fun a ha => k3 a (by omega) (Or.inl (by omega))) wr3
  have K3 : Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) sA μ2 μ3 s2 :=
    Keeps.of_frame (Z := fun a => sp - 56 + 16 ≤ a ∧ a < sp - 56 + 26) hf2.str.base
      (fun a ha hz => k3 a ha (by omega)) rd3 wr3 (fun a hz => hst2 a (by omega) (by omega))
      (fun a hz h => by omega) (fun a hz hg => by unfold Glob at hg; omega)
      (fun c hc hu a ha => by
        have := chunk_bounds H2.wf (hf2.str.base c hc hu)
        have := H2.hbT
        unfold InData at ha; omega)
  have K13 := K12.trans' K3
  rw [Nat.max_self] at K13
  have hf3 : Fmtr sA s2 μ3 F W cap2 (len + nl) := hf2.congr (fun j hj => k3 _ (by omega) (Or.inr (by omega)))
    (fun j hj => k3 _ (by omega) (Or.inr (by omega))) (fun a h1 h2 => ⟨k3 a (by omega) (Or.inl (by omega)), rd3 a⟩)
  have KA3 : Keeps pb spA (fun _ => False) sA μA μ3 s2 := by
    have := KA.trans' (K13.lift (sp' := spA) hA.1 (fun a h ha => by omega))
    rwa [Nat.max_self] at this
  have hro3 : ∀ a, a < 196608 → μ3.read a = μ.read a := fun a ha =>
    K13.ro a (by omega) (Or.inl (by unfold pageSize; omega)) (H.ro a ha)
  have rfn3 : rdN μ3 (vt + 24) 8 = fn := by rw [rdN_frame (fun j hj => hro3 _ (by omega))]; exact rfn
  have hs3 : s2.base % 8 = 0 := hb2 ▸ hba
  rcases debug_field (p := p) (P := P) (R := R) env pb S0 S1 Z hZ HA HR μA sA spA e M C fn x2 ω3 μ3 s2
      (sp - 56) F W (sp - 56 + 16) fnm fnl v vt cap2 (len + nl) 2664 62878 fnm F 0
      (hV.mono (by omega) (fun h1 h2 h3 => rdN_frame (fun j hj => K13.hi _ (by omega) (by omega) (by omega))))
      H3 hs3 hf3 KA3
      ⟨dF, by rw [show sp - 56 + 16 + 8 = sp - 56 + 24 by omega]; exact dr,
        by rw [show sp - 56 + 16 + 9 = sp - 56 + 25 by omega]; exact dh⟩
      (Or.inl rfl) c0 c1 c5 c6 c7 c8 c9 c10 c11 ⟨by omega, by omega⟩ hfnm hvt rfn3 hfn hje hbe
      (by decide) jte_1331 bs_62878 ⟨by omega, by omega, by omega⟩ ⟨by omega, hA.2, by omega⟩ ⟨by omega, hW.2⟩
      ⟨by omega, hF.2.1, hF.2.2⟩ ⟨by omega, by omega, Or.inl (by omega), Or.inl (by omega)⟩
      hvv (by omega) with
    ⟨ω4, μ4, x4, s4, cap4, n4, hn4, run4, H4, hb4, hf4, hc3, hc4, hd4, K4, d0, d1, d5, d6, d7⟩ | hx
  rotate_left
  · refine Or.inr ((Exhausts.pre ((run1.trans run2).trans run3) hx).mono ?_)
    have : cap2 ≤ max cap (max 8 (2 * (len + nl))) := hc2
    omega
  have hst4 : ∀ a, S0 ≤ a → a < S1 → μ4.writable a = true := H4.st
  have kk4 : ∀ o, o + 8 ≤ 56 → (o + 8 ≤ 16 ∨ 26 ≤ o) →
      rdN μ4 (sp - 56 + o) 8 = rdN μ3 (sp - 56 + o) 8 := fun o h1 h2 =>
    rdN_frame (fun j hj => K4.hi _ (by omega) (by omega) (by unfold dlE; omega))
  -- " }"
  obtain ⟨ω5, run5, e0, e1, e5, e6, e7, e8, e9⟩ := sf1_c (p := p) (P := P) (R := R) x4 ω4 μ4 (sp - 56) F W
    ⟨by omega, by omega⟩ d1 (by omega) hd4.fm
    (by rw [show sp - 56 + 24 = sp - 56 + 16 + 8 by omega]; exact hd4.ok)
    (by rw [show sp - 56 + 25 = sp - 56 + 16 + 9 by omega]; exact hd4.has) hf4.flags hf4.buf hf4.vt hf4.vws
    (fun a h1 h2 => Memory.readable_of_writable (hst4 a (by omega) (by omega)))
    (fun a h1 h2 => Memory.readable_of_writable (hst4 a (by omega) (by omega)))
    (fun a h1 h2 => hf4.vrd a (by omega) (by omega))
  rcases write_str (p := p) (P := P) (R := R) env pb S0 S1 HA HR x4 ω5 μ4 sA s4 (sp - 56) W 72827 2 cap4
      (len + nl + n4) 2666 62955 fnm F H4 (hb4 ▸ hs3) hf4.str e0 e1 (e5.trans d5) (e6.trans d6) e7 e8 e9
      ⟨by omega, by omega⟩ (by decide) jte_1332 bs_62955
      ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (Or.inl ⟨by omega, by omega⟩)
      (fun a h1 h2 => hf4.vrd a (by omega) (by omega)) with
    ⟨ω6, μ6, x6, s6, cap6, run6, H6, hb6, hs6, hc5, hc6, K6, g0, g1, g5, g6, g7⟩ | hx
  rotate_left
  · refine Or.inr ((Exhausts.pre ((((run1.trans run2).trans run3).trans run4).trans run5) hx).mono ?_)
    have : cap2 ≤ max cap (max 8 (2 * (len + nl))) := hc2
    have : cap4 ≤ max cap2 (max 8 (2 * (len + nl + n4))) := hc4
    have := hf4.str.lt
    omega
  have hst6 : ∀ a, S0 ≤ a → a < S1 → μ6.writable a = true := H6.st
  have kk6 : ∀ o, o + 8 ≤ 56 → rdN μ6 (sp - 56 + o) 8 = rdN μ4 (sp - 56 + o) 8 := fun o ho =>
    rdN_frame (fun j hj => K6.hi _ (by omega) (by omega) (by omega))
  have w : ∀ o, 32 ≤ o → o + 8 ≤ 56 → rdN μ6 (sp - 56 + o) 8 = rdN μ1 (sp - 56 + o) 8 := fun o h1 h2 => by
    rw [kk6 o (by omega), kk4 o (by omega) (by omega),
      rdN_frame (fun j hj => k3 _ (by omega) (Or.inr (by omega))), kk2 o (by omega)]
  obtain ⟨ω7, run7, m0, m1, m5, m6, m7⟩ := sf1_d (p := p) (P := P) (R := R) x6 ω6 μ6 (sp - 56) ret t v5 v6
    ⟨by omega, by omega⟩ g1 g7 ((w 48 (by omega) (by omega)).trans s48) ((w 40 (by omega) (by omega)).trans s40)
    ((w 32 (by omega) (by omega)).trans s32) hret hjt hbt
    (fun a h1 h2 => Memory.readable_of_writable (hst6 a (by omega) (by omega)))
  have K := ((K13.trans' (K4.lift (sp' := sp) (by omega) (fun a h ha => by unfold dlE at h; omega))).trans'
    (K6.lift (sp' := sp) (by omega) (fun a h _ => h)))
  simp only [Nat.max_self] at K
  have hf6 : Fmtr sA s6 μ6 F W cap6 (len + nl + n4 + 2) :=
    Fmtr.of_keeps hf H K ⟨hF.1, by omega⟩ (fun a h1 h2 h => by omega) hs6
  refine Or.inl ⟨ω7, μ6, x6, s6, cap6, nl + n4 + 2, by omega,
    ((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).mono ?_, H6,
    hb6.trans (hb4.trans hb2), ?_, by omega, ?_, K, m0, by rw [m1]; congr 1; omega, m5, m6, m7⟩
  · omega
  · rwa [show len + (nl + n4 + 2) = len + nl + n4 + 2 by omega]
  · rw [show len + (nl + n4 + 2) = len + nl + n4 + 2 by omega]
    have : cap2 ≤ max cap (max 8 (2 * (len + nl))) := hc2
    have : cap4 ≤ max cap2 (max 8 (2 * (len + nl + n4))) := hc4
    omega

end Services.Bootstrap.Fmt
