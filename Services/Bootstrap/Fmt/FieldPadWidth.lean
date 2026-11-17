import Services.Bootstrap.Fmt.FieldPadWidthSteps

/-!
# `Formatter::pad_integral` with the options of `{:02x}`

`pad_integral` (61857) through a `Formatter` F with the options word o = 0x69000020 (the width flag
and the zero-pad flag set; no `+`, no `#`) and width w (`FmtrO`), into the `String` W:

- `pad_wp`: n ≥ w digits: the plain path, `write_str` of the digits (as `pad_plain`);
- `pad_z2`: one digit and w = 2: the zero-pad path, `write_char` of '0' and then `write_str` of the
  digit; the options word is set to fill '0' for the duration and restored.

Either way `pad_integral` returns `Ok` with the `String` grown by max(n, w) octets, the context
kept and, from sp up, only W … W + 24 changed; or it reaches a failed allocator call.
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- The octets a run may change: the `String`'s 24 and the `Formatter`'s options word. -/
def padE (W F a : Nat) : Prop := (W ≤ a ∧ a < W + 24) ∨ (F + 16 ≤ a ∧ a < F + 24)

/-- **A run that puts back n octets at a0** (they read the same number at the end as at the start)
    keeps the frame without them. -/
theorem Keeps.restore {pb sp a0 n : Nat} {E E' : Nat → Prop} {s₀ s : State} {μ μ' : Memory}
    (h : Keeps pb sp E' s₀ μ μ' s) (hE : ∀ a, E' a → E a ∨ (a0 ≤ a ∧ a < a0 + n))
    (hr : rdN μ' a0 n = rdN μ a0 n) : Keeps pb sp E s₀ μ μ' s :=
  { h with
    hi := fun a ha hb hn => by
      by_cases hz : a0 ≤ a ∧ a < a0 + n
      · have := read_of_rdN hr (a - a0) (by omega)
        rwa [show a0 + (a - a0) = a by omega] at this
      · exact h.hi a ha hb (fun e => (hE a e).elim hn hz) }

/-- **`pad_integral` with options 0x69000020 and width w ≤ n** (61857): as `pad_plain`, the n
    octets of digits at dig are written by the sink's `write_str`. -/
theorem pad_wp {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (x : X) (ω : Regs) (μ : Memory) (s₀ s : State) (sp F W dig n cap len ret t v5 v6 pl w : Nat)
    (H : HeapCtx env pb S0 S1 μ s) (hba : s.base % 8 = 0) (hf : FmtrO s₀ s μ F W cap len 1761607712 w)
    (hwn : w ≤ n)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat F) (h10 : ω[10] = UInt64.ofNat pl)
    (h11 : ω[11] = UInt64.ofNat dig) (h12 : ω[12] = UInt64.ofNat n)
    (hv : v5 < 18446744073709551616 ∧ v6 < 18446744073709551616 ∧ pl < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hsp : S0 + 448 ≤ sp ∧ sp % 8 = 0 ∧ 2147484096 ≤ sp) (hW : sp ≤ W ∧ W + 24 ≤ S1)
    (hF : sp ≤ F ∧ F + 24 ≤ S1 ∧ (F + 24 ≤ W ∨ W + 24 ≤ F))
    (hn : len + n < 134217728)
    (hsrc : (65536 ≤ dig ∧ dig + n + 24 ≤ 196608) ∨
      (sp ≤ dig ∧ dig + n + 16 < 4294967296 ∧ (dig + n ≤ W ∨ W + 24 ≤ dig)))
    (hr : ∀ a, dig ≤ a → a < dig + n → μ.readable a = true) :
    (∃ ω' μ' x' s' cap', FreeStepsH p R 61857 ω μ x t ω' μ' x' (7 * n + 2 * (cap' - cap) + 2100) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ FmtrO s₀ s' μ' F W cap' (len + n) 1761607712 w ∧
      cap ≤ cap' ∧ cap' ≤ max cap (max 8 (2 * (len + n))) ∧
      Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) s₀ μ μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0) ∨
    Exhausts p R pb 61857 ω μ x (7 * n + 1073741824 + 2100) := by
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  have hro : ∀ a, a < 196608 → μ.writable a = false := H.ro
  -- 61857 … 64897
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, a10, s96, s88, s80, s16, s24, fr1, rd1, wr1⟩ :=
    pw_a (p := p) (P := P) (R := R) x ω μ sp F dig n ret v5 v6 W 77016 pl w ⟨by omega, by omega⟩ h0 h1 h5 h6 h7
      h10 h11 h12 ⟨by omega, hv.1, hv.2.1, by omega, by omega, hv.2.2⟩ (Or.inr hF.1) (by omega) hf.opts hf.width
      hwn hf.buf hf.vt ⟨by omega, by omega⟩
      (fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)))
      (fun a h1 h2 => hst a (by omega) (by omega))
  -- write_prefix
  obtain ⟨ω2, μ2, run2, b1, b5, b6, b7, fr2, rd2, wr2⟩ := pi_b (p := p) (P := P) (R := R) x ω1 μ1 (sp - 104)
    ⟨by omega, by omega⟩ a0 a1 a9 a10 (fun a h1 h2 => by rw [wr1]; exact hst a (by omega) (by omega))
  have k2 : ∀ a, sp - 104 ≤ a → a < 4294967296 → μ2.read a = μ1.read a := fun a h1 h2 => fr2 a h2 (Or.inr h1)
  have k12 : ∀ a, a < 4294967296 → (a < sp - 144 ∨ sp ≤ a) → μ2.read a = μ.read a := fun a h1 h2 => by
    rw [fr2 a h1 (by omega), fr1 a h1 (by omega)]
  have kro : ∀ a, a < 196608 → μ2.read a = μ.read a := fun a ha => k12 a (by omega) (Or.inl (by omega))
  -- the tail call
  obtain ⟨ω3, run3, c0, c1, c5, c6, c7, c8, c9⟩ := pi_c (p := p) (P := P) (R := R) x ω2 μ2 (sp - 104) W 77016 dig n
    ret v5 v6 ⟨by omega, by omega⟩ (b1.trans a1) (b5.trans a5) (b6.trans a6) b7 (by omega) (by omega)
    (by rw [rdN_frame (fun j hj => kro _ (by omega))]; exact hf.vws)
    (by rw [rdN_frame (fun j hj => k2 _ (by omega) (by omega))]; exact s16)
    (by rw [rdN_frame (fun j hj => k2 _ (by omega) (by omega))]; exact s24)
    (by rw [rdN_frame (fun j hj => k2 _ (by omega) (by omega))]; exact s96)
    (by rw [rdN_frame (fun j hj => k2 _ (by omega) (by omega))]; exact s88)
    (by rw [rdN_frame (fun j hj => k2 _ (by omega) (by omega))]; exact s80)
    (fun a h1 h2 => by rw [rd2, rd1]; exact hf.vrd a (by omega) (by omega))
    (fun a h1 h2 => by rw [rd2, rd1]; exact Memory.readable_of_writable (hst a (by omega) (by omega)))
  have wr12 : ∀ a, μ2.writable a = μ.writable a := fun a => by rw [wr2, wr1]
  have rd12 : ∀ a, μ2.readable a = μ.readable a := fun a => by rw [rd2, rd1]
  have H2 : HeapCtx env pb S0 S1 μ2 s := ctx_hi H (fun a ha => k12 a (by omega) (Or.inl (by omega))) wr12
  have kW : ∀ j, j < 24 → μ2.read (W + j) = μ.read (W + j) := fun j hj => k12 _ (by omega) (Or.inr (by omega))
  have hs2 : Str s₀ s μ2 W cap len := hf.str.update (fun j hj => kW j (by omega))
    ((rdN_frame (μ := μ) (μ' := μ2) (fun j hj => by
      rw [show W + 16 + j = W + (16 + j) by omega, kW _ (by omega)])).trans hf.str.rl) hf.str.le
  have K1 : Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) s₀ μ μ2 s :=
    Keeps.of_frame (Z := fun a => sp - 144 ≤ a ∧ a < sp) hf.str.base
      (fun a ha hz => k12 a ha (by omega)) rd12 wr12 (fun a hz => hst a (by omega) (by omega))
      (fun a hz h => by omega) (fun a hz hg => by unfold Glob at hg; omega)
      (fun d hd hu a ha => by
        have := chunk_bounds H.wf (hf.str.base d hd hu)
        have := H.hbT
        unfold InData at ha; omega)
  have h1' : ω3[1] = UInt64.ofNat sp := by rw [c1, show sp - 104 + 104 = sp by omega]
  rcases write_str (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω3 μ2 s₀ s sp W dig n cap len ret t v5 v6
      H2 hba hs2 c0 h1' c5 c6 c7 c8 c9 ⟨hv.1, hv.2.1⟩ hret hjt hbt hsp hW hn hsrc
      (fun a h1 h2 => by rw [rd12]; exact hr a h1 h2) with
    ⟨ω4, μ4, x4, s', cap', run4, H4, hb4, hs4, hc1, hc2, K4, e0, e1, e5, e6, e7⟩ | hx
  · have K := K1.trans' K4
    rw [Nat.max_self] at K
    have kF : ∀ a, F ≤ a → a < F + 24 → μ4.read a = μ.read a := fun a h1 h2 =>
      K.hi a (by omega) (by omega) (by omega)
    have kro : ∀ a, 65536 ≤ a → a < 77144 → μ4.read a = μ.read a := fun a h1 h2 =>
      K.ro a (by omega) (Or.inl (by unfold pageSize; omega)) (hro a (by omega))
    refine Or.inl ⟨ω4, μ4, x4, s', cap', (((run1.trans run2).trans run3).trans run4).mono (by omega), H4, hb4,
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a h1 h2 => ?_, hs4⟩, hc1, hc2, K, e0, e1, e5, e6, e7⟩
    · rw [rdN_frame (fun j hj => kF _ (by omega) (by omega))]; exact hf.buf
    · rw [rdN_frame (fun j hj => kF _ (by omega) (by omega))]; exact hf.vt
    · rw [rdN_frame (fun j hj => kF _ (by omega) (by omega))]; exact hf.opts
    · rw [rdN_frame (fun j hj => kF _ (by omega) (by omega))]; exact hf.width
    · rw [rdN_frame (fun j hj => kF _ (by omega) (by omega))]; exact hf.prec
    · rw [rdN_frame (fun j hj => kro _ (by omega) (by omega))]; exact hf.vws
    · rw [rdN_frame (fun j hj => kro _ (by omega) (by omega))]; exact hf.vwc
    · rw [(K.access a (Or.inl (by unfold pageSize; omega))).1]; exact hf.vrd a h1 h2
  · exact Or.inr ((Exhausts.pre ((run1.trans run2).trans run3) hx).mono (by omega))

/-- **`pad_integral` with options 0x69000020, width 2 and one digit** (61857), the zero-pad path:
    the options word at F + 16 is set to fill '0', the sink's `write_char` writes '0', its
    `write_str` writes the digit at dig, and the options word is put back. `pad_integral` returns
    to `t`: `Ok`, the `String` len + 2 long, the context and the frame kept (from sp up only
    W … W + 24 changes), or a failed allocator call. -/
theorem pad_z2 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (x : X) (ω : Regs) (μ : Memory) (s₀ s : State) (sp F W dig cap len ret t v5 v6 pl : Nat)
    (H : HeapCtx env pb S0 S1 μ s) (hba : s.base % 8 = 0) (hf : FmtrO s₀ s μ F W cap len 1761607712 2)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat F) (h10 : ω[10] = UInt64.ofNat pl)
    (h11 : ω[11] = UInt64.ofNat dig) (h12 : ω[12] = UInt64.ofNat 1)
    (hv : v5 < 18446744073709551616 ∧ v6 < 18446744073709551616 ∧ pl < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hsp : S0 + 568 ≤ sp ∧ sp % 8 = 0 ∧ 2147484216 ≤ sp) (hW : sp ≤ W ∧ W + 24 ≤ S1)
    (hF : sp ≤ F ∧ F + 24 ≤ S1 ∧ (F + 24 ≤ W ∨ W + 24 ≤ F))
    (hn : len + 2 < 134217728)
    (hsrc : (65536 ≤ dig ∧ dig + 1 + 24 ≤ 196608) ∨
      (sp ≤ dig ∧ dig + 1 + 16 < 4294967296 ∧ (dig + 1 ≤ W ∨ W + 24 ≤ dig)))
    (hr : ∀ a, dig ≤ a → a < dig + 1 → μ.readable a = true) :
    (∃ ω' μ' x' s' cap', FreeStepsH p R 61857 ω μ x t ω' μ' x' (2 * (cap' - cap) + 3800) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ FmtrO s₀ s' μ' F W cap' (len + 2) 1761607712 2 ∧
      cap ≤ cap' ∧ cap' ≤ max cap (max 8 (2 * (len + 2))) ∧
      Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) s₀ μ μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0) ∨
    Exhausts p R pb 61857 ω μ x (1073741824 + 536870912 + 4000) := by
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  have hro : ∀ a, a < 196608 → μ.writable a = false := H.ro
  have hcap := hf.str.lt
  -- the options word, 8 octets
  have ro8 : rdN μ (F + 16) 8 = 10351542304 := by
    have e1 := rdN_add μ (F + 16) 4 4
    have e2 := rdN_add μ (F + 20) 2 2
    rw [show F + 16 + 4 = F + 20 by omega] at e1
    rw [show F + 20 + 2 = F + 22 by omega, hf.width, hf.prec] at e2
    rw [hf.opts, e2] at e1
    simpa using e1
  -- 61857 … 62076
  obtain ⟨ω0, μ0, run0, q1, q5, q6, q11, t96, t88, t80, t16, t24, t32, t40, fr0, rd0, wr0⟩ :=
    pz_a1 (p := p) (P := P) (R := R) x ω μ sp F dig ret v5 v6 pl ⟨by omega, by omega⟩ h0 h1 h5 h6 h7 h10 h11 h12
      ⟨by omega, hv.1, hv.2.1, by omega, hv.2.2⟩ (Or.inr hF.1) (by omega) hf.opts hf.width
      (fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)))
      (fun a h1 h2 => hst a (by omega) (by omega))
  have k0F : ∀ a, F ≤ a → a < F + 24 → μ0.read a = μ.read a := fun a h1 h2 => fr0 a (by omega) (Or.inr (by omega))
  -- 62076 … 64897
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a9, a10, s56, s0, s8, s72, s64, sF, fr1, rd1, wr1⟩ :=
    pz_a2 (p := p) (P := P) (R := R) x ω0 μ0 (sp - 104) F W 77016 ⟨by omega, by omega⟩ q1 q6 q11
      (Or.inr (by omega)) (by omega)
      (by rw [rdN_frame (fun j hj => k0F _ (by omega) (by omega))]; exact ro8)
      (by rw [rdN_frame (fun j hj => k0F _ (by omega) (by omega))]; exact hf.buf)
      (by rw [rdN_frame (fun j hj => k0F _ (by omega) (by omega))]; exact hf.vt) t32 t40
      (fun a h1 h2 => by rw [rd0]; exact Memory.readable_of_writable (hst a (by omega) (by omega)))
      (fun a h1 h2 => by rw [wr0]; exact hst a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr0]; exact hst a (by omega) (by omega))
  have k1 : ∀ a, (sp - 104 + 16 ≤ a ∧ a < sp - 104 + 56) ∨ (sp - 104 + 80 ≤ a ∧ a < sp) →
      μ1.read a = μ0.read a := fun a h => fr1 a (by omega) (by omega) (by omega)
  have s96 : rdN μ1 (sp - 104 + 96) 8 = ret := by rw [rdN_frame (fun j hj => k1 _ (by omega))]; exact t96
  have s88 : rdN μ1 (sp - 104 + 88) 8 = v5 := by rw [rdN_frame (fun j hj => k1 _ (by omega))]; exact t88
  have s80 : rdN μ1 (sp - 104 + 80) 8 = v6 := by rw [rdN_frame (fun j hj => k1 _ (by omega))]; exact t80
  have s16 : rdN μ1 (sp - 104 + 16) 8 = dig := by rw [rdN_frame (fun j hj => k1 _ (by omega))]; exact t16
  have s24 : rdN μ1 (sp - 104 + 24) 8 = 1 := by rw [rdN_frame (fun j hj => k1 _ (by omega))]; exact t24
  have a5' : ω1[5] = UInt64.ofNat 2 := a5.trans q5
  have rd1' : ∀ a, μ1.readable a = μ.readable a := fun a => by rw [rd1, rd0]
  have wr1' : ∀ a, μ1.writable a = μ.writable a := fun a => by rw [wr1, wr0]
  -- write_prefix
  obtain ⟨ω2, μ2, run2, b1, b5, b6, b7, fr2, rd2, wr2⟩ := pz_b (p := p) (P := P) (R := R) x ω1 μ1 (sp - 104)
    ⟨by omega, by omega⟩ a0 a1 a9 a10 (fun a h1 h2 => by rw [wr1']; exact hst a (by omega) (by omega))
  have k2 : ∀ a, sp - 104 ≤ a → a < 4294967296 → μ2.read a = μ1.read a := fun a h1 h2 => fr2 a h2 (Or.inr h1)
  have k12 : ∀ a, a < 4294967296 → (a < sp - 144 ∨ sp ≤ a) → (a < F + 16 ∨ F + 20 ≤ a) →
      μ2.read a = μ.read a := fun a h1 h2 h3 => by
    rw [fr2 a h1 (by omega), fr1 a h1 (by omega) h3, fr0 a h1 (by omega)]
  have kro : ∀ a, a < 196608 → μ2.read a = μ.read a := fun a ha =>
    k12 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  have wr12 : ∀ a, μ2.writable a = μ.writable a := fun a => by rw [wr2, wr1']
  have rd12 : ∀ a, μ2.readable a = μ.readable a := fun a => by rw [rd2, rd1']
  have H2 : HeapCtx env pb S0 S1 μ2 s :=
    ctx_hi H (fun a ha => k12 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))) wr12
  have kW : ∀ j, j < 24 → μ2.read (W + j) = μ.read (W + j) := fun j hj =>
    k12 _ (by omega) (Or.inr (by omega)) (by omega)
  have hs2 : Str s₀ s μ2 W cap len := hf.str.update (fun j hj => kW j (by omega))
    ((rdN_frame (μ := μ) (μ' := μ2) (fun j hj => by
      rw [show W + 16 + j = W + (16 + j) by omega, kW _ (by omega)])).trans hf.str.rl) hf.str.le
  have K1 : Keeps pb sp (padE W F) s₀ μ μ2 s :=
    Keeps.of_frame (Z := fun a => (sp - 144 ≤ a ∧ a < sp) ∨ (F + 16 ≤ a ∧ a < F + 20)) hf.str.base
      (fun a ha hz => k12 a ha (by omega) (by omega)) rd12 wr12 (fun a hz => hst a (by omega) (by omega))
      (fun a hz h => by unfold padE; omega) (fun a hz hg => by unfold Glob at hg; omega)
      (fun d hd hu a ha => by
        have := chunk_bounds H.wf (hf.str.base d hd hu)
        have := H.hbT
        unfold InData at ha; omega)
  -- the fill loop's first test and the call of write_char
  obtain ⟨ω3, run3, c0, c1, c5, c6, c7, c8⟩ := pz_c (p := p) (P := P) (R := R) x ω2 μ2 (sp - 104) W 77016
    ⟨by omega, by omega⟩ (b1.trans a1) (b5.trans a5') (b6.trans a6) b7 (by omega)
    (by rw [rdN_frame (fun j hj => kro _ (by omega))]; exact hf.vwc)
    (by rw [rdN_frame (fun j hj => k2 _ (by omega) (by omega))]; exact s56)
    (by rw [rdN_frame (fun j hj => k2 _ (by omega) (by omega))]; exact s64)
    (by rw [rdN_frame (fun j hj => k2 _ (by omega) (by omega))]; exact s72)
    (fun a h1 h2 => by rw [rd12]; exact hf.vrd a (by omega) (by omega))
    (fun a h1 h2 => by rw [rd12]; exact Memory.readable_of_writable (hst a (by omega) (by omega)))
  have hT8 : (sp - 104) % 8 = 0 := by omega
  rcases write_char (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω3 μ2 s₀ s (sp - 104) W 48 cap len 2634 62173
      1 1 H2 hba hs2 c0 c1 c5 c6 c7 c8 ⟨by omega, by omega⟩ ⟨by omega, by omega, by omega⟩ jte_1316 bs_62173
      ⟨by omega, hT8, by omega⟩ ⟨by omega, hW.2⟩ (by omega) (by omega) with
    ⟨ω4, μ4, x4, s4, cap4, run4, H4, hb4, hs4, hc41, hc42, K4, d0, d1, d5, d6, d7⟩ | hx
  rotate_left
  · exact Or.inr ((Exhausts.pre (((run0.trans run1).trans run2).trans run3) hx).mono (by omega))
  have kT4 : ∀ a, sp - 104 ≤ a → a < sp → μ4.read a = μ1.read a := fun a h1 h2 => by
    rw [K4.hi a h1 (by omega) (by omega), k2 a h1 (by omega)]
  have kro4 : ∀ a, 65536 ≤ a → a < 77144 → μ4.read a = μ.read a := fun a h1 h2 => by
    rw [K4.ro a (by omega) (Or.inl (by unfold pageSize; omega)) (by rw [wr12]; exact hro a (by omega)), kro a (by omega)]
  have rd4 : ∀ a, (a / pageSize < 48 ∨ pb ≤ a / pageSize) → μ4.readable a = μ.readable a := fun a h => by
    rw [(K4.access a h).1, rd12]
  -- the fill loop's end and the call of write_str
  obtain ⟨ω5, run5, e0, e1, e5, e6, e7, e8, e9⟩ := pz_d (p := p) (P := P) (R := R) x4 ω4 μ4 (sp - 104) W 77016
    dig 1 ⟨by omega, by omega⟩ d1 d5 d6 d7 (by omega)
    (by rw [rdN_frame (fun j hj => kro4 _ (by omega) (by omega))]; exact hf.vws)
    (by rw [rdN_frame (fun j hj => kT4 _ (by omega) (by omega))]; exact s64)
    (by rw [rdN_frame (fun j hj => kT4 _ (by omega) (by omega))]; exact s72)
    (by rw [rdN_frame (fun j hj => kT4 _ (by omega) (by omega))]; exact s16)
    (by rw [rdN_frame (fun j hj => kT4 _ (by omega) (by omega))]; exact s24)
    (fun a h1 h2 => by rw [rd4 a (Or.inl (by unfold pageSize; omega))]; exact hf.vrd a (by omega) (by omega))
    (fun a h1 h2 => Memory.readable_of_writable (H4.st a (by omega) (by omega)))
  have hba4 : s4.base % 8 = 0 := by rw [hb4]; exact hba
  have hr4 : ∀ a, dig ≤ a → a < dig + 1 → μ4.readable a = true := fun a h1 h2 => by
    rcases hsrc with h | h
    · rw [rd4 a (Or.inl (by unfold pageSize; omega))]; exact hr a h1 h2
    · rw [rd4 a (Or.inr (by unfold pageSize; omega))]; exact hr a h1 h2
  rcases write_str (p := p) (P := P) (R := R) env pb S0 S1 HA HR x4 ω5 μ4 s₀ s4 (sp - 104) W dig 1 cap4 (len + 1)
      2636 62240 1 1 H4 hba4 hs4 e0 e1 e5 e6 e7 e8 e9 ⟨by omega, by omega⟩ ⟨by omega, by omega, by omega⟩ jte_1317
      bs_62240 ⟨by omega, hT8, by omega⟩ ⟨by omega, hW.2⟩ (by omega)
      (hsrc.elim Or.inl (fun h => Or.inr ⟨by omega, h.2.1, h.2.2⟩)) hr4 with
    ⟨ω6, μ6, x6, s6, cap6, run6, H6, hb6, hs6, hc61, hc62, K6, g0, g1, g5, g6, g7⟩ | hx
  rotate_left
  · exact Or.inr ((Exhausts.pre (((((run0.trans run1).trans run2).trans run3).trans run4).trans run5) hx).mono (by omega))
  have kT6 : ∀ a, sp - 104 ≤ a → a < sp → μ6.read a = μ1.read a := fun a h1 h2 => by
    rw [K6.hi a h1 (by omega) (by omega), kT4 a h1 h2]
  -- the options word put back, and the return
  obtain ⟨ω7, μ7, run7, f0, f1, f5, f6, f7, fsv, fr7, rd7, wr7⟩ := pz_e (p := p) (P := P) (R := R) x6 ω6 μ6
    (sp - 104) F 10351542304 ret t v5 v6 ⟨by omega, by omega⟩ (by omega) (Or.inr (by omega)) g1 g7
    (by rw [rdN_frame (fun j hj => kT6 _ (by omega) (by omega))]; exact s96)
    (by rw [rdN_frame (fun j hj => kT6 _ (by omega) (by omega))]; exact s88)
    (by rw [rdN_frame (fun j hj => kT6 _ (by omega) (by omega))]; exact s80)
    (by rw [rdN_frame (fun j hj => kT6 _ (by omega) (by omega))]; exact s8)
    (by rw [rdN_frame (fun j hj => kT6 _ (by omega) (by omega))]; exact s0)
    hret hjt hbt (fun a h1 h2 => H6.st a (by omega) (by omega))
    (fun a h1 h2 => Memory.readable_of_writable (H6.st a (by omega) (by omega)))
  have H7 : HeapCtx env pb S0 S1 μ7 s6 := ctx_hi H6 (fun a ha => fr7 a (by omega) (Or.inl (by omega))) wr7
  have K7 : Keeps pb sp (padE W F) s₀ μ6 μ7 s6 :=
    Keeps.of_frame (Z := fun a => F + 16 ≤ a ∧ a < F + 24) hs6.base
      (fun a ha hz => fr7 a ha (by omega)) rd7 wr7 (fun a hz => H6.st a (by omega) (by omega))
      (fun a hz h => by unfold padE; omega) (fun a hz hg => by unfold Glob at hg; omega)
      (fun d hd hu a ha => by
        have := chunk_bounds H6.wf (hs6.base d hd hu)
        have := H6.hbT
        unfold InData at ha; omega)
  have K' := ((K1.trans' (K4.mono (sp' := sp) (by omega) (fun a h => Or.inl h))).trans'
    (K6.mono (sp' := sp) (by omega) (fun a h => Or.inl h))).trans' K7
  simp only [Nat.max_self] at K'
  have K : Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) s₀ μ μ7 s6 :=
    K'.restore (a0 := F + 16) (n := 8) (fun a h => by unfold padE at h; omega) (by rw [fsv, ro8])
  have kF : ∀ a, F ≤ a → a < F + 24 → μ7.read a = μ.read a := fun a h1 h2 =>
    K.hi a (by omega) (by omega) (by omega)
  have kro7 : ∀ a, 65536 ≤ a → a < 77144 → μ7.read a = μ.read a := fun a h1 h2 =>
    K.ro a (by omega) (Or.inl (by unfold pageSize; omega)) (hro a (by omega))
  have kW7 : ∀ j, j < 24 → μ7.read (W + j) = μ6.read (W + j) := fun j hj => fr7 _ (by omega) (by omega)
  have hs7 : Str s₀ s6 μ7 W cap6 (len + 1 + 1) := hs6.update (fun j hj => kW7 j (by omega))
    ((rdN_frame (μ := μ6) (μ' := μ7) (fun j hj => by
      rw [show W + 16 + j = W + (16 + j) by omega, kW7 _ (by omega)])).trans hs6.rl) hs6.le
  refine Or.inl ⟨ω7, μ7, x6, s6, cap6,
    (((((((run0.trans run1).trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).mono (by omega), H7,
    by rw [hb6, hb4], ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a h1 h2 => ?_, hs7⟩, by omega, by omega, K, f0,
    by rw [f1, show sp - 104 + 104 = sp by omega], f5, f6, f7⟩
  · rw [rdN_frame (fun j hj => kF _ (by omega) (by omega))]; exact hf.buf
  · rw [rdN_frame (fun j hj => kF _ (by omega) (by omega))]; exact hf.vt
  · rw [rdN_frame (fun j hj => kF _ (by omega) (by omega))]; exact hf.opts
  · rw [rdN_frame (fun j hj => kF _ (by omega) (by omega))]; exact hf.width
  · rw [rdN_frame (fun j hj => kF _ (by omega) (by omega))]; exact hf.prec
  · rw [rdN_frame (fun j hj => kro7 _ (by omega) (by omega))]; exact hf.vws
  · rw [rdN_frame (fun j hj => kro7 _ (by omega) (by omega))]; exact hf.vwc
  · rw [(K.access a (Or.inl (by unfold pageSize; omega))).1]; exact hf.vrd a h1 h2

end Services.Bootstrap.Fmt
