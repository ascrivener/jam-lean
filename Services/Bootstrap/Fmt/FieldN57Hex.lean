import Services.Bootstrap.Fmt.FieldN56Hex

/-!
# 57485's hex path (57567 … the return)

57485 formats a 128-octet memo (the transfer memo, `Spec.Instr` tag 2 through 33162). When an octet
is a control character or above 127, or `str::from_utf8` fails, it writes the first 8 octets in hex,
as 56340 does: `core::fmt::write` (64495) with the template 70824 and the argument (U + 40, 2534),
U + 40 holding the slice (memo, 8); then it returns.

- `n57h_call`: 57567 … the call of 64495 (U = the stack pointer, 57485's 80-octet frame);
- `n57h_ret`: 57604 … the return;
- `n57_hex`: the whole, at most 21 octets.

Named hypotheses on read-only data: `RO70824` and `RO70833`.
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 57567 … 57598: the slice (a, 8) at U + 40 (a in ω₆), the argument pair (U + 40, 2534) at U, and the
    call of `core::fmt::write` (64495) with the `Formatter`'s sink (W, vt) from F (ω₅), the template
    70824 and the arguments U, returning to 57604 (2514). -/
theorem n57h_call {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (U F a W vt : Nat) (hU : 65536 ≤ U ∧ U + 80 < 4294967296) (hF : F + 16 < 4294967296)
    (hFU : F + 16 ≤ U ∨ U + 56 ≤ F)
    (h1 : ω[1] = UInt64.ofNat U) (h6 : ω[6] = UInt64.ofNat a) (h5 : ω[5] = UInt64.ofNat F)
    (ha : a < 18446744073709551616) (rb : rdN μ F 8 = W) (rv : rdN μ (F + 8) 8 = vt)
    (hrF : ∀ c, F ≤ c → c < F + 16 → μ.readable c = true)
    (hw : ∀ c, U ≤ c → c < U + 56 → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R 57567 ω μ x 64495 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 2514 ∧ ω'[1] = UInt64.ofNat U ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat W ∧ ω'[8] = UInt64.ofNat vt ∧ ω'[9] = UInt64.ofNat 70824 ∧
      ω'[10] = UInt64.ofNat U ∧
      rdN μ' (U + 40) 8 = a ∧ rdN μ' (U + 48) 8 = 8 ∧ rdN μ' U 8 = U + 40 ∧
      rdN μ' (U + 8) 8 = 2534 ∧
      (∀ c, c < 4294967296 → (c < U ∨ U + 56 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, U ≤ c → c < U + 56 → μ.readable c = true := fun c h1 h2 =>
    Memory.readable_of_writable (hw c h1 h2)
  have hW : W < 18446744073709551616 := by rw [← rb]; exact rdN_lt64 μ _
  have hvt : vt < 18446744073709551616 := by rw [← rv]; exact rdN_lt64 μ _
  have h240 : U + 40 < 18446744073709551616 := by omega
  have hU64 : U < 18446744073709551616 := by omega
  have hb5 := (ω[5]).toNat_lt
  have hb6 := (ω[6]).toNat_lt
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, h5, hU, hF, hFU, ha, rb, rv, hrF, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
    all_goals post_simp [h1, rdN_writeN_disjoint, rdN_writeN_same8, rdN_lit8, Num.decodeLE_encodeLE, Nat.reduceMul,
      Nat.reducePow, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hW, Nat.mod_eq_of_lt hvt, Nat.mod_eq_of_lt h240, Nat.mod_eq_of_lt hU64]

/-- 57604 … the return: ω₀, ω₅, ω₆ restored from U + 72, U + 64, U + 56, the frame closed, the
    return to t; ω₇ kept. -/
theorem n57h_ret {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (U r0 t v5 v6 : Nat) (hU : 65536 ≤ U ∧ U + 80 < 4294967296) (h1 : ω[1] = UInt64.ofNat U)
    (r0' : rdN μ (U + 72) 8 = r0) (r5 : rdN μ (U + 64) 8 = v5) (r6 : rdN μ (U + 56) 8 = v6)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hr : ∀ c, U + 56 ≤ c → c < U + 80 → μ.readable c = true) :
    ∃ ω', FreeStepsH p R 57604 ω μ x t ω' μ x 5 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (U + 80) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = ω[7] := by
  have hv5 : v5 < 18446744073709551616 := by rw [← r5]; exact rdN_lt64 μ _
  have hv6 : v6 < 18446744073709551616 := by rw [← r6]; exact rdN_lt64 μ _
  have hr0 : r0 % 18446744073709551616 % 4294967296 = r0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hU, r0', r5, r6, hret, hr0, hjt, hbt, hr, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, Nat.mod_eq_of_lt hv5, Nat.mod_eq_of_lt hv6]

/-- **57485's hex path** (57567 … the return), from 57485's frame U (the stack pointer; ω₀, ω₅, ω₆
    saved at U + 72, U + 64, U + 56), the memo's address a (ω₆, the first 8 octets where `ValAt` puts
    them) and a `Formatter` F into the `String` W (ω₅): `Ok` returned to t, ω₀, ω₅, ω₆ restored, sp
    U + 80, the `String` at most 21 octets longer, the context kept and, from U + 80 up, only
    W … W + 24 changed; or a failed allocator call. -/
theorem n57_hex {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA a : Nat) (hS : S0 ≤ spA)
    (helts : ∀ j, j < 8 → ValAt μA sA spA S1 (a + j) 1) (ha : a + 8 < 18446744073709551616)
    (hRO3 : RO70833 μA) (hRO4 : RO70824 μA)
    (x : X) (ω : Regs) (μ : Memory) (s : State) (U F W cap len r0 t v5 v6 : Nat)
    (H : HeapCtx env pb S0 S1 μ s) (hba : s.base % 8 = 0)
    (KA : Keeps pb spA (fun c => W ≤ c ∧ c < W + 24) sA μA μ s) (hf : Fmtr sA s μ F W cap len)
    (h1 : ω[1] = UInt64.ofNat U) (h6 : ω[6] = UInt64.ofNat a) (h5 : ω[5] = UInt64.ofNat F)
    (r272 : rdN μ (U + 72) 8 = r0) (r264 : rdN μ (U + 64) 8 = v5) (r256 : rdN μ (U + 56) 8 = v6)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hU : S0 + 896 ≤ U ∧ U % 8 = 0 ∧ 2147484544 ≤ U ∧ U + 80 ≤ spA)
    (hW : U + 80 ≤ W ∧ W + 24 ≤ S1) (hF : U + 80 ≤ F ∧ F + 24 ≤ S1 ∧ (F + 24 ≤ W ∨ W + 24 ≤ F))
    (hn : len + 21 < 134217728) :
    (∃ ω' μ' x' s' cap' n, n ≤ 21 ∧
      FreeStepsH p R 57567 ω μ x t ω' μ' x' (7 * n + 2 * (cap' - cap) + 5368751000) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Fmtr sA s' μ' F W cap' (len + n) ∧ cap ≤ cap' ∧
      cap' ≤ max cap (max 8 (2 * (len + n))) ∧
      Keeps pb (U + 80) (fun c => W ≤ c ∧ c < W + 24) sA μ μ' s' ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (U + 80) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0) ∨
    Exhausts p R pb 57567 ω μ x 7516235000 := by
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst : ∀ c, S0 ≤ c → c < S1 → μ.writable c = true := H.st
  have hro : ∀ c, c < 196608 → μ.writable c = false := H.ro
  have hcap := hf.str.lt
  -- 57567 … the call
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, a10, m240, m248, m200, m208, fr1, rd1, wr1⟩ :=
    n57h_call (p := p) (P := P) (R := R) x ω μ U F a W 77016 ⟨by omega, by omega⟩ (by omega) (Or.inr (by omega))
      h1 h6 h5 (by omega) hf.buf hf.vt (fun c h1 h2 => Memory.readable_of_writable (hst c (by omega) (by omega)))
      (fun c h1 h2 => hst c (by omega) (by omega))
  have H1 : HeapCtx env pb S0 S1 μ1 s := ctx_hi H (fun c hc => fr1 c (by omega) (Or.inl (by omega))) wr1
  have K1 : Keeps pb (U + 80) (fun c => W ≤ c ∧ c < W + 24) sA μ μ1 s :=
    Keeps.of_frame (Z := fun c => U ≤ c ∧ c < U + 56) hf.str.base (fun c hc hz => fr1 c hc (by omega)) rd1
      wr1 (fun c hz => hst c (by omega) (by omega)) (fun c hz h => by omega)
      (fun c hz hg => by unfold Glob at hg; omega)
      (fun d hd hu c hc => by
        have := chunk_bounds H.wf (hf.str.base d hd hu)
        have := H.hbT
        unfold InData at hc; omega)
  have KA1 : Keeps pb spA (fun c => W ≤ c ∧ c < W + 24) sA μA μ1 s := by
    have := KA.trans' (K1.mono (sp' := spA) (by omega) (fun c h => h))
    rwa [Nat.max_self] at this
  have hro1 := K1.ro_low H
  have hrow : RoW μ1 := (RoW.mk hf.vws hf.vwc hf.vrd).congr (fun c h1 h2 => hro1 c h2)
  have kro : ∀ c, c < 196608 → μ1.read c = μA.read c := fun c hc =>
    KA1.ro c (by omega) (Or.inl (by unfold pageSize; omega))
      (by rw [← (KA1.access c (Or.inl (by unfold pageSize; omega))).2]; exact H1.ro c hc)
  have hs1 : Str sA s μ1 W cap len := hf.str.update (fun j hj => fr1 _ (by omega) (Or.inr (by omega)))
    ((rdN_frame (μ := μ) (μ' := μ1) (fun j hj => by
      rw [show W + 16 + j = W + (16 + j) by omega, fr1 _ (by omega) (Or.inr (by omega))])).trans hf.str.rl)
    hf.str.le
  -- the argument: 57922 over the slice (a, 8) at U + 40
  have hok := slice_hex_okW (p := p) (P := P) (R := R) env pb S0 S1 800 (Nat.le_refl _) HA HR μ1 sA U W (U + 40) a
    8 (by omega) ⟨by omega, by omega, Or.inl (by omega)⟩
    (fun c h1 h2 => Memory.readable_of_writable (by rw [wr1]; exact hst c (by omega) (by omega))) m240 m248
    ⟨by omega, by omega⟩ (fun j hj => (helts j hj).rebase H1 hS (by omega) KA1) ha
    (hRO3.congr (fun c h1 h2 => kro c (by omega)))
  have hA : ArgsAtW p P R env pb S0 S1 800 μ1 sA U W U 0 [.lit 2, .arg, .lit 3] 16
      (1073741924 + 8 * 536875500) := by
    intro j hj
    simp only [nargs] at hj
    have hj0 : j = 0 := by omega
    subst hj0
    refine ⟨U + 40, 2534, 57922, by omega, by omega, Or.inl (by omega),
      fun c h1 h2 => Memory.readable_of_writable (by rw [wr1]; exact hst c (by omega) (by omega)),
      by rw [show U + 16 * (0 + 0) = U by omega]; exact m200,
      by rw [show U + 16 * (0 + 0) + 8 = U + 8 by omega]; exact m208, by decide, jte_1266, bs_57922, hok⟩
  rcases fmt_writeW (p := p) (P := P) (R := R) env pb S0 S1 800 (by omega) HA HR μ1 sA U U W 70824 U
      2514 57604 ω[5].toNat ω[6].toNat 16 (1073741924 + 8 * 536875500) [.lit 2, .arg, .lit 3] x ω1 μ1 s cap len H1
      hba hs1 ((Keeps.refl _ _ _ _ _).rebase hs1.base) a0 a1 (by rw [a5, UInt64.ofNat_toNat])
      (by rw [a6, UInt64.ofNat_toNat]) a7 a8 a9 a10 ⟨UInt64.toNat_lt _, UInt64.toNat_lt _⟩ (by decide) jte_1256
      bs_57604 ⟨by omega, hU.2.1, by omega⟩ ⟨by omega, Nat.le_refl _, hW.2⟩ hrow
      ((hRO4.congr (fun c h1 h2 => kro c (by omega))).tmpl hrow.vrd) (by simp only [tsize]; omega)
      ⟨by omega, by omega⟩ hA (by simp only [nargs]; omega) (by simp only [tlen]; omega) with
    ⟨ω2, μ2, x2, s2, cap2, n, hn2, run2, H2, hb2, hs2, hc21, hc22, K2, e0, e1, e5, e6, e7⟩ | hx
  · have kU : ∀ c, U + 56 ≤ c → c < U + 80 → μ2.read c = μ.read c := fun c h1 h2 => by
      rw [K2.hi c (by omega) (by omega) (by omega), fr1 c (by omega) (Or.inr (by omega))]
    obtain ⟨ω3, run3, g0, g1, g5, g6, g7⟩ := n57h_ret (p := p) (P := P) (R := R) x2 ω2 μ2 U r0 t v5 v6
      ⟨by omega, by omega⟩ e1
      (by rw [rdN_frame (fun j hj => kU _ (by omega) (by omega))]; exact r272)
      (by rw [rdN_frame (fun j hj => kU _ (by omega) (by omega))]; exact r264)
      (by rw [rdN_frame (fun j hj => kU _ (by omega) (by omega))]; exact r256) hret hjt hbt
      (fun c h1 h2 => Memory.readable_of_writable (H2.st c (by omega) (by omega)))
    have Kf : Keeps pb (U + 80) (fun c => W ≤ c ∧ c < W + 24) sA μ μ2 s2 := by
      have := K1.trans' (K2.mono (sp' := U + 80) (by omega) (fun c h => h))
      rwa [Nat.max_self] at this
    have kF : ∀ c, F ≤ c → c < F + 24 → μ2.read c = μ.read c := fun c h1 h2 =>
      Kf.hi c (by omega) (by omega) (by omega)
    have kro2 : ∀ c, 65536 ≤ c → c < 77144 → μ2.read c = μ.read c := fun c h1 h2 =>
      Kf.ro c (by omega) (Or.inl (by unfold pageSize; omega)) (hro c (by omega))
    refine Or.inl ⟨ω3, μ2, x2, s2, cap2, n, by simpa only [tlen] using hn2,
      ((run1.trans run2).trans run3).mono (by simp only [tcost]; omega), H2, hb2,
      ⟨?_, ?_, ?_, ?_, ?_, ?_, fun c h1 h2 => ?_, hs2⟩, hc21, hc22, Kf, g0, g1, g5, g6, g7.trans e7⟩
    · rw [rdN_frame (fun j hj => kF _ (by omega) (by omega))]; exact hf.buf
    · rw [rdN_frame (fun j hj => kF _ (by omega) (by omega))]; exact hf.vt
    · rw [rdN_frame (fun j hj => kF _ (by omega) (by omega))]; exact hf.opts
    · rw [rdN_frame (fun j hj => kF _ (by omega) (by omega))]; exact hf.width
    · rw [rdN_frame (fun j hj => kro2 _ (by omega) (by omega))]; exact hf.vws
    · rw [rdN_frame (fun j hj => kro2 _ (by omega) (by omega))]; exact hf.vwc
    · rw [(Kf.access c (Or.inl (by unfold pageSize; omega))).1]; exact hf.vrd c h1 h2
  · exact Or.inr ((Exhausts.pre run1 hx).mono (by simp only [tcost]; omega))

end Services.Bootstrap.Fmt
