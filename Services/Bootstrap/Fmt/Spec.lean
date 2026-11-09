import Services.Bootstrap.Fmt.Sink
import Services.Bootstrap.Fmt.PadIntegral

/-!
# A `Formatter` writing into a `String`, and `pad_integral` through it

`Fmtr s₀ s μ F W cap len`: memory μ holds, at F, a `Formatter` whose sink is the `String` at W,
with:
- the `String`'s `fmt::Write` vtable (77016) at F + 8;
- plain options: the word 0x60000020 at F + 16 and width 0 at F + 20 (`{}`, `{:?}`, `{:x}`);
- the vtable's `write_str` (2596) and `write_char` (2592) in read-only data;
- the `String` itself (`Str`).

`pad_plain`: `pad_integral` (61857) through such a `Formatter` is `write_str` of the digits.
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **A `Formatter` at F writing into the `String` at W.** -/
structure Fmtr (s₀ s : State) (μ : Memory) (F W cap len : Nat) : Prop where
  buf : rdN μ F 8 = W
  vt : rdN μ (F + 8) 8 = 77016
  opts : rdN μ (F + 16) 4 = 1610612768
  width : rdN μ (F + 20) 2 = 0
  vws : rdN μ 77040 8 = 2596
  vwc : rdN μ 77048 8 = 2592
  vrd : ∀ a, 77016 ≤ a → a < 77064 → μ.readable a = true
  str : Str s₀ s μ W cap len

/-- **`pad_integral` with plain options** (61857): through a `Formatter` F into the `String` W, the
    len octets of digits at dig are written by the sink's `write_str` and `pad_integral` returns to
    `t` as `write_str` does: `Ok`, the `String` len + n long, the context and the frame kept (from
    sp up only W … W + 24 changes), or a failed allocator call. -/
theorem pad_plain {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (x : X) (ω : Regs) (μ : Memory) (s₀ s : State) (sp F W dig n cap len ret t v5 v6 pl : Nat)
    (H : HeapCtx env pb S0 S1 μ s) (hba : s.base % 8 = 0) (hf : Fmtr s₀ s μ F W cap len)
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
      (sp + 8 ≤ dig ∧ dig + n + 16 < 4294967296 ∧ (dig + n ≤ W ∨ W + 24 ≤ dig)))
    (hr : ∀ a, dig ≤ a → a < dig + n → μ.readable a = true) :
    (∃ ω' μ' x' s' cap', FreeStepsH p R 61857 ω μ x t ω' μ' x' (7 * n + 2 * (cap' - cap) + 2100) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Fmtr s₀ s' μ' F W cap' (len + n) ∧ cap ≤ cap' ∧
      cap' ≤ max cap (max 8 (2 * (len + n))) ∧
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
    pi_a (p := p) (P := P) (R := R) x ω μ sp F dig n ret v5 v6 W 77016 pl ⟨by omega, by omega⟩ h0 h1 h5 h6 h7
      h10 h11 h12 ⟨by omega, hv.1, hv.2.1, by omega, by omega, hv.2.2⟩ (Or.inr hF.1) (by omega) hf.opts hf.width
      hf.buf hf.vt ⟨by omega, by omega⟩ (fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)))
      (fun a h1 h2 => hst a (by omega) (by omega))
  -- write_prefix
  obtain ⟨ω2, μ2, run2, b1, b5, b6, b7, fr2, rd2, wr2⟩ := pi_b (p := p) (P := P) (R := R) x ω1 μ1 (sp - 104)
    ⟨by omega, by omega⟩ a0 a1 a9 a10 (fun a h1 h2 => by rw [wr1]; exact hst a (by omega) (by omega))
  have k2 : ∀ a, sp - 104 ≤ a → a < 4294967296 → μ2.read a = μ1.read a := fun a h1 h2 => fr2 a h2 (Or.inr h1)
  have k12 : ∀ a, a < 4294967296 → (a < sp - 144 ∨ sp ≤ a) → μ2.read a = μ.read a := fun a h1 h2 => by
    rw [fr2 a h1 (by omega), fr1 a h1 (by omega)]
  -- the low reads: the vtable is read-only data, kept
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
    have kro : ∀ a, 77016 ≤ a → a < 77064 → μ4.read a = μ.read a := fun a h1 h2 =>
      K.ro a (by omega) (Or.inl (by unfold pageSize; omega)) (hro a (by omega))
    refine Or.inl ⟨ω4, μ4, x4, s', cap', (((run1.trans run2).trans run3).trans run4).mono (by omega), H4, hb4,
      ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a h1 h2 => ?_, hs4⟩, hc1, hc2, K, e0, e1, e5, e6, e7⟩
    · rw [rdN_frame (fun j hj => kF _ (by omega) (by omega))]; exact hf.buf
    · rw [rdN_frame (fun j hj => kF _ (by omega) (by omega))]; exact hf.vt
    · rw [rdN_frame (fun j hj => kF _ (by omega) (by omega))]; exact hf.opts
    · rw [rdN_frame (fun j hj => kF _ (by omega) (by omega))]; exact hf.width
    · rw [rdN_frame (fun j hj => kro _ (by omega) (by omega))]; exact hf.vws
    · rw [rdN_frame (fun j hj => kro _ (by omega) (by omega))]; exact hf.vwc
    · rw [(K.access a (Or.inl (by unfold pageSize; omega))).1]; exact hf.vrd a h1 h2
  · exact Or.inr ((Exhausts.pre ((run1.trans run2).trans run3) hx).mono (by omega))

end Services.Bootstrap.Fmt
