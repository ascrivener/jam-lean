import Services.Bootstrap.Fmt.Dec2

/-!
# `<u32 as fmt::Display>::fmt`: from the last digit to the return

`dl_tail` (68385): the last digit (`dl_one`), the call of `pad_integral` (`dl_call`, `pad_plain`)
and the return (`dl_ret`).
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **From the last digit to the return** (68385): with the frame T = sp − 72 (ω₁), the `Formatter`
    F (ω₆), the table (ω₇), the quotient q < 10 (ω₈), the offset d (ω₉, 1 ≤ d ≤ 10), the value (ω₁₂)
    and the caller's ω₀, ω₅, ω₆ saved at T + 64, T + 56, T + 48: the digits T + 38 + d' … T + 48 are
    written to the `String` through `pad_integral`, and the function returns as `pad_plain` says. -/
theorem dl_tail {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (x : X) (ω : Regs) (μ : Memory) (s₀ s : State) (sp F W q d y cap len ret t v5 v6 : Nat)
    (H : HeapCtx env pb S0 S1 μ s) (hba : s.base % 8 = 0) (hf : Fmtr s₀ s μ F W cap len)
    (h1 : ω[1] = UInt64.ofNat (sp - 72)) (h6 : ω[6] = UInt64.ofNat F) (h7 : ω[7] = UInt64.ofNat 70844)
    (h8 : ω[8] = UInt64.ofNat q) (h9 : ω[9] = UInt64.ofNat d) (h12 : ω[12] = UInt64.ofNat y)
    (hq : q < 10) (hd : 1 ≤ d ∧ d ≤ 10) (hy : y < 18446744073709551616)
    (rr : rdN μ (sp - 72 + 64) 8 = ret) (r5 : rdN μ (sp - 72 + 56) 8 = v5) (r6 : rdN μ (sp - 72 + 48) 8 = v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hsp : S0 + 520 ≤ sp ∧ sp % 8 = 0 ∧ 2147484168 ≤ sp) (hW : sp ≤ W ∧ W + 24 ≤ S1)
    (hF : sp ≤ F ∧ F + 24 ≤ S1 ∧ (F + 24 ≤ W ∨ W + 24 ≤ F))
    (hn : len + 10 < 134217728) :
    (∃ ω' μ' x' s' cap' n, n ≤ 10 ∧
      FreeStepsH p R 68385 ω μ x t ω' μ' x' (7 * n + 2 * (cap' - cap) + 2200) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Fmtr s₀ s' μ' F W cap' (len + n) ∧ cap ≤ cap' ∧
      cap' ≤ max cap (max 8 (2 * (len + n))) ∧
      Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) s₀ μ μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0) ∨
    Exhausts p R pb 68385 ω μ x (1073741824 + 2400) := by
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  obtain ⟨ω1, μ1, run1, a1, a5, a6, a9, fr1, rd1, wr1⟩ := dl_one (p := p) (P := P) (R := R) x ω μ (sp - 72) q d y
    ⟨by omega, by omega⟩ (by omega) hd hy h1 h7 h8 h9 h12 hf.vrd (hst _ (by omega) (by omega))
  generalize hd'd : (if y = 0 ∨ q ≠ 0 then d - 1 else d) = d' at a9
  have hd' : d' ≤ 10 ∧ d - 1 ≤ d' := by rw [← hd'd]; split <;> omega
  obtain ⟨ω2, run2, b0, b1, b5, b6, b7, b10, b11, b12⟩ := dl_call (p := p) (P := P) (R := R) x ω1 μ1 (sp - 72) d' F
    ⟨by omega, by omega⟩ hd'.1 (by omega) (a1.trans h1) (a6.trans h6) a9
  have k1 : ∀ a, a < 4294967296 → (a < sp - 72 + 38 ∨ sp - 72 + 48 ≤ a) → μ1.read a = μ.read a :=
    fun a h1 h2 => fr1 a h1 (by omega)
  have wr1' := wr1
  have H1 : HeapCtx env pb S0 S1 μ1 s := ctx_hi H (fun a ha => k1 a (by omega) (Or.inl (by omega))) wr1
  have hf1 : Fmtr s₀ s μ1 F W cap len := hf.congr (fun j hj => k1 _ (by omega) (Or.inr (by omega)))
    (fun j hj => k1 _ (by omega) (Or.inr (by omega)))
    (fun a h1 h2 => ⟨k1 a (by omega) (Or.inl (by omega)), rd1 a⟩)
  have K1 : Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) s₀ μ μ1 s :=
    Keeps.of_frame (Z := fun a => sp - 72 + 38 ≤ a ∧ a < sp - 72 + 48) hf.str.base
      (fun a ha hz => k1 a ha (by omega)) rd1 wr1 (fun a hz => hst a (by omega) (by omega))
      (fun a hz h => by omega) (fun a hz hg => by unfold Glob at hg; omega)
      (fun c hc hu a ha => by
        have := chunk_bounds H.wf (hf.str.base c hc hu)
        have := H.hbT
        unfold InData at ha; omega)
  rcases pad_plain (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω2 μ1 s₀ s (sp - 72) F W (sp - 72 + 38 + d')
      (10 - d') cap len 2802 68435 ω2[5].toNat ω2[6].toNat 0 H1 hba hf1 b0 (b1.trans (a1.trans h1))
      UInt64.ofNat_toNat.symm UInt64.ofNat_toNat.symm b7 b10 b11 b12
      ⟨UInt64.toNat_lt _, UInt64.toNat_lt _, by omega⟩
      (by decide) jte_1400 bs_68435
      ⟨by omega, by omega, by omega⟩ ⟨by omega, hW.2⟩ ⟨by omega, hF.2⟩ (by omega)
      (Or.inr ⟨by omega, by omega, Or.inl (by omega)⟩)
      (fun a h1 h2 => Memory.readable_of_writable (by rw [wr1]; exact hst a (by omega) (by omega))) with
    ⟨ω3, μ3, x3, s', cap', run3, H3, hb3, hf3, hc1, hc2, K3, e0, e1, e5, e6, e7⟩ | hx
  · have K := K1.trans' (K3.mono (sp' := sp) (by omega) (fun _ h => h))
    rw [Nat.max_self] at K
    have kk : ∀ a, sp - 72 + 48 ≤ a → a < sp → μ3.read a = μ.read a := fun a h1 h2 => by
      rw [K3.hi a (by omega) (by omega) (by omega), k1 a (by omega) (Or.inr h1)]
    obtain ⟨ω4, run4, f0, f1, f5, f6, f7⟩ := dl_ret (p := p) (P := P) (R := R) x3 ω3 μ3 (sp - 72) ret v5 v6 t
      ⟨by omega, by omega⟩ e1
      (by rw [rdN_frame (fun j hj => kk _ (by omega) (by omega))]; exact rr)
      (by rw [rdN_frame (fun j hj => kk _ (by omega) (by omega))]; exact r5)
      (by rw [rdN_frame (fun j hj => kk _ (by omega) (by omega))]; exact r6)
      hret hjt hbt (fun a h1 h2 => Memory.readable_of_writable (H3.st a (by omega) (by omega)))
    exact Or.inl ⟨ω4, μ3, x3, s', cap', 10 - d', by omega,
      (((run1.trans run2).trans run3).trans run4).mono (by omega), H3, hb3, hf3, hc1, hc2, K, f0,
      by rw [f1, show sp - 72 + 72 = sp by omega], f5, f6, f7.trans e7⟩
  · exact Or.inr ((Exhausts.pre (run1.trans run2) hx).mono (by omega))

end Services.Bootstrap.Fmt
