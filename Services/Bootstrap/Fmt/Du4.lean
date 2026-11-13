import Services.Bootstrap.Fmt.Du3

/-!
# `<u32 as fmt::Display>::fmt`: from the last digit to the return

`du_tail` (68665): the last digit (`du_one`), the call of `pad_integral` (`du_call`, `pad_plain`)
and the return (`du_ret`).
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **From the last digit to the return** (68665): with the frame T = sp − 72 (ω₁), the `Formatter`
    F (ω₆), the table (ω₇), the quotient q < 10 (ω₈), the offset d (ω₉, 1 ≤ d ≤ 20), the value (ω₁₂)
    and the caller's ω₀, ω₅, ω₆ saved at T + 64, T + 56, T + 48: the digits T + 36 + d' … T + 48 are
    written to the `String` through `pad_integral`, and the function returns as `pad_plain` says. -/
theorem du_tail {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (x : X) (ω : Regs) (μ : Memory) (s₀ s : State) (sp F W q d y cap len ret t v5 v6 : Nat)
    (H : HeapCtx env pb S0 S1 μ s) (hba : s.base % 8 = 0) (hf : Fmtr s₀ s μ F W cap len)
    (h1 : ω[1] = UInt64.ofNat (sp - 80)) (h6 : ω[10] = UInt64.ofNat F) (h7 : ω[3] = UInt64.ofNat 70844)
    (h8 : ω[5] = UInt64.ofNat q) (h9 : ω[11] = UInt64.ofNat d) (h12 : ω[2] = UInt64.ofNat y)
    (hq : q < 10) (hd : d ≤ 20 ∧ (y = 0 ∨ q ≠ 0 → 1 ≤ d)) (hy : y < 18446744073709551616)
    (rr : rdN μ (sp - 80 + 72) 8 = ret) (r5 : rdN μ (sp - 80 + 64) 8 = v5) (r6 : rdN μ (sp - 80 + 56) 8 = v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hsp : S0 + 528 ≤ sp ∧ sp % 8 = 0 ∧ 2147484176 ≤ sp) (hW : sp ≤ W ∧ W + 24 ≤ S1)
    (hF : sp ≤ F ∧ F + 24 ≤ S1 ∧ (F + 24 ≤ W ∨ W + 24 ≤ F))
    (hn : len + 20 < 134217728) :
    (∃ ω' μ' x' s' cap' n, n ≤ 20 ∧
      FreeStepsH p R 68665 ω μ x t ω' μ' x' (7 * n + 2 * (cap' - cap) + 2200) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Fmtr s₀ s' μ' F W cap' (len + n) ∧ cap ≤ cap' ∧
      cap' ≤ max cap (max 8 (2 * (len + n))) ∧
      Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) s₀ μ μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0) ∨
    Exhausts p R pb 68665 ω μ x (1073741824 + 2400) := by
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  obtain ⟨ω1, μ1, run1, a1, a6, a9, fr1, rd1, wr1⟩ := du_one (p := p) (P := P) (R := R) x ω μ (sp - 80) q d y
    ⟨by omega, by omega⟩ (by omega) hd hy h1 h7 h8 h9 h12 hf.vrd (hst _ (by omega) (by omega))
  generalize hd'd : (if y = 0 ∨ q ≠ 0 then d - 1 else d) = d' at a9
  have hd' : d' ≤ 20 := by rw [← hd'd]; split <;> omega
  obtain ⟨ω2, run2, b0, b1, b5, b6, b7, b10, b11, b12⟩ := du_call (p := p) (P := P) (R := R) x ω1 μ1 (sp - 80) d' F
    ⟨by omega, by omega⟩ hd' (by omega) (a1.trans h1) (a6.trans h6) a9
  have k1 : ∀ a, a < 4294967296 → (a < sp - 80 + 35 ∨ sp - 80 + 56 ≤ a) → μ1.read a = μ.read a :=
    fun a h1 h2 => fr1 a h1 (by omega)
  have wr1' := wr1
  have H1 : HeapCtx env pb S0 S1 μ1 s := ctx_hi H (fun a ha => k1 a (by omega) (Or.inl (by omega))) wr1
  have hf1 : Fmtr s₀ s μ1 F W cap len := hf.congr (fun j hj => k1 _ (by omega) (Or.inr (by omega)))
    (fun j hj => k1 _ (by omega) (Or.inr (by omega)))
    (fun a h1 h2 => ⟨k1 a (by omega) (Or.inl (by omega)), rd1 a⟩)
  have K1 : Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) s₀ μ μ1 s :=
    Keeps.of_frame (Z := fun a => sp - 80 + 35 ≤ a ∧ a < sp - 80 + 56) hf.str.base
      (fun a ha hz => k1 a ha (by omega)) rd1 wr1 (fun a hz => hst a (by omega) (by omega))
      (fun a hz h => by omega) (fun a hz hg => by unfold Glob at hg; omega)
      (fun c hc hu a ha => by
        have := chunk_bounds H.wf (hf.str.base c hc hu)
        have := H.hbT
        unfold InData at ha; omega)
  rcases pad_plain (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω2 μ1 s₀ s (sp - 80) F W (sp - 80 + 36 + d')
      (20 - d') cap len 2806 68715 ω2[5].toNat ω2[6].toNat 0 H1 hba hf1 b0 (b1.trans (a1.trans h1))
      UInt64.ofNat_toNat.symm UInt64.ofNat_toNat.symm b7 b10 b11 b12
      ⟨UInt64.toNat_lt _, UInt64.toNat_lt _, by omega⟩
      (by decide) jte_1402 bs_68715
      ⟨by omega, by omega, by omega⟩ ⟨by omega, hW.2⟩ ⟨by omega, hF.2⟩ (by omega)
      (Or.inr ⟨by omega, by omega, Or.inl (by omega)⟩)
      (fun a h1 h2 => Memory.readable_of_writable (by rw [wr1]; exact hst a (by omega) (by omega))) with
    ⟨ω3, μ3, x3, s', cap', run3, H3, hb3, hf3, hc1, hc2, K3, e0, e1, e5, e6, e7⟩ | hx
  · have K := K1.trans' (K3.mono (sp' := sp) (by omega) (fun _ h => h))
    rw [Nat.max_self] at K
    have kk : ∀ a, sp - 80 + 56 ≤ a → a < sp → μ3.read a = μ.read a := fun a h1 h2 => by
      rw [K3.hi a (by omega) (by omega) (by omega), k1 a (by omega) (Or.inr h1)]
    obtain ⟨ω4, run4, f0, f1, f5, f6, f7⟩ := du_ret (p := p) (P := P) (R := R) x3 ω3 μ3 (sp - 80) ret v5 v6 t
      ⟨by omega, by omega⟩ e1
      (by rw [rdN_frame (fun j hj => kk _ (by omega) (by omega))]; exact rr)
      (by rw [rdN_frame (fun j hj => kk _ (by omega) (by omega))]; exact r5)
      (by rw [rdN_frame (fun j hj => kk _ (by omega) (by omega))]; exact r6)
      hret hjt hbt (fun a h1 h2 => Memory.readable_of_writable (H3.st a (by omega) (by omega)))
    exact Or.inl ⟨ω4, μ3, x3, s', cap', 20 - d', by omega,
      (((run1.trans run2).trans run3).trans run4).mono (by omega), H3, hb3, hf3, hc1, hc2, K, f0,
      by rw [f1, show sp - 80 + 80 = sp by omega], f5, f6, f7.trans e7⟩
  · exact Or.inr ((Exhausts.pre (run1.trans run2) hx).mono (by omega))

/-- **From the digit pair to the return**: at 68620 when q > 9 (`du_two`, then `du_tail`), else at
    68665 (`du_tail`). -/
theorem du_mid {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (x : X) (ω : Regs) (μ : Memory) (s₀ s : State) (sp F W q d y cap len ret t v5 v6 : Nat)
    (H : HeapCtx env pb S0 S1 μ s) (hba : s.base % 8 = 0) (hf : Fmtr s₀ s μ F W cap len)
    (h1 : ω[1] = UInt64.ofNat (sp - 80)) (h6 : ω[10] = UInt64.ofNat F) (h7 : ω[3] = UInt64.ofNat 70844)
    (h8 : ω[5] = UInt64.ofNat q) (h9 : ω[11] = UInt64.ofNat d) (h12 : ω[2] = UInt64.ofNat y)
    (hq : q < 1000) (hd : (9 < q → 2 ≤ d) ∧ d ≤ 20 ∧ (y = 0 ∨ q ≠ 0 → 1 ≤ d))
    (hcond : 9 < q → y = 0 ∨ q / 100 ≠ 0 → 3 ≤ d)
    (hy : y < 18446744073709551616)
    (rr : rdN μ (sp - 80 + 72) 8 = ret) (r5 : rdN μ (sp - 80 + 64) 8 = v5) (r6 : rdN μ (sp - 80 + 56) 8 = v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hsp : S0 + 528 ≤ sp ∧ sp % 8 = 0 ∧ 2147484176 ≤ sp) (hW : sp ≤ W ∧ W + 24 ≤ S1)
    (hF : sp ≤ F ∧ F + 24 ≤ S1 ∧ (F + 24 ≤ W ∨ W + 24 ≤ F))
    (hn : len + 20 < 134217728) :
    (∃ ω' μ' x' s' cap' n, n ≤ 20 ∧
      FreeStepsH p R (if 9 < q then 68620 else 68665) ω μ x t ω' μ' x' (7 * n + 2 * (cap' - cap) + 2300) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Fmtr s₀ s' μ' F W cap' (len + n) ∧ cap ≤ cap' ∧
      cap' ≤ max cap (max 8 (2 * (len + n))) ∧
      Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) s₀ μ μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0) ∨
    Exhausts p R pb (if 9 < q then 68620 else 68665) ω μ x (1073741824 + 2500) := by
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  by_cases hc : 9 < q
  · rw [if_pos hc]
    obtain ⟨ω1, μ1, run1, a1, a12, a7, a6, a8, a9, fr1, rd1, wr1⟩ := du_two (p := p) (P := P) (R := R)
      x ω μ (sp - 80) q d ⟨by omega, by omega⟩ (by omega) ⟨hd.1 hc, hd.2.1⟩ h1 h7 h8 h9 hf.vrd
      (fun a h1 h2 => hst a (by omega) (by omega))
    have k1 : ∀ a, a < 4294967296 → (a < sp - 80 + 34 ∨ sp - 80 + 56 ≤ a) → μ1.read a = μ.read a :=
      fun a h1 h2 => fr1 a h1 (by omega)
    have H1 : HeapCtx env pb S0 S1 μ1 s := ctx_hi H (fun a ha => k1 a (by omega) (Or.inl (by omega))) wr1
    have hf1 : Fmtr s₀ s μ1 F W cap len := hf.congr (fun j hj => k1 _ (by omega) (Or.inr (by omega)))
      (fun j hj => k1 _ (by omega) (Or.inr (by omega)))
      (fun a h1 h2 => ⟨k1 a (by omega) (Or.inl (by omega)), rd1 a⟩)
    have K1 : Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) s₀ μ μ1 s :=
      Keeps.of_frame (Z := fun a => sp - 80 + 34 ≤ a ∧ a < sp - 80 + 56) hf.str.base
        (fun a ha hz => k1 a ha (by omega)) rd1 wr1 (fun a hz => hst a (by omega) (by omega))
        (fun a hz h => by omega) (fun a hz hg => by unfold Glob at hg; omega)
        (fun c hc hu a ha => by
          have := chunk_bounds H.wf (hf.str.base c hc hu)
          have := H.hbT
          unfold InData at ha; omega)
    have kk : ∀ o, 56 ≤ o → o + 8 ≤ 80 → rdN μ1 (sp - 80 + o) 8 = rdN μ (sp - 80 + o) 8 := fun o h1 h2 =>
      rdN_frame (fun j hj => k1 _ (by omega) (Or.inr (by omega)))
    rcases du_tail (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω1 μ1 s₀ s sp F W (q / 100) (d - 2) y cap len
        ret t v5 v6 H1 hba hf1 (a1.trans h1) (a6.trans h6) (a7.trans h7) a8 a9 (a12.trans h12) (by omega)
        ⟨by omega, fun h => by have := hcond hc h; omega⟩ hy
        (by rw [kk 72 (by omega) (by omega)]; exact rr) (by rw [kk 64 (by omega) (by omega)]; exact r5)
        (by rw [kk 56 (by omega) (by omega)]; exact r6) hret hjt hbt hsp hW hF hn with
      ⟨ω2, μ2, x2, s', cap', n, hn', run2, H2, hb2, hf2, hc1, hc2, K2, e⟩ | hx
    · have K := K1.trans' K2
      rw [Nat.max_self] at K
      exact Or.inl ⟨ω2, μ2, x2, s', cap', n, hn', (run1.trans run2).mono (by omega), H2, hb2, hf2, hc1, hc2, K, e⟩
    · exact Or.inr ((Exhausts.pre run1 hx).mono (by omega))
  · rw [if_neg hc]
    rcases du_tail (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω μ s₀ s sp F W q d y cap len
        ret t v5 v6 H hba hf h1 h6 h7 h8 h9 h12 (by omega) ⟨hd.2.1, hd.2.2⟩ hy rr r5 r6
        hret hjt hbt hsp hW hF hn with
      ⟨ω2, μ2, x2, s', cap', n, hn', run2, rest⟩ | hx
    · exact Or.inl ⟨ω2, μ2, x2, s', cap', n, hn', run2.mono (by omega), rest⟩
    · exact Or.inr (hx.mono (by omega))

end Services.Bootstrap.Fmt
