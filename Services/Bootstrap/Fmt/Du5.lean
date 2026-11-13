import Services.Bootstrap.Fmt.Du4

/-!
# `<u64 as fmt::Display>::fmt` (68449), frame-only: `dec64`
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **`<u64 as fmt::Display>::fmt`, frame-only** (68449): called with the address v of a u64 (ω₇), a
    `Formatter` F into the `String` W with plain options (ω₈), and a return address ω₀ that `djump`
    resolves to `t`, it either:
    - returns `Ok` (ω₇ = 0) to `t`, with ω₀, ω₁, ω₅, ω₆ as they were. The `String` has gained n ≤ 20
      octets (the digits, unspecified), the context is kept, and the frame `Keeps`: from sp up only
      W … W + 24 changes. Or
    - reaches a failed allocator call. -/
theorem dec64 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (x : X) (ω : Regs) (μ : Memory) (s₀ s : State) (sp F W v cap len ret t v5 v6 : Nat)
    (H : HeapCtx env pb S0 S1 μ s) (hba : s.base % 8 = 0) (hf : Fmtr s₀ s μ F W cap len)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat F)
    (hv : v5 < 18446744073709551616 ∧ v6 < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hsp : S0 + 600 ≤ sp ∧ sp % 8 = 0 ∧ 2147484248 ≤ sp) (hW : sp ≤ W ∧ W + 24 ≤ S1)
    (hF : sp ≤ F ∧ F + 24 ≤ S1 ∧ (F + 24 ≤ W ∨ W + 24 ≤ F))
    (hvv : sp ≤ v ∧ v + 8 < 4294967296) (hrv : ∀ a, v ≤ a → a < v + 8 → μ.readable a = true)
    (hn : len + 20 < 134217728) :
    (∃ ω' μ' x' s' cap' n, n ≤ 20 ∧
      FreeStepsH p R 68449 ω μ x t ω' μ' x' (7 * n + 2 * (cap' - cap) + 2700) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Fmtr s₀ s' μ' F W cap' (len + n) ∧ cap ≤ cap' ∧
      cap' ≤ max cap (max 8 (2 * (len + n))) ∧
      Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) s₀ μ μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0) ∨
    Exhausts p R pb 68449 ω μ x (1073741824 + 2900) := by
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  have hX := rdN_lt64 μ v
  obtain ⟨ω1, μ1, run1, a1, a10, a3, a2, sv0, sv5, sv6, fr1, rd1, wr1⟩ := du_entry (p := p) (P := P) (R := R)
    x ω μ sp v F ret v5 v6 ⟨by omega, by omega⟩ h0 h1 h5 h6 h7 h8 ⟨by omega, hv.1, hv.2, by omega⟩
    (by omega) (Or.inr hvv.1) hrv (fun a h1 h2 => hst a (by omega) (by omega))
  generalize hXd : rdN μ v 8 = Xv at run1 a2 hX
  have k1 : ∀ a, a < 4294967296 → (a < sp - 80 ∨ sp ≤ a) → μ1.read a = μ.read a := fun a h1 h2 =>
    fr1 a h1 (by omega)
  have fin : ∀ (ω2 : Regs) (μ2 : Memory) (q d y N : Nat),
      FreeStepsH p R 68449 ω μ x (if 9 < q then 68620 else 68665) ω2 μ2 x N → N ≤ 260 →
      (∀ a, a < 4294967296 → (a < sp - 80 ∨ sp ≤ a) → μ2.read a = μ.read a) →
      (∀ a, μ2.readable a = μ.readable a) → (∀ a, μ2.writable a = μ.writable a) →
      ω2[1] = UInt64.ofNat (sp - 80) → ω2[10] = UInt64.ofNat F → ω2[3] = UInt64.ofNat 70844 →
      ω2[5] = UInt64.ofNat q → ω2[11] = UInt64.ofNat d → ω2[2] = UInt64.ofNat y →
      q < 1000 → (9 < q → 2 ≤ d) → d ≤ 20 → (y = 0 ∨ q ≠ 0 → 1 ≤ d) →
      (9 < q → y = 0 ∨ q / 100 ≠ 0 → 3 ≤ d) → y < 18446744073709551616 →
      rdN μ2 (sp - 80 + 72) 8 = ret → rdN μ2 (sp - 80 + 64) 8 = v5 → rdN μ2 (sp - 80 + 56) 8 = v6 →
      (∃ ω' μ' x' s' cap' n, n ≤ 20 ∧
        FreeStepsH p R 68449 ω μ x t ω' μ' x' (7 * n + 2 * (cap' - cap) + 2700) ∧
        HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Fmtr s₀ s' μ' F W cap' (len + n) ∧ cap ≤ cap' ∧
        cap' ≤ max cap (max 8 (2 * (len + n))) ∧
        Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) s₀ μ μ' s' ∧
        ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
        ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0) ∨
      Exhausts p R pb 68449 ω μ x (1073741824 + 2900) := by
    intro ω2 μ2 q d y N run hN k2 rd2 wr2 g1 g6 g7 g8 g9 g12 hq hd2 hd20 hd1 hcond hy r0 r5 r6
    have H2 : HeapCtx env pb S0 S1 μ2 s := ctx_hi H (fun a ha => k2 a (by omega) (Or.inl (by omega))) wr2
    have hf2 : Fmtr s₀ s μ2 F W cap len := hf.congr (fun j hj => k2 _ (by omega) (Or.inr (by omega)))
      (fun j hj => k2 _ (by omega) (Or.inr (by omega)))
      (fun a h1 h2 => ⟨k2 a (by omega) (Or.inl (by omega)), rd2 a⟩)
    have K2 : Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) s₀ μ μ2 s :=
      Keeps.of_frame (Z := fun a => sp - 80 ≤ a ∧ a < sp) hf.str.base
        (fun a ha hz => k2 a ha (by omega)) rd2 wr2 (fun a hz => hst a (by omega) (by omega))
        (fun a hz h => by omega) (fun a hz hg => by unfold Glob at hg; omega)
        (fun c hc hu a ha => by
          have := chunk_bounds H.wf (hf.str.base c hc hu)
          have := H.hbT
          unfold InData at ha; omega)
    rcases du_mid (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω2 μ2 s₀ s sp F W q d y cap len ret t v5 v6
        H2 hba hf2 g1 g6 g7 g8 g9 g12 hq ⟨hd2, hd20, hd1⟩ hcond hy r0 r5 r6 hret hjt hbt
        ⟨by omega, by omega, by omega⟩ hW hF hn with
      ⟨ω3, μ3, x3, s', cap', n, hn', run3, H3, hb3, hf3, hc1, hc2, K3, e⟩ | hx
    · have K := K2.trans' K3
      rw [Nat.max_self] at K
      exact Or.inl ⟨ω3, μ3, x3, s', cap', n, hn', (run.trans run3).mono (by omega), H3, hb3, hf3, hc1, hc2, K, e⟩
    · exact Or.inr ((Exhausts.pre run hx).mono (by omega))
  by_cases hc : Xv < 1000
  · rw [if_pos hc] at run1
    obtain ⟨ω2, run2, b1, b2, b3, b10, b5, b11⟩ := du_short (p := p) (P := P) (R := R) x ω1 μ1 Xv hc a2
    exact fin ω2 μ1 Xv 20 Xv _ (run1.trans run2) (by omega) k1 rd1 wr1 (b1.trans a1) (b10.trans a10)
      (b3.trans a3) b5 b11 (b2.trans a2) hc (fun _ => by omega) (by omega) (fun _ => by omega)
      (fun _ _ => by omega) hX sv0 sv5 sv6
  · rw [if_neg hc] at run1
    obtain ⟨ω2, μ2, run2, b0, b1, b3, b4, b5, b6, b11, b12, c24, c16, cF, cy, fr2, rd2, wr2⟩ := du_setup (p := p)
      (P := P) (R := R) x ω1 μ1 (sp - 80) F Xv ⟨by omega, by omega⟩ a1 a2 a10 ⟨by omega, hX⟩
      (fun a h1 h2 => by rw [wr1]; exact hst a (by omega) (by omega))
    have rd12 : ∀ a, μ2.readable a = μ.readable a := fun a => by rw [rd2, rd1]
    have wr12 : ∀ a, μ2.writable a = μ.writable a := fun a => by rw [wr2, wr1]
    have hX5 : Xv < 1000 * 10000 ^ 5 := by omega
    obtain ⟨ω3, μ3, c, hc1, hc2, run3, d1, d3, d5, dq, d11, d12, fr3, rd3, wr3⟩ := du_loop (p := p) (P := P)
      (R := R) x (sp - 80) ⟨by omega, by omega⟩ 5 Xv 18446744073709551596 (sp - 80 + 55) ω2 μ2 hX (by omega) hX5
      (by omega) (by omega) (by omega) b0 (b1.trans a1) (b3.trans a3) b4 b5 b6 b11 b12 c16 c24
      (fun a h1 h2 => by rw [rd12]; exact hf.vrd a h1 h2)
      (fun a h1 h2 => by rw [wr12]; exact hst a (by omega) (by omega))
    have f3 : ∀ a, a < 4294967296 → (a < sp - 80 + 36 ∨ sp - 80 + 56 ≤ a) → μ3.read a = μ2.read a :=
      fun a h1 h2 => fr3 a h1 (by omega)
    obtain ⟨ω5, run5, g1, g3, g5, g2, g10, g11⟩ := du_post (p := p) (P := P) (R := R) x ω3 μ3 (sp - 80)
      (Xv / 10000 ^ c) ((18446744073709551596 + 4 * c) % 18446744073709551616) F Xv ⟨by omega, by omega⟩ dq
      (by omega) (d1.trans (b1.trans a1)) d5 d11
      (by rw [rdN_frame (fun j hj => f3 _ (by omega) (Or.inl (by omega)))]; exact cF)
      (by rw [show sp - 80 = sp - 80 + 0 by rfl, rdN_frame (fun j hj => f3 _ (by omega) (Or.inl (by omega)))]; exact cy)
      (fun a h1 h2 => by rw [rd3, rd12]; exact Memory.readable_of_writable (hst a (by omega) (by omega)))
    have hd : (18446744073709551616 - (18446744073709551596 + 4 * c) % 18446744073709551616) %
        18446744073709551616 = 20 - 4 * c := by omega
    rw [hd] at g11
    have kk : ∀ a, sp - 80 + 56 ≤ a → a < sp → μ3.read a = μ1.read a := fun a h1 h2 => by
      rw [f3 a (by omega) (Or.inr h1), fr2 a (by omega) (Or.inr (by omega))]
    exact fin ω5 μ3 (Xv / 10000 ^ c) (20 - 4 * c) Xv _ (((run1.trans run2).trans run3).trans run5) (by omega)
      (fun a h1 h2 => by rw [f3 a h1 (by omega), fr2 a h1 (by omega), k1 a h1 h2])
      (fun a => by rw [rd3, rd12]) (fun a => by rw [wr3, wr12])
      (g1.trans (d1.trans (b1.trans a1))) g10 (g3.trans (d3.trans (b3.trans a3))) g5 g11 g2 dq
      (fun h => by
        rcases Nat.lt_or_ge c 5 with h' | h'
        · omega
        · have : Xv / 10000 ^ c = 0 := by
            rw [Nat.div_eq_of_lt]; calc Xv < 18446744073709551616 := hX
              _ < 10000 ^ 5 := by decide
              _ ≤ 10000 ^ c := Nat.pow_le_pow_right (by decide) h'
          omega)
      (by omega)
      (fun h => by
        rcases h with h | h
        · omega
        · rcases Nat.lt_or_ge c 5 with h' | h'
          · omega
          · have : Xv / 10000 ^ c = 0 := by
              rw [Nat.div_eq_of_lt]; calc Xv < 18446744073709551616 := hX
                _ < 10000 ^ 5 := by decide
                _ ≤ 10000 ^ c := Nat.pow_le_pow_right (by decide) h'
            omega)
      (fun h1 h2 => by
        rcases Nat.lt_or_ge c 5 with h' | h'
        · omega
        · have : Xv / 10000 ^ c = 0 := by
            rw [Nat.div_eq_of_lt]; calc Xv < 18446744073709551616 := hX
              _ < 10000 ^ 5 := by decide
              _ ≤ 10000 ^ c := Nat.pow_le_pow_right (by decide) h'
          omega)
      hX
      (by rw [rdN_frame (fun j hj => kk _ (by omega) (by omega))]; exact sv0)
      (by rw [rdN_frame (fun j hj => kk _ (by omega) (by omega))]; exact sv5)
      (by rw [rdN_frame (fun j hj => kk _ (by omega) (by omega))]; exact sv6)

end Services.Bootstrap.Fmt
