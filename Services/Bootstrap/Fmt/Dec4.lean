import Services.Bootstrap.Fmt.Dec3

/-!
# `<u32 as fmt::Display>::fmt` (68146), frame-only: `dec32`
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **`<u32 as fmt::Display>::fmt`, frame-only** (68146): called with the address v of a u32 (ω₇), a
    `Formatter` F into the `String` W with plain options (ω₈), and a return address ω₀ that `djump`
    resolves to `t`, it either:
    - returns `Ok` (ω₇ = 0) to `t`, with ω₀, ω₁, ω₅, ω₆ as they were. The `String` has gained n ≤ 10
      octets (the digits, unspecified), the context is kept, and the frame `Keeps`: from sp up only
      W … W + 24 changes. Or
    - reaches a failed allocator call. -/
theorem dec32 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
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
    (hvv : (v + 4 ≤ sp - 72 ∨ sp ≤ v) ∧ v + 4 < 4294967296) (hrv : ∀ a, v ≤ a → a < v + 4 → μ.readable a = true)
    (hn : len + 10 < 134217728) :
    (∃ ω' μ' x' s' cap' n, n ≤ 10 ∧
      FreeStepsH p R 68146 ω μ x t ω' μ' x' (7 * n + 2 * (cap' - cap) + 2500) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Fmtr s₀ s' μ' F W cap' (len + n) ∧ cap ≤ cap' ∧
      cap' ≤ max cap (max 8 (2 * (len + n))) ∧
      Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) s₀ μ μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0) ∨
    Exhausts p R pb 68146 ω μ x (1073741824 + 2700) := by
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  have hX := rdN_lt μ v 4
  have hX' : rdN μ v 4 < 4294967296 := by simpa using hX
  -- the entry
  obtain ⟨ω1, μ1, run1, a1, a6, a7, a12, sv0, sv5, sv6, fr1, rd1, wr1⟩ := dl_entry (p := p) (P := P) (R := R)
    x ω μ sp v F ret v5 v6 ⟨by omega, by omega⟩ h0 h1 h5 h6 h7 h8 ⟨by omega, hv.1, hv.2, by omega⟩
    (by omega) hvv.1 hrv (fun a h1 h2 => hst a (by omega) (by omega))
  generalize hXd : rdN μ v 4 = Xv at run1 a12 hX'
  -- everything from here keeps the memory outside the frame T … sp
  have k1 : ∀ a, a < 4294967296 → (a < sp - 72 ∨ sp ≤ a) → μ1.read a = μ.read a := fun a h1 h2 =>
    fr1 a h1 (by omega)
  -- the common end, from a state whose memory differs from μ only in T … sp
  have fin : ∀ (ω2 : Regs) (μ2 : Memory) (q d y N : Nat),
      FreeStepsH p R 68146 ω μ x (if 9 < q then 68340 else 68385) ω2 μ2 x N → N ≤ 120 →
      (∀ a, a < 4294967296 → (a < sp - 72 ∨ sp ≤ a) → μ2.read a = μ.read a) →
      (∀ a, μ2.readable a = μ.readable a) → (∀ a, μ2.writable a = μ.writable a) →
      ω2[1] = UInt64.ofNat (sp - 72) → ω2[6] = UInt64.ofNat F → ω2[7] = UInt64.ofNat 70844 →
      ω2[8] = UInt64.ofNat q → ω2[9] = UInt64.ofNat d → ω2[12] = UInt64.ofNat y →
      q < 1000 → 2 ≤ d → d ≤ 10 → (9 < q → y = 0 ∨ q / 100 ≠ 0 → 3 ≤ d) → y < 18446744073709551616 →
      rdN μ2 (sp - 72 + 64) 8 = ret → rdN μ2 (sp - 72 + 56) 8 = v5 → rdN μ2 (sp - 72 + 48) 8 = v6 →
      (∃ ω' μ' x' s' cap' n, n ≤ 10 ∧
        FreeStepsH p R 68146 ω μ x t ω' μ' x' (7 * n + 2 * (cap' - cap) + 2500) ∧
        HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Fmtr s₀ s' μ' F W cap' (len + n) ∧ cap ≤ cap' ∧
        cap' ≤ max cap (max 8 (2 * (len + n))) ∧
        Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) s₀ μ μ' s' ∧
        ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
        ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0) ∨
      Exhausts p R pb 68146 ω μ x (1073741824 + 2700) := by
    intro ω2 μ2 q d y N run hN k2 rd2 wr2 g1 g6 g7 g8 g9 g12 hq hd2 hd10 hcond hy r0 r5 r6
    have H2 : HeapCtx env pb S0 S1 μ2 s := ctx_hi H (fun a ha => k2 a (by omega) (Or.inl (by omega))) wr2
    have hf2 : Fmtr s₀ s μ2 F W cap len := hf.congr (fun j hj => k2 _ (by omega) (Or.inr (by omega)))
      (fun j hj => k2 _ (by omega) (Or.inr (by omega)))
      (fun a h1 h2 => ⟨k2 a (by omega) (Or.inl (by omega)), rd2 a⟩)
    have K2 : Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) s₀ μ μ2 s :=
      Keeps.of_frame (Z := fun a => sp - 72 ≤ a ∧ a < sp) hf.str.base
        (fun a ha hz => k2 a ha (by omega)) rd2 wr2 (fun a hz => hst a (by omega) (by omega))
        (fun a hz h => by omega) (fun a hz hg => by unfold Glob at hg; omega)
        (fun c hc hu a ha => by
          have := chunk_bounds H.wf (hf.str.base c hc hu)
          have := H.hbT
          unfold InData at ha; omega)
    rcases dl_mid (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω2 μ2 s₀ s sp F W q d y cap len ret t v5 v6
        H2 hba hf2 g1 g6 g7 g8 g9 g12 hq ⟨hd2, hd10⟩ hcond hy r0 r5 r6 hret hjt hbt ⟨by omega, by omega, by omega⟩ hW hF hn with
      ⟨ω3, μ3, x3, s', cap', n, hn', run3, H3, hb3, hf3, hc1, hc2, K3, e⟩ | hx
    · have K := K2.trans' K3
      rw [Nat.max_self] at K
      exact Or.inl ⟨ω3, μ3, x3, s', cap', n, hn', (run.trans run3).mono (by omega), H3, hb3, hf3, hc1, hc2, K, e⟩
    · exact Or.inr ((Exhausts.pre run hx).mono (by omega))
  have rd01 : ∀ a, μ1.readable a = μ.readable a := rd1
  by_cases hc : Xv < 1000
  · -- below 1000: no loop
    rw [if_pos hc] at run1
    have hsx : sx32 Xv = Xv := by unfold sx32; rw [if_pos (by omega)]
    rw [hsx] at a12
    obtain ⟨ω2, run2, b1, b5, b6, b7, b8, b9, b12⟩ := dl_short (p := p) (P := P) (R := R) x ω1 μ1 Xv hc a12
    have e : (if Xv ≤ 9 then 68385 else 68340) = (if 9 < Xv then 68340 else 68385) := by
      split <;> split <;> omega
    rw [e] at run2
    exact fin ω2 μ1 Xv 10 Xv _ (run1.trans run2) (by omega) k1 rd1 wr1 (b1.trans a1) (b6.trans a6)
      (b7.trans a7) b8 b9 b12 hc (by omega) (by omega) (fun _ _ => by omega) (by omega) sv0 sv5 sv6
  · -- at least 1000: the four-digit loop, once or twice
    rw [if_neg hc] at run1
    have hy64 := sx32_lt Xv hX'
    have hym := sx32_mod Xv hX'
    obtain ⟨ω2, μ2, run2, b1, b2, b3, b5, b6, b7, b8, b9, c24, c16, cF, cy, fr2, rd2, wr2⟩ := dl_setup (p := p)
      (P := P) (R := R) x ω1 μ1 (sp - 72) F (sx32 Xv) ⟨by omega, by omega⟩ a1 a6 a12 ⟨by omega, hy64⟩
      (fun a h1 h2 => by rw [wr1]; exact hst a (by omega) (by omega))
    have k2 : ∀ a, a < 4294967296 → (a < sp - 72 ∨ sp ≤ a) → μ2.read a = μ.read a := fun a h1 h2 => by
      rw [fr2 a h1 (by omega), k1 a h1 h2]
    have rd12 : ∀ a, μ2.readable a = μ.readable a := fun a => by rw [rd2, rd1]
    have wr12 : ∀ a, μ2.writable a = μ.writable a := fun a => by rw [wr2, wr1]
    have hstk : ∀ a, sp - 72 ≤ a → a < sp - 72 + 72 → μ2.writable a = true := fun a h1 h2 => by
      rw [wr12]; exact hst a (by omega) (by omega)
    have hrstk : ∀ a, sp - 72 ≤ a → a < sp - 72 + 72 → μ2.readable a = true := fun a h1 h2 =>
      Memory.readable_of_writable (hstk a h1 h2)
    have hro2 : ∀ a, 65536 ≤ a → a < 77144 → μ2.readable a = true := fun a h1 h2 => by
      rw [rd12]; exact hf.vrd a h1 h2
    -- the saved words, above the digit block
    have sv : ∀ {μ' : Memory}, (∀ a, sp - 72 + 48 ≤ a → a < sp → μ'.read a = μ2.read a) →
        rdN μ' (sp - 72 + 64) 8 = ret ∧ rdN μ' (sp - 72 + 56) 8 = v5 ∧ rdN μ' (sp - 72 + 48) 8 = v6 := by
      intro μ' h
      have kk : ∀ o, 48 ≤ o → o + 8 ≤ 72 → rdN μ' (sp - 72 + o) 8 = rdN μ1 (sp - 72 + o) 8 := fun o h1 h2 => by
        rw [rdN_frame (fun j hj => h _ (by omega) (by omega)),
          rdN_frame (fun j hj => fr2 _ (by omega) (Or.inr (by omega)))]
      exact ⟨(kk 64 (by omega) (by omega)).trans sv0, (kk 56 (by omega) (by omega)).trans sv5,
        (kk 48 (by omega) (by omega)).trans sv6⟩
    obtain ⟨ω3, μ3, run3, d1, d2, d3, d7, d8, d9, fr3, rd3, wr3⟩ := dl_iter (p := p) (P := P) (R := R) x ω2 μ2
      (sp - 72) (sx32 Xv) 0 (sp - 72 + 44) ⟨by omega, by omega⟩ hy64 (by omega) (by omega) (by omega)
      ⟨by omega, by omega⟩ (b1.trans a1) b2 b3 (b7.trans a7) b8 b9 c24 c16 hro2 hrstk hstk
    have hlt : (9999999 < sx32 Xv) ↔ 9999999 < Xv := by unfold sx32; split <;> omega
    rw [hym] at d8
    have kd : ∀ {μ' : Memory}, (∀ a, a < 4294967296 → (a < sp - 72 + 40 ∨ sp - 72 + 48 ≤ a) → μ'.read a = μ2.read a) →
        (∀ a, a < 4294967296 → (a < sp - 72 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
        rdN μ' (sp - 72 + 8) 8 = F ∧ rdN μ' (sp - 72) 8 = sx32 Xv ∧
        rdN μ' (sp - 72 + 24) 8 = 10000 ∧ rdN μ' (sp - 72 + 16) 8 = 5243 ∧
        (∀ a, sp - 72 + 48 ≤ a → a < sp → μ'.read a = μ2.read a) := by
      intro μ' h
      refine ⟨fun a h1 h2 => by rw [h a h1 (by omega), k2 a h1 h2], ?_, ?_, ?_, ?_, fun a h1 h2 => h a (by omega) (Or.inr h1)⟩
      · rw [rdN_frame (fun j hj => h _ (by omega) (Or.inl (by omega)))]; exact cF
      · rw [show sp - 72 = sp - 72 + 0 by rfl, rdN_frame (fun j hj => h _ (by omega) (Or.inl (by omega)))]; exact cy
      · rw [rdN_frame (fun j hj => h _ (by omega) (Or.inl (by omega)))]; exact c24
      · rw [rdN_frame (fun j hj => h _ (by omega) (Or.inl (by omega)))]; exact c16
    have hXl : Xv < 4294967296 := hX'
    by_cases h7 : 9999999 < Xv
    · rw [if_pos (hlt.mpr h7)] at run3
      have f3 : ∀ a, a < 4294967296 → (a < sp - 72 + 40 ∨ sp - 72 + 48 ≤ a) → μ3.read a = μ2.read a :=
        fun a h1 h2 => fr3 a h1 (by omega)
      obtain ⟨m0, mF, my, m24, m16, -⟩ := kd f3
      obtain ⟨ω4, μ4, run4, e1, e2, e3, e7, e8, e9, fr4, rd4, wr4⟩ := dl_iter (p := p) (P := P) (R := R) x ω3 μ3
        (sp - 72) (Xv / 10000) ((0 + 18446744073709551612) % 18446744073709551616) (sp - 72 + 40)
        ⟨by omega, by omega⟩ (by omega) (by rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hXl)]; exact (Nat.le_div_iff_mul_le (by decide)).2 (by omega)) (by omega) (by omega) ⟨by omega, by omega⟩
        (d1.trans (b1.trans a1)) (d2.trans b2) (d3.trans b3) (d7.trans (b7.trans a7)) d8 d9 m24 m16
        (fun a h1 h2 => by rw [rd3]; exact hro2 a h1 h2) (fun a h1 h2 => by rw [rd3]; exact hrstk a h1 h2)
        (fun a h1 h2 => by rw [wr3]; exact hstk a h1 h2)
      have eq1 : Xv / 10000 % 4294967296 = Xv / 10000 := Nat.mod_eq_of_lt (by omega)
      have eq2 : Xv / 10000 / 10000 < 43 := by omega
      rw [eq1] at e8
      rw [if_neg (by omega)] at run4
      have f4 : ∀ a, a < 4294967296 → (a < sp - 72 + 40 ∨ sp - 72 + 48 ≤ a) → μ4.read a = μ2.read a :=
        fun a h1 h2 => by rw [fr4 a h1 (by omega), f3 a h1 h2]
      obtain ⟨n0, nF, ny, -, -, nhi⟩ := kd f4
      obtain ⟨ω5, run5, g1, g5, g6, g7, g8, g9, g12⟩ := dl_post (p := p) (P := P) (R := R) x ω4 μ4 (sp - 72)
        (Xv / 10000 / 10000) (((0 + 18446744073709551612) % 18446744073709551616 +
          18446744073709551612) % 18446744073709551616) F (sx32 Xv) ⟨by omega, by omega⟩ (by omega)
        (by omega) (e1.trans (d1.trans (b1.trans a1))) e8 e9 nF ny
        (fun a h1 h2 => by rw [rd4, rd3]; exact hrstk a h1 (by omega))
      obtain ⟨s0', s5', s6'⟩ := sv nhi
      exact fin ω5 μ4 _ 2 (sx32 Xv) _ ((((run1.trans run2).trans run3).trans run4).trans run5) (by omega)
        n0 (fun a => by rw [rd4, rd3, rd12]) (fun a => by rw [wr4, wr3, wr12])
        (g1.trans (e1.trans (d1.trans (b1.trans a1)))) g6 (g7.trans (e7.trans (d7.trans (b7.trans a7)))) g8
        (by rw [g9]) g12 (by omega) (by omega) (by omega)
        (fun _ h => by
          rcases h with h | h
          · have := sx32_mod Xv hX'; rw [h] at this; omega
          · omega)
        hy64 s0' s5' s6'
    · rw [if_neg (by rw [hlt]; exact h7)] at run3
      have f3 : ∀ a, a < 4294967296 → (a < sp - 72 + 40 ∨ sp - 72 + 48 ≤ a) → μ3.read a = μ2.read a :=
        fun a h1 h2 => fr3 a h1 (by omega)
      obtain ⟨n0, nF, ny, -, -, nhi⟩ := kd f3
      obtain ⟨ω5, run5, g1, g5, g6, g7, g8, g9, g12⟩ := dl_post (p := p) (P := P) (R := R) x ω3 μ3 (sp - 72)
        (Xv / 10000) ((0 + 18446744073709551612) % 18446744073709551616) F (sx32 Xv) ⟨by omega, by omega⟩
        (by omega) (by omega) (d1.trans (b1.trans a1)) d8 d9 nF ny
        (fun a h1 h2 => by rw [rd3]; exact hrstk a h1 (by omega))
      obtain ⟨s0', s5', s6'⟩ := sv nhi
      exact fin ω5 μ3 _ 6 (sx32 Xv) _ (((run1.trans run2).trans run3).trans run5) (by omega)
        n0 (fun a => by rw [rd3, rd12]) (fun a => by rw [wr3, wr12])
        (g1.trans (d1.trans (b1.trans a1))) g6 (g7.trans (d7.trans (b7.trans a7))) g8
        (by rw [g9]) g12 (by omega) (by omega) (by omega) (fun _ _ => by omega) hy64 s0' s5' s6'

end Services.Bootstrap.Fmt
