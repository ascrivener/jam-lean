import Services.Bootstrap.Fmt.FieldU8HexSteps
import Services.Bootstrap.Fmt.DebugList

/-!
# `<u8 as fmt::LowerHex>::fmt` (60209) as an argument with the options of `{:02x}`

`u8hex_ok`: called with a `Formatter` carrying the options word 0x69000020 and width 2 (`FmtrO`),
for an octet where `ValAt` puts it, 60209 writes exactly two octets into the `String` (the octet's
two hex digits, zero-padded), frame-only: an `ArgOkO` with M = 2.

The digits come from the read-only table at 71060; only its readability is used (the text written
is not specified).
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- A `Formatter` with options o and width w is kept by a change that keeps its 24 octets, the
    `String`'s 24 octets, the read-only data and its readability. -/
theorem FmtrO.congr {s₀ s : State} {μ μ' : Memory} {F W cap len o w : Nat} (hf : FmtrO s₀ s μ F W cap len o w)
    (kF : ∀ j, j < 24 → μ'.read (F + j) = μ.read (F + j))
    (kW : ∀ j, j < 24 → μ'.read (W + j) = μ.read (W + j))
    (kro : ∀ a, 65536 ≤ a → a < 77144 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a) :
    FmtrO s₀ s μ' F W cap len o w := by
  have rF : ∀ o n, o + n ≤ 24 → rdN μ' (F + o) n = rdN μ (F + o) n := fun o n h =>
    rdN_frame (fun j hj => by rw [show F + o + j = F + (o + j) by omega, kF _ (by omega)])
  have rro : ∀ a, 77016 ≤ a → a + 8 ≤ 77064 → rdN μ' a 8 = rdN μ a 8 := fun a h1 h2 =>
    rdN_frame (fun j hj => (kro _ (by omega) (by omega)).1)
  refine ⟨by rw [show F = F + 0 by rfl, rF 0 8 (by omega)]; exact hf.buf, by rw [rF 8 8 (by omega)]; exact hf.vt,
    by rw [rF 16 4 (by omega)]; exact hf.opts, by rw [rF 20 2 (by omega)]; exact hf.width,
    by rw [rF 22 2 (by omega)]; exact hf.prec,
    by rw [rro _ (by omega) (by omega)]; exact hf.vws, by rw [rro _ (by omega) (by omega)]; exact hf.vwc,
    fun a h1 h2 => by rw [(kro a h1 h2).2]; exact hf.vrd a h1 h2, ?_⟩
  exact hf.str.update (fun j hj => kW j (by omega))
    ((rdN_frame (μ := μ) (μ' := μ') (fun j hj => by
      rw [show W + 16 + j = W + (16 + j) by omega, kW _ (by omega)])).trans hf.str.rl) hf.str.le

/-- **`{:02x}` of an octet** (60209, `<u8 as LowerHex>`) as an argument: for an octet at v where
    `ValAt` puts it, two octets are written. It needs 600 octets of stack (Z ≥ 600).
    The Ok path takes at most 2(cap' − cap) + 3900 steps; the constant 536875000 is the budget a
    failed allocator call may need (the `write_char` before the digit may have grown the `String`). -/
theorem u8hex_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 Z : Nat) (hZ : 600 ≤ Z) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA v : Nat) (hS : S0 ≤ spA) (hv : ValAt μA sA spA S1 v 1) :
    ArgOkO p P R env pb S0 S1 Z μA sA spA 60209 v 1761607712 2 2 536875000 := by
  intro ω μ x s sp F W cap len ret t v5 v6 H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hWA hF hn
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  have hro : ∀ a, a < 196608 → μ.writable a = false := H.ro
  obtain ⟨hrv, hloc⟩ := hv.readable (by omega) H hS hspA K
  -- 60209 … 60229
  obtain ⟨ω1, μ1, run1, a1, a2, a5, a6, a7, a8, a9, a12, s8, fr1, rd1, wr1⟩ := u8x_entry (p := p) (P := P)
    (R := R) x ω μ sp v F ret ⟨by omega, by omega⟩ h0 h1 h7 h8 (by omega) (by omega) (by omega) (by omega)
    (hrv v (Nat.le_refl _) (by omega)) (fun a h1 h2 => hst a (by omega) (by omega))
  have hb : rdN μ v 1 < 256 := rdN_lt μ v 1
  generalize rdN μ v 1 = b at a9 hb
  -- the first digit
  obtain ⟨ω2, μ2, run2, b1, b2, b5, b6, b7, b8, b9, b12, fr2, rd2, wr2⟩ := u8x_iter (p := p) (P := P) (R := R)
    x ω1 μ1 (sp - 16 + 7) b 0 ⟨by omega, by omega⟩ (by omega) (by omega) a7 a8 a9 a12
    (fun a h1 h2 => by rw [rd1]; exact hf.vrd a (by omega) (by omega))
    (by rw [wr1]; exact hst _ (by omega) (by omega))
  -- the frame of the digit loop and the call, for either count k of digits
  have post : ∀ (k : Nat) (ω3 : Regs) (μ3 : Memory) (n0 : Nat), 1 ≤ k → k ≤ 2 →
      FreeStepsH p R 60209 ω μ x 60255 ω3 μ3 x n0 → n0 ≤ 32 →
      ω3[1] = UInt64.ofNat (sp - 16) → ω3[2] = UInt64.ofNat F → ω3[5] = UInt64.ofNat v5 →
      ω3[6] = UInt64.ofNat v6 → ω3[12] = UInt64.ofNat k →
      (∀ a, a < 4294967296 → (a < sp - 16 + 8 - k ∨ sp ≤ a) → μ3.read a = μ.read a) →
      rdN μ3 (sp - 16 + 8) 8 = ret →
      (∀ a, μ3.readable a = μ.readable a) → (∀ a, μ3.writable a = μ.writable a) →
      ((∃ ω' μ' x' s' cap' n, n ≤ 2 ∧
        FreeStepsH p R 60209 ω μ x t ω' μ' x' (7 * n + 2 * (cap' - cap) + 536875000) ∧
        HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ FmtrO sA s' μ' F W cap' (len + n) 1761607712 2 ∧
        cap ≤ cap' ∧ cap' ≤ max cap (max 8 (2 * (len + n))) ∧
        Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) sA μ μ' s' ∧
        ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
        ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0) ∨
      Exhausts p R pb 60209 ω μ x (1073741824 + 536875000)) := by
    intro k ω3 μ3 n0 hk1 hk2 run3 hn0 c1 c2 c5 c6 c12 fr3 s8' rd3 wr3
    have hF64 : F < 18446744073709551616 := by omega
    obtain ⟨ω4, run4, d0, d1, d5, d6, d7, d10, d11, d12⟩ := u8x_post (p := p) (P := P) (R := R) x ω3 μ3 (sp - 16) F k
      ⟨by omega, by omega⟩ ⟨hk1, hk2⟩ c1 c2 c12 hF64
    have H3 : HeapCtx env pb S0 S1 μ3 s := ctx_hi H (fun a ha => fr3 a (by omega) (Or.inl (by omega))) wr3
    have kro3 : ∀ a, 65536 ≤ a → a < 77144 → μ3.read a = μ.read a ∧ μ3.readable a = μ.readable a :=
      fun a h1 h2 => ⟨fr3 a (by omega) (Or.inl (by omega)), rd3 a⟩
    have hf3 : FmtrO sA s μ3 F W cap len 1761607712 2 := hf.congr
      (fun j hj => fr3 _ (by omega) (Or.inr (by omega))) (fun j hj => fr3 _ (by omega) (Or.inr (by omega))) kro3
    have K3 : Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) sA μ μ3 s :=
      Keeps.of_frame (Z := fun a => sp - 16 ≤ a ∧ a < sp) hf.str.base
        (fun a ha hz => fr3 a ha (by omega)) rd3 wr3 (fun a hz => hst a (by omega) (by omega))
        (fun a hz h => by omega) (fun a hz hg => by unfold Glob at hg; omega)
        (fun d hd hu a ha => by
          have := chunk_bounds H.wf (hf.str.base d hd hu)
          have := H.hbT
          unfold InData at ha; omega)
    have hd5 : ω4[5] = UInt64.ofNat v5 := d5.trans c5
    have hd6 : ω4[6] = UInt64.ofNat v6 := d6.trans c6
    have hsrc : (65536 ≤ sp - 16 + 8 - k ∧ sp - 16 + 8 - k + k + 24 ≤ 196608) ∨
        (sp - 16 ≤ sp - 16 + 8 - k ∧ sp - 16 + 8 - k + k + 16 < 4294967296 ∧
          (sp - 16 + 8 - k + k ≤ W ∨ W + 24 ≤ sp - 16 + 8 - k)) := Or.inr ⟨by omega, by omega, Or.inl (by omega)⟩
    have hrd : ∀ a, sp - 16 + 8 - k ≤ a → a < sp - 16 + 8 - k + k → μ3.readable a = true := fun a h1 h2 => by
      rw [rd3]; exact Memory.readable_of_writable (hst a (by omega) (by omega))
    -- the end: from pad_integral's Ok to the return
    have fin : ∀ (ω5 : Regs) (μ5 : Memory) (x5 : X) (s5 : State) (cap5 n5 : Nat), n5 ≤ 3800 →
        FreeStepsH p R 61857 ω4 μ3 x 60280 ω5 μ5 x5 (2 * (cap5 - cap) + n5) →
        HeapCtx env pb S0 S1 μ5 s5 → s5.base = s.base → FmtrO sA s5 μ5 F W cap5 (len + 2) 1761607712 2 →
        cap ≤ cap5 → cap5 ≤ max cap (max 8 (2 * (len + 2))) →
        Keeps pb (sp - 16) (fun a => W ≤ a ∧ a < W + 24) sA μ3 μ5 s5 →
        ω5[1] = UInt64.ofNat (sp - 16) → ω5[5] = UInt64.ofNat v5 → ω5[6] = UInt64.ofNat v6 →
        ω5[7] = UInt64.ofNat 0 →
        (∃ ω' μ' x' s' cap' n, n ≤ 2 ∧
          FreeStepsH p R 60209 ω μ x t ω' μ' x' (7 * n + 2 * (cap' - cap) + 536875000) ∧
          HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ FmtrO sA s' μ' F W cap' (len + n) 1761607712 2 ∧
          cap ≤ cap' ∧ cap' ≤ max cap (max 8 (2 * (len + n))) ∧
          Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) sA μ μ' s' ∧
          ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
          ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0) := by
      intro ω5 μ5 x5 s5 cap5 n5 hn5 run5 H5 hb5 hf5 hc1 hc2 K5 e1 e5 e6 e7
      obtain ⟨ω6, run6, g0, g1, g5, g6, g7⟩ := u8x_ret (p := p) (P := P) (R := R) x5 ω5 μ5 (sp - 16) ret t
        ⟨by omega, by omega⟩ e1
        (by rw [rdN_frame (fun j hj => K5.hi _ (by omega) (by omega) (by omega))]; exact s8') hret hjt hbt
        (fun a h1 h2 => Memory.readable_of_writable (H5.st a (by omega) (by omega)))
      have K := K3.trans' K5
      rw [show max sp (sp - 16) = sp by omega] at K
      exact ⟨ω6, μ5, x5, s5, cap5, 2, Nat.le_refl _, ((run3.trans run4).trans (run5.trans run6)).mono (by omega),
        H5, hb5, hf5, hc1, hc2, K, g0, by rw [g1, show sp - 16 + 16 = sp by omega], g5.trans e5, g6.trans e6,
        g7.trans e7⟩
    rcases Nat.lt_or_ge k 2 with hk | hk
    · -- one digit: the zero-pad path
      have k1 : k = 1 := by omega
      subst k1
      rcases pad_z2 (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω4 μ3 sA s (sp - 16) F W (sp - 16 + 8 - 1) cap
          len 2608 60280 v5 v6 2 H3 hba hf3 d0 d1 hd5 hd6 d7 d10 d11 d12 ⟨hv5, hv6, by omega⟩ (by omega) jte_1303
          bs_60280 ⟨by omega, by omega, by omega⟩ ⟨by omega, hW.2⟩ ⟨by omega, hF.2.1, hF.2.2⟩ (by omega) hsrc hrd with
        ⟨ω5, μ5, x5, s5, cap5, run5, H5, hb5, hf5, hc1, hc2, K5, e0, e1, e5, e6, e7⟩ | hx
      · exact Or.inl (fin ω5 μ5 x5 s5 cap5 3800 (Nat.le_refl _) run5 H5 hb5 hf5 hc1 hc2 K5 e1 e5 e6 e7)
      · exact Or.inr ((Exhausts.pre (run3.trans run4) hx).mono (by omega))
    · -- two digits: the plain path
      have k2 : k = 2 := by omega
      subst k2
      rcases pad_wp (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω4 μ3 sA s (sp - 16) F W (sp - 16 + 8 - 2) 2 cap
          len 2608 60280 v5 v6 2 2 H3 hba hf3 (Nat.le_refl _) d0 d1 hd5 hd6 d7 d10 d11 d12 ⟨hv5, hv6, by omega⟩
          (by omega) jte_1303 bs_60280 ⟨by omega, by omega, by omega⟩ ⟨by omega, hW.2⟩ ⟨by omega, hF.2.1, hF.2.2⟩
          (by omega) hsrc hrd with
        ⟨ω5, μ5, x5, s5, cap5, run5, H5, hb5, hf5, hc1, hc2, K5, e0, e1, e5, e6, e7⟩ | hx
      · exact Or.inl (fin ω5 μ5 x5 s5 cap5 2114 (by omega) (run5.mono (by omega)) H5 hb5 hf5 hc1 hc2 K5 e1 e5 e6 e7)
      · exact Or.inr ((Exhausts.pre (run3.trans run4) hx).mono (by omega))
  by_cases hz : b / 16 = 0
  · rw [if_pos hz] at run2
    exact post 1 ω2 μ2 20 (Nat.le_refl _) (by omega) (run1.trans run2) (by omega) (b1.trans a1) (b2.trans a2)
      (by rw [b5, a5, h5]) (by rw [b6, a6, h6]) b12
      (fun a h1 h2 => by
        rw [fr2 a h1 (by omega), fr1 a h1 (by omega)])
      (by rw [rdN_frame (fun j hj => fr2 _ (by omega) (by omega))]; exact s8)
      (fun a => by rw [rd2, rd1]) (fun a => by rw [wr2, wr1])
  · rw [if_neg hz] at run2
    -- the second digit
    have hz2 : b / 16 / 16 = 0 := by omega
    obtain ⟨ω3, μ3, run3, c1, c2, c5, c6, c7, c8, c9, c12, fr3, rd3, wr3⟩ := u8x_iter (p := p) (P := P) (R := R)
      x ω2 μ2 (sp - 16 + 7 - 1) (b / 16) (0 + 1) ⟨by omega, by omega⟩ (by omega) (by omega) b7 b8 b9 b12
      (fun a h1 h2 => by rw [rd2, rd1]; exact hf.vrd a (by omega) (by omega))
      (by rw [wr2, wr1]; exact hst _ (by omega) (by omega))
    rw [if_pos hz2] at run3
    exact post 2 ω3 μ3 32 (by omega) (Nat.le_refl _) ((run1.trans run2).trans run3) (by omega)
      (c1.trans (b1.trans a1)) (c2.trans (b2.trans a2)) (by rw [c5, b5, a5, h5]) (by rw [c6, b6, a6, h6]) c12
      (fun a h1 h2 => by
        rw [fr3 a h1 (by omega), fr2 a h1 (by omega), fr1 a h1 (by omega)])
      (by rw [rdN_frame (μ := μ1) (fun j hj => by rw [fr3 _ (by omega) (by omega), fr2 _ (by omega) (by omega)])]; exact s8)
      (fun a => by rw [rd3, rd2, rd1]) (fun a => by rw [wr3, wr2, wr1])

end Services.Bootstrap.Fmt
