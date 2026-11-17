import Services.Bootstrap.Fmt.Dec16Steps
import Services.Bootstrap.Fmt.Template
import Services.Bootstrap.Fmt.DebugList

/-!
# `<u16 as fmt::Display>::fmt` (67932), frame-only: `dec16`; `<u16 as Debug>` (28801): `u16_ok`

Step 8 (the u16 fields of `Instr` tags 12 and 24). The text is the binary's own (GP v0.8.0 does not
specify Debug output).
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- The five digit cases of `<u16 as fmt::Display>::fmt`, to the call of `pad_integral`. -/
theorem d16_all {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v F r0 : Nat) (hsp : 196608 + 16 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat v)
    (h8 : ω[8] = UInt64.ofNat F)
    (hv : r0 < 18446744073709551616 ∧ F < 18446744073709551616 ∧ v + 2 < 4294967296)
    (hdis : v + 2 ≤ sp - 16 ∨ sp ≤ v)
    (hrv : ∀ a, v ≤ a → a < v + 2 → μ.readable a = true)
    (hro : ∀ a, 65536 ≤ a → a < 77144 → μ.readable a = true)
    (hw : ∀ a, sp - 16 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ' k, 1 ≤ k ∧ k ≤ 5 ∧ FreeStepsH p R 67932 ω μ x 61857 ω' μ' x 49 ∧
      ω'[0] = UInt64.ofNat 2798 ∧ ω'[1] = UInt64.ofNat (sp - 16) ∧ ω'[7] = UInt64.ofNat F ∧
      ω'[9] = UInt64.ofNat 1 ∧ ω'[10] = UInt64.ofNat 0 ∧ ω'[11] = UInt64.ofNat (sp - 16 + 8 - k) ∧
      ω'[12] = UInt64.ofNat k ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ rdN μ' (sp - 16 + 8) 8 = r0 ∧
      (∀ a, a < 4294967296 → (a < sp - 16 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  by_cases c1 : rdN μ v 2 < 10
  · obtain ⟨ω', μ', run, rest⟩ := d16_lo (p := p) (P := P) (R := R) x ω μ sp v F r0 hsp h0 h1 h7 h8 hv hdis c1
      hrv hro hw
    exact ⟨ω', μ', 1, by omega, by omega, run.mono (by omega), rest⟩
  by_cases c2 : rdN μ v 2 < 100
  · obtain ⟨ω', μ', run, rest⟩ := d16_mid (p := p) (P := P) (R := R) x ω μ sp v F r0 hsp h0 h1 h7 h8 hv hdis
      ⟨by omega, c2⟩ hrv hro hw
    exact ⟨ω', μ', 2, by omega, by omega, run.mono (by omega), rest⟩
  by_cases c3 : rdN μ v 2 < 1000
  · obtain ⟨ω', μ', run, rest⟩ := d16_hi (p := p) (P := P) (R := R) x ω μ sp v F r0 hsp h0 h1 h7 h8 hv hdis
      ⟨by omega, c3⟩ hrv hro hw
    exact ⟨ω', μ', 3, by omega, by omega, run.mono (by omega), rest⟩
  · obtain ⟨ω', μ', run, rest⟩ := d16_big (p := p) (P := P) (R := R) x ω μ sp v F r0
      (if rdN μ v 2 < 10000 then 4 else 5) hsp h0 h1 h7 h8 hv hdis (by omega) rfl hrv hro hw
    refine ⟨ω', μ', if rdN μ v 2 < 10000 then 4 else 5, ?_, ?_, run, rest⟩ <;> split <;> omega

/-- **`<u16 as fmt::Display>::fmt`, frame-only** (67932): as `dec8`, for the address v of a u16; the
    `String` gains n ≤ 5 octets (the digits, unspecified). -/
theorem dec16 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
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
    (hvv : (v + 2 ≤ sp - 16 ∨ sp ≤ v) ∧ v + 2 < 4294967296)
    (hrv : ∀ a, v ≤ a → a < v + 2 → μ.readable a = true)
    (hn : len + 5 < 134217728) :
    (∃ ω' μ' x' s' cap' n, n ≤ 5 ∧
      FreeStepsH p R 67932 ω μ x t ω' μ' x' (7 * n + 2 * (cap' - cap) + 2300) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Fmtr s₀ s' μ' F W cap' (len + n) ∧ cap ≤ cap' ∧
      cap' ≤ max cap (max 8 (2 * (len + n))) ∧
      Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) s₀ μ μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0) ∨
    Exhausts p R pb 67932 ω μ x (1073741824 + 2300) := by
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  obtain ⟨ω1, μ1, k, hk1, hk5, run1, a0, a1, a7, a9, a10, a11, a12, a5, a6, sv0, fr1, rd1, wr1⟩ :=
    d16_all (p := p) (P := P) (R := R) x ω μ sp v F ret ⟨by omega, by omega⟩ h0 h1 h7 h8
      ⟨by omega, by omega, hvv.2⟩ hvv.1 hrv hf.vrd (fun a h1 h2 => hst a (by omega) (by omega))
  have k1 : ∀ a, a < 4294967296 → (a < sp - 16 ∨ sp ≤ a) → μ1.read a = μ.read a := fr1
  have H1 : HeapCtx env pb S0 S1 μ1 s := ctx_hi H (fun a ha => k1 a (by omega) (Or.inl (by omega))) wr1
  have hf1 : Fmtr s₀ s μ1 F W cap len := hf.congr (fun j hj => k1 _ (by omega) (Or.inr (by omega)))
    (fun j hj => k1 _ (by omega) (Or.inr (by omega)))
    (fun a h1 h2 => ⟨k1 a (by omega) (Or.inl (by omega)), rd1 a⟩)
  have K1 : Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) s₀ μ μ1 s :=
    Keeps.of_frame (Z := fun a => sp - 16 ≤ a ∧ a < sp) hf.str.base
      (fun a ha hz => k1 a ha (by omega)) rd1 wr1 (fun a hz => hst a (by omega) (by omega))
      (fun a hz h => by omega) (fun a hz hg => by unfold Glob at hg; omega)
      (fun c hc hu a ha => by
        have := chunk_bounds H.wf (hf.str.base c hc hu)
        have := H.hbT
        unfold InData at ha; omega)
  rcases pad_plain (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω1 μ1 s₀ s (sp - 16) F W (sp - 16 + 8 - k) k
      cap len 2798 68138 v5 v6 0 H1 hba hf1 a0 a1 (a5.trans h5) (a6.trans h6) a7 a10 a11 a12
      ⟨hv.1, hv.2, by omega⟩ (by decide) jte_1398 bs_68138 ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega, hF.2.2⟩ (by omega) (Or.inr ⟨by omega, by omega, Or.inl (by omega)⟩)
      (fun a h1 h2 => by rw [rd1]; exact Memory.readable_of_writable (hst a (by omega) (by omega))) with
    ⟨ω2, μ2, x2, s2, cap2, run2, H2, hb2, hf2, hc1, hc2, K2, b0, b1, b5, b6, b7⟩ | hx
  · have sv2 : rdN μ2 (sp - 16 + 8) 8 = ret := by
      rw [rdN_frame (fun j hj => K2.hi _ (by omega) (by omega) (by omega))]; exact sv0
    obtain ⟨ω3, run3, c0, c1, c5, c6, c7⟩ := d16_b (p := p) (P := P) (R := R) x2 ω2 μ2 (sp - 16) ret t
      ⟨by omega, by omega⟩ b1 sv2 hret hjt hbt
      (fun a h1 h2 => by
        rw [(K2.access a (Or.inr (by unfold pageSize; omega))).1, rd1]
        exact Memory.readable_of_writable (hst a (by omega) (by omega)))
    have K := K1.trans' (K2.lift (sp' := sp) (by omega) (fun a h _ => h))
    rw [Nat.max_self] at K
    refine Or.inl ⟨ω3, μ2, x2, s2, cap2, k, hk5, (run1.trans (run2.trans run3)).mono (by omega), H2, hb2, hf2,
      hc1, hc2, K, c0, by rw [c1]; congr 1; omega, c5.trans b5, c6.trans b6, c7.trans b7⟩
  · exact Or.inr ((Exhausts.pre run1 hx).mono (by omega))

/-- `<u16 as Debug>::fmt` (28801), plain options: on to `<u16 as Display>::fmt` (67932). -/
theorem f_u16 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (F : Nat) (hF : F + 24 < 4294967296) (h8 : ω[8] = UInt64.ofNat F)
    (ro : rdN μ (F + 16) 4 = 1610612768) (hrF : ∀ b, F + 16 ≤ b → b < F + 20 → μ.readable b = true) :
    ∃ ω', FreeStepsH p R 28801 ω μ x 67932 ω' μ x 6 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = ω[7] ∧
      ω'[8] = UInt64.ofNat F := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h8, hF, ro, hrF, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h8, Nat.mod_eq_of_lt (show F < 18446744073709551616 by omega)]

/-- **`<u16 as Debug>::fmt`** (28801, plain options) as a field passed by its address: a u16 where
    `ValAt` puts it; at most 5 octets. -/
theorem u16_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA a : Nat) (hS : S0 ≤ spA) (ha : ValAt μA sA spA S1 a 2) :
    ArgOk p P R env pb S0 S1 600 μA sA spA 28801 a 5 2310 := by
  intro ω μ x s sp F W cap len ret t v5 v6 H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hWA hF hn
  have hS1 := H.hS1
  have hst : ∀ b, S0 ≤ b → b < S1 → μ.writable b = true := H.st
  obtain ⟨hra, hloc⟩ := ha.readable (by decide) H hS hspA K
  obtain ⟨ω1, run1, a0, a1, a5, a6, a7, a8⟩ := f_u16 (p := p) (P := P) (R := R) x ω μ F (by omega) h8 hf.opts
    (fun b h1 h2 => Memory.readable_of_writable (hst b (by omega) (by omega)))
  rcases dec16 (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω1 μ sA s sp F W a cap len ret t v5 v6 H hba hf
      (a0.trans h0) (a1.trans h1) (a5.trans h5) (a6.trans h6) (a7.trans h7) a8 ⟨hv5, hv6⟩ hret hjt hbt
      ⟨hsp.1, hsp.2.1, by omega⟩ hW hF ⟨by omega, by omega⟩ hra (by omega) with
    ⟨ω2, μ2, x2, s2, cap2, n, hn', run2, rest⟩ | hx
  · exact Or.inl ⟨ω2, μ2, x2, s2, cap2, n, hn', (run1.trans run2).mono (by omega), rest⟩
  · exact Or.inr ((Exhausts.pre run1 hx).mono (by omega))

end Services.Bootstrap.Fmt
