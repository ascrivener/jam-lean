import Services.Bootstrap.Fmt.OptionDebugSteps
import Services.Bootstrap.Fmt.ResultDebug

/-!
# `<Option<Vec<u8>> as fmt::Debug>::fmt` (17465), frame-only, plain options

`option_vec_ok`: the `Option` at v (24 octets where `ValAt` puts them) as an `ArgOk`: `None` if its
first word is 2⁶⁴ − 1, otherwise `Some(…)` of the `Vec<u8>` at v (`ref_vec_u8_ok` through
`debug_tuple1`). At most 5·len + 8 octets; the text is not stated. This is the argument of refine's
lookup log line (5398; the lookup host call, GP v0.8.0 Appendix B.7 Ω_L).
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **`<Option<Vec<u8>> as Debug>::fmt`** (17465, plain options) as an argument: the `Option` at v
    (24 octets where `ValAt` puts them). If its first word is not 2⁶⁴ − 1 (`Some`), the `Vec`'s
    pointer and length are ptr and len and its octets are where `ValAt` puts them. At most
    5·len + 8 octets. It needs 912 octets of stack below the caller (Z), and the vtables' `fmt`
    words (74672: 1250, `&Vec<u8>`; 76000: 1788, `&u8`). -/
theorem option_vec_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 Z : Nat) (hZ : 912 ≤ Z) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA v ptr len : Nat) (hS : S0 ≤ spA) (hv : ValAt μA sA spA S1 v 24)
    (hsome : rdN μA v 8 ≠ 18446744073709551615 →
      rdN μA (v + 8) 8 = ptr ∧ rdN μA (v + 16) 8 = len ∧ (∀ j, j < len → ValAt μA sA spA S1 (ptr + j) 1) ∧
      ptr + len < 4294967296)
    (hvt : rdN μA 74672 8 = 1250) (hrvt : rdN μA 76000 8 = 1788) :
    ArgOk p P R env pb S0 S1 Z μA sA spA 17465 v (5 * len + 8) (2684354560 + 4600 * len + 12000) := by
  intro ω μ x s sp F W cap len0 ret t v5 v6 H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hWA hF hn
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  obtain ⟨hrv, hlv⟩ := hv.readable (by decide) H hS hspA K
  have rt : rdN μ v 8 = rdN μA v 8 := by rw [show v = v + 0 by rfl, hv.rdN H K (by omega)]
  by_cases hnone : rdN μA v 8 = 18446744073709551615
  · obtain ⟨ω1, run1, a0, a1, a5, a6, a7, a8, a9⟩ := os_none (p := p) (P := P) (R := R) x ω μ v F W
      ⟨by omega, by omega⟩ h7 h8 (rt.trans hnone) hf.buf hf.vt hf.vws
      (fun b h1 h2 => hf.vrd b h1 h2) (fun b h1 h2 => hrv b h1 (by omega))
      (fun b h1 h2 => Memory.readable_of_writable (hst b (by omega) (by omega)))
    rcases write_str (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω1 μ sA s sp W
        66801 4 cap len0 ret t v5 v6 H hba hf.str
        (a0.trans h0) (a1.trans h1) (a5.trans h5) (a6.trans h6) a7 a8 a9 ⟨hv5, hv6⟩ hret hjt hbt
        ⟨by omega, hsp.2.1, by omega⟩ hW (by omega) (Or.inl ⟨by omega, by omega⟩)
        (fun b h1 h2 => hf.vrd b (by omega) (by omega)) with
      ⟨ω2, μ2, x2, s2, cap2, run2, H2, hb2, hs2, hc1, hc2, K2, rest⟩ | hx
    · refine Or.inl ⟨ω2, μ2, x2, s2, cap2, 4, by omega, (run1.trans run2).mono (by omega), H2, hb2,
        Fmtr.of_keeps hf H K2 ⟨hF.1, by omega⟩ (fun b h1 h2 h => by omega) hs2, hc1, hc2, K2, rest⟩
    · exact Or.inr ((Exhausts.pre run1 hx).mono (by omega))
  · obtain ⟨rp, rl, helts, hpl⟩ := hsome hnone
    obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, a10, a11, s8, s0, fr1, rd1, wr1⟩ := os_some (p := p)
      (P := P) (R := R) x ω μ sp v F ret ⟨by omega, by omega⟩ h0 h1 h7 h8 ⟨by omega, by omega, by omega⟩
      (by omega) (by rw [rt]; exact hnone) (fun b h1 h2 => hrv b h1 (by omega))
      (fun b h1 h2 => hst b (by omega) (by omega))
    have k1 : ∀ b, b < 4294967296 → (b < sp - 16 ∨ sp ≤ b) → μ1.read b = μ.read b := fr1
    have H1 : HeapCtx env pb S0 S1 μ1 s := ctx_hi H (fun b hb => k1 b (by omega) (Or.inl (by omega))) wr1
    have K1 : Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) sA μ μ1 s :=
      Keeps.of_frame (Z := fun b => sp - 16 ≤ b ∧ b < sp) hf.str.base
        (fun b hb hz => k1 b hb (by omega)) rd1 wr1 (fun b hz => hst b (by omega) (by omega))
        (fun b hz h => by omega) (fun b hz hg => by unfold Glob at hg; omega)
        (fun c hc hu b hb => by
          have := chunk_bounds H.wf (hf.str.base c hc hu)
          have := H.hbT
          unfold InData at hb; omega)
    have hf1 : Fmtr sA s μ1 F W cap len0 := hf.congr (fun j hj => k1 _ (by omega) (Or.inr (by omega)))
      (fun j hj => k1 _ (by omega) (Or.inr (by omega))) (fun b h1 h2 => ⟨k1 b (by omega) (Or.inl (by omega)), rd1 b⟩)
    have KA1 : Keeps pb spA (fun _ => False) sA μA μ1 s := by
      have := K.trans' (K1.lift (sp' := spA) hspA (fun b h hb => by omega))
      rwa [Nat.max_self] at this
    rcases debug_tuple1 (p := p) (P := P) (R := R) env pb S0 S1 768 (by decide) HA HR μA sA spA 26807 v
        (5 * len + 2) (2147483648 + 4500 * len + 5000) 1250
        (ref_vec_u8_ok env pb S0 S1 768 (Nat.le_refl _) HA HR μA sA spA v ptr len hS hv rp rl helts hpl hrvt)
        x ω1 μ1 s (sp - 16) F W 66797 4 (sp - 16) 74648 cap len0 670 17507 v5 v6 H1 hba hf1 KA1 a0 a1
        (a5.trans h5) (a6.trans h6) a7 a8 a9 a10 a11 ⟨hv5, hv6⟩
        ⟨by omega, by omega, by omega⟩ (fun b h1 h2 => hf1.vrd b (by omega) (by omega)) ⟨by omega, by omega⟩
        ((ro_keep H1 KA1 (by omega)).trans hvt) (by decide) jte_624 bs_26807 s0 (by decide) jte_334 bs_17507
        ⟨by omega, by omega, by omega⟩ ⟨by omega, hWA⟩ ⟨by omega, hW.2⟩ ⟨by omega, hF.2.1, hF.2.2⟩
        ⟨by omega, by omega, Or.inl (by omega)⟩ (by omega) with
      ⟨ω2, μ2, x2, s2, cap2, n, hn2, run2, H2, hb2, hf2, hc1, hc2, K2, b0, b1, b5, b6, b7⟩ | hx
    · have hst2 : ∀ a, S0 ≤ a → a < S1 → μ2.writable a = true := H2.st
      obtain ⟨ω3, run3, c0, c1, c5, c6, c7⟩ := rd_r (p := p) (P := P) (R := R) x2 ω2 μ2 (sp - 16) ret t 17507
        (Or.inr (Or.inr rfl)) ⟨by omega, by omega⟩ b1
        (by rw [rdN_frame (fun j hj => K2.hi _ (by omega) (by omega) (by omega))]; exact s8) hret hjt hbt
        (fun b h1 h2 => Memory.readable_of_writable (hst2 b (by omega) (by omega)))
      have K := K1.trans' (K2.lift (sp' := sp) (by omega) (fun b h _ => h))
      rw [Nat.max_self] at K
      exact Or.inl ⟨ω3, μ2, x2, s2, cap2, n, by omega, (run1.trans (run2.trans run3)).mono (by omega), H2, hb2,
        hf2, hc1, hc2, K, c0, by rw [c1]; congr 1; omega, c5.trans b5, c6.trans b6, c7.trans b7⟩
    · exact Or.inr ((Exhausts.pre run1 hx).mono (by omega))

end Services.Bootstrap.Fmt
