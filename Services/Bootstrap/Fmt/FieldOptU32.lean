import Services.Bootstrap.Fmt.FieldOptTail
import Services.Bootstrap.Fmt.FieldInt

/-!
# `<&Option<u32> as Debug>::fmt` (36594), step 8

The `maybe_id` field of `CreateService` (tag 0): `None` if the i32 tag at a is 0, otherwise
`Some(…)` of the u32 at a + 4 (`ref_u32_ok`, 37549, through `debug_tuple1` and `fo_tail`). The text
is the binary's own (GP v0.8.0 does not specify Debug output).
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **`<&Option<u32> as Debug>::fmt`** (36594, plain options) as a field (`RefOk`): the slot holds
    the address a of an `Option<u32>` (8 octets where `ValAt` puts them; the tag is the 4 octets at
    a, the value the 4 at a + 4). At most 16 octets. It needs 744 octets of stack below the caller
    (Z) and the vtable's `fmt` word (76096: 1790, `&u32`). -/
theorem ref_opt_u32_36594_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 Z : Nat) (hZ : 744 ≤ Z) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA a : Nat) (hS : S0 ≤ spA) (hv : ValAt μA sA spA S1 a 8)
    (hvt : rdN μA 76096 8 = 1790) :
    RefOk p P R env pb S0 S1 Z μA sA spA 36594 a 16 536900000 := by
  intro ω μ x s sp F W cap len0 ret t v5 v6 q H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hWA hF hn
    hq rq
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst : ∀ c, S0 ≤ c → c < S1 → μ.writable c = true := H.st
  obtain ⟨hrv, hlv⟩ := hv.readable (by decide) H hS hspA K
  have hrq : ∀ b, q ≤ b → b < q + 8 → μ.readable b = true :=
    fun b h1 h2 => Memory.readable_of_writable (hst b (by omega) (by omega))
  have rt : rdN μ a 4 = rdN μA a 4 := rdN_frame (fun j hj => hv.read H K j (by omega))
  have hal : a + 8 < 4294967296 := by omega
  by_cases hnone : rdN μA a 4 = 0
  · obtain ⟨ω1, run1, a0, a1, a5, a6, a7, a8, a9⟩ := o365_none (p := p) (P := P) (R := R) x ω μ q a F W
      ⟨by omega, by omega, by omega⟩ h7 h8 rq (rt.trans hnone) hf.buf hf.vt hf.vws
      (fun b h1 h2 => hf.vrd b h1 h2) hrq (fun b h1 h2 => hrv b h1 (by omega))
      (fun b h1 h2 => Memory.readable_of_writable (hst b (by omega) (by omega)))
    rcases write_str (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω1 μ sA s sp W
        68733 4 cap len0 ret t v5 v6 H hba hf.str
        (a0.trans h0) (a1.trans h1) (a5.trans h5) (a6.trans h6) a7 a8 a9 ⟨hv5, hv6⟩ hret hjt hbt
        ⟨by omega, hsp.2.1, by omega⟩ hW (by omega) (Or.inl ⟨by omega, by omega⟩)
        (fun b h1 h2 => hf.vrd b (by omega) (by omega)) with
      ⟨ω2, μ2, x2, s2, cap2, run2, H2, hb2, hs2, hc1, hc2, K2, rest⟩ | hx
    · refine Or.inl ⟨ω2, μ2, x2, s2, cap2, 4, by omega, (run1.trans run2).mono (by omega), H2, hb2,
        Fmtr.of_keeps hf H K2 ⟨hF.1, by omega⟩ (fun b h1 h2 h => by omega) hs2, hc1, hc2, K2, rest⟩
    · exact Or.inr ((Exhausts.pre run1 hx).mono (by omega))
  · have hv4 : ValAt μA sA spA S1 (a + 4) 4 := by
      rcases hv with ⟨h1, h2, h3⟩ | ⟨c, hc, hu, hd⟩
      · exact Or.inl ⟨by omega, by omega, fun b hb1 hb2 => h3 b (by omega) (by omega)⟩
      · exact Or.inr ⟨c, hc, hu, fun j hj => by rw [show a + 4 + j = a + (4 + j) by omega]; exact hd _ (by omega)⟩
    obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, a10, a11, s8, s0, fr1, rd1, wr1⟩ := o365_some (p := p)
      (P := P) (R := R) x ω μ sp q a F ret ⟨by omega, by omega⟩ h0 h1 h7 h8
      ⟨by omega, by omega, by omega, hal⟩ rq (by rw [rt]; exact hnone) hrq (fun b h1 h2 => hrv b h1 (by omega))
      (fun b h1 h2 => hst b (by omega) (by omega))
    rcases fo_tail (p := p) (P := P) (R := R) env pb S0 S1 Z 600 (by decide) (by omega) HA HR μA sA spA
        37549 (a + 4) 10 2710 1790 36594 13 68725 4 76072 1720 36635
        (ref_u32_ok env pb S0 S1 HA HR μA sA spA (a + 4) hS hv4)
        hvt (by decide) jte_894 bs_37549 (by decide) jte_859 bs_36635 (Or.inr (Or.inr (Or.inl rfl)))
        (by decide) (by decide) (by decide) ω μ x s sp F W cap len0 ret t v5 v6 H hba K hf h5 h6 hv5 hv6 hret
        hjt hbt hsp hspA hW hWA hF (by omega) ω1 μ1 run1 a0 a1 a5 a6 a7 a8 a9 a10 a11 s8 s0 fr1 rd1 wr1 with
      ⟨ω', μ', x', s', cap', n, hn', run, rest⟩ | hx
    · exact Or.inl ⟨ω', μ', x', s', cap', n, by omega, run.mono (by omega), rest⟩
    · exact Or.inr (hx.mono (by omega))

end Services.Bootstrap.Fmt
