import Services.Bootstrap.Fmt.InstrDebugSteps
import Services.Bootstrap.Fmt.StructField1
import Services.Bootstrap.Fmt.ResultDebug

/-!
# `<&Instruction as Debug>::fmt` (26990), frame-only, plain options: the milestone's arms

Each `instr<t>_ok` is the function as a `RefOk` for an element at a (232 octets where `ValAt` puts
them, its discriminant word 2⁶³ − 1 + t), for the tags refine's milestone output can hold (T1's
`DebugLineOk` slot predicate: `MFixed` and `Exported`). The arm calls its
`debug_struct_field*_finish` with the fields' formatters (`FieldOk`), and the function returns
`Ok`. The text is not stated.
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- Part of a value where `ValAt` puts it is where `ValAt` puts it. -/
theorem ValAt.sub {μA : Memory} {sA : State} {spA S1 a n k m : Nat} (h : ValAt μA sA spA S1 a n)
    (hk : k + m ≤ n) : ValAt μA sA spA S1 (a + k) m := by
  rcases h with ⟨h1, h2, h3⟩ | ⟨c, hc, hu, hd⟩
  · exact Or.inl ⟨by omega, by omega, fun b hb1 hb2 => h3 b (by omega) (by omega)⟩
  · exact Or.inr ⟨c, hc, hu, fun j hj => by rw [show a + k + j = a + (k + j) by omega]; exact hd _ (by omega)⟩

/-- **Tag 20, `Exported(n)`** (`debug_struct_field1_finish` with n, the u64 at a + 8, through
    `ref_u64_okV`): at most 40 octets. -/
theorem instr20_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA a : Nat) (hS : S0 ≤ spA) (ha : ValAt μA sA spA S1 a 232)
    (rt : rdN μA a 8 = 9223372036854775827) (rj : rdN μA 67656 4 = 4294901022)
    (rvt : rdN μA 75136 8 = 1794) :
    RefOk p P R env pb S0 S1 1088 μA sA spA 26990 a 40 (1073741824 + 14000) := by
  intro ω μ x s sp F W cap len ret t v5 v6 v H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hWA hF hn
    hv ra
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst : ∀ b, S0 ≤ b → b < S1 → μ.writable b = true := H.st
  obtain ⟨hra, hloc⟩ := ha.readable (by decide) H hS hspA K
  have rt' : rdN μ a 8 = 9223372036854775827 := by
    rw [show a = a + 0 by rfl, ha.rdN H K (by omega)]; exact rt
  -- the dispatch and the arm
  obtain ⟨ω1, μ1, run1, a0, a1, a7, a8, a9, a10, a11, a12, s312, s304, s296, s0, s152, fr1, rd1, wr1⟩ :=
    id_20 (p := p) (P := P) (R := R) x ω μ sp v a F ret v5 v6 ⟨by omega, by omega⟩ h0 h1 h5 h6 h7 h8
      ⟨by omega, hv5, hv6, by omega, by omega, by omega⟩ ⟨Or.inr hv.1, by omega⟩ ra rt'
      ((ro_keep H K (by omega)).trans rj) (fun b h1 h2 => hf.vrd b (by omega) (by omega))
      (fun b h1 h2 => Memory.readable_of_writable (hst b (by omega) (by omega)))
      (fun b h1 h2 => hra b h1 (by omega)) (fun b h1 h2 => hst b (by omega) (by omega))
  have k1 : ∀ b, b < 4294967296 → (b < sp - 320 ∨ sp ≤ b) → μ1.read b = μ.read b := fr1
  have H1 : HeapCtx env pb S0 S1 μ1 s := ctx_hi H (fun b hb => k1 b (by omega) (Or.inl (by omega))) wr1
  have K1 : Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) sA μ μ1 s :=
    Keeps.of_frame (Z := fun b => sp - 320 ≤ b ∧ b < sp) hf.str.base
      (fun b hb hz => k1 b hb (by omega)) rd1 wr1 (fun b hz => hst b (by omega) (by omega))
      (fun b hz h => by omega) (fun b hz hg => by unfold Glob at hg; omega)
      (fun c hc hu b hb => by
        have := chunk_bounds H.wf (hf.str.base c hc hu)
        have := H.hbT
        unfold InData at hb; omega)
  have hf1 : Fmtr sA s μ1 F W cap len := hf.congr (fun j hj => k1 _ (by omega) (Or.inr (by omega)))
    (fun j hj => k1 _ (by omega) (Or.inr (by omega))) (fun b h1 h2 => ⟨k1 b (by omega) (Or.inl (by omega)), rd1 b⟩)
  have KA1 : Keeps pb spA (fun _ => False) sA μA μ1 s := by
    have := K.trans' (K1.lift (sp' := spA) hspA (fun b h hb => by omega))
    rwa [Nat.max_self] at this
  -- the struct
  rcases debug_struct1 (p := p) (P := P) (R := R) env pb S0 S1 600 (Nat.le_refl _) HA HR μA sA spA 37589 20 2950 1794
      x ω1 μ1 s (sp - 320) F W 67712 8 68186 5 (sp - 320 + 152) 75112 cap len 1328 28589 (ω1[5].toNat)
      (ω1[6].toNat)
      (Or.inr ⟨a + 8, ref_u64_okV env pb S0 S1 HA HR μA sA spA (a + 8) hS (ha.sub (by omega)), s152,
        by omega, by omega, Or.inl (by omega)⟩)
      H1 hba hf1 KA1 a0 a1 (by simp) (by simp) a7 a8 a9 a10 a11 a12
      ⟨UInt64.toNat_lt _, UInt64.toNat_lt _⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ s0 ⟨by omega, by omega⟩
      ((ro_keep H1 KA1 (by omega)).trans rvt) (by decide) jte_896 bs_37589 (by decide) jte_663 bs_28589
      ⟨by omega, by omega, by omega⟩ ⟨by omega, hWA⟩ (by omega) (by omega) ⟨by omega, hW.2⟩
      ⟨by omega, hF.2.1, hF.2.2⟩ (by omega) (by omega) with
    ⟨ω2, μ2, x2, s2, cap2, n, hn2, run2, H2, hb2, hf2, hc1, hc2, K2, b0, b1, b5, b6, b7⟩ | hx
  · have hst2 : ∀ b, S0 ≤ b → b < S1 → μ2.writable b = true := H2.st
    have kk : ∀ o, 296 ≤ o → o + 8 ≤ 320 → rdN μ2 (sp - 320 + o) 8 = rdN μ1 (sp - 320 + o) 8 := fun o h1 h2 =>
      rdN_frame (fun j hj => K2.hi _ (by omega) (by omega) (by omega))
    obtain ⟨ω3, run3, c0, c1, c5, c6, c7⟩ := ir_ret (p := p) (P := P) (R := R) x2 ω2 μ2 (sp - 320) ret t v5 v6 28589
      (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) ⟨by omega, by omega⟩ b1 ((kk 312 (by omega) (by omega)).trans s312)
      ((kk 304 (by omega) (by omega)).trans s304) ((kk 296 (by omega) (by omega)).trans s296) hret hjt hbt
      (fun b h1 h2 => Memory.readable_of_writable (hst2 b (by omega) (by omega)))
    have K' := K1.trans' (K2.lift (sp' := sp) (by omega) (fun b h _ => h))
    rw [Nat.max_self] at K'
    exact Or.inl ⟨ω3, μ2, x2, s2, cap2, n, by omega, (run1.trans (run2.trans run3)).mono (by omega), H2, hb2, hf2,
      hc1, hc2, K', c0, by rw [c1]; congr 1; omega, c5, c6, c7.trans b7⟩
  · exact Or.inr ((Exhausts.pre run1 hx).mono (by omega))

end Services.Bootstrap.Fmt
