import Services.Bootstrap.Fmt.FieldInputSteps
import Services.Bootstrap.Fmt.FieldInt
import Services.Bootstrap.Fmt.StructField2
import Services.Bootstrap.Fmt.ResultDebug

/-!
# `<&Input as Debug>::fmt` (36972), step 8

The field of `Instr` tag 21: `Input { seed: <u64>, nb_items: <u8> }` (`debug_struct2`), `seed` by
its address a (`u64b_ok`, 37857) and `nb_items` through a slot holding a + 8 (`ref_u8_ok`, 37527).
The text is the binary's own (GP v0.8.0 does not specify Debug output).
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **`<u64 as Debug>::fmt`** at 37857 (plain options), the same code as 28843 (`u64_ok`): a u64
    where `ValAt` puts it; at most 20 octets. -/
theorem u64b_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA a : Nat) (hS : S0 ≤ spA) (ha : ValAt μA sA spA S1 a 8) :
    ArgOk p P R env pb S0 S1 600 μA sA spA 37857 a 20 2910 := by
  intro ω μ x s sp F W cap len ret t v5 v6 H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hWA hF hn
  have hS1 := H.hS1
  have hst : ∀ b, S0 ≤ b → b < S1 → μ.writable b = true := H.st
  obtain ⟨hra, hloc⟩ := ha.readable (by decide) H hS hspA K
  obtain ⟨ω1, run1, a0, a1, a5, a6, a7, a8⟩ := f_u64b (p := p) (P := P) (R := R) x ω μ F (by omega) h8 hf.opts
    (fun b h1 h2 => Memory.readable_of_writable (hst b (by omega) (by omega)))
  rcases dec64 (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω1 μ sA s sp F W a cap len ret t v5 v6 H hba hf
      (a0.trans h0) (a1.trans h1) (a5.trans h5) (a6.trans h6) (a7.trans h7) a8 ⟨hv5, hv6⟩ hret hjt hbt
      ⟨hsp.1, hsp.2.1, by omega⟩ hW hF ⟨by omega, by omega⟩ hra (by omega) with
    ⟨ω2, μ2, x2, s2, cap2, n, hn', run2, rest⟩ | hx
  · exact Or.inl ⟨ω2, μ2, x2, s2, cap2, n, hn', (run1.trans run2).mono (by omega), rest⟩
  · exact Or.inr ((Exhausts.pre run1 hx).mono (by omega))

/-- **`<&Input as Debug>::fmt`** (36972, plain options) as a field (`RefOk`): the slot holds the
    address a of the struct, the u64 `seed` at a and the octet `nb_items` at a + 8 where `ValAt` puts
    them. At most 52 octets. It needs 840 octets of stack below the caller (Z) and the vtables'
    `fmt` words (76032: 1804, `u64`; 76000: 1788, `&u8`). -/
theorem ref_input_36972_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 Z : Nat) (hZ : 840 ≤ Z) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA a : Nat) (hS : S0 ≤ spA) (hs : ValAt μA sA spA S1 a 8)
    (hb : ValAt μA sA spA S1 (a + 8) 1) (hv1 : rdN μA 76032 8 = 1804) (hv2 : rdN μA 76000 8 = 1788) :
    RefOk p P R env pb S0 S1 Z μA sA spA 36972 a 52 1073800000 := by
  intro ω μ x s sp F W cap len ret t v5 v6 v H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hWA hF hn
    hv ra
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst : ∀ b, S0 ≤ b → b < S1 → μ.writable b = true := H.st
  obtain ⟨-, hloc⟩ := hb.readable (by decide) H hS hspA K
  obtain ⟨ωa, μa, runa, e1, e2, e12, s64a, s56a, s48a, s40a, fra, rda, wra⟩ :=
    in36_a1 (p := p) (P := P) (R := R) x ω μ sp v a F ret v5 v6 ⟨by omega, by omega⟩ h0 h1 h5 h6 h7 h8
      ⟨by omega, hv5, hv6, by omega, by omega, by omega⟩ ra
      (fun b h1 h2 => Memory.readable_of_writable (hst b (by omega) (by omega))) hv.1
      (fun b h1 h2 => hst b (by omega) (by omega))
  obtain ⟨ω1, μ1, runb, a0, a1, a5, a6, a7, a8, a9, a10, a11, a12, s32, s24, s16, s8, s0, frb, rdb, wrb⟩ :=
    in36_a2 (p := p) (P := P) (R := R) x ωa μa (sp - 72) a F ⟨by omega, by omega⟩ e1 e2 e12
      ⟨by omega, by omega⟩ (fun b h1 h2 => by rw [wra b]; exact hst b (by omega) (by omega))
  have run1 := runa.trans runb
  have kb : ∀ o, 40 ≤ o → o + 8 ≤ 72 → rdN μ1 (sp - 72 + o) 8 = rdN μa (sp - 72 + o) 8 := fun o h1 h2 =>
    rdN_frame (fun j hj => frb _ (by omega) (Or.inr (by omega)))
  have s64 := (kb 64 (by omega) (by omega)).trans s64a
  have s56 := (kb 56 (by omega) (by omega)).trans s56a
  have s48 := (kb 48 (by omega) (by omega)).trans s48a
  have s40 := (kb 40 (by omega) (by omega)).trans s40a
  have fr1 : ∀ b, b < 4294967296 → (b < sp - 72 ∨ sp ≤ b) → μ1.read b = μ.read b := fun b hb h =>
    (frb b hb (by omega)).trans (fra b hb h)
  have rd1 : ∀ b, μ1.readable b = μ.readable b := fun b => (rdb b).trans (rda b)
  have wr1 : ∀ b, μ1.writable b = μ.writable b := fun b => (wrb b).trans (wra b)
  have k1 : ∀ b, b < 4294967296 → (b < sp - 72 ∨ sp ≤ b) → μ1.read b = μ.read b := fr1
  have H1 : HeapCtx env pb S0 S1 μ1 s := ctx_hi H (fun b hb => k1 b (by omega) (Or.inl (by omega))) wr1
  have K1 : Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) sA μ μ1 s :=
    Keeps.of_frame (Z := fun b => sp - 72 ≤ b ∧ b < sp) hf.str.base
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
  rcases debug_struct2 (p := p) (P := P) (R := R) env pb S0 S1 600 (Nat.le_refl _) HA HR μA sA spA
      37857 20 2910 1804 37527 3 2300 1788
      x ω1 μ1 s (sp - 72) F W 68712 5 68729 4 a 76008 68741 8 (sp - 72 + 40) 75976 cap len 1752 37053 68741 76008
      (Or.inl (u64b_ok env pb S0 S1 HA HR μA sA spA a hS hs))
      (Or.inr ⟨a + 8, ref_u8_ok env pb S0 S1 HA HR μA sA spA (a + 8) hS hb, s40, by omega, by omega,
        Or.inl (by omega)⟩)
      H1 hba hf1 KA1 a0 a1 a5 a6 a7 a8 a9 a10 a11 a12 ⟨by decide, by decide⟩ (by decide) s0 (by decide) (by decide)
      ((ro_keep H1 KA1 (by omega)).trans hv1) (by decide) jte_901 bs_37857 (by omega)
      ⟨s8, s16, s24, s32⟩ (by decide) (by decide)
      ((ro_keep H1 KA1 (by omega)).trans hv2) (by decide) jte_893 bs_37527 (by omega)
      (by decide) jte_875 bs_37053
      ⟨by omega, by omega, by omega⟩ ⟨by omega, hWA⟩ (by omega) (by omega) ⟨by omega, hW.2⟩
      ⟨by omega, hF.2.1, hF.2.2⟩ (by omega) with
    ⟨ω2, μ2, x2, s2, cap2, n, hn2, run2, H2, hb2, hf2, hc1, hc2, K2, b0, b1, b5, b6, b7⟩ | hx
  · have hst2 : ∀ b, S0 ≤ b → b < S1 → μ2.writable b = true := H2.st
    have kk : ∀ o, 48 ≤ o → o + 8 ≤ 72 → rdN μ2 (sp - 72 + o) 8 = rdN μ1 (sp - 72 + o) 8 := fun o h1 h2 =>
      rdN_frame (fun j hj => K2.hi _ (by omega) (by omega) (by omega))
    obtain ⟨ω3, run3, c0, c1, c5, c6, c7⟩ := in36_r (p := p) (P := P) (R := R) x2 ω2 μ2 (sp - 72) ret v5 v6 t
      ⟨by omega, by omega⟩ b1 ((kk 64 (by omega) (by omega)).trans s64)
      ((kk 56 (by omega) (by omega)).trans s56) ((kk 48 (by omega) (by omega)).trans s48) hret hjt hbt
      (fun b h1 h2 => Memory.readable_of_writable (hst2 b (by omega) (by omega)))
    have K' := K1.trans' (K2.lift (sp' := sp) (by omega) (fun b h _ => h))
    rw [Nat.max_self] at K'
    exact Or.inl ⟨ω3, μ2, x2, s2, cap2, n, by omega, (run1.trans (run2.trans run3)).mono (by omega), H2, hb2, hf2,
      hc1, hc2, K', c0, by rw [c1]; congr 1; omega, c5, c6, c7.trans b7⟩
  · exact Or.inr ((Exhausts.pre run1 hx).mono (by omega))

end Services.Bootstrap.Fmt
