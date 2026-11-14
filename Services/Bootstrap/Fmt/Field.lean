import Services.Bootstrap.Fmt.FieldSteps
import Services.Bootstrap.Fmt.DebugList

/-!
# Field formatters of refine's 6159 `Debug` line: `bool`

`ref_bool_ok`: `<&bool as Debug>::fmt` (37522, plain options) as a field passed through a slot
(`RefOk`): `"false"` or `"true"` by `Formatter::pad`'s plain path, so at most 5 octets. The octet
lies where `ValAt` puts it (on the caller's stack or in an allocated chunk). The text is not
stated.
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **`<&bool as Debug>::fmt`** (37522, plain options) as a field or entry: at most 5 octets, for a
    `bool` where `ValAt` puts it. -/
theorem ref_bool_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA a : Nat) (hS : S0 ≤ spA) (ha : ValAt μA sA spA S1 a 1) :
    RefOk p P R env pb S0 S1 600 μA sA spA 37522 a 5 2100 := by
  intro ω μ x s sp F W cap len ret t v5 v6 v H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hWA hF hn
    hv ra
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  obtain ⟨hra, hloc⟩ := ha.readable (by decide) H hS hspA K
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, fr1, rd1, wr1⟩ := rf_bool (p := p) (P := P) (R := R)
    x ω μ sp v F W a (rdN μ a 1) ret v5 v6 ⟨by omega, by omega⟩ h0 h1 h5 h6 h7 h8
    ⟨by omega, hv5, hv6, by omega, by omega, by omega⟩ (Or.inr hF.1) ra rfl hf.buf hf.vt hf.opts hf.vws hf.vrd
    (fun b h1 h2 => Memory.readable_of_writable (hst b (by omega) (by omega))) hra
    (fun b h1 h2 => Memory.readable_of_writable (hst b (by omega) (by omega)))
    (fun b h1 h2 => hst b (by omega) (by omega))
  generalize hN : (if rdN μ a 1 = 0 then 72794 else 72799) = nm at a8
  generalize hL : (if rdN μ a 1 = 0 then 5 else 4) = L at a9
  have hNL : (nm = 72794 ∧ L = 5) ∨ (nm = 72799 ∧ L = 4) := by
    subst hN hL; split
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  have hL5 : L ≤ 5 := by omega
  have k1 : ∀ c, c < 4294967296 → (c < sp - 24 ∨ sp ≤ c) → μ1.read c = μ.read c := fr1
  have H1 : HeapCtx env pb S0 S1 μ1 s := ctx_hi H (fun c hc => k1 c (by omega) (Or.inl (by omega))) wr1
  have hs1 : Str sA s μ1 W cap len := (hf.congr (fun j hj => k1 _ (by omega) (Or.inr (by omega)))
    (fun j hj => k1 _ (by omega) (Or.inr (by omega)))
    (fun c h1 h2 => ⟨k1 c (by omega) (Or.inl (by omega)), rd1 c⟩)).str
  have K1 : Keeps pb sp (fun c => W ≤ c ∧ c < W + 24) sA μ μ1 s :=
    Keeps.of_frame (Z := fun c => sp - 24 ≤ c ∧ c < sp) hf.str.base
      (fun c hc hz => k1 c hc (by omega)) rd1 wr1 (fun c hz => hst c (by omega) (by omega))
      (fun c hz h => by omega) (fun c hz hg => by unfold Glob at hg; omega)
      (fun c hc hu b hb => by
        have := chunk_bounds H.wf (hf.str.base c hc hu)
        have := H.hbT
        unfold InData at hb; omega)
  rcases write_str (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω1 μ1 sA s sp W nm L cap len ret t v5 v6
      H1 hba hs1 a0 a1 a5 a6 a7 a8 a9 ⟨hv5, hv6⟩ hret hjt hbt ⟨by omega, hsp.2.1, by omega⟩ hW (by omega)
      (Or.inl ⟨by omega, by omega⟩) (fun b h1 h2 => by rw [rd1]; exact hf.vrd b (by omega) (by omega)) with
    ⟨ω2, μ2, x2, s2, cap2, run2, H2, hb2, hs2, hc1, hc2, K2, rest⟩ | hx
  · have K := K1.trans' K2
    rw [Nat.max_self] at K
    refine Or.inl ⟨ω2, μ2, x2, s2, cap2, L, hL5, (run1.trans run2).mono (by omega), H2, hb2,
      Fmtr.of_keeps hf H K ⟨hF.1, by omega⟩ (fun b h1 h2 h => by omega) hs2, hc1, hc2, K, rest⟩
  · exact Or.inr ((Exhausts.pre run1 hx).mono (by omega))

end Services.Bootstrap.Fmt
