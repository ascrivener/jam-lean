import Services.Bootstrap.Fmt.LogSteps
import Services.Bootstrap.Decode.DeallocCall
import Services.Bootstrap.Fmt.Format

/-!
# Accumulate's first log line, after `format!` (6587 … 6630), frame-only

`log_site`: from the return of `format_inner` (6587) with the `String` at sp + 744 (`StrOut`), the
`log` call (6608, the message unspecified) and the `String`'s `dealloc` reach 6630 with the
allocator's context kept, `Outside` from sp up, and every allocated chunk of the state `format!`
started from still allocated with its data.
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.Acc Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

theorem log_site {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (cap : Nat)
    (hcap : 1000 ≤ cap ∧ cap < 2 ^ 64) (env : AccEnv) (envH : RefineHost.Env) (pb S0 S1 : Nat)
    (x : AccCtx) (ω : Regs) (μ : Memory) (s₀ s : State) (sp : Nat)
    (H : HeapCtx envH pb S0 S1 μ s) (hso : StrOut s₀ s μ (sp + 744)) (h1 : ω[1] = UInt64.ofNat sp)
    (hsp : 2147483716 ≤ sp ∧ S0 + 40 ≤ sp ∧ sp + 768 ≤ S1) :
    ∃ ω' μ' s', FreeStepsH p (accContractK cap env) 6587 ω μ x 6630 ω' μ' x 300 ∧
      HeapCtx envH pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Outside pb sp (fun _ => False) μ μ' ∧
      (∀ d ∈ chunks s₀, d.used = true → d ∈ chunks s' ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
      ω'[1] = ω[1] ∧ ω'[6] = ω[6] := by
  have hS1 := H.hS1
  have hst := H.st
  obtain ⟨scap, slen, hs⟩ := hso
  have hr : ∀ a, sp + 744 ≤ a → a < sp + 768 → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (hst a (by omega) (by omega))
  obtain ⟨ω1, run1, a0, a1, a5, a6⟩ := ls_a (p := p) (P := P) (R := accContractK cap env) x ω μ sp (by omega) h1 hr
  -- the log call
  have refl : ∀ d ∈ chunks s₀, d.used = true → d ∈ chunks s ∧ ∀ a, InData d a → μ.read a = μ.read a :=
    fun d hd hu => ⟨hs.base d hd hu, fun _ _ => rfl⟩
  have outR : Outside pb sp (fun _ => False) μ μ :=
    ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ => rfl⟩
  have w1 : (setR7 ω1 Result.WHAT)[1] = UInt64.ofNat sp := by
    simp only [setR7, Vector.getElem_set]; simp [a1, h1]
  have w5 : (setR7 ω1 Result.WHAT)[5] = UInt64.ofNat (rdN μ (sp + 752) 8) := by
    simp only [setR7, Vector.getElem_set]; simp [a5]
  have w0 : (setR7 ω1 Result.WHAT)[0] = ω[0] := by simp only [setR7, Vector.getElem_set]; simp [a0]
  have w6 : (setR7 ω1 Result.WHAT)[6] = ω[6] := by simp only [setR7, Vector.getElem_set]; simp [a6]
  by_cases hc0 : scap = 0
  · subst hc0
    obtain ⟨ω2, run2, b0, b1, b5, b6⟩ := ls_b0 (p := p) (P := P) (R := accContractK cap env) x
      (setR7 ω1 Result.WHAT) μ sp (by omega) w1 hs.rc (fun a h1 h2 => hr a h1 (by omega))
    refine ⟨ω2, μ, s, run1.trans (FreeStepsH.logAcc cap hcap env (d_6608 (p := p) (P := P)) run2) |>.mono (by omega), H, rfl, outR,
      refl, b1.trans (w1.trans h1.symm), b6.trans w6⟩
  · obtain ⟨c, hc, hcu, hca, -, hcf⟩ := hs.buf.resolve_left hc0
    obtain ⟨ω2, run2, b0, b1, b5, b6, b7⟩ := ls_b (p := p) (P := P) (R := accContractK cap env) x
      (setR7 ω1 Result.WHAT) μ sp (rdN μ (sp + 744 + 8) 8) (by omega) (rdN_lt64 μ _) w1 w5
      (by rw [hs.rc]; exact hc0) (fun a h1 h2 => hr a h1 (by omega))
    obtain ⟨ω3, μ3, run3, H3, hb3, hpg, hro, stk, hgl, keep3, c0, c1, c5, c6⟩ :=
      Decode.DeallocCall.dealloc_call (R := accContractK cap env) (p := p) (P := P) envH pb S0 S1 x ω2 μ s sp
        (rdN μ (sp + 744 + 8) 8) 224 6630 c H hc hcu hca b0 (b1.trans w1) b7 (by decide) jte_111 bs_6630 hsp.1
        ⟨hsp.2.1, by omega⟩
    have out3 : Outside pb sp (fun _ => False) μ μ3 :=
      ⟨fun b _ => ⟨by unfold Memory.readable; rw [hpg], by unfold Memory.writable; rw [hpg]⟩,
        fun b hb _ hw => hro b hb hw, fun a ha hb _ => stk a hb ha, hgl⟩
    refine ⟨ω3, μ3, free s (rdN μ (sp + 744 + 8) 8),
      (run1.trans (FreeStepsH.logAcc cap hcap env (d_6608 (p := p) (P := P)) (run2.trans run3))).mono (by omega),
      H3, hb3, out3, fun d hd hu => ?_, c1.trans (b1.trans (w1.trans h1.symm)),
      c6.trans (b6.trans w6)⟩
    have hd' := hs.base d hd hu
    have hne : d ≠ c := fun e => hcf d hd hu (by rw [e])
    exact keep3 d hd' hu hne

end Services.Bootstrap.Fmt
