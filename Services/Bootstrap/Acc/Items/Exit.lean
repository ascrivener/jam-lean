import Services.Bootstrap.Acc.Items.End
import Services.Bootstrap.Acc.Items.Disp
import Services.Bootstrap.Decode.DeallocCall

/-!
# The items loop's exit (6766 → 15359)

When the loop's cursor reaches the end, accumulate frees the items buffer (`dealloc`, 40613, when
its capacity is not 0) and returns (0, 0): no hash (GP eq. `accinvocation`: Ψ_A then takes no yield
from the output). `items_end` composes `il_step_end`, `il_end_free` / `il_end_nofree`,
`dealloc_callG` and `il_ret`.
-/

namespace Services.Bootstrap.Acc
open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.DeallocCall
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
variable {X : Type} {R : HostRel X}

/-- **The items loop's end, 6766 → 15359**: when the cursor (sp + 168) is the end (sp + 144), the
    items buffer q (at sp + 16, capacity c at sp + 32) is freed if c ≠ 0 (a used chunk of the
    allocator's context), and accumulate returns (0, 0): (ω₇, ω₈) = (0, 0), ω₀ the return address
    saved at sp + 1848, the frame popped, at the return's `jumpInd`. The allocator's context holds
    for the state after the free. -/
theorem items_end {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (code : ByteArray)
    (pb S0 S1 : Nat) (x : X) (ω : Regs) (μ : Memory) (s : State) (sp e q c : Nat)
    (H : HeapCtxC code pb S0 S1 μ s) (h1 : ω[1] = UInt64.ofNat sp)
    (hsp : 2147483716 ≤ sp ∧ sp + 1856 < 4294967296) (hS : S0 + 40 ≤ sp ∧ sp + 1856 ≤ S1)
    (m168 : rdN μ (sp + 168) 8 = e) (m144 : rdN μ (sp + 144) 8 = e)
    (m32 : rdN μ (sp + 32) 8 = c) (m16 : rdN μ (sp + 16) 8 = q)
    (hq : c ≠ 0 → ∃ d ∈ chunks s, d.used = true ∧ d.addr + 32 = q) :
    ∃ ω' μ' s', FreeStepsH p R 6766 ω μ x 15359 ω' μ' x 280 ∧
      ω'[7] = UInt64.ofNat 0 ∧ ω'[8] = UInt64.ofNat 0 ∧ ω'[1] = UInt64.ofNat (sp + 1856) ∧
      ω'[0] = UInt64.ofNat (rdN μ (sp + 1848) 8) ∧ ω'[5] = UInt64.ofNat (rdN μ (sp + 1840) 8) ∧
      ω'[6] = UInt64.ofNat (rdN μ (sp + 1832) 8) ∧ HeapCtxC code pb S0 S1 μ' s' ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) := by
  have hst := H.st
  have hrf : ∀ a, sp ≤ a → a < sp + 1856 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega))
  obtain ⟨ω1, run1, f1⟩ := il_step_end (p := p) (P := P) (R := R) x ω μ sp e h1 ⟨by omega, by omega⟩ m168 m144 hrf
  have e1 : ω1[1] = UInt64.ofNat sp := (f1 1 (by decide)).trans h1
  by_cases hc : c = 0
  · subst hc
    obtain ⟨ω2, run2, f2⟩ := il_end_nofree (p := p) (P := P) (R := R) x ω1 μ sp e1 ⟨by omega, by omega⟩ m32 hrf
    obtain ⟨ω3, run3, g7, g8, g1, g0, g5, g6⟩ := il_ret (p := p) (P := P) (R := R) x ω2 μ sp
      ((f2 1 (by decide)).trans e1) ⟨by omega, by omega⟩ hrf
    exact ⟨ω3, μ, s, ((run1.trans run2).trans run3).mono (by omega), g7, g8, g1, g0, g5, g6, H,
      fun _ _ _ => rfl⟩
  · obtain ⟨d, hd, hdu, hda⟩ := hq hc
    obtain ⟨ω2, run2, a0, a1, a7, f2⟩ := il_end_free (p := p) (P := P) (R := R) x ω1 μ sp q c e1
      ⟨by omega, by omega⟩ m32 m16 hc hrf
    obtain ⟨ω3, μ3, run3, H3, -, -, -, stk3, -, -, -, b1, -, -⟩ :=
      dealloc_callG (R := R) (p := p) (P := P) code pb S0 S1 x ω2 μ s sp q 574 15339 d H hd hdu hda a0 a1 a7
        (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_286]) bs_15339 hsp.1 ⟨hS.1, by omega⟩
    have hrf3 : ∀ a, sp ≤ a → a < sp + 1856 → μ3.readable a = true := fun a h1 h2 => by
      have := H3.st a (by omega) (by omega); exact Memory.readable_of_writable this
    have kk : ∀ o, sp ≤ o → o + 8 ≤ sp + 1856 → rdN μ3 o 8 = rdN μ o 8 := fun o h1 h2 => by
      unfold rdN; congr 1; exact PVM.Memory.readN_congr fun j hj => stk3 _ (by omega) (by omega)
    obtain ⟨ω4, run4, g7, g8, g1, g0, g5, g6⟩ := il_ret (p := p) (P := P) (R := R) x ω3 μ3 sp
      (b1.trans a1) ⟨by omega, by omega⟩ hrf3
    refine ⟨ω4, μ3, free s q, ((run1.trans run2).trans (run3.trans run4)).mono (by omega), g7, g8, g1,
      by rw [g0, kk _ (by omega) (by omega)], by rw [g5, kk _ (by omega) (by omega)],
      by rw [g6, kk _ (by omega) (by omega)], H3, stk3⟩

end Services.Bootstrap.Acc
