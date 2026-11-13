import Services.Bootstrap.Alloc.AllocTail
import Services.Bootstrap.Memzero

/-!
# The binary's `alloc_impl` with the zero flag: the tail

`alloc_impl` (41177) stores its argument ω₁₀, the zero flag, at its frame + 112. The tail
(42054 … 42128) computes w = ω₁₀ ∧ flag (ω₁₀ there: whether the block may hold old data); w = 0
returns at 41404 … 41423 as in `AllocTail.lean`, and w ≠ 0 pops the frame and tail-calls `memzero`
(70133) on the block's 32·req data octets, which returns to the caller itself. Both end at the
caller's return target t, with ω₇ the data address, ω₁ the caller's stack pointer, and ω₀, ω₅, ω₆
restored from the frame. The flag-0 lemmas (`an_tail_in`, `an_tail_end`, `an_ret`) are unchanged.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **41404 … 41423 and the return**: ω₇ = ω₁₁, the frame popped, and the jump to the caller's
    return target t (ω₀ = ret from the frame, an entry of **j**). -/
theorem an_retZ {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp ret t : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h144 : rdN μ (sp + 144) 8 = ret)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hsp : sp + 152 < 4294967296) {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1)
    (hr : RdAt μ HT S0 S1) :
    ∃ ω', FreeStepsH p R 41404 ω μ x t ω' μ x 7 ∧ ω'[7] = ω[11] ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[5] = UInt64.ofNat (rdN μ (sp + 136) 8) ∧
      ω'[6] = UInt64.ofNat (rdN μ (sp + 128) 8) ∧ ω'[1] = UInt64.ofNat (sp + 152) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, hr, h144, hret, hjt, hbt, ↓rdN_fold, ↓loadI_fold]
  case post => exact ⟨by reg_val; rfl, by reg_val; rw [h144], by reg_val, by reg_val, by reg_val⟩

end Services.Bootstrap.Alloc
