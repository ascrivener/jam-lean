import Services.Bootstrap.Acc.Handlers.InstrLoopTail

/-!
# R5, the instruction loop: the push when the results `Vec` is full (14420 … 14509)

Spec `onWorkItem`'s `results := results ++ [r]` (GP v0.8.0 Appendix B, Ω_W; bootstrap's own loop).
With len = cap, the `Vec` grows through `finish_grow` (14431 → 14485, the named hypothesis `PushH`);
these are the straight-line pieces either side of it: `il_full` (14420 → 14431) and `il_push2`
(14485 → the memcpy of the result's 144 octets, return 540).
-/

namespace Services.Bootstrap.Acc.Handlers.InstrLoop

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.Alloc Services.Bootstrap.Acc Services.Bootstrap.Spec

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **14420 … 14428, full** (len n = cap at sp + 464 / sp + 448): on to `finish_grow`'s call site
    14431 with ω₅ = n. -/
theorem il_full {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp n : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : 65536 ≤ sp ∧ sp + 1632 < 4294967296)
    (hn : n < 2 ^ 64)
    (mcp : μ.readN (sp + 448) 8 = Num.encodeLE 8 n) (mn : μ.readN (sp + 464) 8 = Num.encodeLE 8 n)
    (hr : ∀ a, sp + 448 ≤ a → a < sp + 472 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 14420 ω μ x 14431 ω' μ x 3 ∧ ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat n ∧
      ω'[6] = ω[6] := by
  have rcp := Handlers.DesignateAlloc.rd8 hn mcp
  have rn := Handlers.DesignateAlloc.rd8 hn mn
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hsp, rcp, rn, hr, ↓rdN_fold]
  · refine ⟨by reg_val, ?_, by reg_val⟩
    all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1, Nat.mod_eq_of_lt hn]

/-- **14485 … 14509, after the growth**: the call of memcpy (68729, return 540) of the 144 octets of
    the result at sp + 1000 to rp + 144·n (rp at sp + 456, n in ω₅); ω₅ kept. -/
theorem il_push2 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp rp n : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat n)
    (hsp : 65536 ≤ sp ∧ sp + 1632 < 4294967296) (hrp : rp + 144 * n < 2 ^ 64)
    (mrp : μ.readN (sp + 456) 8 = Num.encodeLE 8 rp)
    (hr : ∀ a, sp + 456 ≤ a → a < sp + 464 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 14485 ω μ x 68729 ω' μ x 8 ∧ ω'[0] = UInt64.ofNat 540 ∧ ω'[1] = ω[1] ∧
      ω'[5] = ω[5] ∧ ω'[7] = UInt64.ofNat (rp + 144 * n) ∧ ω'[8] = UInt64.ofNat (sp + 1000) ∧
      ω'[9] = UInt64.ofNat 144 := by
  have rrp := Handlers.DesignateAlloc.rd8 (by omega) mrp
  have hn : n < 2 ^ 64 := by omega
  have e144 : (rp + ((n * 16 % 18446744073709551616) + (n * 128 % 18446744073709551616)) %
      18446744073709551616) % 18446744073709551616 = rp + 144 * n := by
    rw [Nat.mod_eq_of_lt (a := n * 16) (by omega), Nat.mod_eq_of_lt (a := n * 128) (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hsp, rrp, hr, ↓rdN_fold]
  · refine ⟨by reg_val, by reg_val, by reg_val, ?_, ?_, by reg_val⟩
    all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1, h5, Nat.mod_eq_of_lt hn]
    all_goals try (congr 1; omega)
    all_goals try (apply UInt64.toNat_inj.1; simp [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat]; omega)

end Services.Bootstrap.Acc.Handlers.InstrLoop
