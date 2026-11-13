import Services.Bootstrap.Acc.Inputs.LoopInd

/-!
# The inputs' glue (44495 … 44674)

In 6630's 144-octet frame (sp): the fetched `Vec<u8>` (cap, ptr, len at sp + 56, + 64, + 72) becomes a
reader {ptr, len} at sp + 104; the count n by `decodeU32A`; the items by `lp_call` into sp + 80; the
fetched buffer freed; `Vec { cap, ptr, len }` written at *(sp + 8); the return. See the Acc README.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **44495 … 44521**, the fetch's `Ok` (cap c ≠ −1 at sp + 56, ptr at + 64, len at + 72): ptr saved at sp,
    the reader {ptr, len} at sp + 104, and the count's decode (ω₇ = sp + 104, return address 2024). -/
theorem g_pre {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp c ptr len : Nat) (h1 : ω[1] = UInt64.ofNat sp) (m56 : rdN μ (sp + 56) 8 = c)
    (m64 : rdN μ (sp + 64) 8 = ptr) (m72 : rdN μ (sp + 72) 8 = len) (hc : c ≠ 18446744073709551615)
    (hsp : 65536 ≤ sp ∧ sp + 144 < 4294967296) (hwf : ∀ a, sp ≤ a → a < sp + 144 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 44495 ω μ x 39710 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat 2024 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = UInt64.ofNat c ∧
      ω'[7] = UInt64.ofNat (sp + 104) ∧
      rdN μ' sp 8 = ptr ∧ μ'.readN (sp + 104) 8 = Num.encodeLE 8 ptr ∧ μ'.readN (sp + 112) 8 = Num.encodeLE 8 len ∧
      (∀ a, a < 4294967296 → (a < sp ∨ sp + 8 ≤ a) → (a < sp + 104 ∨ sp + 120 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp ≤ a → a < sp + 144 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have hc64 : c < 18446744073709551616 := by rw [← m56]; exact rdN_lt64 _ _
  have hp : ptr < 18446744073709551616 := by rw [← m64]; exact rdN_lt64 _ _
  have hl : len < 18446744073709551616 := by rw [← m72]; exact rdN_lt64 _ _
  have hc' : c % 18446744073709551616 ≠ 18446744073709551615 := by rw [Nat.mod_eq_of_lt hc64]; exact hc
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, m56, m64, m72, hc', hwf, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1]
    all_goals try with_reducible rfl
    all_goals try first
      | (rd_simp []; done)
      | rd_simp []
    all_goals try first
      | with_reducible rfl
      | with_reducible exact Nat.mod_eq_of_lt (by omega)
    all_goals first
      | (congr 1; omega)
      | (simp only [Nat.reduceMul, Nat.reducePow]; exact Nat.mod_eq_of_lt (by omega))
      | (congr 1; exact Nat.mod_eq_of_lt (by omega))
      | rfl

end Services.Bootstrap.Acc
