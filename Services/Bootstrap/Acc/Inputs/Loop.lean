import Services.Bootstrap.Acc.Inputs.ItemCall
import Services.Bootstrap.Acc.Inputs.FinishGrowCall

/-!
# `Vec<AccumulateItem>::decode` (44916), the loop

See the Acc README for the map. With n ≤ 89 items (the temporary bound) the buffer of n·184 octets is
allocated once (`fg_new_call`) and never grown.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **44916 … 45036**, n > 0 items (n ≤ 89): the 480-octet frame (s = sp − 480; ω₀, ω₅, ω₆ at
    s + 472, + 464, + 456), out at s, the reader at s + 48, `Vec { cap 0, ptr 8, len 0 }` at s + 64,
    n at s + 32, and `finish_grow` for n·184 octets (align 8) into s + 272 (return address 2040). -/
theorem lp_pre {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp out rd n : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat out)
    (h8 : ω[8] = UInt64.ofNat rd) (h9 : ω[9] = UInt64.ofNat n) (hn : 0 < n ∧ n ≤ 89)
    (hsp : 65536 + 480 ≤ sp ∧ sp < 4294967296) (hout : out < 18446744073709551616)
    (hrd : rd < 18446744073709551616)
    (hwf : ∀ a, sp - 480 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 44916 ω μ x 40852 ω' μ' x 60 ∧
      ω'[0] = UInt64.ofNat 2040 ∧ ω'[1] = UInt64.ofNat (sp - 480) ∧ ω'[5] = UInt64.ofNat n ∧
      ω'[6] = UInt64.ofNat n ∧ ω'[7] = UInt64.ofNat (sp - 480 + 272) ∧ ω'[8] = UInt64.ofNat 0 ∧
      ω'[10] = UInt64.ofNat n ∧ ω'[11] = UInt64.ofNat 8 ∧ ω'[12] = UInt64.ofNat 184 ∧
      rdN μ' (sp - 480 + 472) 8 = ω[0].toNat ∧ rdN μ' (sp - 480 + 464) 8 = ω[5].toNat ∧
      rdN μ' (sp - 480 + 456) 8 = ω[6].toNat ∧ rdN μ' (sp - 480) 8 = out ∧ rdN μ' (sp - 480 + 48) 8 = rd ∧
      rdN μ' (sp - 480 + 32) 8 = n ∧ rdN μ' (sp - 480 + 40) 8 = n ∧ rdN μ' (sp - 480 + 56) 8 = 89 ∧
      rdN μ' (sp - 480 + 64) 8 = 0 ∧ rdN μ' (sp - 480 + 72) 8 = 8 ∧ rdN μ' (sp - 480 + 80) 8 = 0 ∧
      (∀ a, a < 4294967296 → (a < sp - 480 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 480 ≤ a → a < sp → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have hnm : n % 18446744073709551616 = n := by omega
  have hn0 : n ≠ 0 := by omega
  have z : ∀ μ0 : Memory, rdN (μ0.writeN (sp - 480 + 64) [UInt8.ofNat 0, UInt8.ofNat 0, UInt8.ofNat 0,
      UInt8.ofNat 0, UInt8.ofNat 0, UInt8.ofNat 0, UInt8.ofNat 0, UInt8.ofNat 0]) (sp - 480 + 64) 8 = 0 := by
    intro μ0; unfold rdN
    rw [PVM.Memory.readN_writeN_same μ0 (sp - 480 + 64) 8 _ rfl (by unfold PVM.two32; omega)]; rfl
  have hmin : (if n < 89 then n else 89) = n := by split <;> omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h7, h8, h9, hnm, hn0, z, hwf, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h7, h8, h9, hnm, z]
    all_goals try with_reducible rfl
    all_goals try first
      | (rd_simp []; done)
      | rd_simp []
    all_goals try first
      | with_reducible rfl
      | with_reducible exact Nat.mod_eq_of_lt (by omega)
    all_goals first
      | decide
      | (simp only [Nat.reduceMul, Nat.reducePow]; exact Nat.mod_eq_of_lt (UInt64.toNat_lt _))

end Services.Bootstrap.Acc
