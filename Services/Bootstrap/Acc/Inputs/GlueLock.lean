import Services.Bootstrap.Acc.Inputs.FetchVec
import Services.Bootstrap.Alloc.Dealloc

/-!
# The inputs' glue: the allocator's lock around the free (44591 … 44641)

After the items are decoded, the fetched buffer is freed with the allocator's lock taken inline: the
lock word at 206848 (196792 + 10056) set, the free path 42327 called (return address 2028 → 44632) on
the block saved at sp, and the lock byte cleared (196792 + 8192 + 1864). See the Acc README.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **44591 … 44626**: the lock (free: its byte 0) taken, the scratch at 196608 … 196616 used, and the
    call of the free path 42327 on the block saved at sp: ω₇ = 196792, ω₈ = ptr, return address 2028. -/
theorem g_lock {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h6 : ω[6] = UInt64.ofNat 196792)
    (h7 : ω[7] = UInt64.ofNat 206848) (h8 : ω[8] = UInt64.ofNat 1)
    (hl : rdN μ 206848 1 = 0) {HT S0 S1 : Nat} (hH : 206864 ≤ HT) (hsp : S0 ≤ sp ∧ sp + 8 ≤ S1)
    (hsp2 : 2147483648 ≤ sp ∧ sp + 8 < 4294967296) (hwr : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 44591 ω μ x 42327 ω' μ' x 13 ∧
      ω'[0] = UInt64.ofNat 2028 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[7] = UInt64.ofNat 196792 ∧
      ω'[8] = UInt64.ofNat (rdN μ sp 8) ∧
      (∀ a, a < 4294967296 → (a < 196608 ∨ 196616 ≤ a) → (a < 206848 ∨ 206852 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧
      ∀ j : Fin 13, j.val ∉ [0, 4, 7, 8, 9] → ω'[j] = ω[j] := by
  have hr := hwr.rd
  have hand := lock_test (w := rdN μ 206848 4) (by rw [rdN4_mod]; exact hl)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h6, h7, h8, hand, hwr, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, by reg_val; simp [h1], by reg_val, ?_, fun a ha h1 h2 => ?_, fun a => ?_, by reg_frame⟩
    · reg_val
    · rd_simp []
    · rd_simp [hwr]

/-- **44632 … 44641**: the lock byte at 206848 (ω₆ = 196792) cleared. -/
theorem g_unlock {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (h6 : ω[6] = UInt64.ofNat 196792) (hwl : μ.writable 206848 = true) :
    ∃ ω' μ', FreeStepsH p R 44632 ω μ x 44641 ω' μ' x 3 ∧ rdN μ' 206848 1 = 0 ∧
      (∀ a, a < 4294967296 → a ≠ 206848 → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      ω'[7] = UInt64.ofNat 204984 ∧ ∀ j : Fin 13, j.val ∉ [7] → ω'[j] = ω[j] := by
  have hrl : μ.readable 206848 = true := Memory.readable_of_writable hwl
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h6, hwl, hrl]
  case post =>
    refine ⟨?_, fun a ha ha' => ?_, fun a => ?_, fun a => ?_, by reg_val, by reg_frame⟩
    · rd_simp []; rfl
    · simp only [PVM.Memory.writeN_cons, PVM.Memory.writeN_nil]
      exact PVM.read_write_ne' μ 206848 a _ ha' (by omega) ha
    · rd_simp []
    · rd_simp []

end Services.Bootstrap.Acc
