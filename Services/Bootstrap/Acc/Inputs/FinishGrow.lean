import Services.Bootstrap.CodeAAll
import Services.Bootstrap.Alloc.AllocWrap
import PVM.Logic.Go

/-!
# Accumulate's `finish_grow` (40852 / 41016): the allocator's lock around `alloc_impl`

`RawVec`'s growth in accumulate's `Vec` decoders calls 40852 (`finish_grow`), which inlines the
allocator's lock instead of calling the `alloc` / `realloc` wrappers (40494, 40701) refine's
decoders use. With no current block it continues at 41016: the layout's bounds, the lock (the word
at 206848), `alloc_impl` (41177) for ⌈size/32⌉ units of alignment ⌈align/32⌉ with the zero flag
clear, the unlock, and the `Result` written at `out`: `Ok(ptr, size)` (tag 0) or, for a null
block, `Err(align, size)` (tag 1).
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **41016 … 41177**: the layout (align at sp, `out` at sp + 8, size in ω₆) within 2³⁷ − 32, the
    allocator's lock taken, and the call of `alloc_impl`: ω₇ = 196792, ω₈ = ⌈align/32⌉,
    ω₉ = ⌈size/32⌉, ω₁₀ = 0, return address 1996. -/
theorem fg_alloc_lock {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp al size out : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h6 : ω[6] = UInt64.ofNat size)
    (m0 : rdN μ sp 8 = al) (m8 : rdN μ (sp + 8) 8 = out)
    (hal : al + 31 < 68719476736) (hs : size + 31 < 68719476736) (hsp : 65536 ≤ sp ∧ sp + 16 < 4294967296)
    (hout : out < 18446744073709551616)
    (hrs : ∀ a, sp ≤ a → a < sp + 16 → μ.readable a = true)
    (hl : rdN μ 206848 1 = 0) {HT S0 S1 : Nat} (hH : 206864 ≤ HT) (hwr : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 41016 ω μ x 41177 ω' μ' x 30 ∧
      ω'[7] = UInt64.ofNat 196792 ∧ ω'[8] = UInt64.ofNat ((al + 31) / 32) ∧
      ω'[9] = UInt64.ofNat ((size + 31) / 32) ∧ ω'[10] = UInt64.ofNat 0 ∧ ω'[0] = UInt64.ofNat 1996 ∧
      ω'[1] = ω[1] ∧ ω'[4] = ω[4] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      (∀ a, a < 4294967296 → (a < 196608 ∨ 196616 ≤ a) → (a < 206848 ∨ 206852 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) := by
  have hr := hwr.rd
  have hand := lock_test (w := rdN μ 206848 4) (by rw [rdN4_mod]; exact hl)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h6, m0, m8, hrs, hand, show 137438953440 ≥ al by omega,
    show 137438953440 ≥ size by omega, show ¬ 137438953440 < al by omega, show ¬ 137438953440 < size by omega,
    hwr, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, by reg_val, ?_, ?_, by reg_val, by reg_val, ?_, by reg_val, by reg_val,
      fun a ha h1 h2 => ?_, fun a => ?_⟩
    · reg_val
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some',
        List.lookup_nil, Option.getD_none]
      apply UInt64.toNat.inj
      simp only [UInt64.toNat_ofNat']
      simpa using hand
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some',
        List.lookup_nil, Option.getD_none]
      rd_simp []
      simp
    · rd_simp []
    · rd_simp [hwr]

end Services.Bootstrap.Acc
