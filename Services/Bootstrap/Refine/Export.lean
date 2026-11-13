import Services.Bootstrap.Refine.Pass
import Services.Bootstrap.Refine.HostSteps
import Services.Bootstrap.Refine.Exit

/-!
# Refine's `Export` handler (5587 … 5042)

`Instruction::ExportSegs { data: Vec<Vec<u8>> }` (dispatch index 10): for each segment, refine calls `export`
(host 8, Ω_E: GP v0.8.0 Appendix B.4) on its octets, formats and logs the result (5744 → 59375, 5784,
5800), then pushes `Exported(n)` with n the number of segments (quirk Q11: attempts are counted, failed
exports included), frees the segments and their `Vec`, and goes round (5042). The staged element is at
M + 304, its `Vec<Vec<u8>>` `{cap, ptr, len}` at M + 312.
-/

namespace Services.Bootstrap.Refine.Export

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeR
  Services.Bootstrap.Encode.Writer

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 5095 … 5587: back from the staging copy, an element of index 10 (`ExportSegs`, D = 2^63 + 9) goes to
    the handler at 5587, with ω₈ = 10. -/
theorem xd {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (M : Nat) (hM : M + 632 ≤ 4294967296)
    (h1 : ω[1] = UInt64.ofNat M) (h6 : ω[6] = UInt64.ofNat (9223372036854775807 + 10))
    (s128 : μ.readN (M + 128) 8 = Num.encodeLE 8 9223372036854775832)
    (s136 : μ.readN (M + 136) 8 = Num.encodeLE 8 9223372036854775809)
    (hr : ∀ a, M + 128 ≤ a → a < M + 144 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 5095 ω μ x 5587 ω' μ x 10 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧
      ω'[8] = UInt64.ofNat 10 := by
  have r128 := rd8 (by decide) s128
  have r136 := rd8 (by decide) s136
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h6, hM, hr, r128, r136, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_⟩ <;> simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
      List.lookup_nil, Option.getD_none, Option.getD_some]

/-- 5587 … 5639: the handler keeps the index 10 at M + 72 and the segments' `Vec` `{cap, ptr, len}` (from the
    element at `cur`, ω₅) at M + 64, M + 104, M + 56, with 24·len at M + 96; with len ≠ 0 it keeps the end
    ptr + 24·len at M + 152 and goes to the first segment (5653) with ω₅ = ptr. Memory changes only at
    M + 56 … M + 112 and M + 152 … M + 160. -/
theorem xa {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (M cur cap ptr len : Nat) (hM : 65536 ≤ M ∧ M + 632 ≤ 4294967296 ∧ M % 8 = 0)
    (hcur : cur + 32 ≤ 4294967296) (hcM : cur + 32 ≤ M + 56 ∨ M + 160 ≤ cur)
    (hcap : cap < 18446744073709551616) (hptr : ptr + 24 * len < 18446744073709551616) (hlen : len ≠ 0)
    (h1 : ω[1] = UInt64.ofNat M) (h5 : ω[5] = UInt64.ofNat cur) (h8 : ω[8] = UInt64.ofNat 10)
    (s8 : μ.readN (cur + 8) 8 = Num.encodeLE 8 cap) (s16 : μ.readN (cur + 16) 8 = Num.encodeLE 8 ptr)
    (s24 : μ.readN (cur + 24) 8 = Num.encodeLE 8 len)
    (hr : ∀ a, cur + 8 ≤ a → a < cur + 32 → μ.readable a = true)
    (hw : ∀ a, M + 56 ≤ a → a < M + 160 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 5587 ω μ x 5653 ω' μ' x 20 ∧ ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat ptr ∧
      μ'.readN (M + 72) 8 = Num.encodeLE 8 10 ∧ μ'.readN (M + 64) 8 = Num.encodeLE 8 cap ∧
      μ'.readN (M + 104) 8 = Num.encodeLE 8 ptr ∧ μ'.readN (M + 96) 8 = Num.encodeLE 8 (24 * len) ∧
      μ'.readN (M + 56) 8 = Num.encodeLE 8 len ∧ μ'.readN (M + 152) 8 = Num.encodeLE 8 (ptr + 24 * len) ∧
      (∀ a, a < 4294967296 → (a < M + 56 ∨ (M + 112 ≤ a ∧ a < M + 152) ∨ M + 160 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hM0, hM1, hM8⟩ := hM
  have rc := rd8 hcap s8
  have rp := rd8 (by omega) s16
  have rl := rd8 (by omega) s24
  have hl0 : ¬ len = 0 := hlen
  have hr2 : ∀ a, M + 56 ≤ a → a < M + 160 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h8, hM0, hM1, hM8, hcur, hcM, hl0, hr, hr2, hw, rc, rp, rl, Exit.rdN_writeN_enc8,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]
    post_simp

end Services.Bootstrap.Refine.Export
