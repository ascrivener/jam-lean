import Services.Bootstrap.ReaderBig
import PVM.Logic.Go

/-!
# Bootstrap's argument decode: the steps between the summaries

The refine entry decodes its arguments with the summarized functions (`decodeU16`, `decodeU32`,
`read_big`) and a few straight-line steps between them, proved here with `pvm_go`. The frame is the
entry's: ω₁ = sp = 4278058264, the reader at sp + 40.
-/

namespace Services.Bootstrap

open PVM Services.Bootstrap.Code

set_option maxHeartbeats 8000000

variable {X : Type} {R : HostRel X}

/-- After the core index's decode (ω₇ = 0, ω₈ = the value): store it at sp + 32, call the next decode. -/
theorem glueC {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (v : Nat)
    (hv : v < 18446744073709551616) (h7 : ω[7] = UInt64.ofNat 0) (h8 : ω[8] = UInt64.ofNat v)
    (h1 : ω[1] = UInt64.ofNat 4278058264)
    (hw : ∀ a, 4278058296 ≤ a → a < 4278058304 → μ.writable a = true) :
    ∃ ω', FreeStepsH p R 35073 ω μ x 31894 ω' (μ.writeN 4278058296 (Num.encodeLE 8 v)) x 5 ∧
      ω'[0] = UInt64.ofNat 1636 ∧ ω'[1] = UInt64.ofNat 4278058264 ∧ ω'[7] = UInt64.ofNat 4278058304 ∧
      ∀ j : Fin 13, j.val ∉ [0, 7] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, h7, h8, hw, hv, PVM.bitwise_and_m1]
  case post =>
    refine ⟨?_, ?_, ?_, fun j hj => ?_⟩
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some',
        List.lookup_nil, Option.getD_none, h1]
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      simp only [Fin.getElem_fin]
      rw [PVM.getElem_regsNF _ _ _ j.isLt]
      simp [PVM.lookup_cons_nat, hj.1, hj.2]
      rfl

/-- After the item index's decode (ω₇ = 0, ω₈ = the value): store it at sp + 24, call the next decode. -/
theorem glueI {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (v : Nat)
    (hv : v < 18446744073709551616) (h7 : ω[7] = UInt64.ofNat 0) (h8 : ω[8] = UInt64.ofNat v)
    (h1 : ω[1] = UInt64.ofNat 4278058264)
    (hw : ∀ a, 4278058288 ≤ a → a < 4278058296 → μ.writable a = true) :
    ∃ ω', FreeStepsH p R 35092 ω μ x 31894 ω' (μ.writeN 4278058288 (Num.encodeLE 8 v)) x 5 ∧
      ω'[0] = UInt64.ofNat 1638 ∧ ω'[1] = UInt64.ofNat 4278058264 ∧ ω'[7] = UInt64.ofNat 4278058304 ∧
      ∀ j : Fin 13, j.val ∉ [0, 7] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, h7, h8, hw, hv, PVM.bitwise_and_m1]
  case post =>
    refine ⟨?_, ?_, ?_, fun j hj => ?_⟩
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some',
        List.lookup_nil, Option.getD_none, h1]
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      simp only [Fin.getElem_fin]
      rw [PVM.getElem_regsNF _ _ _ j.isLt]
      simp [PVM.lookup_cons_nat, hj.1, hj.2]
      rfl

/-- After the service id's decode (ω₇ = 0, ω₈ = the value): store it at sp + 16, call the next decode. -/
theorem glueS {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (v : Nat)
    (hv : v < 18446744073709551616) (h7 : ω[7] = UInt64.ofNat 0) (h8 : ω[8] = UInt64.ofNat v)
    (h1 : ω[1] = UInt64.ofNat 4278058264)
    (hw : ∀ a, 4278058280 ≤ a → a < 4278058288 → μ.writable a = true) :
    ∃ ω', FreeStepsH p R 35111 ω μ x 31894 ω' (μ.writeN 4278058280 (Num.encodeLE 8 v)) x 5 ∧
      ω'[0] = UInt64.ofNat 1640 ∧ ω'[1] = UInt64.ofNat 4278058264 ∧ ω'[7] = UInt64.ofNat 4278058304 ∧
      ∀ j : Fin 13, j.val ∉ [0, 7] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, h7, h8, hw, hv, PVM.bitwise_and_m1]
  case post =>
    refine ⟨?_, ?_, ?_, fun j hj => ?_⟩
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some',
        List.lookup_nil, Option.getD_none, h1]
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      simp only [Fin.getElem_fin]
      rw [PVM.getElem_regsNF _ _ _ j.isLt]
      simp [PVM.lookup_cons_nat, hj.1, hj.2]
      rfl

/-- After |y| = 0's decode: the payload as an empty `Vec` (the function at 3473), then the call reading
    the 32-octet hash into sp + 56. Memory changes only in [sp − 96, sp + 88). -/
theorem glueVec {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (h7 : ω[7] = UInt64.ofNat 0) (h8 : ω[8] = UInt64.ofNat 0) (h1 : ω[1] = UInt64.ofNat 4278058264)
    (hwf : ∀ a, 4278058168 ≤ a → a < 4278058352 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 35130 ω μ x 58434 ω' μ' x 60 ∧
      ω'[0] = UInt64.ofNat 1644 ∧ ω'[1] = UInt64.ofNat 4278058264 ∧ ω'[5] = ω[5] ∧ ω'[6] = UInt64.ofNat 0 ∧
      ω'[7] = UInt64.ofNat 4278058304 ∧ ω'[8] = UInt64.ofNat 4278058320 ∧ ω'[9] = UInt64.ofNat 32 ∧
      μ'.readN 4278058264 8 = Num.encodeLE 8 0 ∧ μ'.readN 4278058272 8 = Num.encodeLE 8 1 ∧
      (∀ a, a < 4294967296 → (a < 4278058168 ∨ 4278058352 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hrf : ∀ a, 4278058168 ≤ a → a < 4278058352 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h7, h8, hwf, hrf, PVM.bitwise_and_m1]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, PVM.Memory.readN_writeN_same,
      PVM.Memory.readN_writeN_disjoint, PVM.Memory.read_writeN_disjoint, PVM.Memory.readable_writeN,
      PVM.Memory.writable_writeN, PVM.Num.length_encodeLE, List.length_cons, List.length_nil, PVM.two32]
    all_goals try rfl

end Services.Bootstrap
