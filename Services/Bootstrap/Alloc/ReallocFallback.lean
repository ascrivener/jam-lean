import Services.Bootstrap.Alloc.ReallocEntry
import Services.Bootstrap.MemcpyBig

/-!
# The binary's `realloc_impl`: the fallback

When the chunk cannot grow in place, `realloc_impl` (from 43259) allocates a new block
(`alloc_impl`, 41177, returning through the jump table to 43276), copies the old usable size into
it (`memcpy`, 68729, returning to 43295), frees the old chunk (the free path, 42327, returning to
43306) and returns the new address. A failed allocation returns null (43326).
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **43259 … 41177**: the old address kept in ω₅, the allocator's address at sp + 104, and the call
    to `alloc_impl` with the alignment and the request, returning to 43276. -/
theorem rf_call {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp ptr al req : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792)
    (h8 : ω[8] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al) (h10 : ω[10] = UInt64.ofNat req)
    (hp : ptr < 4294967296) (hal : al < 4294967296) (hrq : req < 4294967296)
    (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296) {HT S0 S1 : Nat}
    (hS : S0 ≤ sp ∧ sp + 152 ≤ S1) (hw : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 43259 ω μ x 41177 ω' μ' x 6 ∧
      ω'[5] = UInt64.ofNat ptr ∧ ω'[8] = UInt64.ofNat al ∧
      ω'[9] = UInt64.ofNat req ∧ ω'[10] = UInt64.ofNat 0 ∧ ω'[0] = UInt64.ofNat 2002 ∧
      rdN μ' (sp + 104) 8 = 196792 ∧
      (∀ a, a < 4294967296 → (a < sp + 104 ∨ sp + 112 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧ ∀ j : Fin 13, j.val ∉ [0, 5, 8, 9, 10] → ω'[j] = ω[j] := by
  have hr := hw.rd
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h7, h8, h9, h10, hw, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, by reg_val, ?_, fun a ha h1 => ?_,
      fun a => ?_, by reg_frame⟩
    · rd_simp []; rfl
    · rd_simp []
    · rd_simp [hw]

/-- 41423: `alloc_impl`'s return, through the jump table, to 43276. -/
theorem al_ret_realloc {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (h0 : ω[0] = UInt64.ofNat 2002) : FreeStepsH p R 41423 ω μ x 43276 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0]

/-- **43276 … 68729**, a new block q: the copy of u units from the old address (ω₅) to q, returning
    to 43295; q kept in ω₆. -/
theorem rf_copy {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (q u ptr : Nat) (h7 : ω[7] = UInt64.ofNat q) (h6 : ω[6] = UInt64.ofNat u) (h5 : ω[5] = UInt64.ofNat ptr)
    (hq0 : q ≠ 0) (hq : q < 4294967296) (hu : u < 134217728) (hp : ptr < 4294967296) :
    ∃ ω', FreeStepsH p R 43276 ω μ x 68729 ω' μ x 6 ∧
      ω'[7] = UInt64.ofNat q ∧ ω'[8] = UInt64.ofNat ptr ∧ ω'[9] = UInt64.ofNat (32 * u) ∧
      ω'[6] = UInt64.ofNat q ∧ ω'[0] = UInt64.ofNat 2004 ∧
      ∀ j : Fin 13, j.val ∉ [0, 6, 8, 9] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h7, h6, h5, hq0]
  case post =>
    have e : u * 137438953472 % 18446744073709551616 / 4294967296 = 32 * u := by omega
    refine ⟨?_, by reg_val, ?_, by reg_val, by reg_val, by reg_frame⟩
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, List.lookup_nil,
        Option.getD_none]
      exact h7
    simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, ↓reduceIte, PVM.getD_some', Nat.reduceEqDiff]
    congr 1; omega

/-- **43276 … 40805**, no new block: null, the frame popped. -/
theorem rf_null {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v5 v6 : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 0)
    (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296)
    (s0 : rdN μ (sp + 144) 8 = 1988) (s5 : rdN μ (sp + 136) 8 = v5) (s6 : rdN μ (sp + 128) 8 = v6)
    {HT S0 S1 : Nat} (hS : S0 ≤ sp ∧ sp + 152 ≤ S1) (hr : RdAt μ HT S0 S1) :
    ∃ ω', FreeStepsH p R 43276 ω μ x 40805 ω' μ x 9 ∧ ω'[7] = UInt64.ofNat 0 ∧
      ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat (sp + 152) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, h7, s0, s5, s6, hr, ↓rdN_fold]
  case post => exact ⟨by reg_val, by reg_val, by reg_val, by reg_val, by reg_val⟩

/-- **43295 … 42327**: the call to the free path for the old address (ω₅), returning to 43306. -/
theorem rf_free_call {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp ptr : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat ptr)
    (h104 : rdN μ (sp + 104) 8 = 196792) (hp : ptr < 4294967296) (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296)
    {HT S0 S1 : Nat} (hS : S0 ≤ sp ∧ sp + 152 ≤ S1) (hr : RdAt μ HT S0 S1) :
    ∃ ω', FreeStepsH p R 43295 ω μ x 42327 ω' μ x 3 ∧ ω'[7] = UInt64.ofNat 196792 ∧
      ω'[8] = UInt64.ofNat ptr ∧ ω'[0] = UInt64.ofNat 2006 ∧
      ∀ j : Fin 13, j.val ∉ [0, 7, 8] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, h5, h104, hr, ↓rdN_fold]
  case post => exact ⟨by reg_val, by reg_val, by reg_val, by reg_frame⟩

/-- 42978: the free path's return, through the jump table, to the fallback (43306). -/
theorem free_ret_fallback {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (h0 : ω[0] = UInt64.ofNat 2006) : FreeStepsH p R 42978 ω μ x 43306 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0]

/-- **43306 … 40805**: the new address (ω₆) returned, the frame popped. -/
theorem rf_ret {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp q v5 v6 : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h6 : ω[6] = UInt64.ofNat q) (hq : q < 4294967296)
    (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296)
    (s0 : rdN μ (sp + 144) 8 = 1988) (s5 : rdN μ (sp + 136) 8 = v5) (s6 : rdN μ (sp + 128) 8 = v6)
    {HT S0 S1 : Nat} (hS : S0 ≤ sp ∧ sp + 152 ≤ S1) (hr : RdAt μ HT S0 S1) :
    ∃ ω', FreeStepsH p R 43306 ω μ x 40805 ω' μ x 7 ∧ ω'[7] = UInt64.ofNat q ∧
      ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat (sp + 152) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, h6, s0, s5, s6, hr, ↓rdN_fold]
  case post => exact ⟨by reg_val, by reg_val, by reg_val, by reg_val, by reg_val⟩

end Services.Bootstrap.Alloc
