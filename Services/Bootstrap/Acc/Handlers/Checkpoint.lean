import Services.Bootstrap.Acc.Handlers.Dispatch
import Services.Bootstrap.Acc.ContractC

/-!
# The `Checkpoint` handler (tag 15)

`Checkpoint`'s results write (36170) happens before the dispatch (8650 → 8710), so from the dispatch
point the handler is short:
1. `checkpoint` (Ω_C, id 18) at 9944: y := x (`accContractC` fixes ω₇ to 0; ω₇ is dead here,
   `Acc.CkDead`).
2. `alloc(13, 1)` (40494) for a 13-octet log message, trapping at 15366 if it fails.
3. The message is written and logged (`log`, 100, at 10009), and freed (`dealloc`, 40613).
4. The result is `Ok(Unit)` (the octet 0 at `RES`), and the instruction value at sp + 1144 is
   dropped (4046), returning to 14278.

This file proves step 1 and the steps up to the `alloc` call: `toAlloc`.
-/

namespace Services.Bootstrap.Acc.Handlers.Checkpoint

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Acc
  Services.Bootstrap.Acc.Handlers

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

macro "post_simp" : tactic => `(tactic| (
  all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
    ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, PVM.Memory.readN_writeN_same,
    PVM.Memory.readN_writeN_disjoint, PVM.Memory.read_writeN_disjoint, PVM.Memory.readable_writeN,
    PVM.Memory.writable_writeN, PVM.Num.length_encodeLE, List.length_cons, List.length_nil, PVM.two32,
    JAM.setR7, Vector.getElem_set]))

/-- **From the dispatch to `alloc(13, 1)`**: for `Checkpoint` (the discriminant 2⁶³ + 14), the
    dispatch reaches 9944. `checkpoint` (Ω_C, id 18) sets y := x there. Then the call to `alloc`
    (40494) is made with size ω₇ = 13, alignment ω₈ = 1 and return address ω₀ = 350 (the jump
    table's entry for 9958). Memory changes only at sp + 1380 (4 octets), and ω₁ = sp. -/
theorem toAlloc {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : AccEnv) (x : AccCtx) (ω : Regs)
    (μ : Memory) (bs : List UInt8) (hD : AtDispatch ω μ bs)
    (hdisc : bs.take 8 = Num.encodeLE 8 9223372036854775822) :
    ∃ ω' μ', FreeStepsH p (accContractC env) 8822 ω μ x 40494 ω' μ' (x.1, x.1) 30 ∧
      ω'[0] = UInt64.ofNat 350 ∧ ω'[1] = ω[1] ∧ ω'[7] = UInt64.ofNat 13 ∧ ω'[8] = UInt64.ofNat 1 ∧
      KeepsExcept μ μ' [(4278058532, 4)] ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have h1 := hD.sp
  have h6 := hD.r6
  have c216 := hD.c216
  have hw := hD.frame
  have hrt := hD.tabR
  have hr : ∀ a, 4278057152 ≤ a → a < 4278059008 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have disc := slot_word0 hD.slotB hdisc
  have tab : μ.readN 65796 4 = [148, 0, 255, 255] := tab_entry hD.tab 15 (by decide)
  clear hD hdisc
  obtain ⟨v192, hv192, m192⟩ := word_exists μ 4278057344
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run =>
    refine FreeStepsH.mono (FreeStepsH.trans (i' := 9944) (ω' := ?w1) (μ' := ?m1) (x' := x) (n₁ := 15) (n₂ := 15) ?a
      (FreeStepsH.checkpointAcc env (d_9944 (p := p) (P := P)) ?b)) (by omega)
    case a => pvm_go [m192, hv192, jtsA, h1, h6, c216, disc, tab, hw, hr, hrt]
    case b => pvm_go [JAM.setR7, bs_40494]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, fun a ha hrs => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hrs
    post_simp

end Services.Bootstrap.Acc.Handlers.Checkpoint
