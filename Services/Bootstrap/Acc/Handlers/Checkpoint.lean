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
    case a => pvm_go [m192, hv192, jts, h1, h6, c216, disc, tab, hw, hr, hrt]
    case b => pvm_go [JAM.setR7, bs_40494]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, fun a ha hrs => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hrs
    post_simp

/-- **Between `alloc` and `dealloc`**, from `alloc`'s return (9958) with a block at ω₇ = ptr ≠ 0:
    the 13-octet message is written at ptr and logged (`log`, 100, an id Ψ_A's dispatcher does not
    know, so ω₇ := WHAT and nothing else changes), then `dealloc(ptr, 13, 1)` (40613) is called
    with return address ω₀ = 432 (the jump table's entry for 11866). Memory changes only at
    ptr … ptr + 13; ω₁ is kept. -/
theorem mid {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : AccEnv) (x : AccCtx)
    (ω : Regs) (μ : Memory) (ptr : Nat) (h7 : ω[7] = UInt64.ofNat ptr) (hp0 : ptr ≠ 0)
    (hp : ptr + 13 ≤ 4294967296)
    (hw : ∀ a, ptr ≤ a → a < ptr + 13 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (accContractC env) 9958 ω μ x 40613 ω' μ' x 25 ∧
      ω'[0] = UInt64.ofNat 432 ∧ ω'[1] = ω[1] ∧ ω'[7] = UInt64.ofNat ptr ∧ ω'[8] = UInt64.ofNat 13 ∧
      ω'[9] = UInt64.ofNat 1 ∧ KeepsExcept μ μ' [(ptr, 13)] ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, ptr ≤ a → a < ptr + 13 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hp64 : ptr < 18446744073709551616 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run =>
    refine FreeStepsH.mono (FreeStepsH.trans (i' := 10009) (ω' := ?w1) (μ' := ?m1) (x' := x)
      (n₁ := 12) (n₂ := 12) ?a (FreeStepsH.logAcc env (d_10009 (p := p) (P := P)) ?b)) (by omega)
    case a => pvm_go [h7, hp0, hp64, hw, hr]
    case b => pvm_go [JAM.setR7, bs_40613, bs_11855]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, fun a ha hrs => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hrs
    post_simp

/-- `drop_in_place::<Instruction>`'s jump table at 65536 (in the read-only data), the first 24
    entries. -/
def dropTab : List UInt8 :=
  [144, 0, 255, 255, 122, 0, 255, 255, 122, 0, 255, 255, 122, 0, 255, 255, 122, 0, 255, 255,
   128, 0, 255, 255, 122, 0, 255, 255, 122, 0, 255, 255, 122, 0, 255, 255, 124, 0, 255, 255,
   136, 0, 255, 255, 124, 0, 255, 255, 126, 0, 255, 255, 146, 0, 255, 255, 122, 0, 255, 255,
   122, 0, 255, 255, 122, 0, 255, 255, 132, 0, 255, 255, 134, 0, 255, 255, 140, 0, 255, 255,
   122, 0, 255, 255, 122, 0, 255, 255, 148, 0, 255, 255, 122, 0, 255, 255]

/-- **The end of the handler**, from 11866: the result `Ok(Unit)` (the octet 0 at `RES`), then
    `drop_in_place::<Instruction>` (4046) of the value at sp + 1144, which holds nothing for
    `Checkpoint` (the discriminant 2⁶³ + 14), returning to 14278. Memory changes only at `RES`
    and in the 40 octets below sp; ω₁, ω₅, ω₆ are kept. -/
theorem tail {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] {X : Type} {R : HostRel X}
    (x : X) (ω : Regs) (μ : Memory)
    (h1 : ω[1] = UInt64.ofNat 4278057152)
    (disc : μ.readN 4278058296 8 = Num.encodeLE 8 9223372036854775822)
    (tab : μ.readN 65536 96 = dropTab)
    (hrt : ∀ a, 65536 ≤ a → a < 65632 → μ.readable a = true)
    (hw : ∀ a, 4278057112 ≤ a → a < 4278059008 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 11866 ω μ x 14278 ω' μ' x 40 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧
      ω'[6] = ω[6] ∧ μ'.read RES = 0 ∧
      KeepsExcept μ μ' [(RES, 1), (4278057112, 40)] ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, 4278057112 ≤ a → a < 4278059008 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have tab15 : μ.readN (65536 + 4 * 15) 4 = [122, 0, 255, 255] :=
    Decode.Loop.readN_sub μ 65536 96 (4 * 15) 4 dropTab tab (by omega)
  simp only [Nat.reduceMul, Nat.reduceAdd] at tab15
  clear tab
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [jts, jts, h1, disc, tab15, hw, hr, hrt]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, fun a ha hrs => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp
    · exact h1.symm
    · simp only [RES]
      post_simp
      simp (disch := omega) only [PVM.Memory.writeN_cons, PVM.Memory.writeN_nil, PVM.read_write_eq']
      rfl
    · simp only [RES, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hrs
      post_simp

end Services.Bootstrap.Acc.Handlers.Checkpoint
