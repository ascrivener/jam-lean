import Services.Bootstrap.Acc.Inputs.FetchStep
import Services.Bootstrap.ASem
import PVM.Theorems.InitMem

/-!
# `Spec.accumulate`'s first operation under `ASem`

`step_fetchItems`: `AOp.fetchItems` (two `fetch` calls of kind 14, GP v0.8.0 Appendix B, as the SDK
makes them: the length, then the data) replies ℰ(↕**i**) (`inputsEnc env`) and keeps the context, when
the encoding fits the reply space (at most 2³¹ octets from `outBase` = 2³¹).
-/

namespace Services.Bootstrap.ASem

open PVM JAM Services.Bootstrap.Spec Services.Bootstrap.Acc

/-- One `fetch` of kind 14 into the reply space, z octets asked: ω₇ := |ℰ(↕**i**)| and the first
    min(z, |ℰ(↕**i**)|) octets written at `outBase`; the context kept. -/
theorem call_fetch14 (env : AccEnv) (c : AccCtx) (z : Nat) (hz : z ≤ 2 ^ 31)
    (hL : (inputsEnc env).length ≤ 2 ^ 31) :
    call env 2 [] [outBase, 0, z, 14, 0, 0] c =
      some ⟨.cont, (opGas : Int) - (287 + memGas 400 z), setR7 (argRegs [outBase, 0, z, 14, 0, 0]) (inputsEnc env).length,
        (argMem []).writeN outBase ((inputsEnc env).take (min z (inputsEnc env).length)), c⟩ := by
  have r7 : reg (argRegs [outBase, 0, z, 14, 0, 0]) 7 = outBase := by
    simp [reg, argRegs, Regs.get, outBase]
  have r8 : reg (argRegs [outBase, 0, z, 14, 0, 0]) 8 = 0 := by simp [reg, argRegs, Regs.get]
  have r9 : reg (argRegs [outBase, 0, z, 14, 0, 0]) 9 = z := by
    simp [reg, argRegs, Regs.get]; omega
  have r10 : reg (argRegs [outBase, 0, z, 14, 0, 0]) 10 = 14 := by simp [reg, argRegs, Regs.get]
  have hw : (argMem []).rangeWritable outBase (min z (inputsEnc env).length) = true := by
    apply rangeWritable_of (by unfold outBase; omega)
    intro a h1 h2
    simp only [argMem, List.flatten_nil, Memory.writable_writeN, Memory.writable_setPages]
    have hps : pageSize = 4096 := rfl
    unfold outBase at h1 h2
    simp only [hps, show 16 ≤ a / 4096 ∧ a / 4096 < 16 + (2 ^ 20 - 16) from by omega]
    rfl
  unfold call
  simp only [AccHost.dispatch, hostFetch, charged, r9, r10]
  simp only [show (14 < 16) = True from by decide, ite_true, Constants.CgasY]
  have hg : ¬ opGas < 287 + memGas 400 z := by unfold opGas memGas; omega
  have r11 : reg (argRegs [outBase, 0, z, 14, 0, 0]) 11 = 0 := by simp [reg, argRegs, Regs.get]
  have r12 : reg (argRegs [outBase, 0, z, 14, 0, 0]) 12 = 0 := by simp [reg, argRegs, Regs.get]
  simp only [hg, ite_false, r11, r12, r7, r8]
  simp only [writeValue, fetchValue, Option.map_some]
  simp only [inputsEnc] at hw ⊢
  simp [hw]

/-- **`fetchItems` replies ℰ(↕**i**)** and keeps the context, for an encoding of at most 2³¹ octets. -/
theorem step_fetchItems (env : AccEnv) (c : AccCtx) (hL : (inputsEnc env).length ≤ 2 ^ 31) :
    step env AOp.fetchItems c = some (some (inputsEnc env), c) := by
  have h1 := call_fetch14 env c 0 (by omega) hL
  have h2 := call_fetch14 env c (inputsEnc env).length hL hL
  simp only [step, h1, Option.bind_eq_bind, Option.bind_some]
  have e7 : ∀ z, reg (setR7 (argRegs [outBase, 0, z, 14, 0, 0]) (inputsEnc env).length) 7 =
      (inputsEnc env).length := fun z => by
    simp [reg, setR7, Regs.get]; omega
  have hN : (inputsEnc env).length ≠ Result.NONE := by unfold Result.NONE; omega
  simp only [r7, e7, hN, ite_false, h2, Option.bind_some, outValue]
  rw [Nat.min_self, List.take_length,
    Memory.readN_writeN_same _ _ _ _ rfl (by simp only [two32]; omega)]
  rfl

end Services.Bootstrap.ASem
