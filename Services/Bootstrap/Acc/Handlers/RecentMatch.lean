import Services.Bootstrap.Acc.Handlers.RecentSlotGet
import Services.Bootstrap.Acc.Handlers.RecentCounterImpl
import Services.Bootstrap.Acc.Handlers.KeyBuf
import Services.Bootstrap.Acc.Handlers.RemoveCall

/-!
# `add_recent_work_item`'s slot read and removal as an `Impl` step (8056 → 8172)

`addRecent`'s `match ← load (.recent c) … with | some (p, i) => remove (results p i) | none => ()`
(GP v0.8.0 Appendix B: Ω_R, then Ω_W with an empty value):
- 8056 … 8073: the tag-1 key value {1, c} at sp + 1568, then the ring slot's typed get (34377,
  `slot_get`) into sp + 1144;
- 8079: an empty slot goes to 8172;
- 8086 … 8158: the tag-2 key value (p, i) at sp + 1568, a zeroed buffer at sp + 744, the fixed-buffer
  key encoder (51243, `kf_call`), then 8165 jumps to the SDK's `remove` (48481, `remove_call`),
  which returns to 8172 (or panics on FULL: quirk Q18).
-/

namespace Services.Bootstrap.ASem
open PVM JAM Services.Bootstrap.Spec Services.Bootstrap.Acc

/-- **`remove` evaluated** (GP v0.8.0 B.7, Ω_W with an empty value): ☇ on FULL (quirk Q18), else the
    account written. -/
theorem step_remove (env : AccEnv) (key : Bytes) (c : AccCtx) (hk : argBase + key.length ≤ outBase)
    (hold : ∀ v, c.1.self.storage.get? key = some v → v.length < 2 ^ 63) :
    step env (.remove key) c = if writeR7 c.1.self key [] = Result.FULL then none
      else some ((), (c.1.setSelf (writeSelf c.1.self key []), c.2)) := by
  have r7s : ∀ (ω : Regs) (n : Nat), n < 2 ^ 64 → reg (setR7 ω n) 7 = n := fun ω n hn => by
    unfold reg setR7 Regs.get; simp; exact hn
  have hfit : argBase + [key].flatten.length ≤ outBase := by simpa using hk
  have hA0 : argAt [key] 0 = argBase := by simp [argAt]
  have hkey : (argMem [key]).readN (argAt [key] 0) key.length = key :=
    argMem_readN [key] 0 (by simp) hfit
  have hrd : (argMem [key]).rangeReadable (argAt [key] 0) key.length = true :=
    Services.Witness.rangeReadable_of (fun j a b => argMem_readable _ (by rw [hA0] at a; exact a)
      (by rw [hA0] at b; unfold outBase at hk; omega)) (by rw [hA0]; unfold argBase outBase at *; omega)
  have e := hostWrite_eval opGas (argRegs [argAt [key] 0, key.length, 0, 0])
    (argMem [key]) c.1.self (argAt [key] 0) key.length 0 0 key []
    ((reg_argRegs _ 7 (by decide) (by simp [hA0, argBase])).trans (by simp))
    ((reg_argRegs _ 8 (by decide) (by simp; unfold argBase outBase at hk; omega)).trans (by simp))
    ((reg_argRegs _ 9 (by decide) (by simp)).trans (by simp))
    ((reg_argRegs _ 10 (by decide) (by simp)).trans (by simp))
    (by unfold opGas memGas Constants.CgasWconst Constants.CgasWkeylinear Constants.CgasWvallinear argBase outBase at *
        omega)
    hrd hkey (by simp [Memory.rangeReadable]) (by simp [Memory.readN]) rfl
  simp only [step, call, AccHost.dispatch, AccHost.onSelf, e]
  unfold writeR7 writeSelf
  split
  · simp [r7, r7s _ _ (by decide : Result.FULL < 2 ^ 64)]
  · have hl : (c.1.self.storage.get? key |>.map List.length |>.getD Result.NONE) < 2 ^ 64 ∧
        (c.1.self.storage.get? key |>.map List.length |>.getD Result.NONE) ≠ Result.FULL := by
      cases hv : c.1.self.storage.get? key with
      | none => simp [Result.NONE, Result.FULL]
      | some v => have := hold v hv; simp [Result.FULL]; omega
    simp only [ite_true, Option.bind_eq_bind, Option.bind_some]
    rw [if_neg]
    show ¬ reg (setR7 _ _) 7 = _
    rw [r7s _ _ (by simpa using hl.1)]; simpa using hl.2
    rw [if_neg hl.2]; rfl

end Services.Bootstrap.ASem
