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

namespace Services.Bootstrap.Acc.Handlers.RecentMatch

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.Alloc Services.Bootstrap.Acc Services.Bootstrap.Spec
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Acc.Handlers.KeyEnc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **8056 … 8073**: the tag-1 key value {1, c} at sp + 1568 (the u16 1, then c as a u32 at sp + 1572),
    and the call of the ring slot's typed get (34377) with out ω₇ = sp + 1144, the key value
    ω₈ = sp + 1568 and return address 280. -/
theorem rm_pre {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp c : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat c)
    (hc : c < 18446744073709551616) (hsp : sp + 1576 < 4294967296)
    (hw : ∀ a, sp + 1568 ≤ a → a < sp + 1576 → μ.writable a = true) :
    ∃ ω', FreeStepsH p R 8056 ω μ x 34377 ω'
      ((μ.writeN (sp + 1568) (Num.encodeLE 2 1)).writeN (sp + 1572) (Num.encodeLE 4 c)) x 5 ∧
      ω'[0] = UInt64.ofNat 280 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (sp + 1144) ∧ ω'[8] = UInt64.ofNat (sp + 1568) := by
  rw [show ω = regsNF ω [] from rfl, show Num.encodeLE 2 1 = [UInt8.ofNat 1, UInt8.ofNat 0] from rfl,
    ← encodeLE_mod 4 c, show (256 : Nat) ^ 4 = 4294967296 from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, hsp, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1]

/-- **8079 … 8083, an empty slot**: the u16 0 at sp + 1144 sends the run to 8172 (ω₇ := 0). -/
theorem rm_none {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : sp + 1576 < 4294967296)
    (m : μ.readN (sp + 1144) 2 = Num.encodeLE 2 0)
    (hr : ∀ a, sp + 1144 ≤ a → a < sp + 1146 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 8079 ω μ x 8172 ω' μ x 2 ∧
      ω'[0] = ω[0] ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have r0 : rdN μ (sp + 1144) 2 = 0 := by
    show Num.decodeLE _ = _; rw [m]; rfl
  have b0 : ((μ.read (sp + 1144)).toNat + 256 * (μ.read (sp + 1144 + 1)).toNat) % 18446744073709551616 = 0 := by
    have := r0; unfold rdN at this
    simp [Memory.readN, List.range_succ, Num.decodeLE] at this
    omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hsp, hr, b0]
  · refine ⟨?_, ?_, ?_, ?_⟩
    all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1]

/-- **8079 … 8158, an occupied slot** (the u16 1 at sp + 1144): the slot's 32 octets (the words q₀ … q₃
    at sp + 1146 …) copied to sp + 1572, the zero u32 at sp + 775, the tag u16 2 at sp + 1568, the
    slot's u16 v (at sp + 1178) at sp + 1570, sp + 744 … 776 zeroed; then the call of the fixed-buffer
    key encoder (51243) with the key value ω₇ = sp + 1568, the buffer ω₈ = sp + 744 and return
    address 282. -/
theorem rm_some {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp q0 q1 q2 q3 v : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : sp + 1604 < 4294967296)
    (mt : μ.readN (sp + 1144) 2 = Num.encodeLE 2 1)
    (m0 : μ.readN (sp + 1146) 8 = Num.encodeLE 8 q0) (m1 : μ.readN (sp + 1154) 8 = Num.encodeLE 8 q1)
    (m2 : μ.readN (sp + 1162) 8 = Num.encodeLE 8 q2) (m3 : μ.readN (sp + 1170) 8 = Num.encodeLE 8 q3)
    (hq0 : q0 < 2 ^ 64) (hq1 : q1 < 2 ^ 64) (hq2 : q2 < 2 ^ 64) (hq3 : q3 < 2 ^ 64)
    (mv : μ.readN (sp + 1178) 2 = Num.encodeLE 2 v) (hv : v < 65536)
    (hr : ∀ a, sp + 1144 ≤ a → a < sp + 1180 → μ.readable a = true)
    (hw1 : ∀ a, sp + 744 ≤ a → a < sp + 780 → μ.writable a = true)
    (hw2 : ∀ a, sp + 1568 ≤ a → a < sp + 1604 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 8079 ω μ x 51243 ω' μ' x 24 ∧
      μ' = ((((((((((μ.writeN (sp + 1572) (Num.encodeLE 8 q0)).writeN (sp + 1580) (Num.encodeLE 8 q1)).writeN
        (sp + 1588) (Num.encodeLE 8 q2)).writeN (sp + 1596) (Num.encodeLE 8 q3)).writeN (sp + 775)
        (Num.encodeLE 4 0)).writeN (sp + 1568) (Num.encodeLE 2 2)).writeN (sp + 1570) (Num.encodeLE 2 v)).writeN
        (sp + 744) (Num.encodeLE 8 0)).writeN (sp + 752) (Num.encodeLE 8 0)).writeN (sp + 760)
        (Num.encodeLE 8 0)).writeN (sp + 768) (Num.encodeLE 8 0) ∧
      ω'[0] = UInt64.ofNat 282 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (sp + 1568) ∧ ω'[8] = UInt64.ofNat (sp + 744) := by
  have rt : rdN μ (sp + 1144) 2 = 1 := by show Num.decodeLE _ = _; rw [mt]; rfl
  have rv : rdN μ (sp + 1178) 2 = v := by
    show Num.decodeLE _ = _; rw [mv, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hv]
  have r0 := Handlers.DesignateAlloc.rd8 hq0 m0
  have r1 := Handlers.DesignateAlloc.rd8 hq1 m1
  have r2 := Handlers.DesignateAlloc.rd8 hq2 m2
  have r3 := Handlers.DesignateAlloc.rd8 hq3 m3
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hsp, rt, rv, r0, r1, r2, r3, hr, hw1, hw2, bs_51243, ↓rdN_fold]
  · have hsx : ((if v < 32768 then (v : Int) else (v : Int) - 65536) % 18446744073709551616).toNat % 65536 = v := by
      split <;> omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [hsx, show sp + 1572 + 8 = sp + 1580 by omega, show sp + 1572 + 16 = sp + 1588 by omega,
        show sp + 1572 + 24 = sp + 1596 by omega]
      rfl
    all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1]

/-- The trap at 47977 (`get`'s allocation failure): ☇ (GP §A.5.1). -/
theorem trap_47977 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (ω : Regs) (μ : Memory) :
    FreeExit p 47977 ω μ .panic ω μ := by
  have hd := d_47977 (p := p) (P := P)
  have hs : P.freeStep 47977 ω μ = (.panic, P.next 47977, ω, μ) := by
    simp [Program.freeStep, hd.2.1, Program.exec, Program.finalState, memoryException]
  have := FreeExit.step (p := p) hd.1 hs (by decide)
  simpa using this

/-- The trap at 48533 (`remove`'s FULL, quirk Q18): ☇ (GP §A.5.1). -/
theorem trap_48533 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (ω : Regs) (μ : Memory) :
    FreeExit p 48533 ω μ .panic ω μ := by
  have hd := d_48533 (p := p) (P := P)
  have hs : P.freeStep 48533 ω μ = (.panic, P.next 48533, ω, μ) := by
    simp [Program.freeStep, hd.2.1, Program.exec, Program.finalState, memoryException]
  have := FreeExit.step (p := p) hd.1 hs (by decide)
  simpa using this

/-- **8165**: the call of `remove` (48481) with return address 284; the other registers kept. -/
theorem rm_j {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory) :
    ∃ ω', FreeStepsH p R 8165 ω μ x 48481 ω' μ x 1 ∧ ω'[0] = UInt64.ofNat 284 ∧
      ∀ j : Nat, (hj : j < 13) → j ≠ 0 → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go []
  · refine ⟨by simp [PVM.getElem_regsNF, PVM.lookup_cons_nat], fun j hj h0 => ?_⟩
    simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h0]

/-- **`remove`'s returns** (the `jumpInd` at 48514 or 48531) with ω₀ = 284: on to 8172. -/
theorem rm_back {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (e : Nat) (he : e = 48514 ∨ e = 48531) (h0 : ω[0] = UInt64.ofNat 284) :
    FreeStepsH p R e ω μ x 8172 ω μ x 1 := by
  rcases he with rfl | rfl
  all_goals
    rw [show ω = regsNF ω [] from rfl]
    pvm_go [h0]

end Services.Bootstrap.Acc.Handlers.RecentMatch
