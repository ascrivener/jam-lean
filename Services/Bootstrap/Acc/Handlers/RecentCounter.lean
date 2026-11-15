import Services.Bootstrap.Acc.Handlers.KeyEnc
import Services.Bootstrap.Acc.Wrappers.SetCall

/-!
# `add_recent_work_item`'s counter write (8326 … 8416)

The last step of `add_recent_work_item` (row 8, spec `addRecent`'s `store .counter (fixed 4 c′)`,
GP v0.8.0 Appendix B's Ω_W): with the new counter c′ in ω₇,
1. 8326 … 8342: the key value `RecentWorkItemCounter` (the tag 0) at sp + 1568 and c′ as a `u32` at
   sp + 1000; the key encoder (33843, `kb_call`) builds the key `[0]` in a fresh `Vec` at sp + 1144
   (return address 288 → 8348);
2. 8348 … 8369: `set` (48104, `set_call`) of the key with the four octets at sp + 1000, out at
   sp + 744 (return address 290 → 8376);
3. 8376 … 8402: the key's buffer is freed (`dealloc`, 40613; return address 292 → 8402);
4. 8407 … 8416: `set`'s result must not be `Err` (the word −1 at sp + 744), else the trap at 15361.

This file proves the straight-line segments (`cw_pre`, `cw_mid`, `cw_ret`, `cw_dl`, `cw_ok`,
`cw_err`).
-/

namespace Services.Bootstrap.Acc.Handlers.RecentCounter

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **8326 … 8342**: the tag 0 (a `u16`) at sp + 1568, ω₇'s low four octets at sp + 1000, and the call
    of the key encoder (33843) with out ω₇ = sp + 1144, the key value ω₈ = sp + 1568 and return
    address 288. -/
theorem cw_pre {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp w : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat w)
    (hw64 : w < 18446744073709551616) (hsp : sp + 1576 < 4294967296)
    (hw : ∀ a, (sp + 1568 ≤ a ∧ a < sp + 1570) ∨ (sp + 1000 ≤ a ∧ a < sp + 1004) → μ.writable a = true) :
    ∃ ω', FreeStepsH p R 8326 ω μ x 33843 ω'
      ((μ.writeN (sp + 1568) (Num.encodeLE 2 0)).writeN (sp + 1000) (Num.encodeLE 4 w)) x 5 ∧
      ω'[0] = UInt64.ofNat 288 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[7] = UInt64.ofNat (sp + 1144) ∧
      ω'[8] = UInt64.ofNat (sp + 1568) := by
  have hw1 : ∀ a, sp + 1568 ≤ a → a < sp + 1570 → μ.writable a = true := fun a h1 h2 => hw a (.inl ⟨h1, h2⟩)
  have hw2 : ∀ a, sp + 1000 ≤ a → a < sp + 1004 → μ.writable a = true := fun a h1 h2 => hw a (.inr ⟨h1, h2⟩)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h7, hsp, hw1, hw2]
  · refine ⟨?_, ?_, ?_, ?_⟩
    all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1]

/-- **8348 … 8369**: the key's `Vec` `{cap, ptr, len}` at sp + 1144; the call of `set` (48104) with out
    ω₇ = sp + 744, the key ω₈ = ptr (ω₉ = len octets), the value ω₁₀ = sp + 1000 (ω₁₁ = 4 octets), ptr
    kept in ω₅ and return address 290. Memory is kept. -/
theorem cw_mid {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp ptr len : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : sp + 1576 < 4294967296)
    (hptr : ptr < 18446744073709551616) (hlen : len < 18446744073709551616)
    (mp : μ.readN (sp + 1152) 8 = Num.encodeLE 8 ptr) (ml : μ.readN (sp + 1160) 8 = Num.encodeLE 8 len)
    (hr : ∀ a, sp + 1152 ≤ a → a < sp + 1168 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 8348 ω μ x 48104 ω' μ x 7 ∧
      ω'[0] = UInt64.ofNat 290 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat ptr ∧
      ω'[7] = UInt64.ofNat (sp + 744) ∧ ω'[8] = UInt64.ofNat ptr ∧ ω'[9] = UInt64.ofNat len ∧
      ω'[10] = UInt64.ofNat (sp + 1000) ∧ ω'[11] = UInt64.ofNat 4 := by
  have rp := Handlers.DesignateAlloc.rd8 hptr mp
  have rl := Handlers.DesignateAlloc.rd8 hlen ml
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hsp, rp, rl, hr]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1]

/-- **`set`'s returns** (the `jumpInd` at 48158, 48250 or 48235) with ω₀ = 290: on to 8376. -/
theorem cw_ret {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (e : Nat) (he : e = 48158 ∨ e = 48250 ∨ e = 48235) (h0 : ω[0] = UInt64.ofNat 290) :
    FreeStepsH p R e ω μ x 8376 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  rcases he with rfl | rfl | rfl <;> pvm_go [h0]

/-- **8376 … 8396**, the key's capacity cap ≠ 0 (the word at sp + 1144): `set`'s result word r (at
    sp + 744) saved at sp + 232, and the call of `dealloc` (40613) with ω₇ = ω₅ and return address
    292. -/
theorem cw_dl {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp cap r : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : sp + 1576 < 4294967296)
    (hcap : cap < 18446744073709551616) (hc0 : cap ≠ 0) (hr64 : r < 18446744073709551616)
    (mc : μ.readN (sp + 1144) 8 = Num.encodeLE 8 cap) (mr : μ.readN (sp + 744) 8 = Num.encodeLE 8 r)
    (hrc : ∀ a, sp + 1144 ≤ a → a < sp + 1152 → μ.readable a = true)
    (hrr : ∀ a, sp + 744 ≤ a → a < sp + 752 → μ.readable a = true)
    (hw : ∀ a, sp + 232 ≤ a → a < sp + 240 → μ.writable a = true) :
    ∃ ω', FreeStepsH p R 8376 ω μ x 40613 ω' (μ.writeN (sp + 232) (Num.encodeLE 8 r)) x 7 ∧
      ω'[0] = UInt64.ofNat 292 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[7] = ω[5] := by
  have rc := Handlers.DesignateAlloc.rd8 hcap mc
  have rr := Handlers.DesignateAlloc.rd8 hr64 mr
  have hc0' : cap % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt hcap]; exact hc0
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hsp, rc, rr, hc0', hrc, hrr, hw]
  · refine ⟨?_, ?_, ?_, ?_⟩
    all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1]

/-- **8402 … 8416**, `set`'s result word r (saved at sp + 232) not −1 (`Ok`): on to 8416. -/
theorem cw_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp r : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : sp + 1576 < 4294967296)
    (hr64 : r < 18446744073709551616) (hne : r ≠ 18446744073709551615)
    (mr : μ.readN (sp + 232) 8 = Num.encodeLE 8 r)
    (hrr : ∀ a, sp + 232 ≤ a → a < sp + 240 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 8402 ω μ x 8416 ω' μ x 4 ∧ ω'[1] = UInt64.ofNat sp := by
  have rr := Handlers.DesignateAlloc.rd8 hr64 mr
  have hne' : r % 18446744073709551616 ≠ 18446744073709551615 := by rw [Nat.mod_eq_of_lt hr64]; exact hne
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hsp, rr, hne', hrr]
  · simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1]

/-- **8402 … 8412**, `set`'s result word −1 (`Err`, saved at sp + 232): on to the trap at 15361. -/
theorem cw_err {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : sp + 1576 < 4294967296)
    (mr : μ.readN (sp + 232) 8 = Num.encodeLE 8 18446744073709551615)
    (hrr : ∀ a, sp + 232 ≤ a → a < sp + 240 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 8402 ω μ x 15361 ω' μ x 4 := by
  have rr := Handlers.DesignateAlloc.rd8 (by decide) mr
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_⟩
  pvm_go [h1, hsp, rr, hrr]

end Services.Bootstrap.Acc.Handlers.RecentCounter
