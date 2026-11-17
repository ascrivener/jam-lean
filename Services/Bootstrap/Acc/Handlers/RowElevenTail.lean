import Services.Bootstrap.Acc.Handlers.ResultsDropSeg

/-!
# Row 11: the drops after the results write (15028 / 15050, 15133 … 15212)

`onWorkItem`'s end (GP v0.8.0 Appendix B, Ω_W) frees what the work item's frame owns, in the
binary's order:
- `r11_di0` / `r11_di1` (15028 / 15050 → 33214): the drop of the instructions' `IntoIter` at sp + 472,
  return address 558 (→ 15038, the flag) or 560 (→ 15060, the store);
- `r11_dr` (15133 → 28864): the drop of the results' items, ω₇ = sp + 448, return address 564 (→ 15143);
- `r11_b0` / `r11_b1` (15143): the results buffer (cap at sp + 448, ptr at sp + 456): cap = 0 → 15172,
  else `dealloc` with return address 566 (→ 15172);
- `r11_c0` / `r11_c1` (15172): the buffer at sp + 104 (cap at sp + 128): cap = 0 → 15191, else `dealloc`
  with return address 568 (→ 15191);
- `r11_e0` / `r11_e1` (15191): the buffer at sp + 272 (cap at sp + 264): cap = 0 → 6766, else `dealloc`
  with return address 228 (→ 6766).
-/

namespace Services.Bootstrap.Acc.Handlers.RowEleven

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.Acc.Handlers.ResultsDrop

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **15028 … 15032**: ω₇ := sp + 472, the call of 33214 with return address 558. -/
theorem r11_di0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : sp + 472 < 2 ^ 64) :
    ∃ ω', FreeStepsH p R 15028 ω μ x 33214 ω' μ x 2 ∧ ω'[0] = UInt64.ofNat 558 ∧ ω'[1] = ω[1] ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat (sp + 472) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1]
  · refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, ?_⟩
    simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1, Nat.mod_eq_of_lt hsp]

/-- **15050 … 15054**: ω₇ := sp + 472, the call of 33214 with return address 560. -/
theorem r11_di1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : sp + 472 < 2 ^ 64) :
    ∃ ω', FreeStepsH p R 15050 ω μ x 33214 ω' μ x 2 ∧ ω'[0] = UInt64.ofNat 560 ∧ ω'[1] = ω[1] ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat (sp + 472) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1]
  · refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, ?_⟩
    simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1, Nat.mod_eq_of_lt hsp]

/-- **15133 … 15137**: ω₇ := sp + 448, the call of the results drop 28864 with return address 564. -/
theorem r11_dr {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : sp + 448 < 2 ^ 64) :
    ∃ ω', FreeStepsH p R 15133 ω μ x 28864 ω' μ x 2 ∧ ω'[0] = UInt64.ofNat 564 ∧ ω'[1] = ω[1] ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat (sp + 448) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1]
  · refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, ?_⟩
    simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1, Nat.mod_eq_of_lt hsp]

/-- **15143 … 15147, the results buffer's cap 0** (at sp + 448): on to 15172. -/
theorem r11_b0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : sp + 464 < 4294967296) (mc : rdN μ (sp + 448) 8 = 0)
    (hr : ∀ a, sp + 448 ≤ a → a < sp + 456 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 15143 ω μ x 15172 ω' μ x 2 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hsp, mc, hr, ↓rdN_fold]
  · exact ⟨by reg_val, by reg_val, by reg_val⟩

/-- **15143 … 15166, the results buffer's cap c ≠ 0**: the call of `dealloc` with ω₇ = the buffer (at
    sp + 456), ω₈ = 144·c, ω₉ = 8 and return address 566 (→ 15172). -/
theorem r11_b1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp c q : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : sp + 464 < 4294967296) (mc : rdN μ (sp + 448) 8 = c)
    (hc : c ≠ 0) (mq : rdN μ (sp + 456) 8 = q) (hr : ∀ a, sp + 448 ≤ a → a < sp + 464 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 15143 ω μ x 40613 ω' μ x 9 ∧ ω'[0] = UInt64.ofNat 566 ∧ ω'[1] = ω[1] ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat q := by
  have hc' : c < 2 ^ 64 := mc ▸ rdN_lt8 μ (sp + 448)
  have hq : q < 2 ^ 64 := mq ▸ rdN_lt8 μ (sp + 456)
  have hc0 : c % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt hc']; exact hc
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hsp, mc, hc0, mq, hr, ↓rdN_fold]
  · refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, ?_⟩
    simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.mod_eq_of_lt hq]

/-- **15172 … 15176, the buffer at sp + 104 with cap 0** (at sp + 128): on to 15191. -/
theorem r11_c0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : sp + 136 < 4294967296) (mc : rdN μ (sp + 128) 8 = 0)
    (hr : ∀ a, sp + 128 ≤ a → a < sp + 136 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 15172 ω μ x 15191 ω' μ x 2 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hsp, mc, hr, ↓rdN_fold]
  · exact ⟨by reg_val, by reg_val, by reg_val⟩

/-- **15172 … 15185, the buffer at sp + 104 with cap c ≠ 0**: the call of `dealloc` with ω₇ = the
    buffer, ω₉ = 1 and return address 568 (→ 15191). -/
theorem r11_c1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp c q : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : sp + 136 < 4294967296) (mc : rdN μ (sp + 128) 8 = c)
    (hc : c ≠ 0) (mq : rdN μ (sp + 104) 8 = q) (hr : ∀ a, sp + 104 ≤ a → a < sp + 136 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 15172 ω μ x 40613 ω' μ x 5 ∧ ω'[0] = UInt64.ofNat 568 ∧ ω'[1] = ω[1] ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat q := by
  have hc' : c < 2 ^ 64 := mc ▸ rdN_lt8 μ (sp + 128)
  have hq : q < 2 ^ 64 := mq ▸ rdN_lt8 μ (sp + 104)
  have hc0 : c % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt hc']; exact hc
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hsp, mc, hc0, mq, hr, ↓rdN_fold]
  · refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, ?_⟩
    simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.mod_eq_of_lt hq]

/-- **15191 … 15198, the buffer at sp + 272 with cap 0** (at sp + 264): on to 6766. -/
theorem r11_e0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : sp + 280 < 4294967296) (mc : rdN μ (sp + 264) 8 = 0)
    (hr : ∀ a, sp + 264 ≤ a → a < sp + 272 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 15191 ω μ x 6766 ω' μ x 3 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hsp, mc, hr, ↓rdN_fold]
  · exact ⟨by reg_val, by reg_val, by reg_val⟩

/-- **15191 … 15212, the buffer at sp + 272 with cap c ≠ 0**: the call of `dealloc` with ω₇ = the
    buffer, ω₉ = 1 and return address 228 (→ 6766). -/
theorem r11_e1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp c q : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : sp + 280 < 4294967296) (mc : rdN μ (sp + 264) 8 = c)
    (hc : c ≠ 0) (mq : rdN μ (sp + 272) 8 = q) (hr : ∀ a, sp + 264 ≤ a → a < sp + 280 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 15191 ω μ x 40613 ω' μ x 6 ∧ ω'[0] = UInt64.ofNat 228 ∧ ω'[1] = ω[1] ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat q := by
  have hc' : c < 2 ^ 64 := mc ▸ rdN_lt8 μ (sp + 264)
  have hq : q < 2 ^ 64 := mq ▸ rdN_lt8 μ (sp + 272)
  have hc0 : c % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt hc']; exact hc
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hsp, mc, hc0, mq, hr, ↓rdN_fold]
  · refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, ?_⟩
    simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.mod_eq_of_lt hq]

end Services.Bootstrap.Acc.Handlers.RowEleven
