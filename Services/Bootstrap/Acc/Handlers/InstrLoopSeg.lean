import Services.Bootstrap.Acc.Handlers.RowElevenSeg

/-!
# R5, the instruction loop: straight-line segments (8493 … 8554)

Spec `onWorkItem`'s `for i in is do …` (GP v0.8.0 Appendix B, Ω_W; bootstrap's own loop): the
`IntoIter` of the decoded instructions (`Vec` { cap at sp + 240, len at sp + 248 }, ptr in ω₆) is set
up at sp + 472 { buf, cur, cap, end }, with the index counter at sp + 504:
- `il_setup0` (8493 → 15050): no instructions; on to row 11's second entry (skipping the flag);
- `il_setup1` (8493 → 8554): some instructions; the `Zombify` flag [sp + 160] := 0, then the first
  `next`.
-/

namespace Services.Bootstrap.Acc.Handlers.InstrLoop

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.Alloc Services.Bootstrap.Acc Services.Bootstrap.Spec

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **8493 … 8531, no instructions** (len = 0 at sp + 248): the `IntoIter` { b, b, c, b } at sp + 472,
    the counter 0 at sp + 504, and on to 15050. -/
theorem il_setup0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp b c : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h6 : ω[6] = UInt64.ofNat b)
    (hsp : 65536 ≤ sp ∧ sp + 1632 < 4294967296) (hb : b < 2 ^ 64) (hc : c < 2 ^ 64)
    (mc : μ.readN (sp + 240) 8 = Num.encodeLE 8 c) (ml : μ.readN (sp + 248) 8 = Num.encodeLE 8 0)
    (hr : ∀ a, sp + 240 ≤ a → a < sp + 256 → μ.readable a = true)
    (hw : ∀ a, sp + 472 ≤ a → a < sp + 512 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 8493 ω μ x 15050 ω' μ' x 11 ∧
      ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      μ'.readN (sp + 472) 8 = Num.encodeLE 8 b ∧ μ'.readN (sp + 480) 8 = Num.encodeLE 8 b ∧
      μ'.readN (sp + 488) 8 = Num.encodeLE 8 c ∧ μ'.readN (sp + 496) 8 = Num.encodeLE 8 b ∧
      μ'.readN (sp + 504) 8 = Num.encodeLE 8 0 ∧
      (∀ a, a < 4294967296 → (a < sp + 472 ∨ sp + 512 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rc := Handlers.DesignateAlloc.rd8 hc mc
  have rl := Handlers.DesignateAlloc.rd8 (by decide) ml
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, hsp, rc, rl, hr, hw, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨by reg_val, by reg_val, by reg_val, ?_, ?_, ?_, ?_, ?_, fun a ha h1' => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
      PVM.getD_some', List.lookup_nil, Option.getD_none]
    all_goals try rd_simp []
    all_goals try rfl
    all_goals try (congr 1; omega)
    all_goals try simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1, h6, Nat.mod_eq_of_lt hb]
    all_goals try (congr 1; omega)

/-- **8493 … 8538, some instructions** (len n ≠ 0 at sp + 248): the `IntoIter` { b, b, c, b + 232·n } at
    sp + 472, the counter 0 at sp + 504, the `Zombify` flag 0 at sp + 160, and on to 8554 (ω₆ = b). -/
theorem il_setup1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp b c n : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h6 : ω[6] = UInt64.ofNat b)
    (hsp : 65536 ≤ sp ∧ sp + 1632 < 4294967296) (hb : b + 232 * n < 2 ^ 64) (hc : c < 2 ^ 64) (hn0 : n ≠ 0)
    (mc : μ.readN (sp + 240) 8 = Num.encodeLE 8 c) (ml : μ.readN (sp + 248) 8 = Num.encodeLE 8 n)
    (hr : ∀ a, sp + 240 ≤ a → a < sp + 256 → μ.readable a = true)
    (hw : ∀ a, sp + 472 ≤ a → a < sp + 512 → μ.writable a = true)
    (hwf : ∀ a, sp + 160 ≤ a → a < sp + 168 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 8493 ω μ x 8554 ω' μ' x 12 ∧
      ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      μ'.readN (sp + 472) 8 = Num.encodeLE 8 b ∧ μ'.readN (sp + 480) 8 = Num.encodeLE 8 b ∧
      μ'.readN (sp + 488) 8 = Num.encodeLE 8 c ∧ μ'.readN (sp + 496) 8 = Num.encodeLE 8 (b + 232 * n) ∧
      μ'.readN (sp + 504) 8 = Num.encodeLE 8 0 ∧ μ'.readN (sp + 160) 8 = Num.encodeLE 8 0 ∧
      (∀ a, a < 4294967296 → (a < sp + 472 ∨ sp + 512 ≤ a) → (a < sp + 160 ∨ sp + 168 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rc := Handlers.DesignateAlloc.rd8 hc mc
  have rl := Handlers.DesignateAlloc.rd8 (by omega) ml
  have hn' : n ≠ 0 := hn0
  have e232 : (232 * n % 18446744073709551616 + b) % 18446744073709551616 = b + 232 * n := by
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, hsp, rc, rl, hr, hw, hwf, hn', rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨by reg_val, by reg_val, by reg_val, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1' h2' => ?_, fun a => ?_,
      fun a => ?_⟩
    all_goals try simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
      PVM.getD_some', List.lookup_nil, Option.getD_none]
    all_goals try rd_simp []
    all_goals try rfl
    all_goals try (congr 1; omega)
    all_goals try simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1, h6, Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega)]
    all_goals try (congr 1; omega)

/-- **8540 … 8551, the end**: cur = end ([sp + 480] = [sp + 496]); on to 15028. -/
theorem il_head_end {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp e : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : 65536 ≤ sp ∧ sp + 1632 < 4294967296) (he : e < 2 ^ 64)
    (mc : μ.readN (sp + 480) 8 = Num.encodeLE 8 e) (me : μ.readN (sp + 496) 8 = Num.encodeLE 8 e)
    (hr : ∀ a, sp + 480 ≤ a → a < sp + 504 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 8540 ω μ x 15028 ω' μ x 4 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] := by
  have rc := Handlers.DesignateAlloc.rd8 he mc
  have re := Handlers.DesignateAlloc.rd8 he me
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hsp, rc, re, hr, ↓rdN_fold]
  · exact ⟨by reg_val, by reg_val⟩

/-- **8540 … 8548, more**: cur ≠ end; on to 8554 with ω₆ = cur. -/
theorem il_head {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp c e : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : 65536 ≤ sp ∧ sp + 1632 < 4294967296) (hc : c < 2 ^ 64)
    (he : e < 2 ^ 64) (hce : c ≠ e)
    (mc : μ.readN (sp + 480) 8 = Num.encodeLE 8 c) (me : μ.readN (sp + 496) 8 = Num.encodeLE 8 e)
    (hr : ∀ a, sp + 480 ≤ a → a < sp + 504 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 8540 ω μ x 8554 ω' μ x 3 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = UInt64.ofNat c := by
  have rc := Handlers.DesignateAlloc.rd8 hc mc
  have re := Handlers.DesignateAlloc.rd8 he me
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hsp, rc, re, hr, hce, ↓rdN_fold]
  · refine ⟨by reg_val, by reg_val, ?_⟩
    simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.mod_eq_of_lt hc]

/-- **8554 … 8568, `None`**: cur := c + 232 at sp + 480; the slot's word0 at c is 2⁶⁴ − 2; on to 15028. -/
theorem il_next_none {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp c : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h6 : ω[6] = UInt64.ofNat c)
    (hsp : 65536 ≤ sp ∧ sp + 1632 < 4294967296) (hc : 65536 ≤ c ∧ c + 232 ≤ sp)
    (mw : μ.readN c 8 = Num.encodeLE 8 18446744073709551614)
    (hr : ∀ a, c ≤ a → a < c + 8 → μ.readable a = true)
    (hw : ∀ a, sp + 480 ≤ a → a < sp + 488 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 8554 ω μ x 15028 ω' μ' x 5 ∧ ω'[1] = ω[1] ∧
      μ'.readN (sp + 480) 8 = Num.encodeLE 8 (c + 232) ∧
      (∀ a, a < 4294967296 → (a < sp + 480 ∨ sp + 488 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rw0 := Handlers.DesignateAlloc.rd8 (by decide) mw
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, hsp, hc, hc.2, rw0, hr, hw, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨by reg_val, ?_, fun a ha h1' => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
      PVM.getD_some', List.lookup_nil, Option.getD_none]
    all_goals try rd_simp []
    all_goals try rfl
    all_goals try (congr 1; omega)
    all_goals try simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1, h6]
    all_goals try (congr 1; omega)

/-- **8554 … 8582, `Some`**: cur := c + 232 at sp + 480; the slot's word0 w ≠ 2⁶⁴ − 2 in ω₅; the call of
    memcpy (68729, return 296) of the slot's other 224 octets (from c + 8) to sp + 512. -/
theorem il_next {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp c w : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h6 : ω[6] = UInt64.ofNat c)
    (hsp : 65536 ≤ sp ∧ sp + 1632 < 4294967296) (hc : 65536 ≤ c ∧ c + 232 ≤ sp)
    (hw64 : w < 2 ^ 64) (hwN : w ≠ 18446744073709551614)
    (mw : μ.readN c 8 = Num.encodeLE 8 w)
    (hr : ∀ a, c ≤ a → a < c + 8 → μ.readable a = true)
    (hw : ∀ a, sp + 480 ≤ a → a < sp + 488 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 8554 ω μ x 68729 ω' μ' x 8 ∧ ω'[0] = UInt64.ofNat 296 ∧ ω'[1] = ω[1] ∧
      ω'[5] = UInt64.ofNat w ∧ ω'[7] = UInt64.ofNat (sp + 512) ∧ ω'[8] = UInt64.ofNat (c + 8) ∧
      ω'[9] = UInt64.ofNat 224 ∧
      μ'.readN (sp + 480) 8 = Num.encodeLE 8 (c + 232) ∧
      (∀ a, a < 4294967296 → (a < sp + 480 ∨ sp + 488 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rw0 := Handlers.DesignateAlloc.rd8 hw64 mw
  have hwN' : w % 18446744073709551616 ≠ 18446744073709551614 := by rw [Nat.mod_eq_of_lt hw64]; exact hwN
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, hsp, hc, hc.2, rw0, hr, hw, hwN, hwN', rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨by reg_val, by reg_val, ?_, ?_, ?_, by reg_val, ?_, fun a ha h1' => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
      PVM.getD_some', List.lookup_nil, Option.getD_none]
    all_goals try rd_simp []
    all_goals try rfl
    all_goals try (congr 1; omega)
    all_goals try simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1, h6, Nat.mod_eq_of_lt hw64]
    all_goals try (congr 1; omega)

/-- **8589 … 8620**: the index k at sp + 504 saved at sp + 736, k + 1 at sp + 504, the word0 w (ω₅) at
    sp + 744, and the call of memcpy (68729, return 298) of the 224 octets at sp + 512 to sp + 752. -/
theorem il_copy2 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp k w : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat w)
    (hsp : 65536 ≤ sp ∧ sp + 1632 < 4294967296) (hk : k + 1 < 2 ^ 64) (hw64 : w < 2 ^ 64)
    (mk : μ.readN (sp + 504) 8 = Num.encodeLE 8 k)
    (hr : ∀ a, sp + 504 ≤ a → a < sp + 512 → μ.readable a = true)
    (hw : ∀ a, sp + 504 ≤ a → a < sp + 512 → μ.writable a = true)
    (hw2 : ∀ a, sp + 736 ≤ a → a < sp + 752 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 8589 ω μ x 68729 ω' μ' x 9 ∧ ω'[0] = UInt64.ofNat 298 ∧ ω'[1] = ω[1] ∧
      ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat (sp + 752) ∧ ω'[8] = UInt64.ofNat (sp + 512) ∧
      ω'[9] = UInt64.ofNat 224 ∧
      μ'.readN (sp + 504) 8 = Num.encodeLE 8 (k + 1) ∧ μ'.readN (sp + 736) 8 = Num.encodeLE 8 k ∧
      μ'.readN (sp + 744) 8 = Num.encodeLE 8 w ∧
      (∀ a, a < 4294967296 → (a < sp + 504 ∨ sp + 512 ≤ a) → (a < sp + 736 ∨ sp + 752 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rk := Handlers.DesignateAlloc.rd8 (by omega) mk
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hsp, rk, hr, hw, hw2, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨by reg_val, by reg_val, by reg_val, ?_, ?_, by reg_val, ?_, ?_, ?_, fun a ha h1' h2' => ?_,
      fun a => ?_, fun a => ?_⟩
    all_goals try simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
      PVM.getD_some', List.lookup_nil, Option.getD_none]
    all_goals try rd_simp []
    all_goals try rfl
    all_goals try (congr 1; omega)
    all_goals try simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1, h5, Nat.mod_eq_of_lt hw64,
      Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt hk]
    all_goals try (congr 1; omega)

/-- The tag the loop decodes from a slot's word0 w (with the frame constants 2⁶³ at sp + 184 and 2⁶³ + 1
    at sp + 216): w − 2⁶³ + 1 for w in the niche [2⁶³, 2⁶³ + 24), else 0 (the dataful variant
    `CreateService`). -/
def slotTag (w : Nat) : Nat := if 9223372036854775808 ≤ w ∧ w < 9223372036854775832 then w - 9223372036854775807 else 0

/-- **8627 … 8650, another tag** (neither 3 = `Zombify` nor 15 = `Checkpoint`): on to 8735. -/
theorem il_tag_other {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp w : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat w)
    (hsp : 65536 ≤ sp ∧ sp + 1632 < 4294967296) (hw64 : w < 2 ^ 64) (ht3 : slotTag w ≠ 3) (ht15 : slotTag w ≠ 15)
    (m184 : μ.readN (sp + 184) 8 = Num.encodeLE 8 9223372036854775808)
    (m216 : μ.readN (sp + 216) 8 = Num.encodeLE 8 9223372036854775809)
    (hr : ∀ a, sp + 184 ≤ a → a < sp + 224 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 8627 ω μ x 8735 ω' μ x 8 ∧ ω'[1] = ω[1] := by
  have r184 := Handlers.DesignateAlloc.rd8 (by decide) m184
  have r216 := Handlers.DesignateAlloc.rd8 (by decide) m216
  unfold slotTag at ht3 ht15
  rw [show ω = regsNF ω [] from rfl]
  by_cases hn : 9223372036854775808 ≤ w ∧ w < 9223372036854775832
  · rw [if_pos hn] at ht3 ht15
    obtain ⟨t, rfl⟩ : ∃ t, w = 9223372036854775807 + t := ⟨w - 9223372036854775807, by omega⟩
    have ht : t = 1 ∨ t = 2 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 ∨ t = 16 ∨ t = 17 ∨ t = 18 ∨ t = 19 ∨ t = 20 ∨ t = 21 ∨ t = 22 ∨ t = 23 ∨ t = 24 := by omega
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · refine ⟨?_, ?_, ?_⟩
      rotate_left
      · pvm_go [h1, h5, hsp, r184, r216, hr, ↓rdN_fold]
      · exact by reg_val
  · have hc7 : (if (if w < 9223372036854775808 then (w : Int) else (w : Int) - 18446744073709551616) <
        -9223372036854775784 then 1 else 0 : Nat) = 0 := by
      have : ¬ ((if w < 9223372036854775808 then (w : Int) else (w : Int) - 18446744073709551616) <
          -9223372036854775784) := by split <;> omega
      rw [if_neg this]
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h5, hsp, r184, r216, hr, hc7, ↓rdN_fold]
    · exact by reg_val

/-- **8627 … 8734, `Zombify`** (tag 3): the flag [sp + 160] := 1, on to 8735. -/
theorem il_tag_zomb {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp w : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat w)
    (hsp : 65536 ≤ sp ∧ sp + 1632 < 4294967296) (hw64 : w < 2 ^ 64) (ht : slotTag w = 3)
    (m184 : μ.readN (sp + 184) 8 = Num.encodeLE 8 9223372036854775808)
    (m216 : μ.readN (sp + 216) 8 = Num.encodeLE 8 9223372036854775809)
    (hr : ∀ a, sp + 184 ≤ a → a < sp + 224 → μ.readable a = true)
    (hw : ∀ a, sp + 160 ≤ a → a < sp + 168 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 8627 ω μ x 8735 ω' μ' x 9 ∧ ω'[1] = ω[1] ∧
      μ'.readN (sp + 160) 8 = Num.encodeLE 8 1 ∧
      (∀ a, a < 4294967296 → (a < sp + 160 ∨ sp + 168 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r184 := Handlers.DesignateAlloc.rd8 (by decide) m184
  have r216 := Handlers.DesignateAlloc.rd8 (by decide) m216
  have hw' : w = 9223372036854775810 := by unfold slotTag at ht; split at ht <;> omega
  subst hw'
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hsp, r184, r216, hr, hw, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨by reg_val, ?_, fun a ha h1' => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
      PVM.getD_some', List.lookup_nil, Option.getD_none]
    all_goals try rd_simp []
    all_goals try rfl
    all_goals try (congr 1; omega)

/-- **8627 … 8710, `Checkpoint`** (tag 15): the results so far are written before the dispatch. As
    `r11_pre`: the tag-2 key value at sp + 1568 (the package hash from sp + 312, the item index from
    sp + 176), ω₇ := rp (sp + 456), ω₈ := n (sp + 464), ω₉ := sp + 1568, and the call of 36170 with return
    address 300 (→ 8716). -/
theorem il_tag_ck {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp w q0 q1 q2 q3 v rp n : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat w)
    (hsp : 65536 ≤ sp ∧ sp + 1632 < 4294967296) (hw64 : w < 2 ^ 64) (ht : slotTag w = 15)
    (m184 : μ.readN (sp + 184) 8 = Num.encodeLE 8 9223372036854775808)
    (m216 : μ.readN (sp + 216) 8 = Num.encodeLE 8 9223372036854775809)
    (m0 : μ.readN (sp + 312) 8 = Num.encodeLE 8 q0) (m1 : μ.readN (sp + 320) 8 = Num.encodeLE 8 q1)
    (m2 : μ.readN (sp + 328) 8 = Num.encodeLE 8 q2) (m3 : μ.readN (sp + 336) 8 = Num.encodeLE 8 q3)
    (hq0 : q0 < 2 ^ 64) (hq1 : q1 < 2 ^ 64) (hq2 : q2 < 2 ^ 64) (hq3 : q3 < 2 ^ 64)
    (mv : μ.readN (sp + 176) 8 = Num.encodeLE 8 v) (hv : v < 2 ^ 64)
    (mrp : μ.readN (sp + 456) 8 = Num.encodeLE 8 rp) (hrp : rp < 2 ^ 64)
    (mn : μ.readN (sp + 464) 8 = Num.encodeLE 8 n) (hn : n < 2 ^ 64)
    (hr : ∀ a, sp + 176 ≤ a → a < sp + 472 → μ.readable a = true)
    (hw : ∀ a, sp + 1568 ≤ a → a < sp + 1604 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 8627 ω μ x 36170 ω' μ' x 26 ∧
      ω'[0] = UInt64.ofNat 300 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[7] = UInt64.ofNat rp ∧ ω'[8] = UInt64.ofNat n ∧
      ω'[9] = UInt64.ofNat (sp + 1568) ∧
      μ'.readN (sp + 1568) 2 = Num.encodeLE 2 2 ∧ μ'.readN (sp + 1570) 2 = Num.encodeLE 2 v ∧
      μ'.readN (sp + 1572) 8 = Num.encodeLE 8 q0 ∧ μ'.readN (sp + 1580) 8 = Num.encodeLE 8 q1 ∧
      μ'.readN (sp + 1588) 8 = Num.encodeLE 8 q2 ∧ μ'.readN (sp + 1596) 8 = Num.encodeLE 8 q3 ∧
      (∀ a, a < 4294967296 → (a < sp + 1568 ∨ sp + 1604 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r184 := Handlers.DesignateAlloc.rd8 (by decide) m184
  have r216 := Handlers.DesignateAlloc.rd8 (by decide) m216
  have r0 := Handlers.DesignateAlloc.rd8 hq0 m0
  have r1 := Handlers.DesignateAlloc.rd8 hq1 m1
  have r2 := Handlers.DesignateAlloc.rd8 hq2 m2
  have r3 := Handlers.DesignateAlloc.rd8 hq3 m3
  have rv := Handlers.DesignateAlloc.rd8 hv mv
  have rrp := Handlers.DesignateAlloc.rd8 hrp mrp
  have rn := Handlers.DesignateAlloc.rd8 hn mn
  have hw' : w = 9223372036854775822 := by unfold slotTag at ht; split at ht <;> omega
  subst hw'
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hsp, r184, r216, r0, r1, r2, r3, rv, rrp, rn, hr, hw, bs_36170, rdN_writeN_disjoint,
      ↓rdN_fold]
  · refine ⟨by reg_val, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1' => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
      PVM.getD_some', List.lookup_nil, Option.getD_none]
    all_goals try rd_simp []
    all_goals try rfl
    all_goals try (congr 1; omega)
    all_goals try simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1]
    all_goals try (congr 1; omega)
    all_goals try exact PVM.encodeLE_mod 2 v

/-- **8716 … 8720, `Ok`**: ω₇'s low octet is 255 (the checkpoint's results write succeeded); on to
    8735. -/
theorem il_ck_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (h7 : ω[7] = UInt64.ofNat 18446744073709551615) :
    ∃ ω', FreeStepsH p R 8716 ω μ x 8735 ω' μ x 2 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h7]
  · exact ⟨by reg_val, by reg_val, by reg_val⟩

/-- **8716 … 8726, `Err`** (ω₇ = 3, `set`'s code for FULL): on to the trap at 15361. -/
theorem il_ck_err {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (h7 : ω[7] = UInt64.ofNat 3) : ∃ ω', FreeStepsH p R 8716 ω μ x 15361 ω' μ x 4 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_⟩
  rotate_left
  · pvm_go [h7]

/-- **8735 … 8772**: the argument pair (sp + 744, 2272) at sp + 1144 (its pointer sp + 744 stored at
    sp + 1000), and the call of `format!` (59375, return 302) with ω₇ = sp + 1568, ω₈ = 66194 (the
    template), ω₉ = sp + 1144. -/
theorem il_log_pre {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : 65536 ≤ sp ∧ sp + 1632 < 4294967296)
    (hw : ∀ a, sp + 1000 ≤ a → a < sp + 1008 → μ.writable a = true)
    (hw2 : ∀ a, sp + 1144 ≤ a → a < sp + 1160 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 8735 ω μ x 59375 ω' μ' x 10 ∧
      ω'[0] = UInt64.ofNat 302 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (sp + 1568) ∧ ω'[8] = UInt64.ofNat 66194 ∧ ω'[9] = UInt64.ofNat (sp + 1144) ∧
      μ'.readN (sp + 1000) 8 = Num.encodeLE 8 (sp + 744) ∧
      μ'.readN (sp + 1144) 8 = Num.encodeLE 8 (sp + 1000) ∧ μ'.readN (sp + 1152) 8 = Num.encodeLE 8 2272 ∧
      (∀ a, a < 4294967296 → (a < sp + 1000 ∨ sp + 1008 ≤ a) → (a < sp + 1144 ∨ sp + 1160 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hsp, hw, hw2, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, ?_, by reg_val, ?_, ?_, ?_, ?_,
      fun a ha h1' h2' => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
      PVM.getD_some', List.lookup_nil, Option.getD_none]
    all_goals try rd_simp []
    all_goals try rfl
    all_goals try (congr 1; omega)
    all_goals try simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1]
    all_goals try (congr 1; omega)

/-- **8779 … 8815**: the `String` { c, q, l } that `format!` left at sp + 1568 saved at sp + 976, and
    the call of memcpy (68729, return 304) of the 232 octets at sp + 744 to sp + 1144. -/
theorem il_log_post {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp c q l : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : 65536 ≤ sp ∧ sp + 1632 < 4294967296)
    (hc : c < 2 ^ 64) (hq : q < 2 ^ 64) (hl : l < 2 ^ 64)
    (mc : μ.readN (sp + 1568) 8 = Num.encodeLE 8 c) (mq : μ.readN (sp + 1576) 8 = Num.encodeLE 8 q)
    (ml : μ.readN (sp + 1584) 8 = Num.encodeLE 8 l)
    (hr : ∀ a, sp + 1568 ≤ a → a < sp + 1592 → μ.readable a = true)
    (hw : ∀ a, sp + 976 ≤ a → a < sp + 1000 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 8779 ω μ x 68729 ω' μ' x 10 ∧
      ω'[0] = UInt64.ofNat 304 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (sp + 1144) ∧ ω'[8] = UInt64.ofNat (sp + 744) ∧ ω'[9] = UInt64.ofNat 232 ∧
      μ'.readN (sp + 976) 8 = Num.encodeLE 8 c ∧ μ'.readN (sp + 984) 8 = Num.encodeLE 8 q ∧
      μ'.readN (sp + 992) 8 = Num.encodeLE 8 l ∧
      (∀ a, a < 4294967296 → (a < sp + 976 ∨ sp + 1000 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rc := Handlers.DesignateAlloc.rd8 hc mc
  have rq := Handlers.DesignateAlloc.rd8 hq mq
  have rl := Handlers.DesignateAlloc.rd8 hl ml
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hsp, rc, rq, rl, hr, hw, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, ?_, ?_, by reg_val, ?_, ?_, ?_,
      fun a ha h1' => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
      PVM.getD_some', List.lookup_nil, Option.getD_none]
    all_goals try rd_simp []
    all_goals try rfl
    all_goals try (congr 1; omega)
    all_goals try simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1, Nat.mod_eq_of_lt hc,
      Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hl]
    all_goals try (congr 1; omega)

end Services.Bootstrap.Acc.Handlers.InstrLoop
