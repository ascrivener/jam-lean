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

end Services.Bootstrap.Acc.Handlers.InstrLoop
