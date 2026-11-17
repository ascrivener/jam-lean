import Services.Bootstrap.Acc.Handlers.ResultsInitSeg

/-!
# Row 11: the final results write, the caller's segments (15038 … 15133)

Spec `onWorkItem`'s `unless (is.any zombify) (store key (encodeResults results))` (GP v0.8.0 Appendix B,
Ω_W; quirk Q4), with key = `Key.results package item`:
- `r11_flag` (15038 → 15060 or 15133): the `Zombify` flag's low bit at sp + 160; clear → the store,
  set → past it;
- `r11_pre` (15060 → 36170): as row 9's `r9_pre` (the tag-2 key value at sp + 1568, ω₇ := [sp + 456],
  ω₈ := [sp + 464], ω₉ := sp + 1568), with ω₆ := sp + 1572 and return address 562;
- `r11_ok` (15121 → 15133): ω₇'s low octet is 255 (`Ok`); `r11_err` (15121 → 15361): otherwise.
-/

namespace Services.Bootstrap.Acc.Handlers.RowEleven

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.Alloc Services.Bootstrap.Acc Services.Bootstrap.Spec

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **15038 … 15045**: the word z at sp + 160 with z % 2 = 0 (no `Zombify`): on to the store at 15060. -/
theorem r11_flag0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp z : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : sp + 168 < 4294967296) (hz : z < 2 ^ 64) (hz0 : z % 2 = 0)
    (mz : μ.readN (sp + 160) 8 = Num.encodeLE 8 z) (hr : ∀ a, sp + 160 ≤ a → a < sp + 168 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 15038 ω μ x 15060 ω' μ x 3 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have rz := Handlers.DesignateAlloc.rd8 hz mz
  have hz' : Exec.bitwise (fun x1 x2 => x1 && x2) z 1 % 18446744073709551616 = 0 := by
    rw [PVM.bitwise_and_m1]; omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hsp, rz, hz', hr, ↓rdN_fold]
  · exact ⟨by reg_val, by reg_val, by reg_val⟩

/-- **15038 … 15048**: z % 2 = 1 (a `Zombify`): on to 15133, past the store. -/
theorem r11_flag1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp z : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : sp + 168 < 4294967296) (hz : z < 2 ^ 64) (hz1 : z % 2 = 1)
    (mz : μ.readN (sp + 160) 8 = Num.encodeLE 8 z) (hr : ∀ a, sp + 160 ≤ a → a < sp + 168 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 15038 ω μ x 15133 ω' μ x 4 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have rz := Handlers.DesignateAlloc.rd8 hz mz
  have hz' : Exec.bitwise (fun x1 x2 => x1 && x2) z 1 % 18446744073709551616 = 1 := by
    rw [PVM.bitwise_and_m1]; omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hsp, rz, hz', hr, ↓rdN_fold]
  · exact ⟨by reg_val, by reg_val, by reg_val⟩

/-- **15060 … 15115**: the tag-2 key value at sp + 1568 (as `r9_pre`), ω₇ := rp (sp + 456), ω₈ := n
    (sp + 464), ω₉ := sp + 1568, ω₆ := sp + 1572, and the call of 36170 with return address 562. -/
theorem r11_pre {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp q0 q1 q2 q3 v rp n : Nat) (h1 : ω[1] = UInt64.ofNat sp)
    (hsp : 65536 ≤ sp ∧ sp + 1632 < 4294967296)
    (m0 : μ.readN (sp + 312) 8 = Num.encodeLE 8 q0) (m1 : μ.readN (sp + 320) 8 = Num.encodeLE 8 q1)
    (m2 : μ.readN (sp + 328) 8 = Num.encodeLE 8 q2) (m3 : μ.readN (sp + 336) 8 = Num.encodeLE 8 q3)
    (hq0 : q0 < 2 ^ 64) (hq1 : q1 < 2 ^ 64) (hq2 : q2 < 2 ^ 64) (hq3 : q3 < 2 ^ 64)
    (mv : μ.readN (sp + 176) 8 = Num.encodeLE 8 v) (hv : v < 2 ^ 64)
    (mrp : μ.readN (sp + 456) 8 = Num.encodeLE 8 rp) (hrp : rp < 2 ^ 64)
    (mn : μ.readN (sp + 464) 8 = Num.encodeLE 8 n) (hn : n < 2 ^ 64)
    (hr : ∀ a, sp + 176 ≤ a → a < sp + 472 → μ.readable a = true)
    (hw : ∀ a, sp + 1568 ≤ a → a < sp + 1604 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 15060 ω μ x 36170 ω' μ' x 17 ∧
      ω'[0] = UInt64.ofNat 562 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧
      ω'[6] = UInt64.ofNat (sp + 1572) ∧ ω'[7] = UInt64.ofNat rp ∧ ω'[8] = UInt64.ofNat n ∧
      ω'[9] = UInt64.ofNat (sp + 1568) ∧
      μ'.readN (sp + 1568) 2 = Num.encodeLE 2 2 ∧ μ'.readN (sp + 1570) 2 = Num.encodeLE 2 v ∧
      μ'.readN (sp + 1572) 8 = Num.encodeLE 8 q0 ∧ μ'.readN (sp + 1580) 8 = Num.encodeLE 8 q1 ∧
      μ'.readN (sp + 1588) 8 = Num.encodeLE 8 q2 ∧ μ'.readN (sp + 1596) 8 = Num.encodeLE 8 q3 ∧
      (∀ a, a < 4294967296 → (a < sp + 1568 ∨ sp + 1604 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r0 := Handlers.DesignateAlloc.rd8 hq0 m0
  have r1 := Handlers.DesignateAlloc.rd8 hq1 m1
  have r2 := Handlers.DesignateAlloc.rd8 hq2 m2
  have r3 := Handlers.DesignateAlloc.rd8 hq3 m3
  have rv := Handlers.DesignateAlloc.rd8 hv mv
  have rrp := Handlers.DesignateAlloc.rd8 hrp mrp
  have rn := Handlers.DesignateAlloc.rd8 hn mn
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hsp, r0, r1, r2, r3, rv, rrp, rn, hr, hw, bs_36170, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨by reg_val, ?_, by reg_val, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      fun a ha h1' => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
      PVM.getD_some', List.lookup_nil, Option.getD_none]
    all_goals try rd_simp []
    all_goals try rfl
    all_goals try (congr 1; omega)
    all_goals try simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1]
    all_goals try (congr 1; omega)
    all_goals try exact PVM.encodeLE_mod 2 v

/-- **15121 … 15129, `Ok`**: ω₇'s low octet is 255; on to 15133. -/
theorem r11_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (h7 : ω[7] = UInt64.ofNat 18446744073709551615) :
    ∃ ω', FreeStepsH p R 15121 ω μ x 15133 ω' μ x 3 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h7]
  · exact ⟨by reg_val, by reg_val, by reg_val⟩

/-- **15121 … 15129, `Err`** (ω₇ = 3, `set`'s code for FULL): on to the trap at 15361. -/
theorem r11_err {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (h7 : ω[7] = UInt64.ofNat 3) : ∃ ω', FreeStepsH p R 15121 ω μ x 15361 ω' μ x 3 := by
  rw [show ω = regsNF ω [] from rfl]
  exact ⟨_, by pvm_go [h7]⟩

end Services.Bootstrap.Acc.Handlers.RowEleven
