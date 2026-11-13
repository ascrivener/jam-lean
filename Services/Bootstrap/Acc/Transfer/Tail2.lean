import Services.Bootstrap.Acc.Transfer.Encode

/-!
# `on_transfer`'s second write (7799 … 6766): "transfer{n}" := ℰ₄(source) ++ ℰ₈(amount) ++ memo

After `format!("transfer{}", n)` has left the key `String` at sp + 512 (cap, ptr, len):
- 7799 … 68729 (`t2_rec`): the record (amount at sp + 1568, source at sp + 1576, then the memo
  copied from sp + 1144 to sp + 1580 by `memcpy`), the key's length parked at sp + 248;
- 7846 … 40494 (`t2_enc_pre`): the encoding helper's frame s = sp − 64 and `alloc(140, 1)`
  (`Encode.lean`), the encoded `Vec` at sp + 744;
- 7888 … 48104 (`t2_set`): `set(out = sp + 264, key, value)`;
- 7915 (`t2_chk_ok`, `t2_chk_full`): `Err` (−1 at sp + 264, FULL) traps at 15361 (`orPanic`), else the
  value's `Vec` is freed; 7946 (`t2_kfree`, `t2_knofree`): the key's `String` freed, back to the
  items loop at 6766.
-/

namespace Services.Bootstrap.Acc
open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
variable {X : Type} {R : HostRel X}

/-- **7799 … 68729**: the record (amount, source) at sp + 1568, the key's length at sp + 248, ω₅ the
    key's address, and `memcpy(sp + 1580, sp + 1144, 128)` (return address 270). -/
theorem t2_rec {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp src am kp kl : Nat) (h1 : ω[1] = UInt64.ofNat sp)
    (hsp : 65536 ≤ sp ∧ sp + 1856 < 4294967296) (hwf : ∀ a, sp ≤ a → a < sp + 1856 → μ.writable a = true)
    (m472 : rdN μ (sp + 472) 4 = src) (m1000 : rdN μ (sp + 1000) 8 = am)
    (m520 : rdN μ (sp + 520) 8 = kp) (m528 : rdN μ (sp + 528) 8 = kl) :
    ∃ ω' μ', FreeStepsH p R 7799 ω μ x 68729 ω' μ' x 11 ∧
      ω'[0] = UInt64.ofNat 270 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[7] = UInt64.ofNat (sp + 1580) ∧
      ω'[8] = UInt64.ofNat (sp + 1144) ∧ ω'[9] = UInt64.ofNat 128 ∧ ω'[5] = UInt64.ofNat kp ∧
      ω'[6] = ω[6] ∧
      rdN μ' (sp + 248) 8 = kl ∧ rdN μ' (sp + 1568) 8 = am ∧ rdN μ' (sp + 1576) 4 = src ∧
      (∀ a, a < 4294967296 → (a < sp + 248 ∨ sp + 256 ≤ a) → (a < sp + 1568 ∨ sp + 1580 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp ≤ a → a < sp + 1856 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have l520 := m520 ▸ rdN_lt64 μ (sp + 520)
  have l528 := m528 ▸ rdN_lt64 μ (sp + 528)
  have l1000 := m1000 ▸ rdN_lt64 μ (sp + 1000)
  have hsv : Num.decodeLE (μ.readN (sp + 472) 4) < 4294967296 := rdN_lt μ (sp + 472) 4
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, hwf, hr, m1000, m520, m528, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, (by reg_val <;> exact h1), by reg_val, by reg_val, by reg_val,
      (by reg_val; try rw [Nat.mod_eq_of_lt l520]), (by reg_val <;> rfl), ?_, ?_, ?_,
      fun a ha h1 h2 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']
    all_goals try (simp (disch := pvm_arith) only [rdN, PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same,
      Num.decodeLE_encodeLE])
    all_goals try (simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint]; done)
    all_goals try (simp only [Memory.readable_writeN, Memory.writable_writeN])
    all_goals first | rfl | exact Nat.mod_eq_of_lt (by omega) | skip
    rw [enc_sxw _ hsv, Nat.mod_eq_of_lt hsv]; exact m472

/-- **7846 … 40494**: the encoding helper's frame s = sp − 64 (ω₀ = 272, ω₅, ω₆ at s + 56, + 48,
    + 40), ω₅ = out = sp + 744, ω₆ = the record sp + 1568, and `alloc(140, 1)` (return address 1576,
    to 34071). -/
theorem t2_enc_pre {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : 65536 + 64 ≤ sp ∧ sp + 1856 < 4294967296)
    (hwf : ∀ a, sp - 64 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 7846 ω μ x 40494 ω' μ' x 13 ∧
      ω'[0] = UInt64.ofNat 1576 ∧ ω'[1] = UInt64.ofNat (sp - 64) ∧ ω'[7] = UInt64.ofNat 140 ∧
      ω'[8] = UInt64.ofNat 1 ∧ ω'[5] = UInt64.ofNat (sp + 744) ∧ ω'[6] = UInt64.ofNat (sp + 1568) ∧
      rdN μ' (sp - 64 + 56) 8 = 272 ∧ rdN μ' (sp - 64 + 48) 8 = ω[5].toNat ∧
      rdN μ' (sp - 64 + 40) 8 = ω[6].toNat ∧
      (∀ a, a < 4294967296 → (a < sp - 64 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 64 ≤ a → a < sp → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, hwf, hr]
  case post =>
    refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, by reg_val, by reg_val, ?_, ?_, ?_,
      fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']
    all_goals try (simp (disch := pvm_arith) only [rdN, PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same,
      Num.decodeLE_encodeLE])
    all_goals try (simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint]; done)
    all_goals try (simp only [Memory.readable_writeN, Memory.writable_writeN])
    all_goals first | rfl | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _) | skip

/-- **7888 … 48104**: `set(out = sp + 264, key = (ω₅, the length at sp + 248), value = the `Vec` at
    sp + 744)` (return address 274). -/
theorem t2_set {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp kl vp vl : Nat) (h1 : ω[1] = UInt64.ofNat sp)
    (hsp : 65536 ≤ sp ∧ sp + 1856 < 4294967296) (hrf : ∀ a, sp ≤ a → a < sp + 1856 → μ.readable a = true)
    (m248 : rdN μ (sp + 248) 8 = kl) (m752 : rdN μ (sp + 752) 8 = vp) (m760 : rdN μ (sp + 760) 8 = vl) :
    ∃ ω', FreeStepsH p R 7888 ω μ x 48104 ω' μ x 7 ∧
      ω'[0] = UInt64.ofNat 274 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[7] = UInt64.ofNat (sp + 264) ∧
      ω'[8] = ω[5] ∧ ω'[9] = UInt64.ofNat kl ∧ ω'[10] = UInt64.ofNat vp ∧ ω'[11] = UInt64.ofNat vl ∧
      ω'[6] = UInt64.ofNat vp ∧ ω'[5] = ω[5] := by
  have l248 := m248 ▸ rdN_lt64 μ (sp + 248)
  have l752 := m752 ▸ rdN_lt64 μ (sp + 752)
  have l760 := m760 ▸ rdN_lt64 μ (sp + 760)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, hrf, m248, m752, m760, ↓rdN_fold]
  case post =>
    refine ⟨by reg_val, (by reg_val <;> exact h1), by reg_val, (by reg_val <;> rfl), ?_, ?_, ?_, ?_,
      (by reg_val <;> rfl)⟩ <;> (reg_val; try simp only [Nat.mod_eq_of_lt l248, Nat.mod_eq_of_lt l752,
        Nat.mod_eq_of_lt l760])

/-- `set`'s returns (48158, 48250, 48235) to 7915 (ω₀ = 274). -/
theorem t2_j {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (e : Nat) (he : e = 48158 ∨ e = 48250 ∨ e = 48235) (h0 : ω[0] = UInt64.ofNat 274) :
    FreeStepsH p R e ω μ x 7915 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  rcases he with rfl | rfl | rfl <;> pvm_go [h0]

/-- **7915 … 15361**, `set` returned `Err` (−1 at sp + 264, FULL): the trap (`orPanic`). -/
theorem t2_chk_full {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : 65536 ≤ sp ∧ sp + 1856 < 4294967296)
    (hrf : ∀ a, sp ≤ a → a < sp + 1856 → μ.readable a = true)
    (m : rdN μ (sp + 264) 8 = 18446744073709551615) :
    ∃ ω', FreeStepsH p R 7915 ω μ x 15361 ω' μ x 4 := by
  rw [show ω = regsNF ω [] from rfl]
  exact ⟨_, by pvm_go [h1, hrf, m, ↓rdN_fold]⟩

/-- **7915 … 40613**, `set` returned `Ok` (w ≠ −1 at sp + 264): `dealloc` of the value's `Vec`
    (ω₇ = its address ω₆, its capacity at sp + 744 ≠ 0; return address 276, to 7946). -/
theorem t2_chk_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp w cap vp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h6 : ω[6] = UInt64.ofNat vp)
    (hsp : 65536 ≤ sp ∧ sp + 1856 < 4294967296)
    (hrf : ∀ a, sp ≤ a → a < sp + 1856 → μ.readable a = true)
    (m : rdN μ (sp + 264) 8 = w) (hw : w ≠ 18446744073709551615) (mc : rdN μ (sp + 744) 8 = cap)
    (hc : cap ≠ 0) (hvp : vp < 18446744073709551616) :
    ∃ ω', FreeStepsH p R 7915 ω μ x 40613 ω' μ x 8 ∧ ω'[0] = UInt64.ofNat 276 ∧
      ω'[1] = UInt64.ofNat sp ∧ ω'[7] = UInt64.ofNat vp ∧ ω'[8] = UInt64.ofNat cap ∧
      ω'[5] = ω[5] := by
  have lw := m ▸ rdN_lt64 μ (sp + 264)
  have lc := mc ▸ rdN_lt64 μ (sp + 744)
  have hw' : w % 18446744073709551616 ≠ 18446744073709551615 := by rw [Nat.mod_eq_of_lt lw]; exact hw
  have hc' : cap % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt lc]; exact hc
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, h6, hrf, m, mc, hw', hc', ↓rdN_fold]
  case post =>
    exact ⟨by reg_val, (by reg_val <;> exact h1), (by reg_val; try rw [Nat.mod_eq_of_lt hvp]),
      (by reg_val; try rw [Nat.mod_eq_of_lt lc]), (by reg_val <;> rfl)⟩

/-- **7946 … 40613**, the key's capacity cap ≠ 0 (at sp + 512): `dealloc` of the key (ω₇ = ω₅;
    return address 228, to the items loop's head 6766). -/
theorem t2_kfree {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp cap kp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat kp)
    (hsp : 65536 ≤ sp ∧ sp + 1856 < 4294967296)
    (hrf : ∀ a, sp ≤ a → a < sp + 1856 → μ.readable a = true)
    (mc : rdN μ (sp + 512) 8 = cap) (hc : cap ≠ 0) (hkp : kp < 18446744073709551616) :
    ∃ ω', FreeStepsH p R 7946 ω μ x 40613 ω' μ x 6 ∧ ω'[0] = UInt64.ofNat 228 ∧
      ω'[1] = UInt64.ofNat sp ∧ ω'[7] = UInt64.ofNat kp ∧ ω'[8] = UInt64.ofNat cap := by
  have lc := mc ▸ rdN_lt64 μ (sp + 512)
  have hc' : cap % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt lc]; exact hc
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, h5, hrf, mc, hc', ↓rdN_fold]
  case post =>
    exact ⟨by reg_val, (by reg_val <;> exact h1), (by reg_val; try rw [Nat.mod_eq_of_lt hkp]),
      (by reg_val; try rw [Nat.mod_eq_of_lt lc])⟩

/-- **7946 … 6766**, the key's capacity 0: back to the items loop's head. -/
theorem t2_knofree {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : 65536 ≤ sp ∧ sp + 1856 < 4294967296)
    (hrf : ∀ a, sp ≤ a → a < sp + 1856 → μ.readable a = true) (mc : rdN μ (sp + 512) 8 = 0) :
    ∃ ω', FreeStepsH p R 7946 ω μ x 6766 ω' μ x 2 ∧ ∀ j : Fin 13, j.val ∉ [8] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, hrf, mc, ↓rdN_fold]
  case post => exact by reg_frame

end Services.Bootstrap.Acc
