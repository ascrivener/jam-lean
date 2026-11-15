import Services.Bootstrap.Acc.Wrappers.Get

/-!
# The SDK's `set` (48104): a write of this service's storage

`set(key, value)` makes one Ω_W call (`write`, GP v0.8.0 Appendix B) with the key at ω₇ (ω₈ octets)
and the value at ω₉ (ω₁₀ octets), then stores `Result<Option<u64>, Error>` at out:
- a reply L < 2⁶⁴ − 9 (the old value's length): `Ok(Some(L))`, (1, L) (`sw_some`);
- the error codes 2⁶⁴ − 9 … 2⁶⁴ − 1 go through a table of i32 offsets in read-only data at 69040 to
  `jumpInd`: NONE (no old value) to `Ok(None)`, 0 (`sw_none`), FULL to `Err`, −1 and the code 3
  (`sw_full`). The other codes Ω_W does not return for this service.
The frame is 24 octets (s = sp − 24): ω₆, ω₅, ω₀ at s, + 8, + 16.
-/

namespace Services.Bootstrap.Acc
open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
variable {X : Type} {R : HostRel X}

/-- **48104 … 48132**: the frame s = sp − 24 (ω₀, ω₅, ω₆ saved at s + 16, + 8, + 0), out = ω₇ moved
    to ω₅, ω₆ = 2⁶⁴ − 10 (the largest non-error reply), and Ω_W's registers: the key at ω₇ (ω₈
    octets), the value at ω₉ (ω₁₀ octets), from ω₈ … ω₁₁ at the call; ω₀ = 2134. -/
theorem sw_pre {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : 65536 + 24 ≤ sp ∧ sp < 4294967296)
    (hwf : ∀ a, sp - 24 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 48104 ω μ x 48132 ω' μ' x 12 ∧
      ω'[1] = UInt64.ofNat (sp - 24) ∧ ω'[5] = ω[7] ∧ ω'[6] = UInt64.ofNat 18446744073709551606 ∧
      ω'[7] = ω[8] ∧ ω'[8] = ω[9] ∧ ω'[9] = ω[10] ∧ ω'[10] = ω[11] ∧ ω'[0] = UInt64.ofNat 2134 ∧
      rdN μ' (sp - 24 + 16) 8 = ω[0].toNat ∧ rdN μ' (sp - 24 + 8) 8 = ω[5].toNat ∧
      rdN μ' (sp - 24) 8 = ω[6].toNat ∧
      (∀ a, a < 4294967296 → (a < sp - 24 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      ∀ j : Fin 13, j.val ∉ [0, 1, 5, 6, 7, 8, 9, 10] → ω'[j] = ω[j] := by
  have hr : ∀ a, sp - 24 ≤ a → a < sp → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, hwf, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, (by reg_val <;> simp [UInt64.ofNat_toNat]), by reg_val, (by reg_val <;> simp [UInt64.ofNat_toNat]), (by reg_val <;> simp [UInt64.ofNat_toNat]),
      (by reg_val <;> simp [UInt64.ofNat_toNat]), (by reg_val <;> simp [UInt64.ofNat_toNat]), by reg_val, ?_, ?_, ?_,
      fun a ha h1 => ?_, fun a => ?_, fun a => ?_, by reg_frame⟩
    all_goals try (rd_simp []; done)
    all_goals try rd_simp []
    all_goals try with_reducible rfl
    all_goals try exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)

/-- **48134 … 48158**, a reply L < 2⁶⁴ − 9 (the old value's length): `Ok(Some(L))` (1, L) at out, ω₀,
    ω₅, ω₆ restored and the frame popped, at the return's `jumpInd`. -/
theorem sw_some {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp out r0 r5 r6 : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat out)
    (h6 : ω[6] = UInt64.ofNat 18446744073709551606) (L : Nat) (h7 : ω[7] = UInt64.ofNat L) (hL : L < 18446744073709551607)
    (hsp : 65536 ≤ sp ∧ sp + 24 < 4294967296) (hout : 65536 ≤ out ∧ out + 16 < 4294967296)
    (m0 : μ.readN sp 8 = Num.encodeLE 8 r6) (m8 : μ.readN (sp + 8) 8 = Num.encodeLE 8 r5)
    (m16 : μ.readN (sp + 16) 8 = Num.encodeLE 8 r0)
    (hrf : ∀ a, sp ≤ a → a < sp + 24 → μ.readable a = true)
    (hwo : ∀ a, out ≤ a → a < out + 16 → μ.writable a = true) (dos : out + 16 ≤ sp ∨ sp + 24 ≤ out)
    (hr0 : r0 < 18446744073709551616) (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616) :
    ∃ ω' μ', FreeStepsH p R 48134 ω μ x 48158 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (sp + 24) ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 ∧ μ'.readN out 8 = Num.encodeLE 8 1 ∧ μ'.readN (out + 8) 8 = Num.encodeLE 8 L ∧
      (∀ a, a < 4294967296 → (a < out ∨ out + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hro : ∀ a, out ≤ a → a < out + 16 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwo a h1 h2)
  have q0 : rdN μ sp 8 = r6 := by unfold rdN; rw [m0, Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt hr6
  have q8 : rdN μ (sp + 8) 8 = r5 := by unfold rdN; rw [m8, Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt hr5
  have q16 : rdN μ (sp + 16) 8 = r0 := by unfold rdN; rw [m16, Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt hr0
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, h6, h7, m0, m8, m16, hrf, hwo, hro, Nat.mod_eq_of_lt (show L < 18446744073709551616 by omega)]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', Option.getD_none, h1, PVM.Memory.readN_writeN_disjoint, m0, m8, m16,
      rdN_writeN_disjoint, q0, q8, q16]
    all_goals try rw [Nat.mod_eq_of_lt (by assumption)]
    all_goals try simp only [show out + 0 = out from rfl]
    all_goals try (simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same]; done)
    all_goals try (simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same]; decide)
    all_goals try (intro a ha1 ha2; simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint])
    all_goals try (intro a; simp only [Memory.readable_writeN, Memory.writable_writeN])

/-- **48134 … 48250**, the reply NONE (no old value): through the error table at 69040 (entry 8,
    −66888, to 48237), `Ok(None)` (0) at out, ω₀, ω₅, ω₆ restored and the frame popped. -/
theorem sw_none {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp out r0 r5 r6 : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat out)
    (h6 : ω[6] = UInt64.ofNat 18446744073709551606) (h7 : ω[7] = UInt64.ofNat 18446744073709551615)
    (ht : rdN μ 69072 4 = 4294900408) (htr : ∀ a, 69072 ≤ a → a < 69076 → μ.readable a = true)
    (hsp : 65536 ≤ sp ∧ sp + 24 < 4294967296) (hout : 65536 ≤ out ∧ out + 16 < 4294967296)
    (m0 : μ.readN sp 8 = Num.encodeLE 8 r6) (m8 : μ.readN (sp + 8) 8 = Num.encodeLE 8 r5)
    (m16 : μ.readN (sp + 16) 8 = Num.encodeLE 8 r0)
    (hrf : ∀ a, sp ≤ a → a < sp + 24 → μ.readable a = true)
    (hwo : ∀ a, out ≤ a → a < out + 16 → μ.writable a = true) (dos : out + 16 ≤ sp ∨ sp + 24 ≤ out)
    (hr0 : r0 < 18446744073709551616) (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616) :
    ∃ ω' μ', FreeStepsH p R 48134 ω μ x 48250 ω' μ' x 30 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (sp + 24) ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 ∧ μ'.readN out 8 = Num.encodeLE 8 0 ∧
      (∀ a, a < 4294967296 → (a < out ∨ out + 8 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hro : ∀ a, out ≤ a → a < out + 16 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwo a h1 h2)
  have q0 : rdN μ sp 8 = r6 := by unfold rdN; rw [m0, Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt hr6
  have q8 : rdN μ (sp + 8) 8 = r5 := by unfold rdN; rw [m8, Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt hr5
  have q16 : rdN μ (sp + 16) 8 = r0 := by unfold rdN; rw [m16, Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt hr0
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, h6, h7, m0, m8, m16, hrf, hwo, hro, ht, htr, ↓rdN_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', Option.getD_none, h1, PVM.Memory.readN_writeN_disjoint, m0, m8, m16,
      rdN_writeN_disjoint, q0, q8, q16]
    all_goals try rw [Nat.mod_eq_of_lt (by assumption)]
    all_goals try simp only [show out + 0 = out from rfl]
    all_goals try (simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same]; done)
    all_goals try (simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same]; decide)
    all_goals try (intro a ha1 ha2; simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint])
    all_goals try (intro a; simp only [Memory.readable_writeN, Memory.writable_writeN])

/-- **48134 … 48235**, the reply FULL (2⁶⁴ − 5): through the error table at 69040 (entry 4, −66894,
    to 48207), `Err` (−1, then the code 3 in one octet) at out, ω₀, ω₅, ω₆ restored and the frame
    popped. -/
theorem sw_full {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp out r0 r5 r6 : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat out)
    (h6 : ω[6] = UInt64.ofNat 18446744073709551606) (h7 : ω[7] = UInt64.ofNat 18446744073709551611)
    (ht : rdN μ 69056 4 = 4294900402) (htr : ∀ a, 69056 ≤ a → a < 69060 → μ.readable a = true)
    (hsp : 65536 ≤ sp ∧ sp + 24 < 4294967296) (hout : 65536 ≤ out ∧ out + 16 < 4294967296)
    (m0 : μ.readN sp 8 = Num.encodeLE 8 r6) (m8 : μ.readN (sp + 8) 8 = Num.encodeLE 8 r5)
    (m16 : μ.readN (sp + 16) 8 = Num.encodeLE 8 r0)
    (hrf : ∀ a, sp ≤ a → a < sp + 24 → μ.readable a = true)
    (hwo : ∀ a, out ≤ a → a < out + 16 → μ.writable a = true) (dos : out + 16 ≤ sp ∨ sp + 24 ≤ out)
    (hr0 : r0 < 18446744073709551616) (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616) :
    ∃ ω' μ', FreeStepsH p R 48134 ω μ x 48235 ω' μ' x 30 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (sp + 24) ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 ∧ μ'.readN out 8 = Num.encodeLE 8 18446744073709551615 ∧
      μ'.readN (out + 8) 1 = [3] ∧
      (∀ a, a < 4294967296 → (a < out ∨ out + 9 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hro : ∀ a, out ≤ a → a < out + 16 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwo a h1 h2)
  have q0 : rdN μ sp 8 = r6 := by unfold rdN; rw [m0, Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt hr6
  have q8 : rdN μ (sp + 8) 8 = r5 := by unfold rdN; rw [m8, Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt hr5
  have q16 : rdN μ (sp + 16) 8 = r0 := by unfold rdN; rw [m16, Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt hr0
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, h6, h7, m0, m8, m16, hrf, hwo, hro, ht, htr, ↓rdN_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', Option.getD_none, h1, PVM.Memory.readN_writeN_disjoint, m0, m8, m16,
      rdN_writeN_disjoint, q0, q8, q16]
    all_goals try rw [Nat.mod_eq_of_lt (by assumption)]
    all_goals try simp only [show out + 0 = out from rfl]
    all_goals try (simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same]; done)
    all_goals try (simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same]; decide)
    all_goals try (intro a ha1 ha2; simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint])
    all_goals try (intro a; simp only [Memory.readable_writeN, Memory.writable_writeN])

end Services.Bootstrap.Acc
