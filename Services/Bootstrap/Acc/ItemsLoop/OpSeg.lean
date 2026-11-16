import Services.Bootstrap.Acc.Inputs.FetchVec

/-!
# The items loop's operand arm: straight-line segments (R2)

- `op_ok_pre`, 7009 → 7050: a work output (the word at sp + 288, the output's capacity, is not −1):
  the output's pointer (sp + 296) saved at sp + 104 and, with its length (sp + 304), stored as the
  decode's reader at sp + 1144 / 1152; ω₅ = −1, ω₆ = the capacity, ω₇ = sp + 1568 (the result),
  ω₈ = sp + 1144 (the reader).
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **7009 → 7050**, a work output (see the module doc). -/
theorem op_ok_pre {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp cp ptr len : Nat) (h1 : ω[1] = UInt64.ofNat sp)
    (hsp : 65536 ≤ sp ∧ sp + 1856 < 4294967296)
    (m288 : rdN μ (sp + 288) 8 = cp) (hcp : cp ≠ 18446744073709551615)
    (m296 : rdN μ (sp + 296) 8 = ptr) (m304 : rdN μ (sp + 304) 8 = len)
    (hrf : ∀ a, sp ≤ a → a < sp + 1856 → μ.readable a = true)
    (hwf : ∀ a, sp ≤ a → a < sp + 1856 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 7009 ω μ x 7050 ω' μ' x 11 ∧
      ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat 18446744073709551615 ∧
      ω'[6] = UInt64.ofNat cp ∧ ω'[7] = UInt64.ofNat (sp + 1568) ∧ ω'[8] = UInt64.ofNat (sp + 1144) ∧
      rdN μ' (sp + 104) 8 = ptr ∧ rdN μ' (sp + 1144) 8 = ptr ∧ rdN μ' (sp + 1152) 8 = len ∧
      (∀ a, a < 4294967296 → (a < sp + 104 ∨ sp + 112 ≤ a) → (a < sp + 1144 ∨ sp + 1160 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hcp' : ¬ (cp % 18446744073709551616 = 18446744073709551615) := by
    rw [Nat.mod_eq_of_lt (by rw [← m288]; exact rdN_lt64 _ _)]; exact hcp
  subst m296 m304
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, m288, hcp', hrf, hwf, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val; simp [h1], by reg_val, by reg_val, by reg_val, by reg_val, ?_, ?_, ?_,
      fun a ha h1 h2 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try (rd_simp []; done)
    all_goals (simp (disch := pvm_arith) only [rdN, PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same,
      Num.decodeLE_encodeLE]; try simp)
    all_goals first | exact Nat.mod_eq_of_lt (rdN_lt64 _ _) | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _) |
      (exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))) | skip
    all_goals first | rfl | exact rdN_lt64 _ _

/-- **7080 → 15361**, the decode failed (the word at sp + 1568 is ω₅ = −1): `panic`. -/
theorem od_fail {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat 18446744073709551615)
    (hsp : 65536 ≤ sp ∧ sp + 1856 < 4294967296)
    (m : rdN μ (sp + 1568) 8 = 18446744073709551615)
    (hrf : ∀ a, sp ≤ a → a < sp + 1856 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 7080 ω μ x 15361 ω' μ x 4 := by
  rw [show ω = regsNF ω [] from rfl]
  exact ⟨_, by pvm_go [h1, h5, m, hrf, ↓rdN_fold, ↓loadI_fold]⟩

/-- **7080 → 8013**, the decode succeeded with no instructions: the `Vec`'s cap to sp + 240, ω₆ (the
    output's capacity) to sp + 128, the `u16` item to sp + 176, the length 0 to sp + 248, the empty
    results `Vec` { 0, 8, 0 } at sp + 448, and the package (sp + 312 … 344) copied to sp + 512. -/
theorem od_ok0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp c : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat 18446744073709551615)
    (hsp : 65536 ≤ sp ∧ sp + 1856 < 4294967296)
    (m1568 : rdN μ (sp + 1568) 8 = c) (hc : c ≠ 18446744073709551615) (m1584 : rdN μ (sp + 1584) 8 = 0)
    (hrf : ∀ a, sp ≤ a → a < sp + 1856 → μ.readable a = true)
    (hwf : ∀ a, sp ≤ a → a < sp + 1856 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 7080 ω μ x 8013 ω' μ' x 25 ∧ ω'[1] = UInt64.ofNat sp ∧
      ω'[6] = UInt64.ofNat (rdN μ (sp + 1576) 8) ∧
      rdN μ' (sp + 240) 8 = c ∧ rdN μ' (sp + 128) 8 = ω[6].toNat ∧
      rdN μ' (sp + 176) 8 = rdN μ (sp + 1592) 2 ∧ rdN μ' (sp + 248) 8 = 0 ∧
      rdN μ' (sp + 448) 8 = 0 ∧ rdN μ' (sp + 456) 8 = 8 ∧ rdN μ' (sp + 464) 8 = 0 ∧
      rdN μ' (sp + 512) 8 = rdN μ (sp + 312) 8 ∧ rdN μ' (sp + 520) 8 = rdN μ (sp + 320) 8 ∧
      rdN μ' (sp + 528) 8 = rdN μ (sp + 328) 8 ∧ rdN μ' (sp + 536) 8 = rdN μ (sp + 336) 8 ∧
      (∀ a, a < 4294967296 → (a < sp + 128 ∨ sp + 136 ≤ a) → (a < sp + 176 ∨ sp + 184 ≤ a) →
        (a < sp + 240 ∨ sp + 256 ≤ a) → (a < sp + 448 ∨ sp + 472 ≤ a) → (a < sp + 512 ∨ sp + 544 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hc' : ¬ (c % 18446744073709551616 = 18446744073709551615) := by
    rw [Nat.mod_eq_of_lt (by rw [← m1568]; exact rdN_lt64 _ _)]; exact hc
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, m1568, hc', m1584, hrf, hwf, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val; simp [h1], by reg_val, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      fun a ha h1 h2 h3 h4 h5 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try (rd_simp []; done)
    all_goals (simp (disch := pvm_arith) only [rdN, PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same,
      Num.decodeLE_encodeLE]; try simp)
    all_goals first | rfl | decide | (exact rdN_lt64 _ _) | (exact Nat.lt_trans (rdN_lt μ _ 2) (by decide)) |
      (rw [← m1568]; exact rdN_lt64 _ _) | omega | skip

/-- **7080 → 40494**, the decode succeeded with n ≠ 0 instructions: the same stores as `od_ok0` up to
    sp + 248, then `alloc(144·n, 8)` for the results (return address 240, to 7145). -/
theorem od_okn {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp c n : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat 18446744073709551615)
    (hsp : 65536 ≤ sp ∧ sp + 1856 < 4294967296)
    (m1568 : rdN μ (sp + 1568) 8 = c) (hc : c ≠ 18446744073709551615) (m1584 : rdN μ (sp + 1584) 8 = n)
    (hn : n ≠ 0) (hn1 : n < 4294967296)
    (hrf : ∀ a, sp ≤ a → a < sp + 1856 → μ.readable a = true)
    (hwf : ∀ a, sp ≤ a → a < sp + 1856 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 7080 ω μ x 40494 ω' μ' x 17 ∧ ω'[0] = UInt64.ofNat 240 ∧
      ω'[1] = UInt64.ofNat sp ∧ ω'[7] = UInt64.ofNat (144 * n) ∧ ω'[8] = UInt64.ofNat 8 ∧
      ω'[6] = UInt64.ofNat (rdN μ (sp + 1576) 8) ∧
      rdN μ' (sp + 240) 8 = c ∧ rdN μ' (sp + 128) 8 = ω[6].toNat ∧
      rdN μ' (sp + 176) 8 = rdN μ (sp + 1592) 2 ∧ rdN μ' (sp + 248) 8 = n ∧
      (∀ a, a < 4294967296 → (a < sp + 128 ∨ sp + 136 ≤ a) → (a < sp + 176 ∨ sp + 184 ≤ a) →
        (a < sp + 240 ∨ sp + 256 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hc' : ¬ (c % 18446744073709551616 = 18446744073709551615) := by
    rw [Nat.mod_eq_of_lt (by rw [← m1568]; exact rdN_lt64 _ _)]; exact hc
  have hn' : n % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt (by omega)]; exact hn
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, m1568, hc', m1584, hn', hrf, hwf, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, by reg_val; simp [h1], ?_, by reg_val, by reg_val, ?_, ?_, ?_, ?_,
      fun a ha h1 h2 h3 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try (rd_simp []; done)
    all_goals (simp (disch := pvm_arith) only [rdN, PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same,
      Num.decodeLE_encodeLE]; try simp)
    · reg_val
      apply UInt64.toNat.inj
      simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat]
      omega
    all_goals first | rfl | decide | (exact rdN_lt64 _ _) | (exact Nat.lt_trans (rdN_lt μ _ 2) (by decide)) |
      (rw [← m1568]; exact rdN_lt64 _ _) | omega | skip

/-- `alloc`'s return (40611) to 7145 (ω₀ = 240). -/
theorem od_j240 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (h0 : ω[0] = UInt64.ofNat 240) : FreeStepsH p R 40611 ω μ x 7145 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0]

/-- **7145 → 15364**, the results' `alloc` returned null: the allocation-failure trap. -/
theorem od_null {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (h7 : ω[7] = UInt64.ofNat 0) : ∃ ω', FreeStepsH p R 7145 ω μ x 15364 ω' μ x 3 := by
  rw [show ω = regsNF ω [] from rfl]
  exact ⟨_, by pvm_go [h7]⟩

/-- **7145 → 8013**, the results' block r ≠ 0: the results `Vec` { n, r, 0 } at sp + 448 (n from
    sp + 248) and the package (sp + 312 … 344) copied to sp + 512. -/
theorem od_alloc {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp r n : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat r) (hr0 : r ≠ 0)
    (hr : r < 4294967296) (hsp : 65536 ≤ sp ∧ sp + 1856 < 4294967296) (m248 : rdN μ (sp + 248) 8 = n)
    (hrf : ∀ a, sp ≤ a → a < sp + 1856 → μ.readable a = true)
    (hwf : ∀ a, sp ≤ a → a < sp + 1856 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 7145 ω μ x 8013 ω' μ' x 16 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[6] = ω[6] ∧
      rdN μ' (sp + 448) 8 = n ∧ rdN μ' (sp + 456) 8 = r ∧ rdN μ' (sp + 464) 8 = 0 ∧
      rdN μ' (sp + 512) 8 = rdN μ (sp + 312) 8 ∧ rdN μ' (sp + 520) 8 = rdN μ (sp + 320) 8 ∧
      rdN μ' (sp + 528) 8 = rdN μ (sp + 328) 8 ∧ rdN μ' (sp + 536) 8 = rdN μ (sp + 336) 8 ∧
      (∀ a, a < 4294967296 → (a < sp + 448 ∨ sp + 472 ≤ a) → (a < sp + 512 ∨ sp + 544 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr0' : r % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt (by omega)]; exact hr0
  subst m248
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h7, hr0', hrf, hwf, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val; simp [h1], by reg_val, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_,
      fun a => ?_⟩
    all_goals try (rd_simp []; done)
    all_goals (simp (disch := pvm_arith) only [rdN, PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same,
      Num.decodeLE_encodeLE]; try simp)
    all_goals first | exact Nat.mod_eq_of_lt (rdN_lt64 _ _) | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _) |
      (exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))) | skip
    all_goals first | rfl | exact rdN_lt64 _ _ | omega

end Services.Bootstrap.Acc
