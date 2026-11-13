import Services.Bootstrap.Acc.Inputs.FetchVec

/-!
# `on_transfer`'s count: "transfer-count" decoded (7237 → 7326)

Spec: `n := ((← op (AOp.read key)).bind (decode (Dec.fixedN 4))).getD 0` (quirk Q12). After the
helper `get` leaves `Option<Vec<u8>>` at sp + 1568:
- `None` (capacity −1): n = 0 (`trd_none`);
- else a slice reader over the value at sp + 744 and `read_exact` of 4 octets into sp + 1568
  (`trd_some`, 58434, return 246 → 7288); the value's buffer freed when its capacity is not 0
  (`trd_free`, `trd_nofree`, `trd_back`); then n = the u32 read, or 0 if `read_exact` failed (a value
  shorter than 4 octets) (`trd_n`). Trailing octets are ignored, as `decode` does.
-/

namespace Services.Bootstrap.Acc
open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
variable {X : Type} {R : HostRel X}

/-- **7237 … 7326**, "transfer-count" absent (`None` at sp + 1568): n = 0 in ω₆. -/
theorem trd_none {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : 65536 ≤ sp ∧ sp + 1856 < 4294967296)
    (m : μ.readN (sp + 1568) 8 = Num.encodeLE 8 18446744073709551615)
    (hrf : ∀ a, sp ≤ a → a < sp + 1856 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 7237 ω μ x 7326 ω' μ x 6 ∧ ω'[6] = UInt64.ofNat 0 ∧
      ∀ j : Fin 13, j.val ∉ [5, 6] → ω'[j] = ω[j] := by
  have q : rdN μ (sp + 1568) 8 = 18446744073709551615 := by unfold rdN; rw [m]; decide
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, q, hrf, ↓rdN_fold]
  case post => exact ⟨by reg_val, by reg_frame⟩

/-- **7237 … 58434**, "transfer-count" present (`Some(Vec { cap, ptr, len })` at sp + 1568, cap ≠ −1):
    ptr saved at sp + 248, the reader (ptr, len) at sp + 744, the u32 0 at sp + 1568, and the call of
    `read_exact(sp + 744, sp + 1568, 4)` (return address 246); ω₅ = cap. -/
theorem trd_some {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp cap ptr len : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : 65536 ≤ sp ∧ sp + 1856 < 4294967296)
    (m0 : μ.readN (sp + 1568) 8 = Num.encodeLE 8 cap) (m8 : μ.readN (sp + 1576) 8 = Num.encodeLE 8 ptr)
    (m16 : μ.readN (sp + 1584) 8 = Num.encodeLE 8 len) (hc : cap < 18446744073709551615)
    (hp : ptr < 18446744073709551616) (hl : len < 18446744073709551616)
    (hwf : ∀ a, sp ≤ a → a < sp + 1856 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 7237 ω μ x 58434 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat 246 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat cap ∧
      ω'[7] = UInt64.ofNat (sp + 744) ∧ ω'[8] = UInt64.ofNat (sp + 1568) ∧ ω'[9] = UInt64.ofNat 4 ∧
      rdN μ' (sp + 744) 8 = ptr ∧ rdN μ' (sp + 752) 8 = len ∧ rdN μ' (sp + 248) 8 = ptr ∧
      (∀ a, a < 4294967296 → (a < sp + 248 ∨ sp + 256 ≤ a) → (a < sp + 744 ∨ sp + 760 ≤ a) →
        (a < sp + 1568 ∨ sp + 1572 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      ∀ j : Fin 13, j.val ∉ [0, 5, 7, 8, 9] → ω'[j] = ω[j] := by
  have hr : ∀ a, sp ≤ a → a < sp + 1856 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have q0 : rdN μ (sp + 1568) 8 = cap := by unfold rdN; rw [m0, Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt (by omega)
  have q8 : rdN μ (sp + 1576) 8 = ptr := by unfold rdN; rw [m8, Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt hp
  have q16 : rdN μ (sp + 1584) 8 = len := by unfold rdN; rw [m16, Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt hl
  have hc' : cap % 18446744073709551616 ≠ 18446744073709551615 := by rw [Nat.mod_eq_of_lt (by omega)]; omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, q0, q8, q16, hc', hwf, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, (by reg_val <;> exact h1), (by reg_val; try rw [Nat.mod_eq_of_lt (by omega)]), by reg_val,
      by reg_val, by reg_val, ?_, ?_, ?_, fun a ha h1 h2 h3 => ?_, fun a => ?_, fun a => ?_, by reg_frame⟩
    all_goals try simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']
    all_goals try (simp (disch := pvm_arith) only [rdN, PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same,
      Num.decodeLE_encodeLE])
    all_goals try (simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint]; done)
    all_goals try (simp only [Memory.readable_writeN, Memory.writable_writeN])
    all_goals first | rfl | decide | exact Nat.mod_eq_of_lt (by omega) | skip

/-- **7288 … 40613**, after `read_exact`, the value's capacity cap ≠ 0: ω₆ = the i32 at sp + 1568,
    `read_exact`'s result ω₇ saved at sp + 240, and the call of `dealloc` on ptr (from sp + 248), size
    cap, align 1 (return address 248). -/
theorem trd_free {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp cap ptr : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat cap)
    (hsp : 65536 ≤ sp ∧ sp + 1856 < 4294967296) (hc : cap ≠ 0) (hc64 : cap < 18446744073709551616)
    (m248 : rdN μ (sp + 248) 8 = ptr) (hwf : ∀ a, sp ≤ a → a < sp + 1856 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 7288 ω μ x 40613 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 248 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[7] = UInt64.ofNat ptr ∧
      ω'[6] = UInt64.ofNat (sxw 4 (rdN μ (sp + 1568) 4)) ∧
      rdN μ' (sp + 240) 8 = ω[7].toNat ∧
      (∀ a, a < 4294967296 → (a < sp + 240 ∨ sp + 248 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp ≤ a → a < sp + 1856 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have hc' : cap % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt hc64]; exact hc
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, hc', m248, hwf, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, (by reg_val <;> exact h1), ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']
    all_goals try (simp (disch := pvm_arith) only [rdN, PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same,
      Num.decodeLE_encodeLE, rdN_writeN_disjoint, m248])
    all_goals try (simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint]; done)
    all_goals try (simp only [Memory.readable_writeN, Memory.writable_writeN])
    all_goals first | rfl | decide | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _) | skip

/-- **7288 … 7320**, the value's capacity 0: no `dealloc`; ω₆ = the i32 at sp + 1568. -/
theorem trd_nofree {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat 0)
    (hsp : 65536 ≤ sp ∧ sp + 1856 < 4294967296) (hrf : ∀ a, sp ≤ a → a < sp + 1856 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 7288 ω μ x 7320 ω' μ x 3 ∧
      ω'[6] = UInt64.ofNat (sxw 4 (rdN μ (sp + 1568) 4)) ∧
      ∀ j : Fin 13, j.val ∉ [6] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, h5, hrf, ↓rdN_fold, ↓loadI_fold]
  case post => exact ⟨by reg_val, by reg_frame⟩

/-- **7315 … 7320**: `read_exact`'s result back in ω₇ (from sp + 240). -/
theorem trd_back {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : 65536 ≤ sp ∧ sp + 1856 < 4294967296)
    (hrf : ∀ a, sp ≤ a → a < sp + 1856 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 7315 ω μ x 7320 ω' μ x 3 ∧ ω'[7] = UInt64.ofNat (rdN μ (sp + 240) 8) ∧
      ∀ j : Fin 13, j.val ∉ [7] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, hrf, ↓rdN_fold]
  case post => exact ⟨by reg_val, by reg_frame⟩

/-- **7320 … 7326**: `read_exact` succeeded (ω₇ = 0): n = ω₆ as decoded; it failed: n = 0
    (`.getD 0`, quirk Q12). -/
theorem trd_n {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (r : Nat) (h7 : ω[7] = UInt64.ofNat r) (hr : r < 18446744073709551616) :
    ∃ ω', FreeStepsH p R 7320 ω μ x 7326 ω' μ x 3 ∧
      ω'[6] = (if r = 0 then ω[6] else UInt64.ofNat 0) ∧ ∀ j : Fin 13, j.val ∉ [6] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  by_cases h0 : r = 0
  · subst h0
    refine ⟨?ω', ?run, ?post⟩
    case run => pvm_go [h7]
    case post => exact ⟨by simp, fun j _ => rfl⟩
  · have h0' : r % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt hr]; exact h0
    refine ⟨?ω2, ?run2, ?post2⟩
    case run2 => pvm_go [h7, h0']
    case post2 => exact ⟨by rw [if_neg h0]; reg_val, by reg_frame⟩

end Services.Bootstrap.Acc
