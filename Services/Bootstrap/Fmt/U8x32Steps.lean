import Services.Bootstrap.Fmt.Tac

/-!
# `<&[u8; 32] as fmt::Debug>::fmt` (36529, then 37996): the steps

36529 follows the slot at v to the array's address a and jumps to `<[u8; 32] as Debug>::fmt`
(37996). That opens a frame T = sp − 48 (ω₀, ω₅, ω₆ saved at T + 40, T + 32, T + 24), calls
`Formatter::debug_list` (61708) with the `DebugList` at T, then makes 32 calls of `DebugList::entry`
(66019), unrolled: entry i stores a + i in the slot T + 16 and passes it with the vtable 75976
(`<&u8 as Debug>`). The return addresses are 1818 (→ 38018), 1820 + 2i (→ 38042 + 19i, i ≤ 30),
1882 (→ 38631) and 1884 (→ 38639). Then `DebugList::finish` (66310) and the return.

- `a8_a`: 36529 … 38012, to `debug_list`;
- `a8_e0`: 38018 … 38036, entry 0; `a8_e i` (1 ≤ i ≤ 30): 38042 + 19(i − 1), entry i (from the
  generated `a8_e1` … `a8_e30`); `a8_e31`: 38612, entry 31 (it also sets ω₅ := a + 31);
- `a8_jt i`: the return of entry i (i ≤ 30);
- `a8_f`: 38631, to `finish`; `a8_r`: 38639 … 38651, the return.
-/

namespace Services.Bootstrap.Fmt

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 36529 … 38012: the slot v's word a; the frame T = sp − 48 with ω₀, ω₅, ω₆ saved; on to
    `Formatter::debug_list` (61708) with the `DebugList` at T and F (ω₈ kept). -/
theorem a8_a {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v a r0 v5 v6 : Nat) (hsp : 196608 + 48 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat v)
    (hv : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616 ∧
      v + 8 < 4294967296)
    (ra : rdN μ v 8 = a) (hrv : ∀ c, v ≤ c → c < v + 8 → μ.readable c = true)
    (hw : ∀ c, sp - 48 ≤ c → c < sp → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R 36529 ω μ x 61708 ω' μ' x 9 ∧
      ω'[0] = UInt64.ofNat 1818 ∧ ω'[1] = UInt64.ofNat (sp - 48) ∧ ω'[5] = UInt64.ofNat a ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat (sp - 48) ∧ ω'[8] = ω[8] ∧
      rdN μ' (sp - 48 + 40) 8 = r0 ∧ rdN μ' (sp - 48 + 32) 8 = v5 ∧ rdN μ' (sp - 48 + 24) 8 = v6 ∧
      (∀ c, c < 4294967296 → (c < sp - 24 ∨ sp ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, sp - 48 ≤ c → c < sp → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  have ha : a < 18446744073709551616 := ra ▸ rdN_lt64 μ v
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, hsp, hv, ra, hrv, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h0, h1, h5, h6, h7,
      Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt hv.2.2.1, Nat.mod_eq_of_lt ha, ra]

/-- 38018 … 38036: entry 0: a in the slot T + 16; on to `DebugList::entry` (66019) with the
    `DebugList` T, the slot and the vtable 75976 (also kept in ω₆). -/
theorem a8_e0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T a : Nat) (hT : 65536 ≤ T ∧ T + 48 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat a) (ha : a < 18446744073709551616)
    (hw : ∀ c, T ≤ c → c < T + 48 → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R 38018 ω μ x 66019 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 1820 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = UInt64.ofNat 75976 ∧
      ω'[7] = UInt64.ofNat T ∧ ω'[8] = UInt64.ofNat (T + 16) ∧ ω'[9] = UInt64.ofNat 75976 ∧
      rdN μ' (T + 16) 8 = a ∧
      (∀ c, c < 4294967296 → (c < T + 16 ∨ T + 24 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, T ≤ c → c < T + 48 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hT, ha, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h5, Nat.mod_eq_of_lt ha]

theorem a8_e1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T a : Nat) (hT : 65536 ≤ T ∧ T + 48 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat a) (h6 : ω[6] = UInt64.ofNat 75976) (ha : a + 31 < 18446744073709551616)
    (hw : ∀ c, T ≤ c → c < T + 48 → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R 38042 ω μ x 66019 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 1822 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat T ∧ ω'[8] = UInt64.ofNat (T + 16) ∧ ω'[9] = UInt64.ofNat 75976 ∧
      rdN μ' (T + 16) 8 = a + 1 ∧
      (∀ c, c < 4294967296 → (c < T + 16 ∨ T + 24 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, T ≤ c → c < T + 48 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hT, ha, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h5, h6,
      Nat.mod_eq_of_lt (show a + 1 < 18446744073709551616 by omega)]

theorem a8_e2 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T a : Nat) (hT : 65536 ≤ T ∧ T + 48 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat a) (h6 : ω[6] = UInt64.ofNat 75976) (ha : a + 31 < 18446744073709551616)
    (hw : ∀ c, T ≤ c → c < T + 48 → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R 38061 ω μ x 66019 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 1824 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat T ∧ ω'[8] = UInt64.ofNat (T + 16) ∧ ω'[9] = UInt64.ofNat 75976 ∧
      rdN μ' (T + 16) 8 = a + 2 ∧
      (∀ c, c < 4294967296 → (c < T + 16 ∨ T + 24 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, T ≤ c → c < T + 48 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hT, ha, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h5, h6,
      Nat.mod_eq_of_lt (show a + 2 < 18446744073709551616 by omega)]

theorem a8_e3 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T a : Nat) (hT : 65536 ≤ T ∧ T + 48 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat a) (h6 : ω[6] = UInt64.ofNat 75976) (ha : a + 31 < 18446744073709551616)
    (hw : ∀ c, T ≤ c → c < T + 48 → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R 38080 ω μ x 66019 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 1826 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat T ∧ ω'[8] = UInt64.ofNat (T + 16) ∧ ω'[9] = UInt64.ofNat 75976 ∧
      rdN μ' (T + 16) 8 = a + 3 ∧
      (∀ c, c < 4294967296 → (c < T + 16 ∨ T + 24 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, T ≤ c → c < T + 48 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hT, ha, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h5, h6,
      Nat.mod_eq_of_lt (show a + 3 < 18446744073709551616 by omega)]

theorem a8_e4 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T a : Nat) (hT : 65536 ≤ T ∧ T + 48 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat a) (h6 : ω[6] = UInt64.ofNat 75976) (ha : a + 31 < 18446744073709551616)
    (hw : ∀ c, T ≤ c → c < T + 48 → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R 38099 ω μ x 66019 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 1828 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat T ∧ ω'[8] = UInt64.ofNat (T + 16) ∧ ω'[9] = UInt64.ofNat 75976 ∧
      rdN μ' (T + 16) 8 = a + 4 ∧
      (∀ c, c < 4294967296 → (c < T + 16 ∨ T + 24 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, T ≤ c → c < T + 48 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hT, ha, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h5, h6,
      Nat.mod_eq_of_lt (show a + 4 < 18446744073709551616 by omega)]

theorem a8_e5 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T a : Nat) (hT : 65536 ≤ T ∧ T + 48 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat a) (h6 : ω[6] = UInt64.ofNat 75976) (ha : a + 31 < 18446744073709551616)
    (hw : ∀ c, T ≤ c → c < T + 48 → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R 38118 ω μ x 66019 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 1830 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat T ∧ ω'[8] = UInt64.ofNat (T + 16) ∧ ω'[9] = UInt64.ofNat 75976 ∧
      rdN μ' (T + 16) 8 = a + 5 ∧
      (∀ c, c < 4294967296 → (c < T + 16 ∨ T + 24 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, T ≤ c → c < T + 48 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hT, ha, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h5, h6,
      Nat.mod_eq_of_lt (show a + 5 < 18446744073709551616 by omega)]

theorem a8_e6 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T a : Nat) (hT : 65536 ≤ T ∧ T + 48 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat a) (h6 : ω[6] = UInt64.ofNat 75976) (ha : a + 31 < 18446744073709551616)
    (hw : ∀ c, T ≤ c → c < T + 48 → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R 38137 ω μ x 66019 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 1832 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat T ∧ ω'[8] = UInt64.ofNat (T + 16) ∧ ω'[9] = UInt64.ofNat 75976 ∧
      rdN μ' (T + 16) 8 = a + 6 ∧
      (∀ c, c < 4294967296 → (c < T + 16 ∨ T + 24 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, T ≤ c → c < T + 48 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hT, ha, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h5, h6,
      Nat.mod_eq_of_lt (show a + 6 < 18446744073709551616 by omega)]

theorem a8_e7 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T a : Nat) (hT : 65536 ≤ T ∧ T + 48 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat a) (h6 : ω[6] = UInt64.ofNat 75976) (ha : a + 31 < 18446744073709551616)
    (hw : ∀ c, T ≤ c → c < T + 48 → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R 38156 ω μ x 66019 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 1834 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat T ∧ ω'[8] = UInt64.ofNat (T + 16) ∧ ω'[9] = UInt64.ofNat 75976 ∧
      rdN μ' (T + 16) 8 = a + 7 ∧
      (∀ c, c < 4294967296 → (c < T + 16 ∨ T + 24 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, T ≤ c → c < T + 48 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hT, ha, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h5, h6,
      Nat.mod_eq_of_lt (show a + 7 < 18446744073709551616 by omega)]

theorem a8_e8 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T a : Nat) (hT : 65536 ≤ T ∧ T + 48 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat a) (h6 : ω[6] = UInt64.ofNat 75976) (ha : a + 31 < 18446744073709551616)
    (hw : ∀ c, T ≤ c → c < T + 48 → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R 38175 ω μ x 66019 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 1836 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat T ∧ ω'[8] = UInt64.ofNat (T + 16) ∧ ω'[9] = UInt64.ofNat 75976 ∧
      rdN μ' (T + 16) 8 = a + 8 ∧
      (∀ c, c < 4294967296 → (c < T + 16 ∨ T + 24 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, T ≤ c → c < T + 48 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hT, ha, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h5, h6,
      Nat.mod_eq_of_lt (show a + 8 < 18446744073709551616 by omega)]

theorem a8_e9 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T a : Nat) (hT : 65536 ≤ T ∧ T + 48 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat a) (h6 : ω[6] = UInt64.ofNat 75976) (ha : a + 31 < 18446744073709551616)
    (hw : ∀ c, T ≤ c → c < T + 48 → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R 38194 ω μ x 66019 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 1838 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat T ∧ ω'[8] = UInt64.ofNat (T + 16) ∧ ω'[9] = UInt64.ofNat 75976 ∧
      rdN μ' (T + 16) 8 = a + 9 ∧
      (∀ c, c < 4294967296 → (c < T + 16 ∨ T + 24 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, T ≤ c → c < T + 48 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hT, ha, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h5, h6,
      Nat.mod_eq_of_lt (show a + 9 < 18446744073709551616 by omega)]

theorem a8_e10 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T a : Nat) (hT : 65536 ≤ T ∧ T + 48 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat a) (h6 : ω[6] = UInt64.ofNat 75976) (ha : a + 31 < 18446744073709551616)
    (hw : ∀ c, T ≤ c → c < T + 48 → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R 38213 ω μ x 66019 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 1840 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat T ∧ ω'[8] = UInt64.ofNat (T + 16) ∧ ω'[9] = UInt64.ofNat 75976 ∧
      rdN μ' (T + 16) 8 = a + 10 ∧
      (∀ c, c < 4294967296 → (c < T + 16 ∨ T + 24 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, T ≤ c → c < T + 48 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hT, ha, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h5, h6,
      Nat.mod_eq_of_lt (show a + 10 < 18446744073709551616 by omega)]

theorem a8_e11 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T a : Nat) (hT : 65536 ≤ T ∧ T + 48 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat a) (h6 : ω[6] = UInt64.ofNat 75976) (ha : a + 31 < 18446744073709551616)
    (hw : ∀ c, T ≤ c → c < T + 48 → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R 38232 ω μ x 66019 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 1842 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat T ∧ ω'[8] = UInt64.ofNat (T + 16) ∧ ω'[9] = UInt64.ofNat 75976 ∧
      rdN μ' (T + 16) 8 = a + 11 ∧
      (∀ c, c < 4294967296 → (c < T + 16 ∨ T + 24 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, T ≤ c → c < T + 48 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hT, ha, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h5, h6,
      Nat.mod_eq_of_lt (show a + 11 < 18446744073709551616 by omega)]

theorem a8_e12 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T a : Nat) (hT : 65536 ≤ T ∧ T + 48 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat a) (h6 : ω[6] = UInt64.ofNat 75976) (ha : a + 31 < 18446744073709551616)
    (hw : ∀ c, T ≤ c → c < T + 48 → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R 38251 ω μ x 66019 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 1844 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat T ∧ ω'[8] = UInt64.ofNat (T + 16) ∧ ω'[9] = UInt64.ofNat 75976 ∧
      rdN μ' (T + 16) 8 = a + 12 ∧
      (∀ c, c < 4294967296 → (c < T + 16 ∨ T + 24 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, T ≤ c → c < T + 48 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hT, ha, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h5, h6,
      Nat.mod_eq_of_lt (show a + 12 < 18446744073709551616 by omega)]

theorem a8_e13 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T a : Nat) (hT : 65536 ≤ T ∧ T + 48 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat a) (h6 : ω[6] = UInt64.ofNat 75976) (ha : a + 31 < 18446744073709551616)
    (hw : ∀ c, T ≤ c → c < T + 48 → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R 38270 ω μ x 66019 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 1846 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat T ∧ ω'[8] = UInt64.ofNat (T + 16) ∧ ω'[9] = UInt64.ofNat 75976 ∧
      rdN μ' (T + 16) 8 = a + 13 ∧
      (∀ c, c < 4294967296 → (c < T + 16 ∨ T + 24 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, T ≤ c → c < T + 48 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hT, ha, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h5, h6,
      Nat.mod_eq_of_lt (show a + 13 < 18446744073709551616 by omega)]

theorem a8_e14 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T a : Nat) (hT : 65536 ≤ T ∧ T + 48 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat a) (h6 : ω[6] = UInt64.ofNat 75976) (ha : a + 31 < 18446744073709551616)
    (hw : ∀ c, T ≤ c → c < T + 48 → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R 38289 ω μ x 66019 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 1848 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat T ∧ ω'[8] = UInt64.ofNat (T + 16) ∧ ω'[9] = UInt64.ofNat 75976 ∧
      rdN μ' (T + 16) 8 = a + 14 ∧
      (∀ c, c < 4294967296 → (c < T + 16 ∨ T + 24 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, T ≤ c → c < T + 48 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hT, ha, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h5, h6,
      Nat.mod_eq_of_lt (show a + 14 < 18446744073709551616 by omega)]

theorem a8_e15 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T a : Nat) (hT : 65536 ≤ T ∧ T + 48 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat a) (h6 : ω[6] = UInt64.ofNat 75976) (ha : a + 31 < 18446744073709551616)
    (hw : ∀ c, T ≤ c → c < T + 48 → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R 38308 ω μ x 66019 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 1850 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat T ∧ ω'[8] = UInt64.ofNat (T + 16) ∧ ω'[9] = UInt64.ofNat 75976 ∧
      rdN μ' (T + 16) 8 = a + 15 ∧
      (∀ c, c < 4294967296 → (c < T + 16 ∨ T + 24 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, T ≤ c → c < T + 48 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hT, ha, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h5, h6,
      Nat.mod_eq_of_lt (show a + 15 < 18446744073709551616 by omega)]

theorem a8_e16 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T a : Nat) (hT : 65536 ≤ T ∧ T + 48 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat a) (h6 : ω[6] = UInt64.ofNat 75976) (ha : a + 31 < 18446744073709551616)
    (hw : ∀ c, T ≤ c → c < T + 48 → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R 38327 ω μ x 66019 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 1852 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat T ∧ ω'[8] = UInt64.ofNat (T + 16) ∧ ω'[9] = UInt64.ofNat 75976 ∧
      rdN μ' (T + 16) 8 = a + 16 ∧
      (∀ c, c < 4294967296 → (c < T + 16 ∨ T + 24 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, T ≤ c → c < T + 48 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hT, ha, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h5, h6,
      Nat.mod_eq_of_lt (show a + 16 < 18446744073709551616 by omega)]

theorem a8_e17 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T a : Nat) (hT : 65536 ≤ T ∧ T + 48 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat a) (h6 : ω[6] = UInt64.ofNat 75976) (ha : a + 31 < 18446744073709551616)
    (hw : ∀ c, T ≤ c → c < T + 48 → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R 38346 ω μ x 66019 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 1854 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat T ∧ ω'[8] = UInt64.ofNat (T + 16) ∧ ω'[9] = UInt64.ofNat 75976 ∧
      rdN μ' (T + 16) 8 = a + 17 ∧
      (∀ c, c < 4294967296 → (c < T + 16 ∨ T + 24 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, T ≤ c → c < T + 48 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hT, ha, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h5, h6,
      Nat.mod_eq_of_lt (show a + 17 < 18446744073709551616 by omega)]

theorem a8_e18 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T a : Nat) (hT : 65536 ≤ T ∧ T + 48 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat a) (h6 : ω[6] = UInt64.ofNat 75976) (ha : a + 31 < 18446744073709551616)
    (hw : ∀ c, T ≤ c → c < T + 48 → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R 38365 ω μ x 66019 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 1856 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat T ∧ ω'[8] = UInt64.ofNat (T + 16) ∧ ω'[9] = UInt64.ofNat 75976 ∧
      rdN μ' (T + 16) 8 = a + 18 ∧
      (∀ c, c < 4294967296 → (c < T + 16 ∨ T + 24 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, T ≤ c → c < T + 48 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hT, ha, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h5, h6,
      Nat.mod_eq_of_lt (show a + 18 < 18446744073709551616 by omega)]

theorem a8_e19 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T a : Nat) (hT : 65536 ≤ T ∧ T + 48 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat a) (h6 : ω[6] = UInt64.ofNat 75976) (ha : a + 31 < 18446744073709551616)
    (hw : ∀ c, T ≤ c → c < T + 48 → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R 38384 ω μ x 66019 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 1858 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat T ∧ ω'[8] = UInt64.ofNat (T + 16) ∧ ω'[9] = UInt64.ofNat 75976 ∧
      rdN μ' (T + 16) 8 = a + 19 ∧
      (∀ c, c < 4294967296 → (c < T + 16 ∨ T + 24 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, T ≤ c → c < T + 48 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hT, ha, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h5, h6,
      Nat.mod_eq_of_lt (show a + 19 < 18446744073709551616 by omega)]

theorem a8_e20 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T a : Nat) (hT : 65536 ≤ T ∧ T + 48 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat a) (h6 : ω[6] = UInt64.ofNat 75976) (ha : a + 31 < 18446744073709551616)
    (hw : ∀ c, T ≤ c → c < T + 48 → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R 38403 ω μ x 66019 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 1860 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat T ∧ ω'[8] = UInt64.ofNat (T + 16) ∧ ω'[9] = UInt64.ofNat 75976 ∧
      rdN μ' (T + 16) 8 = a + 20 ∧
      (∀ c, c < 4294967296 → (c < T + 16 ∨ T + 24 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, T ≤ c → c < T + 48 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hT, ha, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h5, h6,
      Nat.mod_eq_of_lt (show a + 20 < 18446744073709551616 by omega)]

theorem a8_e21 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T a : Nat) (hT : 65536 ≤ T ∧ T + 48 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat a) (h6 : ω[6] = UInt64.ofNat 75976) (ha : a + 31 < 18446744073709551616)
    (hw : ∀ c, T ≤ c → c < T + 48 → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R 38422 ω μ x 66019 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 1862 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat T ∧ ω'[8] = UInt64.ofNat (T + 16) ∧ ω'[9] = UInt64.ofNat 75976 ∧
      rdN μ' (T + 16) 8 = a + 21 ∧
      (∀ c, c < 4294967296 → (c < T + 16 ∨ T + 24 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, T ≤ c → c < T + 48 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hT, ha, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h5, h6,
      Nat.mod_eq_of_lt (show a + 21 < 18446744073709551616 by omega)]

theorem a8_e22 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T a : Nat) (hT : 65536 ≤ T ∧ T + 48 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat a) (h6 : ω[6] = UInt64.ofNat 75976) (ha : a + 31 < 18446744073709551616)
    (hw : ∀ c, T ≤ c → c < T + 48 → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R 38441 ω μ x 66019 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 1864 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat T ∧ ω'[8] = UInt64.ofNat (T + 16) ∧ ω'[9] = UInt64.ofNat 75976 ∧
      rdN μ' (T + 16) 8 = a + 22 ∧
      (∀ c, c < 4294967296 → (c < T + 16 ∨ T + 24 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, T ≤ c → c < T + 48 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hT, ha, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h5, h6,
      Nat.mod_eq_of_lt (show a + 22 < 18446744073709551616 by omega)]

theorem a8_e23 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T a : Nat) (hT : 65536 ≤ T ∧ T + 48 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat a) (h6 : ω[6] = UInt64.ofNat 75976) (ha : a + 31 < 18446744073709551616)
    (hw : ∀ c, T ≤ c → c < T + 48 → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R 38460 ω μ x 66019 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 1866 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat T ∧ ω'[8] = UInt64.ofNat (T + 16) ∧ ω'[9] = UInt64.ofNat 75976 ∧
      rdN μ' (T + 16) 8 = a + 23 ∧
      (∀ c, c < 4294967296 → (c < T + 16 ∨ T + 24 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, T ≤ c → c < T + 48 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hT, ha, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h5, h6,
      Nat.mod_eq_of_lt (show a + 23 < 18446744073709551616 by omega)]

theorem a8_e24 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T a : Nat) (hT : 65536 ≤ T ∧ T + 48 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat a) (h6 : ω[6] = UInt64.ofNat 75976) (ha : a + 31 < 18446744073709551616)
    (hw : ∀ c, T ≤ c → c < T + 48 → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R 38479 ω μ x 66019 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 1868 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat T ∧ ω'[8] = UInt64.ofNat (T + 16) ∧ ω'[9] = UInt64.ofNat 75976 ∧
      rdN μ' (T + 16) 8 = a + 24 ∧
      (∀ c, c < 4294967296 → (c < T + 16 ∨ T + 24 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, T ≤ c → c < T + 48 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hT, ha, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h5, h6,
      Nat.mod_eq_of_lt (show a + 24 < 18446744073709551616 by omega)]

theorem a8_e25 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T a : Nat) (hT : 65536 ≤ T ∧ T + 48 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat a) (h6 : ω[6] = UInt64.ofNat 75976) (ha : a + 31 < 18446744073709551616)
    (hw : ∀ c, T ≤ c → c < T + 48 → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R 38498 ω μ x 66019 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 1870 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat T ∧ ω'[8] = UInt64.ofNat (T + 16) ∧ ω'[9] = UInt64.ofNat 75976 ∧
      rdN μ' (T + 16) 8 = a + 25 ∧
      (∀ c, c < 4294967296 → (c < T + 16 ∨ T + 24 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, T ≤ c → c < T + 48 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hT, ha, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h5, h6,
      Nat.mod_eq_of_lt (show a + 25 < 18446744073709551616 by omega)]

theorem a8_e26 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T a : Nat) (hT : 65536 ≤ T ∧ T + 48 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat a) (h6 : ω[6] = UInt64.ofNat 75976) (ha : a + 31 < 18446744073709551616)
    (hw : ∀ c, T ≤ c → c < T + 48 → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R 38517 ω μ x 66019 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 1872 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat T ∧ ω'[8] = UInt64.ofNat (T + 16) ∧ ω'[9] = UInt64.ofNat 75976 ∧
      rdN μ' (T + 16) 8 = a + 26 ∧
      (∀ c, c < 4294967296 → (c < T + 16 ∨ T + 24 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, T ≤ c → c < T + 48 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hT, ha, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h5, h6,
      Nat.mod_eq_of_lt (show a + 26 < 18446744073709551616 by omega)]

theorem a8_e27 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T a : Nat) (hT : 65536 ≤ T ∧ T + 48 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat a) (h6 : ω[6] = UInt64.ofNat 75976) (ha : a + 31 < 18446744073709551616)
    (hw : ∀ c, T ≤ c → c < T + 48 → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R 38536 ω μ x 66019 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 1874 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat T ∧ ω'[8] = UInt64.ofNat (T + 16) ∧ ω'[9] = UInt64.ofNat 75976 ∧
      rdN μ' (T + 16) 8 = a + 27 ∧
      (∀ c, c < 4294967296 → (c < T + 16 ∨ T + 24 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, T ≤ c → c < T + 48 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hT, ha, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h5, h6,
      Nat.mod_eq_of_lt (show a + 27 < 18446744073709551616 by omega)]

theorem a8_e28 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T a : Nat) (hT : 65536 ≤ T ∧ T + 48 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat a) (h6 : ω[6] = UInt64.ofNat 75976) (ha : a + 31 < 18446744073709551616)
    (hw : ∀ c, T ≤ c → c < T + 48 → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R 38555 ω μ x 66019 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 1876 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat T ∧ ω'[8] = UInt64.ofNat (T + 16) ∧ ω'[9] = UInt64.ofNat 75976 ∧
      rdN μ' (T + 16) 8 = a + 28 ∧
      (∀ c, c < 4294967296 → (c < T + 16 ∨ T + 24 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, T ≤ c → c < T + 48 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hT, ha, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h5, h6,
      Nat.mod_eq_of_lt (show a + 28 < 18446744073709551616 by omega)]

theorem a8_e29 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T a : Nat) (hT : 65536 ≤ T ∧ T + 48 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat a) (h6 : ω[6] = UInt64.ofNat 75976) (ha : a + 31 < 18446744073709551616)
    (hw : ∀ c, T ≤ c → c < T + 48 → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R 38574 ω μ x 66019 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 1878 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat T ∧ ω'[8] = UInt64.ofNat (T + 16) ∧ ω'[9] = UInt64.ofNat 75976 ∧
      rdN μ' (T + 16) 8 = a + 29 ∧
      (∀ c, c < 4294967296 → (c < T + 16 ∨ T + 24 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, T ≤ c → c < T + 48 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hT, ha, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h5, h6,
      Nat.mod_eq_of_lt (show a + 29 < 18446744073709551616 by omega)]

theorem a8_e30 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T a : Nat) (hT : 65536 ≤ T ∧ T + 48 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat a) (h6 : ω[6] = UInt64.ofNat 75976) (ha : a + 31 < 18446744073709551616)
    (hw : ∀ c, T ≤ c → c < T + 48 → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R 38593 ω μ x 66019 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 1880 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat T ∧ ω'[8] = UInt64.ofNat (T + 16) ∧ ω'[9] = UInt64.ofNat 75976 ∧
      rdN μ' (T + 16) 8 = a + 30 ∧
      (∀ c, c < 4294967296 → (c < T + 16 ∨ T + 24 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, T ≤ c → c < T + 48 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hT, ha, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h5, h6,
      Nat.mod_eq_of_lt (show a + 30 < 18446744073709551616 by omega)]

/-- **Entry i of 1 … 30** (38042 + 19(i − 1)): a + i in the slot T + 16; on to `DebugList::entry`
    (66019) with the return address 1820 + 2i. -/
theorem a8_e {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (i T a : Nat) (hi : 1 ≤ i ∧ i ≤ 30) (hT : 65536 ≤ T ∧ T + 48 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat a) (h6 : ω[6] = UInt64.ofNat 75976) (ha : a + 31 < 18446744073709551616)
    (hw : ∀ c, T ≤ c → c < T + 48 → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R (38042 + 19 * (i - 1)) ω μ x 66019 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat (1820 + 2 * i) ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat T ∧ ω'[8] = UInt64.ofNat (T + 16) ∧ ω'[9] = UInt64.ofNat 75976 ∧
      rdN μ' (T + 16) 8 = a + i ∧
      (∀ c, c < 4294967296 → (c < T + 16 ∨ T + 24 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  rcases (show i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact a8_e1 (p := p) (P := P) (R := R) x ω μ T a hT h1 h5 h6 ha hw
  · exact a8_e2 (p := p) (P := P) (R := R) x ω μ T a hT h1 h5 h6 ha hw
  · exact a8_e3 (p := p) (P := P) (R := R) x ω μ T a hT h1 h5 h6 ha hw
  · exact a8_e4 (p := p) (P := P) (R := R) x ω μ T a hT h1 h5 h6 ha hw
  · exact a8_e5 (p := p) (P := P) (R := R) x ω μ T a hT h1 h5 h6 ha hw
  · exact a8_e6 (p := p) (P := P) (R := R) x ω μ T a hT h1 h5 h6 ha hw
  · exact a8_e7 (p := p) (P := P) (R := R) x ω μ T a hT h1 h5 h6 ha hw
  · exact a8_e8 (p := p) (P := P) (R := R) x ω μ T a hT h1 h5 h6 ha hw
  · exact a8_e9 (p := p) (P := P) (R := R) x ω μ T a hT h1 h5 h6 ha hw
  · exact a8_e10 (p := p) (P := P) (R := R) x ω μ T a hT h1 h5 h6 ha hw
  · exact a8_e11 (p := p) (P := P) (R := R) x ω μ T a hT h1 h5 h6 ha hw
  · exact a8_e12 (p := p) (P := P) (R := R) x ω μ T a hT h1 h5 h6 ha hw
  · exact a8_e13 (p := p) (P := P) (R := R) x ω μ T a hT h1 h5 h6 ha hw
  · exact a8_e14 (p := p) (P := P) (R := R) x ω μ T a hT h1 h5 h6 ha hw
  · exact a8_e15 (p := p) (P := P) (R := R) x ω μ T a hT h1 h5 h6 ha hw
  · exact a8_e16 (p := p) (P := P) (R := R) x ω μ T a hT h1 h5 h6 ha hw
  · exact a8_e17 (p := p) (P := P) (R := R) x ω μ T a hT h1 h5 h6 ha hw
  · exact a8_e18 (p := p) (P := P) (R := R) x ω μ T a hT h1 h5 h6 ha hw
  · exact a8_e19 (p := p) (P := P) (R := R) x ω μ T a hT h1 h5 h6 ha hw
  · exact a8_e20 (p := p) (P := P) (R := R) x ω μ T a hT h1 h5 h6 ha hw
  · exact a8_e21 (p := p) (P := P) (R := R) x ω μ T a hT h1 h5 h6 ha hw
  · exact a8_e22 (p := p) (P := P) (R := R) x ω μ T a hT h1 h5 h6 ha hw
  · exact a8_e23 (p := p) (P := P) (R := R) x ω μ T a hT h1 h5 h6 ha hw
  · exact a8_e24 (p := p) (P := P) (R := R) x ω μ T a hT h1 h5 h6 ha hw
  · exact a8_e25 (p := p) (P := P) (R := R) x ω μ T a hT h1 h5 h6 ha hw
  · exact a8_e26 (p := p) (P := P) (R := R) x ω μ T a hT h1 h5 h6 ha hw
  · exact a8_e27 (p := p) (P := P) (R := R) x ω μ T a hT h1 h5 h6 ha hw
  · exact a8_e28 (p := p) (P := P) (R := R) x ω μ T a hT h1 h5 h6 ha hw
  · exact a8_e29 (p := p) (P := P) (R := R) x ω μ T a hT h1 h5 h6 ha hw
  · exact a8_e30 (p := p) (P := P) (R := R) x ω μ T a hT h1 h5 h6 ha hw

/-- The return of entry i ≤ 30: 1820 + 2i → 38042 + 19i, a block start. -/
theorem a8_jt {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (i : Nat) (hi : i ≤ 30) :
    P.jumpTable.getD ((1820 + 2 * i) / 2 - 1) 0 = 38042 + 19 * i ∧ P.isBlockStart (38042 + 19 * i) = true := by
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨jte_909, bs_38042⟩
  · exact ⟨jte_910, bs_38061⟩
  · exact ⟨jte_911, bs_38080⟩
  · exact ⟨jte_912, bs_38099⟩
  · exact ⟨jte_913, bs_38118⟩
  · exact ⟨jte_914, bs_38137⟩
  · exact ⟨jte_915, bs_38156⟩
  · exact ⟨jte_916, bs_38175⟩
  · exact ⟨jte_917, bs_38194⟩
  · exact ⟨jte_918, bs_38213⟩
  · exact ⟨jte_919, bs_38232⟩
  · exact ⟨jte_920, bs_38251⟩
  · exact ⟨jte_921, bs_38270⟩
  · exact ⟨jte_922, bs_38289⟩
  · exact ⟨jte_923, bs_38308⟩
  · exact ⟨jte_924, bs_38327⟩
  · exact ⟨jte_925, bs_38346⟩
  · exact ⟨jte_926, bs_38365⟩
  · exact ⟨jte_927, bs_38384⟩
  · exact ⟨jte_928, bs_38403⟩
  · exact ⟨jte_929, bs_38422⟩
  · exact ⟨jte_930, bs_38441⟩
  · exact ⟨jte_931, bs_38460⟩
  · exact ⟨jte_932, bs_38479⟩
  · exact ⟨jte_933, bs_38498⟩
  · exact ⟨jte_934, bs_38517⟩
  · exact ⟨jte_935, bs_38536⟩
  · exact ⟨jte_936, bs_38555⟩
  · exact ⟨jte_937, bs_38574⟩
  · exact ⟨jte_938, bs_38593⟩
  · exact ⟨jte_939, bs_38612⟩

/-- 38612 … 38625: entry 31: ω₅ := a + 31, also in the slot; on to `DebugList::entry` (66019) with
    the return address 1882. -/
theorem a8_e31 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T a : Nat) (hT : 65536 ≤ T ∧ T + 48 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat a) (h6 : ω[6] = UInt64.ofNat 75976) (ha : a + 31 < 18446744073709551616)
    (hw : ∀ c, T ≤ c → c < T + 48 → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R 38612 ω μ x 66019 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 1882 ∧ ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat (a + 31) ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat T ∧ ω'[8] = UInt64.ofNat (T + 16) ∧ ω'[9] = UInt64.ofNat 75976 ∧
      rdN μ' (T + 16) 8 = a + 31 ∧
      (∀ c, c < 4294967296 → (c < T + 16 ∨ T + 24 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, T ≤ c → c < T + 48 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hT, ha, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h5, h6,
      Nat.mod_eq_of_lt ha]

/-- 38631: on to `DebugList::finish` (66310) with the `DebugList` T and the return address 1884. -/
theorem a8_f {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T : Nat) (hT : 65536 ≤ T ∧ T + 48 < 4294967296) (h1 : ω[1] = UInt64.ofNat T) :
    ∃ ω', FreeStepsH p R 38631 ω μ x 66310 ω' μ x 2 ∧
      ω'[0] = UInt64.ofNat 1884 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat T := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hT]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1]

/-- 38639 … 38651: ω₀, ω₅, ω₆ restored from T + 40, T + 32, T + 24; the frame closed; return. -/
theorem a8_r {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T r0 t v5 v6 : Nat) (hT : 65536 ≤ T ∧ T + 48 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (r0' : rdN μ (T + 40) 8 = r0) (r5 : rdN μ (T + 32) 8 = v5) (r6 : rdN μ (T + 24) 8 = v6)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) (hr : ∀ c, T ≤ c → c < T + 48 → μ.readable c = true) :
    ∃ ω', FreeStepsH p R 38639 ω μ x t ω' μ x 5 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (T + 48) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = ω[7] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hT, r0', r5, r6, hret, hjt, hbt, hr, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, Nat.mod_eq_of_lt (show r0 < 18446744073709551616 by omega),
      Nat.mod_eq_of_lt (rdN_lt64 μ (T + 32)), Nat.mod_eq_of_lt (rdN_lt64 μ (T + 24)), r5, r6]

end Services.Bootstrap.Fmt
