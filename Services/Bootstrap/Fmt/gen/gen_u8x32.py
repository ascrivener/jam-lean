hdr = '''import Services.Bootstrap.Fmt.Tac

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
'''
def ei(i):
    pc = 38042 + 19*(i-1)
    return f'''
theorem a8_e{i} {{p : ByteArray}} {{P : Program}} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T a : Nat) (hT : 65536 ≤ T ∧ T + 48 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat a) (h6 : ω[6] = UInt64.ofNat 75976) (ha : a + 31 < 18446744073709551616)
    (hw : ∀ c, T ≤ c → c < T + 48 → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R {pc} ω μ x 66019 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat {1820 + 2*i} ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat T ∧ ω'[8] = UInt64.ofNat (T + 16) ∧ ω'[9] = UInt64.ofNat 75976 ∧
      rdN μ' (T + 16) 8 = a + {i} ∧
      (∀ c, c < 4294967296 → (c < T + 16 ∨ T + 24 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, T ≤ c → c < T + 48 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hT, ha, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h5, h6,
      Nat.mod_eq_of_lt (show a + {i} < 18446744073709551616 by omega)]
'''
out = hdr
for i in range(1,31): out += ei(i)
cases = ' | '.join(['rfl']*30)
eqs = ' ∨ '.join([f'i = {i}' for i in range(1,31)])
out += f'''
/-- **Entry i of 1 … 30** (38042 + 19(i − 1)): a + i in the slot T + 16; on to `DebugList::entry`
    (66019) with the return address 1820 + 2i. -/
theorem a8_e {{p : ByteArray}} {{P : Program}} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (i T a : Nat) (hi : 1 ≤ i ∧ i ≤ 30) (hT : 65536 ≤ T ∧ T + 48 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat a) (h6 : ω[6] = UInt64.ofNat 75976) (ha : a + 31 < 18446744073709551616)
    (hw : ∀ c, T ≤ c → c < T + 48 → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R (38042 + 19 * (i - 1)) ω μ x 66019 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat (1820 + 2 * i) ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat T ∧ ω'[8] = UInt64.ofNat (T + 16) ∧ ω'[9] = UInt64.ofNat 75976 ∧
      rdN μ' (T + 16) 8 = a + i ∧
      (∀ c, c < 4294967296 → (c < T + 16 ∨ T + 24 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  rcases (show {eqs} by omega) with {cases}
'''
for i in range(1,31):
    out += f'  · exact a8_e{i} (p := p) (P := P) (R := R) x ω μ T a hT h1 h5 h6 ha hw\n'
eqs0 = ' ∨ '.join([f'i = {i}' for i in range(0,31)])
cases0 = ' | '.join(['rfl']*31)
out += f'''
/-- The return of entry i ≤ 30: 1820 + 2i → 38042 + 19i, a block start. -/
theorem a8_jt {{p : ByteArray}} {{P : Program}} [HasCode p P] [HasCodeF p P] (i : Nat) (hi : i ≤ 30) :
    P.jumpTable.getD ((1820 + 2 * i) / 2 - 1) 0 = 38042 + 19 * i ∧ P.isBlockStart (38042 + 19 * i) = true := by
  rcases (show {eqs0} by omega) with {cases0}
'''
for i in range(0,31):
    out += f'  · exact ⟨jte_{909+i}, bs_{38042+19*i}⟩\n'
out += '''
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
'''
open('/home/user/jam-lean/Services/Bootstrap/Fmt/U8x32Steps.lean','w').write(out)
