import Services.Bootstrap.Fmt.Tac

/-!
# `<Vec<Instruction> as fmt::Debug>::fmt` (29675): the steps

As `VecDebugSteps` (`<&Vec<u8> as Debug>`, 26807), for 232-octet elements: ω₇ is the `Vec` (cap, ptr,
len) itself. The frame T = sp − 64: ω₀, ω₅, ω₆ at T + 56, T + 48, T + 40; the element vtable (75784,
`&Instruction`'s `Debug`) at T + 0; the next element's address at T + 8; the `DebugList` at T + 16;
the slot holding the current element's address at T + 32. The pointer runs in ω₆ and the octets
left (232 · the elements left) in ω₅.

- `vi_a` (29675 … 29696): `debug_list` (61708) on D = T + 16, returning to 29702 (1384);
- `vi_b` (29702 … 29716), len ≠ 0: ω₅ := 232 · len, the vtable to T + 0; `vi_b0`, len = 0: to 29752;
- `vi_l` (29717 … 29735): the element at q: q + 232 to T + 8, q to the slot T + 32, and
  `DebugList::entry` (66019), returning to 29742 (1386);
- `vi_n` (29742 … 29749): m − 232 octets left; on to 29717 or 29752;
- `vi_e` (29752 … 29755): `DebugList::finish` (66310) on D, returning to 29762 (1388);
- `vi_r` (29762 … 29774): ω₀, ω₅, ω₆ restored, sp := T + 64, return.
-/

namespace Services.Bootstrap.Fmt

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

theorem vi_a {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v ptr len r0 v5 v6 : Nat) (hsp : 196608 + 64 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat v)
    (hv : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616 ∧
      v + 24 < 4294967296)
    (hdis : v + 24 ≤ sp - 64 ∨ sp ≤ v)
    (rp : rdN μ (v + 8) 8 = ptr) (rl : rdN μ (v + 16) 8 = len)
    (hrv : ∀ a, v + 8 ≤ a → a < v + 24 → μ.readable a = true)
    (hw : ∀ a, sp - 64 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 29675 ω μ x 61708 ω' μ' x 8 ∧
      ω'[0] = UInt64.ofNat 1384 ∧ ω'[1] = UInt64.ofNat (sp - 64) ∧ ω'[5] = UInt64.ofNat len ∧
      ω'[6] = UInt64.ofNat ptr ∧ ω'[7] = UInt64.ofNat (sp - 64 + 16) ∧ ω'[8] = ω[8] ∧
      rdN μ' (sp - 64 + 56) 8 = r0 ∧ rdN μ' (sp - 64 + 48) 8 = v5 ∧ rdN μ' (sp - 64 + 40) 8 = v6 ∧
      (∀ a, a < 4294967296 → (a < sp - 64 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 64 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hp : ptr < 18446744073709551616 := rp ▸ rdN_lt64 μ _
  have hl : len < 18446744073709551616 := rl ▸ rdN_lt64 μ _
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, hsp, hv, hdis, rp, rl, hrv, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h0, h1, h5, h6, h7,
      Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1,
      Nat.mod_eq_of_lt hv.2.2.1]

theorem vi_b {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T len : Nat) (hT : 65536 ≤ T ∧ T + 64 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat len) (hl : 0 < len ∧ 232 * len < 18446744073709551616)
    (hw : ∀ a, T ≤ a → a < T + 8 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 29702 ω μ x 29717 ω' μ' x 5 ∧
      ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat (232 * len) ∧ ω'[6] = ω[6] ∧ rdN μ' T 8 = 75784 ∧
      (∀ a, a < 4294967296 → (a < T ∨ T + 8 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, T ≤ a → a < T + 8 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hne : len ≠ 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hT, hl, hne, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h5]
    all_goals first | (rw [rdN_lit8 _ _ _ rfl (by omega)]; decide) | (congr 1; omega) | skip

theorem vi_b0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (h5 : ω[5] = UInt64.ofNat 0) :
    FreeStepsH p R 29702 ω μ x 29752 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h5]

theorem vi_l {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T q : Nat) (hT : 65536 ≤ T ∧ T + 64 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h6 : ω[6] = UInt64.ofNat q) (hq : q + 232 < 18446744073709551616) (r0 : rdN μ T 8 = 75784)
    (hw : ∀ a, T ≤ a → a < T + 64 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 29717 ω μ x 66019 ω' μ' x 7 ∧
      ω'[0] = UInt64.ofNat 1386 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (T + 16) ∧ ω'[8] = UInt64.ofNat (T + 32) ∧ ω'[9] = UInt64.ofNat 75784 ∧
      rdN μ' (T + 8) 8 = q + 232 ∧ rdN μ' (T + 32) 8 = q ∧
      (∀ a, a < 4294967296 → (a < T + 8 ∨ T + 16 ≤ a) → (a < T + 32 ∨ T + 40 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, T ≤ a → a < T + 64 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, hT, hq, r0, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h6,
      Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt (show q < 18446744073709551616 by omega)]

theorem vi_n {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T m q : Nat) (hT : 65536 ≤ T ∧ T + 64 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat m) (hm : 232 ≤ m ∧ m < 18446744073709551616) (r8 : rdN μ (T + 8) 8 = q)
    (hr : ∀ a, T ≤ a → a < T + 64 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 29742 ω μ x (if m - 232 = 0 then 29752 else 29717) ω' μ x 3 ∧
      ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat (m - 232) ∧ ω'[6] = UInt64.ofNat q := by
  have hq : q < 18446744073709551616 := r8 ▸ rdN_lt64 μ _
  rw [show ω = regsNF ω [] from rfl]
  by_cases hz : m - 232 = 0
  · rw [if_pos hz]
    have hm1 : m = 232 := by omega
    subst hm1
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h5, hT, r8, hr, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_⟩
      all_goals post_simp [h1, h5, Nat.mod_eq_of_lt hq]
  · rw [if_neg hz]
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h5, hT, hm, hz, r8, hr, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_⟩
      all_goals post_simp [h1, h5, Nat.mod_eq_of_lt hq]
      all_goals first | (congr 1; omega) | skip

theorem vi_e {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T : Nat) (hT : 65536 ≤ T ∧ T + 64 < 4294967296) (h1 : ω[1] = UInt64.ofNat T) :
    ∃ ω', FreeStepsH p R 29752 ω μ x 66310 ω' μ x 2 ∧
      ω'[0] = UInt64.ofNat 1388 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (T + 16) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hT]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1]

theorem vi_r {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T r0 t v5 v6 : Nat) (hT : 65536 ≤ T ∧ T + 64 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (r0' : rdN μ (T + 56) 8 = r0) (r5 : rdN μ (T + 48) 8 = v5) (r6 : rdN μ (T + 40) 8 = v6)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) (hr : ∀ a, T ≤ a → a < T + 64 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 29762 ω μ x t ω' μ x 5 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (T + 64) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = ω[7] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hT, r0', r5, r6, hret, hjt, hbt, hr, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, Nat.mod_eq_of_lt (show r0 < 18446744073709551616 by omega),
      Nat.mod_eq_of_lt (rdN_lt64 μ (T + 48)), Nat.mod_eq_of_lt (rdN_lt64 μ (T + 40)), r5, r6]

end Services.Bootstrap.Fmt
