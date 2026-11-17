import Services.Bootstrap.Fmt.FieldU8Hex

/-!
# 57922, a slice of octets in hex: the steps

57922 is called with v (ω₇) the address of a slice's (pointer, length) pair and a `Formatter` F (ω₈).
For a length 1 ≤ len < 1027 it writes each octet with `core::fmt::write` (64495), the template
70833 (`{:02x}`) and the argument (T + 56, 2532), 2532 resolving to 57917 (`<&u8 as LowerHex>`),
where T + 56 holds the octet's address.

- `sh_entry`: 57922 … 57975, the frame at T = sp − 104;
- `sh_iter`: 57976 … the call of 64495;
- `sh_next`: 58012 … the next octet (57976) or the end (58215);
- `sh_end`: 58215 … the return.
-/

namespace Services.Bootstrap.Fmt

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 57922 … 57975, a length 1 ≤ len < 1027: the frame at T = sp − 104 (ω₀, ω₅, ω₆ at T + 96, T + 88,
    T + 80; the `Formatter`'s sink (buf, vt) at T + 48, T + 40; 2532 at T + 32; the template 70833
    at T + 24), the length in ω₅ and the pointer in ω₉. -/
theorem sh_entry {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v F r0 v5 v6 ptr len buf vt : Nat) (hsp : 65536 + 104 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat F)
    (hv : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616)
    (hvb : v + 16 < 4294967296 ∧ (v + 16 ≤ sp - 104 ∨ sp ≤ v)) (hFb : F + 16 < 4294967296 ∧ (F + 16 ≤ sp - 104 ∨ sp ≤ F))
    (rp : rdN μ v 8 = ptr) (rl : rdN μ (v + 8) 8 = len) (hl : 1 ≤ len ∧ len < 1027)
    (rb : rdN μ F 8 = buf) (rv : rdN μ (F + 8) 8 = vt)
    (hrv : ∀ a, v ≤ a → a < v + 16 → μ.readable a = true)
    (hrF : ∀ a, F ≤ a → a < F + 16 → μ.readable a = true)
    (hw : ∀ a, sp - 104 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 57922 ω μ x 57976 ω' μ' x 18 ∧
      ω'[1] = UInt64.ofNat (sp - 104) ∧ ω'[5] = UInt64.ofNat len ∧ ω'[9] = UInt64.ofNat ptr ∧
      rdN μ' (sp - 104 + 96) 8 = r0 ∧ rdN μ' (sp - 104 + 88) 8 = v5 ∧ rdN μ' (sp - 104 + 80) 8 = v6 ∧
      rdN μ' (sp - 104 + 48) 8 = buf ∧ rdN μ' (sp - 104 + 40) 8 = vt ∧
      rdN μ' (sp - 104 + 32) 8 = 2532 ∧ rdN μ' (sp - 104 + 24) 8 = 70833 ∧
      (∀ a, a < 4294967296 → (a < sp - 104 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 104 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hptr : ptr < 18446744073709551616 := by rw [← rp]; exact rdN_lt64 μ _
  have hbuf : buf < 18446744073709551616 := by rw [← rb]; exact rdN_lt64 μ _
  have hvt : vt < 18446744073709551616 := by rw [← rv]; exact rdN_lt64 μ _
  have hl1 : ¬ 1027 ≤ len := by omega
  have hl0 : len ≠ 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, hsp, hv, hvb, hFb, rp, rl, hl, hl1, hl0, rb, rv, hrv, hrF, hw, hr,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, rdN_lit8, Num.decodeLE_encodeLE, Nat.reduceMul,
      Nat.reducePow, Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1,
      Nat.mod_eq_of_lt hv.2.2, Nat.mod_eq_of_lt hptr, Nat.mod_eq_of_lt hbuf, Nat.mod_eq_of_lt hvt]

/-- 57976 … 58006, the octet at q (ω₉): q at T + 56, the argument pair (T + 56, 2532) at T + 64, and
    the call of `core::fmt::write` (64495) with the sink (W, vt) from T + 48, T + 40, the template
    from T + 24 and the arguments T + 64, returning to 58012 (2536); the count m stays in ω₅ and q
    goes to ω₆. -/
theorem sh_iter {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T W vt q m : Nat) (hT : 65536 ≤ T ∧ T + 104 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat T) (h5 : ω[5] = UInt64.ofNat m) (h9 : ω[9] = UInt64.ofNat q)
    (hq : q < 18446744073709551616)
    (r48 : rdN μ (T + 48) 8 = W) (r40 : rdN μ (T + 40) 8 = vt) (r32 : rdN μ (T + 32) 8 = 2532)
    (r24 : rdN μ (T + 24) 8 = 70833)
    (hw : ∀ a, T ≤ a → a < T + 104 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 57976 ω μ x 64495 ω' μ' x 13 ∧
      ω'[0] = UInt64.ofNat 2536 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[5] = UInt64.ofNat m ∧
      ω'[6] = UInt64.ofNat q ∧ ω'[7] = UInt64.ofNat W ∧ ω'[8] = UInt64.ofNat vt ∧
      ω'[9] = UInt64.ofNat 70833 ∧ ω'[10] = UInt64.ofNat (T + 64) ∧
      rdN μ' (T + 56) 8 = q ∧ rdN μ' (T + 64) 8 = T + 56 ∧ rdN μ' (T + 72) 8 = 2532 ∧
      (∀ a, a < 4294967296 → (a < T + 56 ∨ T + 80 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, T ≤ a → a < T + 104 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hW : W < 18446744073709551616 := by rw [← r48]; exact rdN_lt64 μ _
  have hvt : vt < 18446744073709551616 := by rw [← r40]; exact rdN_lt64 μ _
  have hb5 := (ω[5]).toNat_lt
  have h56 : T + 56 < 18446744073709551616 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h9, hT, hq, r48, r40, r32, r24, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [h1, h5, rdN_writeN_disjoint, rdN_writeN_same8, rdN_lit8, Num.decodeLE_encodeLE,
      Nat.reduceMul, Nat.reducePow, Nat.mod_eq_of_lt h56,
      Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hW,
      Nat.mod_eq_of_lt hvt]

/-- 58012 … 58025, after an `Ok` (ω₇ = 0): the count m − 1 (ω₅) and the next octet q + 1 (ω₉); on to
    57976 while m − 1 ≠ 0, else to 58215. -/
theorem sh_next {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (m q : Nat) (hm : 1 ≤ m ∧ m < 1027) (hq : q + 1 < 18446744073709551616)
    (h5 : ω[5] = UInt64.ofNat m) (h6 : ω[6] = UInt64.ofNat q) (h7 : ω[7] = UInt64.ofNat 0) :
    ∃ ω', FreeStepsH p R 58012 ω μ x (if m - 1 = 0 then 58215 else 57976) ω' μ x 5 ∧
      ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat (m - 1) ∧ ω'[9] = UInt64.ofNat (q + 1) := by
  rw [show ω = regsNF ω [] from rfl]
  by_cases hz : m - 1 = 0
  · rw [if_pos hz]
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h5, h6, h7, hm, hq, hz]
    · refine ⟨?_, ?_, ?_⟩
      all_goals post_simp [h5, h6]
  · rw [if_neg hz]
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h5, h6, h7, hm, hq, hz]
    · refine ⟨?_, ?_, ?_⟩
      all_goals post_simp [h5, h6]

/-- 58215 … the return: `Ok` (ω₇ = 0), ω₀, ω₅, ω₆ restored from T + 96, T + 88, T + 80, the frame
    closed, the return to t. -/
theorem sh_end {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T r0 t v5 v6 : Nat) (hT : 65536 ≤ T ∧ T + 104 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (r0' : rdN μ (T + 96) 8 = r0) (r5 : rdN μ (T + 88) 8 = v5) (r6 : rdN μ (T + 80) 8 = v6)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hr : ∀ a, T + 80 ≤ a → a < T + 104 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 58215 ω μ x t ω' μ x 8 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (T + 104) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0 := by
  have hv5 : v5 < 18446744073709551616 := by rw [← r5]; exact rdN_lt64 μ _
  have hv6 : v6 < 18446744073709551616 := by rw [← r6]; exact rdN_lt64 μ _
  have hr0 : r0 % 18446744073709551616 % 4294967296 = r0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hT, r0', r5, r6, hret, hr0, hjt, hbt, hr, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, Nat.mod_eq_of_lt hv5, Nat.mod_eq_of_lt hv6]

end Services.Bootstrap.Fmt
