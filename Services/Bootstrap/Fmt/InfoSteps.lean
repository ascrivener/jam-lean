import Services.Bootstrap.Fmt.ReadExact
import Services.Bootstrap.Fmt.InfoStep
import Services.Bootstrap.CodeAAll

/-!
# `info` of the accumulating service (49454): the decode of its record, step by step

The inner function (frame 264 octets at T) zeroes a 96-octet buffer at T + 64 (`memset`), calls
`info` (6) on the service itself into it, then reads the record back through a slice reader at
T + 160 over the buffer (`read_exact`, `rd_u64`, `rd_u32`): the code hash (32 octets), b, t, g,
m, o (8 each), i (4), f (8), r, a, p (4 each), 96 octets in all. Each read succeeds, since the
reader holds 96 octets whatever `info` wrote. The values are not stated.

`ib` … `ik`: the segments between the reads, each from the previous read's `Ok` to the next call.
-/

namespace Services.Bootstrap.Fmt

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 48601 … 58434: after an `Ok`, the next field: `read_exact(T + 160, T + 208, 8)`, returning to
    2162. Only T … T + 160 and T + 176 … T + 240 change. -/
theorem ib {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (T : Nat) (hT : 65536 ≤ T ∧ T + 264 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h7 : ω[7] = UInt64.ofNat 0) (hr : ∀ a, T ≤ a → a < T + 264 → μ.readable a = true)
    (hw : ∀ a, T ≤ a → a < T + 264 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 48601 ω μ x 58434 ω' μ' x 16 ∧
      ω'[0] = UInt64.ofNat 2162 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[7] = UInt64.ofNat (T + 160) ∧ ω'[8] = UInt64.ofNat (T + 208) ∧ ω'[9] = UInt64.ofNat 8 ∧
      (∀ a, a < 4294967296 → (a < T ∨ (T + 160 ≤ a ∧ a < T + 176) ∨ T + 240 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have b01 : Exec.bitwise (· && ·) 0 1 = 0 := by decide
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hT, hr, hw, b01, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- 48659 … 58434: after an `Ok`, the next field: `read_exact(T + 160, T + 208, 8)`, returning to
    2164. Only T … T + 160 and T + 176 … T + 240 change. -/
theorem ic {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (T : Nat) (hT : 65536 ≤ T ∧ T + 264 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h7 : ω[7] = UInt64.ofNat 0) (hr : ∀ a, T ≤ a → a < T + 264 → μ.readable a = true)
    (hw : ∀ a, T ≤ a → a < T + 264 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 48659 ω μ x 58434 ω' μ' x 8 ∧
      ω'[0] = UInt64.ofNat 2164 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[7] = UInt64.ofNat (T + 160) ∧ ω'[8] = UInt64.ofNat (T + 208) ∧ ω'[9] = UInt64.ofNat 8 ∧
      (∀ a, a < 4294967296 → (a < T ∨ (T + 160 ≤ a ∧ a < T + 176) ∨ T + 240 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have b01 : Exec.bitwise (· && ·) 0 1 = 0 := by decide
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hT, hr, hw, b01, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- 48688 … 58434: after an `Ok`, the next field: `read_exact(T + 160, T + 208, 8)`, returning to
    2166. Only T … T + 160 and T + 176 … T + 240 change. -/
theorem id {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (T : Nat) (hT : 65536 ≤ T ∧ T + 264 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h7 : ω[7] = UInt64.ofNat 0) (hr : ∀ a, T ≤ a → a < T + 264 → μ.readable a = true)
    (hw : ∀ a, T ≤ a → a < T + 264 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 48688 ω μ x 58434 ω' μ' x 8 ∧
      ω'[0] = UInt64.ofNat 2166 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[7] = UInt64.ofNat (T + 160) ∧ ω'[8] = UInt64.ofNat (T + 208) ∧ ω'[9] = UInt64.ofNat 8 ∧
      (∀ a, a < 4294967296 → (a < T ∨ (T + 160 ≤ a ∧ a < T + 176) ∨ T + 240 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have b01 : Exec.bitwise (· && ·) 0 1 = 0 := by decide
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hT, hr, hw, b01, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- 48717 … 58434: after an `Ok`, the next field: `read_exact(T + 160, T + 208, 8)`, returning to
    2168. Only T … T + 160 and T + 176 … T + 240 change. -/
theorem ie {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (T : Nat) (hT : 65536 ≤ T ∧ T + 264 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h7 : ω[7] = UInt64.ofNat 0) (hr : ∀ a, T ≤ a → a < T + 264 → μ.readable a = true)
    (hw : ∀ a, T ≤ a → a < T + 264 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 48717 ω μ x 58434 ω' μ' x 10 ∧
      ω'[0] = UInt64.ofNat 2168 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[7] = UInt64.ofNat (T + 160) ∧ ω'[8] = UInt64.ofNat (T + 208) ∧ ω'[9] = UInt64.ofNat 8 ∧
      (∀ a, a < 4294967296 → (a < T ∨ (T + 160 ≤ a ∧ a < T + 176) ∨ T + 240 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have b01 : Exec.bitwise (· && ·) 0 1 = 0 := by decide
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hT, hr, hw, b01, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- 48750 … 46040: after an `Ok`, the next field: `rd_u64`, returning to
    2170. Only T … T + 160 and T + 176 … T + 240 change. -/
theorem if_ {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (T : Nat) (hT : 65536 ≤ T ∧ T + 264 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h7 : ω[7] = UInt64.ofNat 0) (hr : ∀ a, T ≤ a → a < T + 264 → μ.readable a = true)
    (hw : ∀ a, T ≤ a → a < T + 264 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 48750 ω μ x 46040 ω' μ' x 7 ∧
      ω'[0] = UInt64.ofNat 2170 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[7] = UInt64.ofNat (T + 160) ∧
      (∀ a, a < 4294967296 → (a < T ∨ (T + 160 ≤ a ∧ a < T + 176) ∨ T + 240 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have b01 : Exec.bitwise (· && ·) 0 1 = 0 := by decide
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hT, hr, hw, b01, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- 48772 … 46008: after an `Ok`, the next field: `rd_u32`, returning to
    2172. Only T … T + 160 and T + 176 … T + 240 change. -/
theorem ig {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (T : Nat) (hT : 65536 ≤ T ∧ T + 264 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h7 : ω[7] = UInt64.ofNat 0) (hr : ∀ a, T ≤ a → a < T + 264 → μ.readable a = true)
    (hw : ∀ a, T ≤ a → a < T + 264 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 48772 ω μ x 46008 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 2172 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[7] = UInt64.ofNat (T + 160) ∧
      (∀ a, a < 4294967296 → (a < T ∨ (T + 160 ≤ a ∧ a < T + 176) ∨ T + 240 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have b01 : Exec.bitwise (· && ·) 0 1 = 0 := by decide
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hT, hr, hw, b01, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- 48792 … 46040: after an `Ok`, the next field: `rd_u64`, returning to
    2174. Only T … T + 160 and T + 176 … T + 240 change. -/
theorem ih {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (T : Nat) (hT : 65536 ≤ T ∧ T + 264 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h7 : ω[7] = UInt64.ofNat 0) (hr : ∀ a, T ≤ a → a < T + 264 → μ.readable a = true)
    (hw : ∀ a, T ≤ a → a < T + 264 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 48792 ω μ x 46040 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 2174 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[7] = UInt64.ofNat (T + 160) ∧
      (∀ a, a < 4294967296 → (a < T ∨ (T + 160 ≤ a ∧ a < T + 176) ∨ T + 240 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have b01 : Exec.bitwise (· && ·) 0 1 = 0 := by decide
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hT, hr, hw, b01, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- 48812 … 46008: after an `Ok`, the next field: `rd_u32`, returning to
    2176. Only T … T + 160 and T + 176 … T + 240 change. -/
theorem ii {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (T : Nat) (hT : 65536 ≤ T ∧ T + 264 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h7 : ω[7] = UInt64.ofNat 0) (hr : ∀ a, T ≤ a → a < T + 264 → μ.readable a = true)
    (hw : ∀ a, T ≤ a → a < T + 264 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 48812 ω μ x 46008 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 2176 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[7] = UInt64.ofNat (T + 160) ∧
      (∀ a, a < 4294967296 → (a < T ∨ (T + 160 ≤ a ∧ a < T + 176) ∨ T + 240 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have b01 : Exec.bitwise (· && ·) 0 1 = 0 := by decide
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hT, hr, hw, b01, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- 48832 … 46008: after an `Ok`, the next field: `rd_u32`, returning to
    2178. Only T … T + 160 and T + 176 … T + 240 change. -/
theorem ij {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (T : Nat) (hT : 65536 ≤ T ∧ T + 264 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h7 : ω[7] = UInt64.ofNat 0) (hr : ∀ a, T ≤ a → a < T + 264 → μ.readable a = true)
    (hw : ∀ a, T ≤ a → a < T + 264 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 48832 ω μ x 46008 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 2178 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[7] = UInt64.ofNat (T + 160) ∧
      (∀ a, a < 4294967296 → (a < T ∨ (T + 160 ≤ a ∧ a < T + 176) ∨ T + 240 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have b01 : Exec.bitwise (· && ·) 0 1 = 0 := by decide
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hT, hr, hw, b01, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- 48852 … 46008: after an `Ok`, the next field: `rd_u32`, returning to
    2180. Only T … T + 160 and T + 176 … T + 240 change. -/
theorem ik {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (T : Nat) (hT : 65536 ≤ T ∧ T + 264 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h7 : ω[7] = UInt64.ofNat 0) (hr : ∀ a, T ≤ a → a < T + 264 → μ.readable a = true)
    (hw : ∀ a, T ≤ a → a < T + 264 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 48852 ω μ x 46008 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 2180 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[7] = UInt64.ofNat (T + 160) ∧
      (∀ a, a < 4294967296 → (a < T ∨ (T + 160 ≤ a ∧ a < T + 176) ∨ T + 240 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have b01 : Exec.bitwise (· && ·) 0 1 = 0 := by decide
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hT, hr, hw, b01, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, h1, h7]

end Services.Bootstrap.Fmt
