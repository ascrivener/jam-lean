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
    2162. Only T … T + 56 and T + 176 … T + 240 change. -/
theorem ib {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (T : Nat) (hT : 65536 ≤ T ∧ T + 264 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h7 : ω[7] = UInt64.ofNat 0) (hr : ∀ a, T ≤ a → a < T + 264 → μ.readable a = true)
    (hw : ∀ a, T ≤ a → a < T + 264 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 48601 ω μ x 58434 ω' μ' x 16 ∧
      ω'[0] = UInt64.ofNat 2162 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[7] = UInt64.ofNat (T + 160) ∧ ω'[8] = UInt64.ofNat (T + 208) ∧ ω'[9] = UInt64.ofNat 8 ∧
      (∀ a, a < 4294967296 → (a < T ∨ (T + 56 ≤ a ∧ a < T + 176) ∨ T + 240 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have b01 : Exec.bitwise (· && ·) 0 1 = 0 := by decide
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hT, hr, hw, b01, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- 48659 … 58434: after an `Ok`, the next field: `read_exact(T + 160, T + 208, 8)`, returning to
    2164. Only T … T + 56 and T + 176 … T + 240 change. -/
theorem ic {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (T : Nat) (hT : 65536 ≤ T ∧ T + 264 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h7 : ω[7] = UInt64.ofNat 0) (hr : ∀ a, T ≤ a → a < T + 264 → μ.readable a = true)
    (hw : ∀ a, T ≤ a → a < T + 264 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 48659 ω μ x 58434 ω' μ' x 8 ∧
      ω'[0] = UInt64.ofNat 2164 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[7] = UInt64.ofNat (T + 160) ∧ ω'[8] = UInt64.ofNat (T + 208) ∧ ω'[9] = UInt64.ofNat 8 ∧
      (∀ a, a < 4294967296 → (a < T ∨ (T + 56 ≤ a ∧ a < T + 176) ∨ T + 240 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have b01 : Exec.bitwise (· && ·) 0 1 = 0 := by decide
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hT, hr, hw, b01, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- 48688 … 58434: after an `Ok`, the next field: `read_exact(T + 160, T + 208, 8)`, returning to
    2166. Only T … T + 56 and T + 176 … T + 240 change. -/
theorem id {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (T : Nat) (hT : 65536 ≤ T ∧ T + 264 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h7 : ω[7] = UInt64.ofNat 0) (hr : ∀ a, T ≤ a → a < T + 264 → μ.readable a = true)
    (hw : ∀ a, T ≤ a → a < T + 264 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 48688 ω μ x 58434 ω' μ' x 8 ∧
      ω'[0] = UInt64.ofNat 2166 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[7] = UInt64.ofNat (T + 160) ∧ ω'[8] = UInt64.ofNat (T + 208) ∧ ω'[9] = UInt64.ofNat 8 ∧
      (∀ a, a < 4294967296 → (a < T ∨ (T + 56 ≤ a ∧ a < T + 176) ∨ T + 240 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have b01 : Exec.bitwise (· && ·) 0 1 = 0 := by decide
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hT, hr, hw, b01, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- 48717 … 58434: after an `Ok`, the next field: `read_exact(T + 160, T + 208, 8)`, returning to
    2168. Only T … T + 56 and T + 176 … T + 240 change. -/
theorem ie {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (T : Nat) (hT : 65536 ≤ T ∧ T + 264 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h7 : ω[7] = UInt64.ofNat 0) (hr : ∀ a, T ≤ a → a < T + 264 → μ.readable a = true)
    (hw : ∀ a, T ≤ a → a < T + 264 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 48717 ω μ x 58434 ω' μ' x 10 ∧
      ω'[0] = UInt64.ofNat 2168 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[7] = UInt64.ofNat (T + 160) ∧ ω'[8] = UInt64.ofNat (T + 208) ∧ ω'[9] = UInt64.ofNat 8 ∧
      (∀ a, a < 4294967296 → (a < T ∨ (T + 56 ≤ a ∧ a < T + 176) ∨ T + 240 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have b01 : Exec.bitwise (· && ·) 0 1 = 0 := by decide
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hT, hr, hw, b01, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- 48750 … 46040: after an `Ok`, the next field: `rd_u64`, returning to
    2170. Only T … T + 56 and T + 176 … T + 240 change. -/
theorem if_ {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (T : Nat) (hT : 65536 ≤ T ∧ T + 264 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h7 : ω[7] = UInt64.ofNat 0) (hr : ∀ a, T ≤ a → a < T + 264 → μ.readable a = true)
    (hw : ∀ a, T ≤ a → a < T + 264 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 48750 ω μ x 46040 ω' μ' x 7 ∧
      ω'[0] = UInt64.ofNat 2170 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[7] = UInt64.ofNat (T + 160) ∧
      (∀ a, a < 4294967296 → (a < T ∨ (T + 56 ≤ a ∧ a < T + 176) ∨ T + 240 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have b01 : Exec.bitwise (· && ·) 0 1 = 0 := by decide
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hT, hr, hw, b01, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- 48772 … 46008: after an `Ok`, the next field: `rd_u32`, returning to
    2172. Only T … T + 56 and T + 176 … T + 240 change. -/
theorem ig {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (T : Nat) (hT : 65536 ≤ T ∧ T + 264 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h7 : ω[7] = UInt64.ofNat 0) (hr : ∀ a, T ≤ a → a < T + 264 → μ.readable a = true)
    (hw : ∀ a, T ≤ a → a < T + 264 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 48772 ω μ x 46008 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 2172 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[7] = UInt64.ofNat (T + 160) ∧
      (∀ a, a < 4294967296 → (a < T ∨ (T + 56 ≤ a ∧ a < T + 176) ∨ T + 240 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have b01 : Exec.bitwise (· && ·) 0 1 = 0 := by decide
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hT, hr, hw, b01, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- 48792 … 46040: after an `Ok`, the next field: `rd_u64`, returning to
    2174. Only T … T + 56 and T + 176 … T + 240 change. -/
theorem ih {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (T : Nat) (hT : 65536 ≤ T ∧ T + 264 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h7 : ω[7] = UInt64.ofNat 0) (hr : ∀ a, T ≤ a → a < T + 264 → μ.readable a = true)
    (hw : ∀ a, T ≤ a → a < T + 264 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 48792 ω μ x 46040 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 2174 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[7] = UInt64.ofNat (T + 160) ∧
      (∀ a, a < 4294967296 → (a < T ∨ (T + 56 ≤ a ∧ a < T + 176) ∨ T + 240 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have b01 : Exec.bitwise (· && ·) 0 1 = 0 := by decide
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hT, hr, hw, b01, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- 48812 … 46008: after an `Ok`, the next field: `rd_u32`, returning to
    2176. Only T … T + 56 and T + 176 … T + 240 change. -/
theorem ii {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (T : Nat) (hT : 65536 ≤ T ∧ T + 264 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h7 : ω[7] = UInt64.ofNat 0) (hr : ∀ a, T ≤ a → a < T + 264 → μ.readable a = true)
    (hw : ∀ a, T ≤ a → a < T + 264 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 48812 ω μ x 46008 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 2176 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[7] = UInt64.ofNat (T + 160) ∧
      (∀ a, a < 4294967296 → (a < T ∨ (T + 56 ≤ a ∧ a < T + 176) ∨ T + 240 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have b01 : Exec.bitwise (· && ·) 0 1 = 0 := by decide
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hT, hr, hw, b01, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- 48832 … 46008: after an `Ok`, the next field: `rd_u32`, returning to
    2178. Only T … T + 56 and T + 176 … T + 240 change. -/
theorem ij {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (T : Nat) (hT : 65536 ≤ T ∧ T + 264 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h7 : ω[7] = UInt64.ofNat 0) (hr : ∀ a, T ≤ a → a < T + 264 → μ.readable a = true)
    (hw : ∀ a, T ≤ a → a < T + 264 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 48832 ω μ x 46008 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 2178 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[7] = UInt64.ofNat (T + 160) ∧
      (∀ a, a < 4294967296 → (a < T ∨ (T + 56 ≤ a ∧ a < T + 176) ∨ T + 240 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have b01 : Exec.bitwise (· && ·) 0 1 = 0 := by decide
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hT, hr, hw, b01, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- 48852 … 46008: after an `Ok`, the next field: `rd_u32`, returning to
    2180. Only T … T + 56 and T + 176 … T + 240 change. -/
theorem ik {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (T : Nat) (hT : 65536 ≤ T ∧ T + 264 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h7 : ω[7] = UInt64.ofNat 0) (hr : ∀ a, T ≤ a → a < T + 264 → μ.readable a = true)
    (hw : ∀ a, T ≤ a → a < T + 264 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 48852 ω μ x 46008 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 2180 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[7] = UInt64.ofNat (T + 160) ∧
      (∀ a, a < 4294967296 → (a < T ∨ (T + 56 ≤ a ∧ a < T + 176) ∨ T + 240 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have b01 : Exec.bitwise (· && ·) 0 1 = 0 := by decide
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hT, hr, hw, b01, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- 49454 … 49507: the outer function's 120-octet frame at O = S − 120 (ω₀ at +112, ω₅ at +104), and
    the inner function's 264-octet frame at T = O − 264 (its return address 2192 at T + 256, the
    destination D at T + 248, ω₆ at T + 240, the result's address O at T + 56); then `memset` of the
    96 octets at T + 64, returning to 48534 (2158). -/
theorem io_entry {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (S D r0 v5 v6 : Nat) (hS : 65536 + 384 ≤ S ∧ S < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat D)
    (hv : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616 ∧
      D < 18446744073709551616)
    (hw : ∀ a, S - 384 ≤ a → a < S → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 49454 ω μ x 70133 ω' μ' x 18 ∧
      ω'[0] = UInt64.ofNat 2158 ∧ ω'[1] = UInt64.ofNat (S - 384) ∧ ω'[6] = UInt64.ofNat 18446744073709551615 ∧
      ω'[7] = UInt64.ofNat (S - 384 + 64) ∧ ω'[8] = UInt64.ofNat 0 ∧ ω'[9] = UInt64.ofNat 96 ∧
      rdN μ' (S - 120 + 112) 8 = r0 ∧ rdN μ' (S - 120 + 104) 8 = v5 ∧ rdN μ' (S - 384 + 256) 8 = 2192 ∧
      rdN μ' (S - 384 + 248) 8 = D ∧ rdN μ' (S - 384 + 240) 8 = v6 ∧ rdN μ' (S - 384 + 56) 8 = S - 120 ∧
      (∀ a, a < 4294967296 → (a < S - 384 ∨ S ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S - 384 ≤ a → a < S → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, hS, hv, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, rdN_lit8, Num.decodeLE_encodeLE, h0, h1, h5, h6, h7,
      Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt hv.2.2.1, Nat.mod_eq_of_lt hv.2.2.2]

/-- 48534 … 48545: `info`'s arguments: the service itself (ω₇ = 2⁶⁴ − 1, from ω₆), the buffer T + 64,
    offset 0 and length 96. -/
theorem io_a1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (T : Nat) (hT : 65536 ≤ T ∧ T + 264 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h6 : ω[6] = UInt64.ofNat 18446744073709551615) :
    ∃ ω', FreeStepsH p R 48534 ω μ x 48547 ω' μ x 5 ∧
      ω'[1] = UInt64.ofNat T ∧ ω'[7] = UInt64.ofNat 18446744073709551615 ∧ ω'[8] = UInt64.ofNat (T + 64) ∧
      ω'[9] = UInt64.ofNat 0 ∧ ω'[10] = UInt64.ofNat 96 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h6, hT]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, h6]

/-- 48549 … 48595: `info` returned a length L below 2⁶⁴ − 9 (not an error): the reader at T + 160
    over the 96 octets at T + 64, T + 208 … T + 240 zeroed, and `read_exact(T + 160, T + 208, 32)`
    (the code hash), returning to 48601 (2160). -/
theorem io_a2 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (T L : Nat) (hT : 65536 ≤ T ∧ T + 264 < 4294967296) (hL : L < 18446744073709551607)
    (h1 : ω[1] = UInt64.ofNat T) (h7 : ω[7] = UInt64.ofNat L)
    (hw : ∀ a, T ≤ a → a < T + 264 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 48549 ω μ x 58434 ω' μ' x 15 ∧
      ω'[0] = UInt64.ofNat 2160 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[7] = UInt64.ofNat (T + 160) ∧
      ω'[8] = UInt64.ofNat (T + 208) ∧ ω'[9] = UInt64.ofNat 32 ∧
      rdN μ' (T + 160) 8 = T + 64 ∧ rdN μ' (T + 160 + 8) 8 = 96 ∧
      (∀ a, a < 4294967296 → (a < T + 160 ∨ (T + 176 ≤ a ∧ a < T + 208) ∨ T + 240 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, T ≤ a → a < T + 264 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hT, hL, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, rdN_lit8, Num.decodeLE_encodeLE, h1, h7]

/-- 48871 … the return to 49510 (2192): after the last read's `Ok`, the record `Some(info)` (104
    octets, tag 1 at +0) stored at O (read from T + 56), ω₀, ω₅, ω₆ restored from T + 256, T + 248,
    T + 240 and the inner frame closed (sp = T + 264). -/
theorem io_l {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (T D v6 : Nat) (hT : 65536 ≤ T ∧ T + 264 + 104 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat T) (h7 : ω[7] = UInt64.ofNat 0)
    (rO : rdN μ (T + 56) 8 = T + 264) (r0 : rdN μ (T + 256) 8 = 2192) (r5 : rdN μ (T + 248) 8 = D)
    (r6 : rdN μ (T + 240) 8 = v6)
    (hr : ∀ a, T ≤ a → a < T + 264 → μ.readable a = true)
    (hw : ∀ a, T + 264 ≤ a → a < T + 264 + 104 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 48871 ω μ x 49510 ω' μ' x 40 ∧
      ω'[1] = UInt64.ofNat (T + 264) ∧ ω'[5] = UInt64.ofNat D ∧ ω'[6] = UInt64.ofNat v6 ∧
      rdN μ' (T + 264) 8 = 1 ∧
      (∀ a, a < 4294967296 → (a < T + 264 ∨ T + 264 + 104 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have b01 : Exec.bitwise (· && ·) 0 1 = 0 := by decide
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hT, rO, r0, r5, r6, hr, hw, b01, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, rdN_lit8, Num.decodeLE_encodeLE, h1, h7,
      Nat.mod_eq_of_lt (rdN_lt64 μ (T + 248)), Nat.mod_eq_of_lt (rdN_lt64 μ (T + 240)), r5, r6]

/-- 49510 … 49523: the result is `Some` (tag 1 at O): `memcpy(D, O + 8, 96)`, returning to 49529
    (2194). -/
theorem io_b {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (O D : Nat) (hO : 65536 ≤ O ∧ O + 120 < 4294967296) (hD : D < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat O) (h5 : ω[5] = UInt64.ofNat D) (rt : rdN μ O 8 = 1)
    (hr : ∀ a, O ≤ a → a < O + 8 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 49510 ω μ x 68729 ω' μ x 6 ∧
      ω'[0] = UInt64.ofNat 2194 ∧ ω'[1] = UInt64.ofNat O ∧ ω'[5] = UInt64.ofNat D ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat D ∧ ω'[8] = UInt64.ofNat (O + 8) ∧ ω'[9] = UInt64.ofNat 96 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, hO, hD, rt, hr, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, h5, Nat.mod_eq_of_lt hD]

/-- 49529 … the return: ω₀, ω₅ restored from O + 112, O + 104, the frame closed (sp = O + 120). -/
theorem io_c {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (O r0 t v5 : Nat) (hO : 65536 ≤ O ∧ O + 120 < 4294967296) (h1 : ω[1] = UInt64.ofNat O)
    (r0' : rdN μ (O + 112) 8 = r0) (r5 : rdN μ (O + 104) 8 = v5)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) (hr : ∀ a, O + 104 ≤ a → a < O + 120 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 49529 ω μ x t ω' μ x 5 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (O + 120) ∧ ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = ω[6] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hO, r0', r5, hret, hjt, hbt, hr, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, Nat.mod_eq_of_lt (show r0 < 18446744073709551616 by omega),
      Nat.mod_eq_of_lt (rdN_lt64 μ (O + 104))]

end Services.Bootstrap.Fmt
