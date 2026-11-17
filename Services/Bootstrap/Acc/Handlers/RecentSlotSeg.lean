import Services.Bootstrap.Acc.Handlers.RecentSlot

/-!
# The ring slot's typed `get` (34377): the segments after `get`

The straight-line pieces of 34377 from `get`'s `Some` (34434) on, in the 112-octet frame at S:
- `sg_some` (34434 → 58434): the value's `Vec` {cap, ptr, len} at S + 24, cap ≠ −1: cap kept in
  ω₆, ptr saved at S, the reader {ptr, len} at S + 8, and `read_exact` of 32 octets into S + 56;
- `sg_r2` (34485 → 58434, the first read gave 0): the 32 octets copied to S + 24, then
  `read_exact` of 2 octets into S + 56;
- `sg_short0` / `sg_shortD` (34485 or 34531, a read gave 1): the `u16` 0 (`None`) at out, then the
  return (cap = 0) or `dealloc` of the value's buffer (cap ≠ 0);
- `sg_ok0` / `sg_okD` (34531, the second read gave 0): the 32 octets at out + 2, the 2 at out + 34,
  the `u16` 1 (`Some`) at out, then the return (cap = 0) or `dealloc` (cap ≠ 0);
- `sg_ret` (34623, `dealloc`'s return): the return.
-/

namespace Services.Bootstrap.Acc.Handlers.RecentSlot

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **34434 … 34479**, `get` returned `Some` (the value's `Vec` {cap, ptr, len} at S + 24 with
    cap ≠ −1): cap in ω₆, ptr at S, the slice reader {ptr, len} at S + 8, the 32 octets at S + 56
    zeroed, and the call of `read_exact` (58434) with ω₇ = S + 8, ω₈ = S + 56, ω₉ = 32 and return
    address 1604. Memory changes only in S … S + 24 and S + 56 … S + 88. -/
theorem sg_some {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (S cap ptr len : Nat) (h1 : ω[1] = UInt64.ofNat S) (hS : 65536 ≤ S ∧ S + 112 < 4294967296)
    (hcap : cap < 18446744073709551616) (hc1 : cap ≠ 18446744073709551615)
    (hptr : ptr < 18446744073709551616) (hlen : len < 18446744073709551616)
    (mc : μ.readN (S + 24) 8 = Num.encodeLE 8 cap) (mp : μ.readN (S + 32) 8 = Num.encodeLE 8 ptr)
    (ml : μ.readN (S + 40) 8 = Num.encodeLE 8 len)
    (hw : ∀ a, S ≤ a → a < S + 112 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 34434 ω μ x 58434 ω' μ' x 17 ∧
      ω'[0] = UInt64.ofNat 1604 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = ω[5] ∧ ω'[6] = UInt64.ofNat cap ∧
      ω'[7] = UInt64.ofNat (S + 8) ∧ ω'[8] = UInt64.ofNat (S + 56) ∧ ω'[9] = UInt64.ofNat 32 ∧
      μ'.readN S 8 = Num.encodeLE 8 ptr ∧ μ'.readN (S + 8) 8 = Num.encodeLE 8 ptr ∧
      μ'.readN (S + 16) 8 = Num.encodeLE 8 len ∧
      (∀ a, a < 4294967296 → (a < S ∨ S + 24 ≤ a) → (a < S + 56 ∨ S + 88 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S ≤ a → a < S + 112 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have qc := Handlers.DesignateAlloc.rd8 hcap mc
  have qp := Handlers.DesignateAlloc.rd8 hptr mp
  have ql := Handlers.DesignateAlloc.rd8 hlen ml
  have hc1' : cap % 18446744073709551616 ≠ 18446744073709551615 := by rw [Nat.mod_eq_of_lt hcap]; exact hc1
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hS, qc, qp, ql, hc1', hr, hw, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [h1, Nat.mod_eq_of_lt hptr, Nat.mod_eq_of_lt hlen, Nat.mod_eq_of_lt hcap]

/-- **34485 … 34525**, the first `read_exact` returned 0: the four words w₀ … w₃ at S + 56 copied to
    S + 24, the `u16` 0 at S + 56, and the call of `read_exact` (58434) with ω₇ = S + 8, ω₈ = S + 56,
    ω₉ = 2 and return address 1606. Memory changes only in S + 24 … S + 58. -/
theorem sg_r2 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (S w0 w1 w2 w3 : Nat) (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat 0)
    (hS : 65536 ≤ S ∧ S + 112 < 4294967296)
    (hw0 : w0 < 18446744073709551616) (hw1 : w1 < 18446744073709551616)
    (hw2 : w2 < 18446744073709551616) (hw3 : w3 < 18446744073709551616)
    (m0 : μ.readN (S + 56) 8 = Num.encodeLE 8 w0) (m1 : μ.readN (S + 64) 8 = Num.encodeLE 8 w1)
    (m2 : μ.readN (S + 72) 8 = Num.encodeLE 8 w2) (m3 : μ.readN (S + 80) 8 = Num.encodeLE 8 w3)
    (hw : ∀ a, S ≤ a → a < S + 112 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 34485 ω μ x 58434 ω' μ' x 15 ∧
      ω'[0] = UInt64.ofNat 1606 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (S + 8) ∧ ω'[8] = UInt64.ofNat (S + 56) ∧ ω'[9] = UInt64.ofNat 2 ∧
      μ'.readN (S + 24) 8 = Num.encodeLE 8 w0 ∧ μ'.readN (S + 32) 8 = Num.encodeLE 8 w1 ∧
      μ'.readN (S + 40) 8 = Num.encodeLE 8 w2 ∧ μ'.readN (S + 48) 8 = Num.encodeLE 8 w3 ∧
      (∀ a, a < 4294967296 → (a < S + 24 ∨ S + 58 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S ≤ a → a < S + 112 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have q0 := Handlers.DesignateAlloc.rd8 hw0 m0
  have q1 := Handlers.DesignateAlloc.rd8 hw1 m1
  have q2 := Handlers.DesignateAlloc.rd8 hw2 m2
  have q3 := Handlers.DesignateAlloc.rd8 hw3 m3
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hS, q0, q1, q2, q3, hr, hw, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [h1, h7, Nat.mod_eq_of_lt hw0, Nat.mod_eq_of_lt hw1, Nat.mod_eq_of_lt hw2,
      Nat.mod_eq_of_lt hw3]

/-- **34485 or 34531 … the return**, a read returned r ≠ 0 and the value's capacity (ω₆) is 0: the
    `u16` 0 (`None`) at out (ω₅), ω₀, ω₅, ω₆ restored from S + 104, + 96, + 88, the frame popped and
    the return to t. -/
theorem sg_short0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (i S out r r0 v5 v6 t : Nat) (hi : i = 34485 ∨ i = 34531) (h1 : ω[1] = UInt64.ofNat S)
    (h5 : ω[5] = UInt64.ofNat out) (h6 : ω[6] = UInt64.ofNat 0) (h7 : ω[7] = UInt64.ofNat r)
    (hr64 : r < 18446744073709551616) (hr0' : r ≠ 0)
    (hS : 65536 ≤ S ∧ S + 112 < 4294967296) (hout : S + 112 ≤ out ∧ out + 36 < 4294967296)
    (m104 : μ.readN (S + 104) 8 = Num.encodeLE 8 r0) (m96 : μ.readN (S + 96) 8 = Num.encodeLE 8 v5)
    (m88 : μ.readN (S + 88) 8 = Num.encodeLE 8 v6)
    (hr0 : r0 < 18446744073709551616) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hr : ∀ a, S + 88 ≤ a → a < S + 112 → μ.readable a = true)
    (hw : ∀ a, out ≤ a → a < out + 2 → μ.writable a = true) :
    ∃ ω', FreeStepsH p R i ω μ x t ω' (μ.writeN out (Num.encodeLE 2 0)) x 9 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (S + 112) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 := by
  have q104 := Handlers.DesignateAlloc.rd8 hr0 m104
  have q96 := Handlers.DesignateAlloc.rd8 hv5 m96
  have q88 := Handlers.DesignateAlloc.rd8 hv6 m88
  have hr' : r % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt hr64]; exact hr0'
  rw [show ω = regsNF ω [] from rfl]
  rcases hi with rfl | rfl
  all_goals
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h5, h6, h7, hr', hS, hout, q104, q96, q88, hret, hjt, hbt, hr, hw, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_⟩
      all_goals post_simp [h1, h5]

/-- **34485 or 34531 … 34617**, a read returned r ≠ 0 and the value's capacity cap (ω₆) is not 0: the
    `u16` 0 (`None`) at out (ω₅), and the call of `dealloc` (40613) with ω₇ = the pointer saved at S
    and return address 1608. -/
theorem sg_shortD {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (i S out r cap ptr : Nat) (hi : i = 34485 ∨ i = 34531) (h1 : ω[1] = UInt64.ofNat S)
    (h5 : ω[5] = UInt64.ofNat out) (h6 : ω[6] = UInt64.ofNat cap) (h7 : ω[7] = UInt64.ofNat r)
    (hr64 : r < 18446744073709551616) (hr0' : r ≠ 0) (hcap : cap < 18446744073709551616) (hc0 : cap ≠ 0)
    (hptr : ptr < 18446744073709551616)
    (hS : 65536 ≤ S ∧ S + 112 < 4294967296) (hout : S + 112 ≤ out ∧ out + 36 < 4294967296)
    (mp : μ.readN S 8 = Num.encodeLE 8 ptr)
    (hr : ∀ a, S ≤ a → a < S + 8 → μ.readable a = true)
    (hw : ∀ a, out ≤ a → a < out + 2 → μ.writable a = true) :
    ∃ ω', FreeStepsH p R i ω μ x 40613 ω' (μ.writeN out (Num.encodeLE 2 0)) x 7 ∧
      ω'[0] = UInt64.ofNat 1608 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat out ∧
      ω'[6] = UInt64.ofNat cap ∧ ω'[7] = UInt64.ofNat ptr := by
  have qp := Handlers.DesignateAlloc.rd8 hptr mp
  have hr' : r % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt hr64]; exact hr0'
  have hc' : cap % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt hcap]; exact hc0
  rw [show ω = regsNF ω [] from rfl]
  rcases hi with rfl | rfl
  all_goals
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h5, h6, h7, hr', hc', hS, hout, qp, hr, hw, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      all_goals post_simp [h1, h5, h6]

/-- The `Some` record at out: the four words w₀ … w₃ at out + 2, the `u16` k at out + 34 and the
    `u16` 1 at out. -/
def okMem (μ : Memory) (out w0 w1 w2 w3 k : Nat) : Memory :=
  ((((((μ.writeN (out + 2) (Num.encodeLE 8 w0)).writeN (out + 10) (Num.encodeLE 8 w1)).writeN (out + 18)
    (Num.encodeLE 8 w2)).writeN (out + 26) (Num.encodeLE 8 w3)).writeN (out + 34) (Num.encodeLE 2 k)).writeN out
    (Num.encodeLE 2 1))

/-- **34531 … the return**, the second read returned 0 and the value's capacity (ω₆) is 0: the
    `Some` record (`okMem`, from the words at S + 24 … S + 56 and the `u16` at S + 56) at out (ω₅),
    then ω₀, ω₅, ω₆ restored, the frame popped and the return to t. -/
theorem sg_ok0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (S out w0 w1 w2 w3 k r0 v5 v6 t : Nat) (h1 : ω[1] = UInt64.ofNat S)
    (h5 : ω[5] = UInt64.ofNat out) (h6 : ω[6] = UInt64.ofNat 0) (h7 : ω[7] = UInt64.ofNat 0)
    (hS : 65536 ≤ S ∧ S + 112 < 4294967296) (hout : S + 112 ≤ out ∧ out + 36 < 4294967296)
    (hw0 : w0 < 18446744073709551616) (hw1 : w1 < 18446744073709551616)
    (hw2 : w2 < 18446744073709551616) (hw3 : w3 < 18446744073709551616) (hk : k < 65536)
    (m0 : μ.readN (S + 24) 8 = Num.encodeLE 8 w0) (m1 : μ.readN (S + 32) 8 = Num.encodeLE 8 w1)
    (m2 : μ.readN (S + 40) 8 = Num.encodeLE 8 w2) (m3 : μ.readN (S + 48) 8 = Num.encodeLE 8 w3)
    (mk : μ.readN (S + 56) 2 = Num.encodeLE 2 k)
    (m104 : μ.readN (S + 104) 8 = Num.encodeLE 8 r0) (m96 : μ.readN (S + 96) 8 = Num.encodeLE 8 v5)
    (m88 : μ.readN (S + 88) 8 = Num.encodeLE 8 v6)
    (hr0 : r0 < 18446744073709551616) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hr : ∀ a, S + 24 ≤ a → a < S + 112 → μ.readable a = true)
    (hw : ∀ a, out ≤ a → a < out + 36 → μ.writable a = true) :
    ∃ ω', FreeStepsH p R 34531 ω μ x t ω' (okMem μ out w0 w1 w2 w3 k) x 21 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (S + 112) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 := by
  have q0 := Handlers.DesignateAlloc.rd8 hw0 m0
  have q1 := Handlers.DesignateAlloc.rd8 hw1 m1
  have q2 := Handlers.DesignateAlloc.rd8 hw2 m2
  have q3 := Handlers.DesignateAlloc.rd8 hw3 m3
  have qk : rdN μ (S + 56) 2 = k := by
    show Num.decodeLE _ = _; rw [mk, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (by simpa using hk)]
  have q104 := Handlers.DesignateAlloc.rd8 hr0 m104
  have q96 := Handlers.DesignateAlloc.rd8 hv5 m96
  have q88 := Handlers.DesignateAlloc.rd8 hv6 m88
  unfold okMem
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, h6, h7, hS, hout, q0, q1, q2, q3, qk, q104, q96, q88, hret, hjt, hbt, hr, hw,
      Nat.mod_eq_of_lt hk, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, h5]

/-- **34531 … 34617**, the second read returned 0 and the value's capacity cap (ω₆) is not 0: the
    `Some` record (`okMem`) at out (ω₅), then the call of `dealloc` (40613) with ω₇ = the pointer
    saved at S and return address 1608. -/
theorem sg_okD {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (S out w0 w1 w2 w3 k cap ptr : Nat) (h1 : ω[1] = UInt64.ofNat S)
    (h5 : ω[5] = UInt64.ofNat out) (h6 : ω[6] = UInt64.ofNat cap) (h7 : ω[7] = UInt64.ofNat 0)
    (hcap : cap < 18446744073709551616) (hc0 : cap ≠ 0) (hptr : ptr < 18446744073709551616)
    (hS : 65536 ≤ S ∧ S + 112 < 4294967296) (hout : S + 112 ≤ out ∧ out + 36 < 4294967296)
    (hw0 : w0 < 18446744073709551616) (hw1 : w1 < 18446744073709551616)
    (hw2 : w2 < 18446744073709551616) (hw3 : w3 < 18446744073709551616) (hk : k < 65536)
    (m0 : μ.readN (S + 24) 8 = Num.encodeLE 8 w0) (m1 : μ.readN (S + 32) 8 = Num.encodeLE 8 w1)
    (m2 : μ.readN (S + 40) 8 = Num.encodeLE 8 w2) (m3 : μ.readN (S + 48) 8 = Num.encodeLE 8 w3)
    (mk : μ.readN (S + 56) 2 = Num.encodeLE 2 k) (mp : μ.readN S 8 = Num.encodeLE 8 ptr)
    (hr : ∀ a, S ≤ a → a < S + 112 → μ.readable a = true)
    (hw : ∀ a, out ≤ a → a < out + 36 → μ.writable a = true) :
    ∃ ω', FreeStepsH p R 34531 ω μ x 40613 ω' (okMem μ out w0 w1 w2 w3 k) x 19 ∧
      ω'[0] = UInt64.ofNat 1608 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat out ∧
      ω'[6] = UInt64.ofNat cap ∧ ω'[7] = UInt64.ofNat ptr := by
  have q0 := Handlers.DesignateAlloc.rd8 hw0 m0
  have q1 := Handlers.DesignateAlloc.rd8 hw1 m1
  have q2 := Handlers.DesignateAlloc.rd8 hw2 m2
  have q3 := Handlers.DesignateAlloc.rd8 hw3 m3
  have qk : rdN μ (S + 56) 2 = k := by
    show Num.decodeLE _ = _; rw [mk, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (by simpa using hk)]
  have qp := Handlers.DesignateAlloc.rd8 hptr mp
  have hc' : cap % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt hcap]; exact hc0
  unfold okMem
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, h6, h7, hc', hS, hout, q0, q1, q2, q3, qk, qp, hr, hw,
      Nat.mod_eq_of_lt hk, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, h5, h6]

/-- **34623 … the return** (`dealloc`'s return): ω₀, ω₅, ω₆ restored from S + 104, + 96, + 88, the
    frame popped and the return to t. -/
theorem sg_ret {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (S r0 v5 v6 t : Nat) (h1 : ω[1] = UInt64.ofNat S) (hS : 65536 ≤ S ∧ S + 112 < 4294967296)
    (m104 : μ.readN (S + 104) 8 = Num.encodeLE 8 r0) (m96 : μ.readN (S + 96) 8 = Num.encodeLE 8 v5)
    (m88 : μ.readN (S + 88) 8 = Num.encodeLE 8 v6)
    (hr0 : r0 < 18446744073709551616) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hr : ∀ a, S + 88 ≤ a → a < S + 112 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 34623 ω μ x t ω' μ x 5 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (S + 112) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 := by
  have q104 := Handlers.DesignateAlloc.rd8 hr0 m104
  have q96 := Handlers.DesignateAlloc.rd8 hv5 m96
  have q88 := Handlers.DesignateAlloc.rd8 hv6 m88
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hS, q104, q96, q88, hret, hjt, hbt, hr, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1]

end Services.Bootstrap.Acc.Handlers.RecentSlot
