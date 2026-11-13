import Services.Bootstrap.Fmt.Memcpy
import Services.Bootstrap.Fmt.Tac
import Services.Bootstrap.Alloc.Rep

/-!
# A slice reader's `read_exact` (58434), and the `u64`/`u32` reads through it

The reader at Rd is a slice: its next octet's address `ptr` at Rd and the octets left `len` at
Rd + 8. `read_exact(Rd, dst, n)` (58434), with n ≤ len, copies the n octets at ptr to dst
(`memcpy`), moves the reader to (ptr + n, len − n) and returns 0 (`Ok`).

`rd_u64` (46040) and `rd_u32` (46008) read 8 and 4 octets through it into their own frame and
return 0 in ω₇ and the value in ω₈. These are frame-only: the values are not stated.

These are the steps:
- `re_a`: 58434 … `memcpy` (68729);
- `re_b`: 58474 … the return;
- `read_exact`: both, with `memcpy_frame`.
-/

namespace Services.Bootstrap.Fmt

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 58434 … 58468, n ≤ len: the 40-octet frame at sp − 40 (ω₀, ω₅, ω₆ at +32, +24, +16; ptr at +0,
    Rd at +8) and `memcpy(dst, ptr, n)` called, returning to 58474 (2550); n in ω₅ and len in ω₆. -/
theorem re_a {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp Rd dst n ptr len r0 v5 v6 : Nat) (hsp : 65536 + 40 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat Rd) (h8 : ω[8] = UInt64.ofNat dst)
    (h9 : ω[9] = UInt64.ofNat n)
    (hv : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616 ∧
      dst < 18446744073709551616 ∧ n < 18446744073709551616)
    (hRd : Rd + 16 ≤ sp - 40 ∨ sp ≤ Rd) (hRd1 : Rd + 16 < 4294967296)
    (rp : rdN μ Rd 8 = ptr) (rl : rdN μ (Rd + 8) 8 = len) (hn : n ≤ len)
    (hrR : ∀ a, Rd ≤ a → a < Rd + 16 → μ.readable a = true)
    (hw : ∀ a, sp - 40 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 58434 ω μ x 68729 ω' μ' x 16 ∧
      ω'[0] = UInt64.ofNat 2550 ∧ ω'[1] = UInt64.ofNat (sp - 40) ∧ ω'[5] = UInt64.ofNat n ∧
      ω'[6] = UInt64.ofNat len ∧ ω'[7] = UInt64.ofNat dst ∧ ω'[8] = UInt64.ofNat ptr ∧
      ω'[9] = UInt64.ofNat n ∧
      rdN μ' (sp - 40) 8 = ptr ∧ rdN μ' (sp - 40 + 8) 8 = Rd ∧ rdN μ' (sp - 40 + 16) 8 = v6 ∧
      rdN μ' (sp - 40 + 24) 8 = v5 ∧ rdN μ' (sp - 40 + 32) 8 = r0 ∧
      (∀ a, a < 4294967296 → (a < sp - 40 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 40 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hp64 : ptr < 18446744073709551616 := rp ▸ rdN_lt64 μ Rd
  have hl64 : len < 18446744073709551616 := rl ▸ rdN_lt64 μ (Rd + 8)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, h9, hsp, hv, hRd, hRd1, rp, rl, hn, hrR, hw, hr, hp64, hl64,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h0, h1, h5, h6, h7, h8, h9,
      Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt hv.2.2.1, Nat.mod_eq_of_lt hv.2.2.2.1,
      Nat.mod_eq_of_lt hv.2.2.2.2, Nat.mod_eq_of_lt hp64, Nat.mod_eq_of_lt hl64, rp, rl]

/-- 58474 … the return, after `memcpy`: the reader at Rd goes to (ptr + n, len − n), ω₀, ω₅, ω₆
    are restored from the frame at F = sp − 40, and 0 (`Ok`) is returned. -/
theorem re_b {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (F Rd n ptr len r0 t v5 v6 : Nat) (hF : 65536 ≤ F ∧ F + 40 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat F) (h5 : ω[5] = UInt64.ofNat n) (h6 : ω[6] = UInt64.ofNat len)
    (hn : n ≤ len) (hl : len < 18446744073709551616)
    (rp : rdN μ F 8 = ptr) (rR : rdN μ (F + 8) 8 = Rd) (r6 : rdN μ (F + 16) 8 = v6)
    (r5 : rdN μ (F + 24) 8 = v5) (r0' : rdN μ (F + 32) 8 = r0)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hRd : Rd + 16 ≤ F ∨ F + 40 ≤ Rd) (hRd1 : Rd + 16 < 4294967296) (hp : ptr + n < 18446744073709551616)
    (hr : ∀ a, F ≤ a → a < F + 40 → μ.readable a = true)
    (hwR : ∀ a, Rd ≤ a → a < Rd + 16 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 58474 ω μ x t ω' μ' x 14 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (F + 40) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0 ∧
      rdN μ' Rd 8 = ptr + n ∧ rdN μ' (Rd + 8) 8 = len - n ∧
      (∀ a, a < 4294967296 → (a < Rd ∨ Rd + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hn64 : n < 18446744073709551616 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hF, hn, hl, rp, rR, r6, r5, r0', hret, hjt, hbt, hRd, hRd1, hp, hr, hwR,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h5, h6,
      Nat.mod_eq_of_lt hn64, Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hp,
      Nat.mod_eq_of_lt (rdN_lt64 μ (F + 32)), Nat.mod_eq_of_lt (rdN_lt64 μ (F + 24)),
      Nat.mod_eq_of_lt (rdN_lt64 μ (F + 16)), rp, rR]

/-- **`read_exact` on a slice reader** (58434): from the reader at Rd (ω₇, holding ptr and len),
    dst (ω₈) and n ≤ len (ω₉), and a return address ω₀ that `djump` resolves to t, it copies the
    n octets at ptr to dst, moves the reader to (ptr + n, len − n) and returns 0 to t, with ω₀, ω₁,
    ω₅, ω₆ as they were. Memory changes only in sp − 88 … sp, dst … dst + n and Rd … Rd + 16. -/
theorem read_exact {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp Rd dst n ptr len r0 t : Nat) (hsp : 65536 + 88 ≤ sp ∧ sp < 4294967296 ∧ sp % 8 = 0)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat Rd)
    (h8 : ω[8] = UInt64.ofNat dst) (h9 : ω[9] = UInt64.ofNat n)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (rp : rdN μ Rd 8 = ptr) (rl : rdN μ (Rd + 8) 8 = len) (hn : n ≤ len)
    (hRd : Rd + 16 ≤ sp - 88 ∨ sp ≤ Rd) (hRd1 : Rd + 16 < 4294967296)
    (hs : 65536 ≤ ptr ∧ ptr + n + 16 < 4294967296) (hd : 65536 ≤ dst ∧ dst + n + 16 < 4294967296)
    (hdj : dst + n + 24 ≤ ptr ∨ ptr + n + 24 ≤ dst) (hfd : sp ≤ dst ∨ dst + n ≤ sp - 88)
    (hfs : sp ≤ ptr ∨ ptr + n + 16 ≤ sp - 88)
    (hRdd : Rd + 16 ≤ dst ∨ dst + n ≤ Rd)
    (hr : ∀ a, ptr ≤ a → a < ptr + n → μ.readable a = true)
    (hw : ∀ a, dst ≤ a → a < dst + n → μ.writable a = true)
    (hwR : ∀ a, Rd ≤ a → a < Rd + 16 → μ.writable a = true)
    (hwf : ∀ a, sp - 88 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 58434 ω μ x t ω' μ' x (7 * n + 350) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat 0 ∧
      rdN μ' Rd 8 = ptr + n ∧ rdN μ' (Rd + 8) 8 = len - n ∧
      (∀ a, a < 4294967296 → (a < dst ∨ dst + n ≤ a) → (a < sp - 88 ∨ sp ≤ a) → (a < Rd ∨ Rd + 16 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hl64 : len < 18446744073709551616 := rl ▸ rdN_lt64 μ (Rd + 8)
  have hrR : ∀ a, Rd ≤ a → a < Rd + 16 → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (hwR a h1 h2)
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, m0, m8, m16, m24, m32, fr1, rd1, wr1⟩ :=
    re_a (p := p) (P := P) (R := R) x ω μ sp Rd dst n ptr len r0 ω[5].toNat ω[6].toNat ⟨by omega, hsp.2.1⟩
      h0 h1 UInt64.ofNat_toNat.symm UInt64.ofNat_toNat.symm h7 h8 h9
      ⟨by omega, UInt64.toNat_lt _, UInt64.toNat_lt _, by omega, by omega⟩ (by omega) hRd1 rp rl hn hrR
      (fun a h1 h2 => hwf a (by omega) h2)
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, fr2, rd2, wr2⟩ := memcpy_frame (p := p) (P := P) (R := R) x ω1 μ1
    2550 58474 (sp - 40) dst ptr n a0 a1 a7 a8 a9 (by decide) jte_1274 bs_58474
    ⟨by omega, by omega, by omega⟩ hs hd hdj (by omega) (by omega)
    (fun a h1 h2 => by rw [rd1]; exact hr a h1 h2) (fun a h1 h2 => by rw [wr1]; exact hw a h1 h2)
    (fun a h1 h2 => by rw [wr1]; exact hwf a (by omega) (by omega))
  have k2 : ∀ a, sp - 40 ≤ a → a < sp → μ2.read a = μ1.read a := fun a h1 h2 =>
    fr2 a (by omega) (by omega) (Or.inr h1)
  obtain ⟨ω3, μ3, run3, c0, c1, c5, c6, c7, cp, cl, fr3, rd3, wr3⟩ := re_b (p := p) (P := P) (R := R) x ω2 μ2
    (sp - 40) Rd n ptr len r0 t ω[5].toNat ω[6].toNat ⟨by omega, by omega⟩ (b1.trans a1) (b5.trans a5)
    (b6.trans a6) hn hl64
    (by rw [rdN_frame (fun j hj => k2 _ (by omega) (by omega))]; exact m0)
    (by rw [rdN_frame (fun j hj => k2 _ (by omega) (by omega))]; exact m8)
    (by rw [rdN_frame (fun j hj => k2 _ (by omega) (by omega))]; exact m16)
    (by rw [rdN_frame (fun j hj => k2 _ (by omega) (by omega))]; exact m24)
    (by rw [rdN_frame (fun j hj => k2 _ (by omega) (by omega))]; exact m32)
    hret hjt hbt (by omega) hRd1 (by omega)
    (fun a h1 h2 => by rw [rd2, rd1]; exact Memory.readable_of_writable (hwf a (by omega) (by omega)))
    (fun a h1 h2 => by rw [wr2, wr1]; exact hwR a h1 h2)
  refine ⟨ω3, μ3, ((run1.trans run2).trans run3).mono (by omega), c0.trans h0.symm,
    by rw [c1, h1, show sp - 40 + 40 = sp by omega], c5.trans UInt64.ofNat_toNat,
    c6.trans UInt64.ofNat_toNat, c7, cp, cl, fun a ha hd' hf hR => ?_, fun a => ?_, fun a => ?_⟩
  · rw [fr3 a ha hR, fr2 a ha hd' (by omega), fr1 a ha (by omega)]
  · rw [rd3, rd2, rd1]
  · rw [wr3, wr2, wr1]

/-- 46040 … 46053: `rd_u64`'s 16-octet frame at sp − 16 (ω₀ at +8, the word 0 at +0) and
    `read_exact(Rd, sp − 16, 8)`, returning to 46059 (2068). -/
theorem u64_a {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp r0 : Nat) (hsp : 65536 + 16 ≤ sp ∧ sp < 4294967296) (h0 : ω[0] = UInt64.ofNat r0)
    (h1 : ω[1] = UInt64.ofNat sp) (hr0 : r0 < 18446744073709551616)
    (hw : ∀ a, sp - 16 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 46040 ω μ x 58434 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 2068 ∧ ω'[1] = UInt64.ofNat (sp - 16) ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = ω[7] ∧ ω'[8] = UInt64.ofNat (sp - 16) ∧ ω'[9] = UInt64.ofNat 8 ∧
      rdN μ' (sp - 16 + 8) 8 = r0 ∧
      (∀ a, a < 4294967296 → (a < sp - 16 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 16 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, hsp, hr0, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h0, h1,
      Nat.mod_eq_of_lt hr0]

/-- 46008 … 46023: `rd_u32`'s 16-octet frame at sp − 16 (ω₀ at +8, the u32 0 at +4) and
    `read_exact(Rd, sp − 12, 4)`, returning to 46029 (2066). -/
theorem u32_a {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp r0 : Nat) (hsp : 65536 + 16 ≤ sp ∧ sp < 4294967296) (h0 : ω[0] = UInt64.ofNat r0)
    (h1 : ω[1] = UInt64.ofNat sp) (hr0 : r0 < 18446744073709551616)
    (hw : ∀ a, sp - 16 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 46008 ω μ x 58434 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 2066 ∧ ω'[1] = UInt64.ofNat (sp - 16) ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = ω[7] ∧ ω'[8] = UInt64.ofNat (sp - 16 + 4) ∧ ω'[9] = UInt64.ofNat 4 ∧
      rdN μ' (sp - 16 + 8) 8 = r0 ∧
      (∀ a, a < 4294967296 → (a < sp - 16 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 16 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, hsp, hr0, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h0, h1,
      Nat.mod_eq_of_lt hr0]

/-- 46059 / 46029 … the return: the value reloaded into ω₈, ω₀ from F + 8, the frame closed. -/
theorem uN_b {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (i F r0 t : Nat) (hi : i = 46059 ∨ i = 46029) (hF : 65536 ≤ F ∧ F + 16 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat F) (r0' : rdN μ (F + 8) 8 = r0)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) (hr : ∀ a, F ≤ a → a < F + 16 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R i ω μ x t ω' μ x 4 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (F + 16) ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = ω[7] := by
  rw [show ω = regsNF ω [] from rfl]
  rcases hi with rfl | rfl
  all_goals
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, hF, r0', hret, hjt, hbt, hr, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      all_goals post_simp [h1, Nat.mod_eq_of_lt (show r0 < 18446744073709551616 by omega)]

/-- **`rd_u64` (46040) and `rd_u32` (46008) on a slice reader**, frame-only: from the reader at Rd
    (ω₇) with len ≥ k octets left at ptr (k = 8 or 4) and a return address ω₀ that `djump`
    resolves to t, they return 0 (`Ok`) in ω₇ to t, with ω₀, ω₁, ω₅, ω₆ as they were and the
    reader at (ptr + k, len − k). The value is not stated. Memory changes only in sp − 104 … sp and
    Rd … Rd + 16. -/
theorem rd_uN {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (e k sp Rd ptr len r0 t : Nat) (he : (e = 46040 ∧ k = 8) ∨ (e = 46008 ∧ k = 4))
    (hsp : 65536 + 104 ≤ sp ∧ sp < 4294967296 ∧ sp % 8 = 0)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat Rd)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (rp : rdN μ Rd 8 = ptr) (rl : rdN μ (Rd + 8) 8 = len) (hn : k ≤ len)
    (hRd : sp ≤ Rd) (hRd1 : Rd + 16 < 4294967296)
    (hs : sp + 24 ≤ ptr ∧ ptr + k + 16 < 4294967296) (hRp : Rd + 16 ≤ ptr ∨ ptr + k ≤ Rd)
    (hr : ∀ a, ptr ≤ a → a < ptr + k → μ.readable a = true)
    (hwR : ∀ a, Rd ≤ a → a < Rd + 16 → μ.writable a = true)
    (hwf : ∀ a, sp - 104 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R e ω μ x t ω' μ' x 420 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat 0 ∧
      rdN μ' Rd 8 = ptr + k ∧ rdN μ' (Rd + 8) 8 = len - k ∧
      (∀ a, a < 4294967296 → (a < sp - 104 ∨ sp ≤ a) → (a < Rd ∨ Rd + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr0 : r0 < 18446744073709551616 := by omega
  have entry : ∃ ω1 μ1 i ri, (i = 46059 ∨ i = 46029) ∧ FreeStepsH p R e ω μ x 58434 ω1 μ1 x 6 ∧
      ω1[0] = UInt64.ofNat ri ∧ (0 < ri ∧ ri ≤ 2806 ∧ ri % 2 = 0) ∧ ω1[1] = UInt64.ofNat (sp - 16) ∧
      ω1[5] = ω[5] ∧ ω1[6] = ω[6] ∧ ω1[7] = ω[7] ∧ ω1[9] = UInt64.ofNat k ∧
      (∃ dst, ω1[8] = UInt64.ofNat dst ∧ sp - 16 ≤ dst ∧ dst + k ≤ sp - 8) ∧
      rdN μ1 (sp - 16 + 8) 8 = r0 ∧ P.jumpTable.getD (ri / 2 - 1) 0 = i ∧
      P.isBlockStart i = true ∧
      (∀ a, a < 4294967296 → (a < sp - 16 ∨ sp ≤ a) → μ1.read a = μ.read a) ∧
      (∀ a, μ1.readable a = μ.readable a) ∧ (∀ a, μ1.writable a = μ.writable a) := by
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨ω1, μ1, run, a0, a1, a5, a6, a7, a8, a9, m8, fr, rd, wr⟩ := u64_a (p := p) (P := P) (R := R)
        x ω μ sp r0 ⟨by omega, by omega⟩ h0 h1 hr0 (fun a h1 h2 => hwf a (by omega) h2)
      exact ⟨ω1, μ1, 46059, 2068, Or.inl rfl, run, a0, by decide, a1, a5, a6, a7, a9, ⟨sp - 16, a8, by omega, by omega⟩, m8,
        jte_1033, bs_46059, fr, rd, wr⟩
    · obtain ⟨ω1, μ1, run, a0, a1, a5, a6, a7, a8, a9, m8, fr, rd, wr⟩ := u32_a (p := p) (P := P) (R := R)
        x ω μ sp r0 ⟨by omega, by omega⟩ h0 h1 hr0 (fun a h1 h2 => hwf a (by omega) h2)
      exact ⟨ω1, μ1, 46029, 2066, Or.inr rfl, run, a0, by decide, a1, a5, a6, a7, a9, ⟨sp - 16 + 4, a8, by omega, by omega⟩, m8,
        jte_1032, bs_46029, fr, rd, wr⟩
  obtain ⟨ω1, μ1, i, ri, hi, run1, a0, hri, a1, a5, a6, a7, a9, ⟨dst, a8, hd1, hd2⟩, m8, hji, hbi, fr1, rd1, wr1⟩ := entry
  have hk : k = 8 ∨ k = 4 := by omega
  have k1 : ∀ a, sp ≤ a → a < 4294967296 → μ1.read a = μ.read a := fun a h1 h2 => fr1 a h2 (Or.inr h1)
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, bp, bl, fr2, rd2, wr2⟩ := read_exact (p := p) (P := P) (R := R) x ω1
    μ1 (sp - 16) Rd dst k ptr len ri i ⟨by omega, by omega, by omega⟩ a0 a1 (a7.trans h7) a8 a9
    hri hji hbi
    (by rw [rdN_frame (fun j hj => k1 _ (by omega) (by omega))]; exact rp)
    (by rw [rdN_frame (fun j hj => k1 _ (by omega) (by omega))]; exact rl) hn (Or.inr (by omega)) hRd1
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
    (Or.inr (by omega)) (fun a h1 h2 => by rw [rd1]; exact hr a h1 h2)
    (fun a h1 h2 => by rw [wr1]; exact hwf a (by omega) (by omega))
    (fun a h1 h2 => by rw [wr1]; exact hwR a h1 h2)
    (fun a h1 h2 => by rw [wr1]; exact hwf a (by omega) (by omega))
  obtain ⟨ω3, run3, c0, c1, c5, c6, c7⟩ := uN_b (p := p) (P := P) (R := R) x ω2 μ2 i (sp - 16) r0 t hi
    ⟨by omega, by omega⟩ (b1.trans a1)
    (by rw [rdN_frame (fun j hj => fr2 _ (by omega) (by omega) (Or.inr (by omega)) (Or.inl (by omega)))]; exact m8)
    hret hjt hbt (fun a h1 h2 => by rw [rd2, rd1]; exact Memory.readable_of_writable (hwf a (by omega) (by omega)))
  refine ⟨ω3, μ2, ((run1.trans run2).trans run3).mono (by omega), c0.trans h0.symm,
    by rw [c1, h1, show sp - 16 + 16 = sp by omega], c5.trans (b5.trans a5), c6.trans (b6.trans a6), c7.trans b7,
    bp, bl, fun a ha h1 h2 => ?_, fun a => by rw [rd2, rd1], fun a => by rw [wr2, wr1]⟩
  rw [fr2 a ha (by omega) (by omega) h2, fr1 a ha (by omega)]

end Services.Bootstrap.Fmt
