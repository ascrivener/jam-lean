import Services.Bootstrap.Acc.Handlers.KeyEnc
import Services.Bootstrap.Fmt.ReadExact

/-!
# The ring slot's typed `get` (34377)

`add_recent_work_item` reads ring slot c (`RecentWorkItem(c)`) with the function at 34377: from out
(ω₇) and a key value at kp (ω₈), in a 112-octet frame at S = sp − 112,
1. 34377 … 34394: ω₀, ω₅, ω₆ saved at S + 104, + 96, + 88; out kept in ω₅; the key encoder (33843,
   `kb_call`) builds the key's `Vec` at S + 56 (return address 1598 → 34400);
2. 34400 … 34411: `get` (47857, `get_call`) of the key, its `Option<Vec<u8>>` at S + 24 (return
   address 1600 → 34417);
3. 34417 … 34428: the key's buffer is freed if its capacity is not 0 (`dealloc`, 40613; return
   address 1602 → 34434);
4. 34434: `None` (the word −1 at S + 24): the `u16` 0 (`None`) at out, and the return;
5. otherwise the value is read as a slice reader {vptr, vlen} at S + 8: `read_exact` (58434) of 32
   octets into S + 56 (return address 1604 → 34485), copied to S + 24, then of 2 octets into S + 56
   (1606 → 34531). If either read is short, the `u16` 0 at out (34534); otherwise (34571) the 32
   octets at out + 2, the `u16` at out + 34 and the `u16` 1 (`Some`) at out;
6. the value's buffer is freed if its capacity is not 0 (34610, `dealloc`; return address 1608 →
   34623), and the return.

This file proves the straight-line segments, and `re_short` (`read_exact` with fewer octets left than
asked: ω₇ = 1).
-/

namespace Services.Bootstrap.Acc.Handlers.RecentSlot

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **`read_exact` on a slice reader with fewer octets left than asked** (58434, len < n): it returns
    1 (`Err`) in ω₇ to t, with ω₀, ω₁, ω₅, ω₆ as they were; memory changes only in sp − 40 … sp. -/
theorem re_short {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp Rd n len r0 t : Nat) (hsp : 65536 + 40 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat Rd)
    (h9 : ω[9] = UInt64.ofNat n) (hn64 : n < 18446744073709551616)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (rl : rdN μ (Rd + 8) 8 = len) (hn : len < n) (hRd1 : Rd + 16 < 4294967296)
    (hRd : Rd + 16 ≤ sp - 40 ∨ sp ≤ Rd)
    (hrR : ∀ a, Rd + 8 ≤ a → a < Rd + 16 → μ.readable a = true)
    (hw : ∀ a, sp - 40 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 58434 ω μ x t ω' μ' x 14 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat 1 ∧
      (∀ a, a < 4294967296 → (a < sp - 40 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 40 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hl64 : len < 18446744073709551616 := rl ▸ rdN_lt64 μ (Rd + 8)
  have hr0 : r0 < 18446744073709551616 := by omega
  have q0 : ω[0].toNat = r0 := by rw [h0]; exact UInt64.toNat_ofNat_of_lt' hr0
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h7, h9, hsp, hn64, hRd, hRd1, rl, hn, hrR, hw, hr, hl64, hret, hjt, hbt,
      Nat.mod_eq_of_lt hr0, Nat.mod_eq_of_lt hn64, Nat.mod_eq_of_lt hl64,
      Nat.mod_eq_of_lt (UInt64.toNat_lt ω[5]), Nat.mod_eq_of_lt (UInt64.toNat_lt ω[6]),
      rdN_writeN_disjoint, Fmt.rdN_writeN_same8, Num.decodeLE_encodeLE, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, Fmt.rdN_writeN_same8, Num.decodeLE_encodeLE, h0, h1, h7, h9,
      Nat.mod_eq_of_lt hn64, Nat.mod_eq_of_lt hl64, rl, UInt64.ofNat_toNat]

/-- **34377 … 34394**: the 112-octet frame at S = sp − 112 (ω₀, ω₅, ω₆ saved at sp − 8, − 16, − 24),
    out (ω₇) kept in ω₅, and the call of the key encoder (33843) with out ω₇ = sp − 56, the key
    value ω₈ as it was and return address 1598. -/
theorem sg_pre {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp out : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat out)
    (hout : out < 18446744073709551616) (hsp : 65536 + 112 ≤ sp ∧ sp < 4294967296) (hw : ∀ a, sp - 24 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 34377 ω μ x 33843 ω' μ' x 7 ∧
      ω'[0] = UInt64.ofNat 1598 ∧ ω'[1] = UInt64.ofNat (sp - 112) ∧ ω'[5] = UInt64.ofNat out ∧
      ω'[7] = UInt64.ofNat (sp - 56) ∧ ω'[8] = ω[8] ∧
      μ'.readN (sp - 8) 8 = Num.encodeLE 8 ω[0].toNat ∧ μ'.readN (sp - 16) 8 = Num.encodeLE 8 ω[5].toNat ∧
      μ'.readN (sp - 24) 8 = Num.encodeLE 8 ω[6].toNat ∧
      (∀ a, a < 4294967296 → (a < sp - 24 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hsp, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp only [show sp - 112 + 104 = sp - 8 by omega, show sp - 112 + 96 = sp - 16 by omega,
      show sp - 112 + 88 = sp - 24 by omega, show sp - 112 + 56 = sp - 56 by omega]
    all_goals post_simp [h1, h7, Nat.mod_eq_of_lt hout]

/-- **34400 … 34411**: the key's `Vec` `{cap, ptr, len}` at S + 56; the call of `get` (47857) with out
    ω₇ = S + 24, the key ω₈ = ptr (ω₉ = len octets), ptr kept in ω₆ and return address 1600. -/
theorem sg_get {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (S ptr len : Nat) (h1 : ω[1] = UInt64.ofNat S) (hS : S + 112 < 4294967296)
    (hptr : ptr < 18446744073709551616) (hlen : len < 18446744073709551616)
    (mp : μ.readN (S + 64) 8 = Num.encodeLE 8 ptr) (ml : μ.readN (S + 72) 8 = Num.encodeLE 8 len)
    (hr : ∀ a, S + 64 ≤ a → a < S + 80 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 34400 ω μ x 47857 ω' μ x 5 ∧
      ω'[0] = UInt64.ofNat 1600 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = ω[5] ∧ ω'[6] = UInt64.ofNat ptr ∧
      ω'[7] = UInt64.ofNat (S + 24) ∧ ω'[8] = UInt64.ofNat ptr ∧ ω'[9] = UInt64.ofNat len := by
  have rp := Handlers.DesignateAlloc.rd8 hptr mp
  have rl := Handlers.DesignateAlloc.rd8 hlen ml
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hS, rp, rl, hr, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1]

/-- **34417 … 34428**, the key's capacity cap ≠ 0 (at S + 56): the call of `dealloc` (40613) with
    ω₇ = ω₆ and return address 1602. -/
theorem sg_dl {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (S cap : Nat) (h1 : ω[1] = UInt64.ofNat S) (hS : S + 112 < 4294967296)
    (hcap : cap < 18446744073709551616) (hc0 : cap ≠ 0) (mc : μ.readN (S + 56) 8 = Num.encodeLE 8 cap)
    (hr : ∀ a, S + 56 ≤ a → a < S + 64 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 34417 ω μ x 40613 ω' μ x 5 ∧
      ω'[0] = UInt64.ofNat 1602 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = ω[6] := by
  have rc := Handlers.DesignateAlloc.rd8 hcap mc
  have hc0' : cap % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt hcap]; exact hc0
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hS, rc, hc0', hr, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1]

/-- **34434 … the return**, `get` returned `None` (the word −1 at S + 24): the `u16` 0 at out (ω₅),
    ω₀, ω₅, ω₆ restored from S + 104, + 96, + 88, the frame popped and the return to t. -/
theorem sg_none {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (S out r0 v5 v6 t : Nat) (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat out)
    (hS : 65536 ≤ S ∧ S + 112 < 4294967296) (hout : out + 2 < 4294967296)
    (dout : out + 2 ≤ S + 88 ∨ S + 112 ≤ out)
    (m24 : μ.readN (S + 24) 8 = Num.encodeLE 8 18446744073709551615)
    (m104 : μ.readN (S + 104) 8 = Num.encodeLE 8 r0) (m96 : μ.readN (S + 96) 8 = Num.encodeLE 8 v5)
    (m88 : μ.readN (S + 88) 8 = Num.encodeLE 8 v6)
    (hr0 : r0 < 18446744073709551616) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hr : ∀ a, S + 24 ≤ a → a < S + 112 → μ.readable a = true)
    (hw : ∀ a, out ≤ a → a < out + 2 → μ.writable a = true) :
    ∃ ω', FreeStepsH p R 34434 ω μ x t ω' (μ.writeN out (Num.encodeLE 2 0)) x 10 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (S + 112) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 := by
  have q24 := Handlers.DesignateAlloc.rd8 (by decide) m24
  have q104 := Handlers.DesignateAlloc.rd8 hr0 m104
  have q96 := Handlers.DesignateAlloc.rd8 hv5 m96
  have q88 := Handlers.DesignateAlloc.rd8 hv6 m88
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, hS, hout, dout, q24, q104, q96, q88, hret, hjt, hbt, hr, hw, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, h5]

end Services.Bootstrap.Acc.Handlers.RecentSlot
