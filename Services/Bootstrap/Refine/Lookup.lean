import Services.Bootstrap.Refine.Pass
import Services.Bootstrap.Refine.LookupHost
import Services.Bootstrap.Refine.Exit

/-!
# Refine's eager `Lookup` handler (5278 … 5558), the straight-line pieces

`Instruction::Lookup { service, hash, eager }` (dispatch index 8) with `eager` set: refine calls the SDK's
`foreign_historical_lookup` (49015), which makes Ω_H (host 7, GP v0.8.0 Appendix B.4) twice, first for the
preimage's length and then into a fresh buffer of that length; formats and logs the result (5398 → 59375, 5428,
5441); pushes `LookedUp(result)`; drops the staged element (4046) and goes round (5042). The staged element is at
M + 304: the service id (u32) at M + 312, the hash at the input element's octets 12 … 44 (ω₅ = cur), the flag at
M + 348. The pieces of `foreign_historical_lookup` itself are in `LookupWrap.lean`.
-/

namespace Services.Bootstrap.Refine.Lookup

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeR
  Services.Bootstrap.Encode.Writer

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- A u32 read back from its encoding. -/
theorem rd4 {μ : Memory} {a w : Nat} (hw : w < 2 ^ 32) (h : μ.readN a 4 = Num.encodeLE 4 w) : rdN μ a 4 = w := by
  show Num.decodeLE _ = _
  rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hw]

/-- A u32 sign-extended and then zero-extended by the shift pair (`shlo_l 32`, `shlo_r 32`) is itself. -/
theorem zext32 {svc : Nat} (h : svc < 4294967296) :
    ((if svc < 2147483648 then (svc : Int) else (svc : Int) - 4294967296) % 18446744073709551616).toNat *
      4294967296 % 18446744073709551616 / 4294967296 = svc := by
  split <;> omega

/-- 5095 … 5288: back from the staging copy, an element of index 8 (`Lookup`, D = 2^63 + 7) whose flag (the staged
    octet at M + 348) is set goes on into the eager handler at 5288. -/
theorem ld {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (M : Nat) (hb : rdN μ (M + 348) 1 ≠ 0) (hM : M + 632 ≤ 4294967296)
    (h1 : ω[1] = UInt64.ofNat M) (h6 : ω[6] = UInt64.ofNat (9223372036854775807 + 8))
    (s128 : μ.readN (M + 128) 8 = Num.encodeLE 8 9223372036854775832)
    (s136 : μ.readN (M + 136) 8 = Num.encodeLE 8 9223372036854775809)
    (hr : ∀ a, M + 128 ≤ a → a < M + 144 → μ.readable a = true)
    (hr2 : ∀ a, M + 348 ≤ a → a < M + 349 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 5095 ω μ x 5288 ω' μ x 12 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have r128 := rd8 (by decide) s128
  have r136 := rd8 (by decide) s136
  have hb' : ¬ rdN μ (M + 348) 1 % 18446744073709551616 = 0 := by
    have := rdN_lt μ (M + 348) 1
    rw [Nat.mod_eq_of_lt (by omega)]; exact hb
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h6, hM, hr, hr2, hb', r128, r136, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_⟩ <;> simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
      List.lookup_nil, Option.getD_none, h6]

/-- 5288 … 5366: the hash (the input element's octets 12 … 44, at `cur` = ω₅) is copied to M + 168 … M + 200;
    `foreign_historical_lookup`'s frame G = M − 48 holds the service id (zero-extended, from the u32 at M + 312) at
    G, the hash's address M + 168 at G + 8, the output address M + 560 at G + 16, ω₆, ω₅ at G + 24, G + 32 and the
    return address 170 at G + 40; at the `ecalli 7` (5366) ω₇ = the service id, ω₈ = M + 168 and ω₉ = ω₁₀ = ω₁₁ = 0
    (the length query). Memory changes only at M − 48 … M and M + 168 … M + 200. -/
theorem la {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (M cur svc : Nat) (hM : 65536 ≤ M ∧ M + 632 ≤ 4294967296 ∧ M % 8 = 0)
    (hcur : cur + 44 ≤ 4294967296) (hcM : cur + 44 ≤ M - 48 ∨ M + 200 ≤ cur ∨ (M ≤ cur ∧ cur + 44 ≤ M + 168))
    (hsvc : svc < 4294967296)
    (h1 : ω[1] = UInt64.ofNat M) (h5 : ω[5] = UInt64.ofNat cur)
    (s312 : μ.readN (M + 312) 4 = Num.encodeLE 4 svc)
    (hr : ∀ a, cur + 12 ≤ a → a < cur + 44 → μ.readable a = true)
    (hr2 : ∀ a, M + 312 ≤ a → a < M + 316 → μ.readable a = true)
    (hw : ∀ a, M - 48 ≤ a → a < M → μ.writable a = true)
    (hw2 : ∀ a, M + 168 ≤ a → a < M + 200 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 5288 ω μ x 5366 ω' μ' x 26 ∧ ω'[1] = UInt64.ofNat (M - 48) ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat svc ∧ ω'[8] = UInt64.ofNat (M + 168) ∧
      ω'[9] = UInt64.ofNat 0 ∧ ω'[10] = UInt64.ofNat 0 ∧ ω'[11] = UInt64.ofNat 0 ∧
      μ'.readN (M + 168) 8 = μ.readN (cur + 12) 8 ∧ μ'.readN (M + 176) 8 = μ.readN (cur + 20) 8 ∧
      μ'.readN (M + 184) 8 = μ.readN (cur + 28) 8 ∧ μ'.readN (M + 192) 8 = μ.readN (cur + 36) 8 ∧
      μ'.readN (M - 48) 8 = Num.encodeLE 8 svc ∧ μ'.readN (M - 48 + 8) 8 = Num.encodeLE 8 (M + 168) ∧
      μ'.readN (M - 48 + 16) 8 = Num.encodeLE 8 (M + 560) ∧ μ'.readN (M - 48 + 24) 8 = Num.encodeLE 8 ω[6].toNat ∧
      μ'.readN (M - 48 + 32) 8 = Num.encodeLE 8 cur ∧ μ'.readN (M - 48 + 40) 8 = Num.encodeLE 8 170 ∧
      (∀ a, a < 4294967296 → (a < M - 48 ∨ M ≤ a) → (a < M + 168 ∨ M + 200 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hM0, hM1, hM8⟩ := hM
  have rs := rd4 hsvc s312
  have hm : ∀ a, rdN μ a 8 % 18446744073709551616 = rdN μ a 8 := fun a => Nat.mod_eq_of_lt (rdN_lt64 μ a)
  have hz := zext32 hsvc
  have hr3 : ∀ a, M - 48 ≤ a → a < M → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hM0, hM1, hM8, hcur, hcM, hsvc, hr, hr2, hr3, hw, hw2, rs, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_,
      fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, hm, hz, encodeLE_rdN, Memory.length_readN]
    post_simp

/-- 5372 … 59375: the `format!` call for the log line: its one argument (M + 560, the `Debug` function from M + 32)
    at M + 536, the template from M + 24, the `String` at M + 584, return address 172 (→ 5405). Memory changes only
    at M + 536 … M + 552. -/
theorem lf {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (M : Nat) (hM : 65536 ≤ M ∧ M + 632 ≤ 4294967296 ∧ M % 8 = 0)
    (h1 : ω[1] = UInt64.ofNat M)
    (s24 : μ.readN (M + 24) 8 = Num.encodeLE 8 66506) (s32 : μ.readN (M + 32) 8 = Num.encodeLE 8 668)
    (hr : ∀ a, M + 24 ≤ a → a < M + 40 → μ.readable a = true)
    (hw : ∀ a, M + 536 ≤ a → a < M + 552 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 5372 ω μ x 59375 ω' μ' x 8 ∧ ω'[0] = UInt64.ofNat 172 ∧ ω'[1] = ω[1] ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat (M + 584) ∧ ω'[8] = UInt64.ofNat 66506 ∧
      ω'[9] = UInt64.ofNat (M + 536) ∧
      μ'.readN (M + 536) 8 = Num.encodeLE 8 (M + 560) ∧ μ'.readN (M + 544) 8 = Num.encodeLE 8 668 ∧
      (∀ a, a < 4294967296 → (a < M + 536 ∨ M + 552 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hM0, hM1, hM8⟩ := hM
  have r24 := rd8 (by decide) s24
  have r32 := rd8 (by decide) s32
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hM0, hM1, hM8, hr, hw, r24, r32, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]
    post_simp

/-- 5405 … 5428: the `String` `{cap, ptr, len}` at M + 584: the `log` arguments, level 2, target from M + 16
    (66793, 4 octets), message (ptr, len), with ω₅ = ptr and ω₆ = cap. -/
theorem ll {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (M cap ptr len : Nat) (hM : 65536 ≤ M ∧ M + 632 ≤ 4294967296 ∧ M % 8 = 0)
    (hcap : cap < 18446744073709551616) (hptr : ptr < 18446744073709551616) (hlen : len < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat M) (s16 : μ.readN (M + 16) 8 = Num.encodeLE 8 66793)
    (s584 : μ.readN (M + 584) 8 = Num.encodeLE 8 cap) (s592 : μ.readN (M + 592) 8 = Num.encodeLE 8 ptr)
    (s600 : μ.readN (M + 600) 8 = Num.encodeLE 8 len)
    (hr : ∀ a, M + 584 ≤ a → a < M + 608 → μ.readable a = true)
    (hr2 : ∀ a, M + 16 ≤ a → a < M + 24 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 5405 ω μ x 5428 ω' μ x 8 ∧ ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat ptr ∧
      ω'[6] = UInt64.ofNat cap := by
  obtain ⟨hM0, hM1, hM8⟩ := hM
  have rc := rd8 hcap s584
  have rp := rd8 hptr s592
  have rl := rd8 hlen s600
  have r16 := rd8 (by decide) s16
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hM0, hM1, hM8, hr, hr2, rc, rp, rl, r16, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]

/-- 5430 … 40613, the `String`'s capacity (ω₆) nonzero: `dealloc(ptr, cap, 1)` (ω₇ = ω₅ = ptr; return address 174
    → 5448). -/
theorem lfr {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (cap : Nat) (hcap : cap ≠ 0) (hcap' : cap < 18446744073709551616)
    (h6 : ω[6] = UInt64.ofNat cap) :
    ∃ ω', FreeStepsH p R 5430 ω μ x 40613 ω' μ x 6 ∧ ω'[0] = UInt64.ofNat 174 ∧ ω'[1] = ω[1] ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = ω[5] := by
  have hc0 : ¬ cap = 0 := hcap
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h6, hc0, hcap']
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some']

/-- 5430 … 5448, capacity 0: no free. -/
theorem lfz {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (h6 : ω[6] = UInt64.ofNat 0) :
    ∃ ω', FreeStepsH p R 5430 ω μ x 5448 ω' μ x 2 ∧ ω'[1] = ω[1] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h6]
  · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, List.lookup_nil,
      Option.getD_none]

/-- 5448 … 5493 with room in the output (len ≠ cap, at M + 264 and M + 248): the result's three words (M + 560 …
    M + 576) copied to M + 584 … M + 608, with ω₅ = len. Memory changes only at M + 584 … M + 608. -/
theorem lp0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (M cap len w0 w1 w2 : Nat) (hM : 65536 ≤ M ∧ M + 632 ≤ 4294967296 ∧ M % 8 = 0)
    (hne : len ≠ cap) (hcap : cap < 18446744073709551616) (hlen : len < 18446744073709551616)
    (hw0 : w0 < 18446744073709551616) (hw1 : w1 < 18446744073709551616) (hw2 : w2 < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat M)
    (s560 : μ.readN (M + 560) 8 = Num.encodeLE 8 w0) (s568 : μ.readN (M + 568) 8 = Num.encodeLE 8 w1)
    (s576 : μ.readN (M + 576) 8 = Num.encodeLE 8 w2)
    (sc : μ.readN (M + 248) 8 = Num.encodeLE 8 cap) (sl : μ.readN (M + 264) 8 = Num.encodeLE 8 len)
    (hr : ∀ a, M + 248 ≤ a → a < M + 272 → μ.readable a = true)
    (hr2 : ∀ a, M + 560 ≤ a → a < M + 584 → μ.readable a = true)
    (hw : ∀ a, M + 584 ≤ a → a < M + 608 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 5448 ω μ x 5493 ω' μ' x 9 ∧ ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat len ∧
      μ'.readN (M + 584) 8 = Num.encodeLE 8 w0 ∧ μ'.readN (M + 592) 8 = Num.encodeLE 8 w1 ∧
      μ'.readN (M + 600) 8 = Num.encodeLE 8 w2 ∧
      (∀ a, a < 4294967296 → (a < M + 584 ∨ M + 608 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hM0, hM1, hM8⟩ := hM
  have rc := rd8 hcap sc
  have rl := rd8 hlen sl
  have r0 := rd8 hw0 s560
  have r1 := rd8 hw1 s568
  have r2 := rd8 hw2 s576
  have hne' : ¬ len = cap := hne
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hM0, hM1, hM8, hne', hr, hr2, hw, rc, rl, r0, r1, r2, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]
    post_simp

/-- 5448 … 32785, the output full (len = cap): as `lp0`, then `grow_one` for the output `Vec` at M + 248 (return
    address 176 → 5493). -/
theorem lpg {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (M len w0 w1 w2 : Nat) (hM : 65536 ≤ M ∧ M + 632 ≤ 4294967296 ∧ M % 8 = 0)
    (hlen : len < 18446744073709551616)
    (hw0 : w0 < 18446744073709551616) (hw1 : w1 < 18446744073709551616) (hw2 : w2 < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat M)
    (s560 : μ.readN (M + 560) 8 = Num.encodeLE 8 w0) (s568 : μ.readN (M + 568) 8 = Num.encodeLE 8 w1)
    (s576 : μ.readN (M + 576) 8 = Num.encodeLE 8 w2)
    (sc : μ.readN (M + 248) 8 = Num.encodeLE 8 len) (sl : μ.readN (M + 264) 8 = Num.encodeLE 8 len)
    (hr : ∀ a, M + 248 ≤ a → a < M + 272 → μ.readable a = true)
    (hr2 : ∀ a, M + 560 ≤ a → a < M + 584 → μ.readable a = true)
    (hw : ∀ a, M + 584 ≤ a → a < M + 608 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 5448 ω μ x 32785 ω' μ' x 11 ∧ ω'[0] = UInt64.ofNat 176 ∧ ω'[1] = ω[1] ∧
      ω'[5] = UInt64.ofNat len ∧ ω'[7] = UInt64.ofNat (M + 248) ∧
      μ'.readN (M + 584) 8 = Num.encodeLE 8 w0 ∧ μ'.readN (M + 592) 8 = Num.encodeLE 8 w1 ∧
      μ'.readN (M + 600) 8 = Num.encodeLE 8 w2 ∧
      (∀ a, a < 4294967296 → (a < M + 584 ∨ M + 608 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hM0, hM1, hM8⟩ := hM
  have rc := rd8 hlen sc
  have rl := rd8 hlen sl
  have r0 := rd8 hw0 s560
  have r1 := rd8 hw1 s568
  have r2 := rd8 hw2 s576
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hM0, hM1, hM8, hr, hr2, hw, rc, rl, r0, r1, r2, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]
    post_simp

/-- 5493 … 4046: the slot ptr + 232·len (ptr at M + 256, len = ω₅) gets the discriminant word from M + 8
    (`LookedUp`, 2^63 + 17) and the result's three words (from M + 584 … M + 608); len + 1 at M + 264; then the drop
    of the staged element at M + 304 (4046, return address 178 → 5558). Memory changes only at the slot's first
    32 octets and at M + 264 … M + 272. -/
theorem lps {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (M ptr len w0 w1 w2 : Nat) (hM : 65536 ≤ M ∧ M + 632 ≤ 4294967296 ∧ M % 8 = 0)
    (hptr : ptr + 232 * len + 32 ≤ 4294967296) (hpM : ptr + 232 * len + 32 ≤ M ∨ M + 632 ≤ ptr + 232 * len)
    (hw0 : w0 < 18446744073709551616) (hw1 : w1 < 18446744073709551616) (hw2 : w2 < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat M) (h5 : ω[5] = UInt64.ofNat len)
    (s8 : μ.readN (M + 8) 8 = Num.encodeLE 8 9223372036854775825)
    (s256 : μ.readN (M + 256) 8 = Num.encodeLE 8 ptr)
    (s584 : μ.readN (M + 584) 8 = Num.encodeLE 8 w0) (s592 : μ.readN (M + 592) 8 = Num.encodeLE 8 w1)
    (s600 : μ.readN (M + 600) 8 = Num.encodeLE 8 w2)
    (hr : ∀ a, M + 8 ≤ a → a < M + 16 → μ.readable a = true)
    (hr2 : ∀ a, M + 256 ≤ a → a < M + 264 → μ.readable a = true)
    (hr3 : ∀ a, M + 584 ≤ a → a < M + 608 → μ.readable a = true)
    (hw : ∀ a, ptr + 232 * len ≤ a → a < ptr + 232 * len + 32 → μ.writable a = true)
    (hwl : ∀ a, M + 264 ≤ a → a < M + 272 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 5493 ω μ x 4046 ω' μ' x 16 ∧ ω'[0] = UInt64.ofNat 178 ∧ ω'[1] = ω[1] ∧
      ω'[7] = UInt64.ofNat (M + 304) ∧
      μ'.readN (ptr + 232 * len) 8 = Num.encodeLE 8 9223372036854775825 ∧
      μ'.readN (ptr + 232 * len + 8) 8 = Num.encodeLE 8 w0 ∧ μ'.readN (ptr + 232 * len + 16) 8 = Num.encodeLE 8 w1 ∧
      μ'.readN (ptr + 232 * len + 24) 8 = Num.encodeLE 8 w2 ∧ μ'.readN (M + 264) 8 = Num.encodeLE 8 (len + 1) ∧
      (∀ a, a < 4294967296 → (a < ptr + 232 * len ∨ ptr + 232 * len + 32 ≤ a) → (a < M + 264 ∨ M + 272 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hM0, hM1, hM8⟩ := hM
  have r8 := rd8 (by decide) s8
  have rp := rd8 (by omega) s256
  have r0 := rd8 hw0 s584
  have r1 := rd8 hw1 s592
  have r2 := rd8 hw2 s600
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hM0, hM1, hM8, hptr, hpM, hr, hr2, hr3, hw, hwl, r8, rp, r0, r1, r2, rdN_writeN_disjoint,
      ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, Nat.mul_comm len 232]
    post_simp

/-- The entry of `drop_in_place::<Instruction>`'s table (65536, read-only data) for index 8 (`Lookup`): the offset
    of the jump-table address 122, whose entry is the plain return 4115. -/
def dropEntry8 : List UInt8 := [122, 0, 255, 255]

/-- The return address 178, just stored as an immediate at a, read back. -/
theorem rdN_writeN_178 (μ : Memory) (a : Nat) (ha : a + 8 ≤ 4294967296) :
    rdN (μ.writeN a [UInt8.ofNat 178, UInt8.ofNat 0, UInt8.ofNat 0, UInt8.ofNat 0, UInt8.ofNat 0, UInt8.ofNat 0,
      UInt8.ofNat 0, UInt8.ofNat 0]) a 8 = 178 := by
  unfold rdN
  rw [Memory.readN_writeN_same _ _ _ _ (by simp) (by simp only [two32]; omega)]
  rfl

/-- 4046 … 5558, `drop_in_place::<Instruction>` of the staged `Lookup` (D = 2^63 + 7 at M + 304): it owns nothing,
    so the table's arm (`dropEntry8`, at 65568) returns at once, to 178 (→ 5558), and on to the loop head 5042.
    Memory changes only at the frame M − 40 … M. -/
theorem ldrop {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (M : Nat) (hM : 131072 ≤ M ∧ M + 632 ≤ 4294967296 ∧ M % 8 = 0)
    (h0 : ω[0] = UInt64.ofNat 178) (h1 : ω[1] = UInt64.ofNat M) (h7 : ω[7] = UInt64.ofNat (M + 304))
    (s304 : μ.readN (M + 304) 8 = Num.encodeLE 8 9223372036854775815)
    (tab : μ.readN 65568 4 = dropEntry8)
    (hr : ∀ a, M + 304 ≤ a → a < M + 312 → μ.readable a = true)
    (hr2 : ∀ a, 65568 ≤ a → a < 65572 → μ.readable a = true)
    (hw : ∀ a, M - 40 ≤ a → a < M → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 4046 ω μ x 5042 ω' μ' x 26 ∧ ω'[1] = ω[1] ∧
      (∀ a, a < 4294967296 → (a < M - 40 ∨ M ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hM0, hM1, hM8⟩ := hM
  have rD := rd8 (by decide) s304
  have rt : rdN μ 65568 4 = 4294901882 := by
    show Num.decodeLE _ = _
    rw [tab]; rfl
  have hr3 : ∀ a, M - 40 ≤ a → a < M → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h7, hM0, hM1, hM8, hr, hr2, hr3, hw, rD, rt, rdN_writeN_178, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]
    post_simp

end Services.Bootstrap.Refine.Lookup
