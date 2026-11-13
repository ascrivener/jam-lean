import Services.Bootstrap.Encode.Prefix
import Services.Bootstrap.Encode.Variants
import Services.Bootstrap.Encode.Yield

/-!
# Refine's output encoder: the straight-line pieces of the function at 30073

Refine's body (6248 … 6291) opens an 80-octet frame at M for the output encoder (ω₀ = 204 saved at
M + 72, the result's address at M, the work item's address S0 at M + 8, the instruction count n at
M + 16), allocates 232 n + 6 octets and enters 30073 with the buffer in ω₇. There the encoder:

* sets up the writer `{232 n + 6, buf, 0}` at M + 24 and calls the length prefix with the count, as a
  32-bit word at M + 52 (`t1`; back at 30122);
* for each element (232 octets from E = S0's instruction pointer), calls `Instruction::encode_to`
  (`t2`, falling into 30145; back at 30215, `t3`);
* appends the work item's 16-bit `work_item_index` from S0 + 24 (`t4`; back at 30250);
* copies the writer to the result and returns (`t5`).
-/

namespace Services.Bootstrap.Encode.Top

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.Encode.Writer

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 30073 … 30116: with the buffer `buf` ≠ 0 in ω₇ and its capacity in ω₅, the writer `{cap, buf, 0}`
    goes to M + 24, the count n (< 2^32, at M + 16) to M + 52 as a 32-bit word, and the encoder calls the
    length prefix (return address 1416 → 30122) with ω₇ = M + 52, ω₈ = M + 24 and the element pointer
    E (from S0 + 8) in ω₅. -/
theorem t1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (M buf cap S0 E n : Nat) (hM : M + 80 ≤ 4294967296) (hbuf : 0 < buf ∧ buf < 18446744073709551616)
    (hcap : cap < 18446744073709551616) (hn : n < 4294967296)
    (h1 : ω[1] = UInt64.ofNat M) (h5 : ω[5] = UInt64.ofNat cap) (h7 : ω[7] = UInt64.ofNat buf)
    (s8 : μ.readN (M + 8) 8 = Num.encodeLE 8 S0) (s16 : μ.readN (M + 16) 8 = Num.encodeLE 8 n)
    (hS0 : S0 + 16 ≤ 4294967296) (hS0M : S0 + 16 ≤ M ∨ M + 80 ≤ S0)
    (sE : μ.readN (S0 + 8) 8 = Num.encodeLE 8 E) (hE : E < 18446744073709551616)
    (hr : ∀ a, M ≤ a → a < M + 80 → μ.readable a = true)
    (hrS : ∀ a, S0 + 8 ≤ a → a < S0 + 16 → μ.readable a = true)
    (hw : ∀ a, M + 24 ≤ a → a < M + 56 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 30073 ω μ x 30977 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat 1416 ∧ ω'[1] = UInt64.ofNat M ∧ ω'[5] = UInt64.ofNat E ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (M + 52) ∧ ω'[8] = UInt64.ofNat (M + 24) ∧
      μ'.readN (M + 24) 8 = Num.encodeLE 8 cap ∧ μ'.readN (M + 32) 8 = Num.encodeLE 8 buf ∧
      μ'.readN (M + 40) 8 = Num.encodeLE 8 0 ∧ rdN μ' (M + 52) 4 = n ∧
      (∀ a, a < 4294967296 → (a < M + 24 ∨ M + 56 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r8 := rd8 (by omega) s8
  have r16 := rd8 (by omega) s16
  have rE := rd8 hE sE
  have hbuf0 : ¬ buf = 0 := by omega
  have hsh : n / 4294967296 = 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h7, hM, hbuf0, hsh, hS0, hS0M, hr, hrS, hw, r8, r16, rE, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, Nat.mod_eq_of_lt hE]
    post_simp
    all_goals try assumption
    all_goals try (show Num.decodeLE _ = _
                   rw [Memory.readN_writeN_same _ _ _ _ (Num.length_encodeLE _ _) (by simp only [two32]; omega),
                     Num.decodeLE_encodeLE]; omega)

/-- 30122 … 30145, for n ≠ 0 at M + 16: the encoder stores the next element's address E + 232 at
    M + 16 and calls `Instruction::encode_to` for the element at E (ω₅) on the writer at M + 24 (return
    address 1418 → 30215). -/
theorem tA {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (M E n : Nat) (hM : M + 80 ≤ 4294967296) (hE : E + 232 < 18446744073709551616) (hn : 0 < n ∧ n < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat M) (h5 : ω[5] = UInt64.ofNat E) (s16 : μ.readN (M + 16) 8 = Num.encodeLE 8 n)
    (hr : ∀ a, M + 16 ≤ a → a < M + 24 → μ.readable a = true)
    (hw : ∀ a, M + 16 ≤ a → a < M + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 30122 ω μ x 30145 ω' μ' x 10 ∧
      ω'[0] = UInt64.ofNat 1418 ∧ ω'[1] = UInt64.ofNat M ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat E ∧ ω'[8] = UInt64.ofNat (M + 24) ∧
      μ'.readN (M + 16) 8 = Num.encodeLE 8 (E + 232) ∧
      (∀ a, a < 4294967296 → (a < M + 16 ∨ M + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r16 := rd8 hn.2 s16
  have hn0 : ¬ n = 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hM, hn0, hr, hw, r16, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5]
    post_simp
    all_goals try assumption

/-- 30215 … 30145, with r + 232 octets of elements left (r ≠ 0) in ω₆: back from an element, the
    encoder steps to the next one, E' (from M + 16), stores E' + 232 there and calls
    `Instruction::encode_to` for it (return address 1418). -/
theorem tB {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (M E r : Nat) (hM : M + 80 ≤ 4294967296) (hE : E + 232 < 18446744073709551616)
    (hr0 : 0 < r ∧ r + 232 < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat M) (h6 : ω[6] = UInt64.ofNat (r + 232))
    (s16 : μ.readN (M + 16) 8 = Num.encodeLE 8 E)
    (hr : ∀ a, M + 16 ≤ a → a < M + 24 → μ.readable a = true)
    (hw : ∀ a, M + 16 ≤ a → a < M + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 30215 ω μ x 30145 ω' μ' x 10 ∧
      ω'[0] = UInt64.ofNat 1418 ∧ ω'[1] = UInt64.ofNat M ∧ ω'[5] = UInt64.ofNat E ∧
      ω'[6] = UInt64.ofNat r ∧ ω'[7] = UInt64.ofNat E ∧ ω'[8] = UInt64.ofNat (M + 24) ∧
      μ'.readN (M + 16) 8 = Num.encodeLE 8 (E + 232) ∧
      (∀ a, a < 4294967296 → (a < M + 16 ∨ M + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r16 := rd8 (by omega) s16
  have hr0' : ¬ (r + 232 + 18446744073709551384) % 18446744073709551616 = 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, hM, hr0', hr, hw, r16, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h6]
    post_simp
    all_goals try assumption
    all_goals try (congr 1; omega)

/-- 30225 … 30244: the work item's 16-bit `work_item_index` (at S0 + 24, S0 from M + 8) goes to M + 52 and
    the encoder calls `Vec<u8>::extend_from_slice` for its 2 octets on the writer at M + 24 (return
    address 1420 → 30250). From 30215 after the last element (232 left in ω₆), or from 30122 for n = 0. -/
theorem tC {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (e M S0 : Nat) (he : (e = 30215 ∧ ω[6] = UInt64.ofNat 232) ∨ (e = 30122 ∧ μ.readN (M + 16) 8 = Num.encodeLE 8 0))
    (hM : M + 80 ≤ 4294967296) (hS0 : S0 + 26 ≤ 4294967296) (hS0M : S0 + 26 ≤ M + 52 ∨ M + 54 ≤ S0)
    (h1 : ω[1] = UInt64.ofNat M) (s8 : μ.readN (M + 8) 8 = Num.encodeLE 8 S0)
    (hr : ∀ a, M + 8 ≤ a → a < M + 24 → μ.readable a = true)
    (hrS : ∀ a, S0 + 24 ≤ a → a < S0 + 26 → μ.readable a = true)
    (hw : ∀ a, M + 52 ≤ a → a < M + 54 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R e ω μ x 58508 ω' μ' x 16 ∧
      ω'[0] = UInt64.ofNat 1420 ∧ ω'[1] = UInt64.ofNat M ∧
      ω'[7] = UInt64.ofNat (M + 24) ∧ ω'[8] = UInt64.ofNat (M + 52) ∧ ω'[9] = UInt64.ofNat 2 ∧
      μ'.readN (M + 52) 2 = μ.readN (S0 + 24) 2 ∧
      (∀ a, a < 4294967296 → (a < M + 52 ∨ M + 54 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r8 := rd8 (by omega) s8
  have hsx : Num.encodeLE 2 (sxw 2 (rdN μ (S0 + 24) 2)) = μ.readN (S0 + 24) 2 := by
    rw [encodeLE_sxw 2 _ (Or.inl rfl) (rdN_lt μ _ 2), encodeLE_rdN]
  have hm : ∀ w : Nat, w % 18446744073709551616 % 65536 = w % 256 ^ 2 := fun w => by omega
  rw [show ω = regsNF ω [] from rfl]
  rcases he with ⟨rfl, h6⟩ | ⟨rfl, s16⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h6, hM, hS0, hS0M, hr, hrS, hw, r8, ↓rdN_fold, ↓loadI_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]
      post_simp
      all_goals try assumption
      all_goals try (rw [← hsx, hm, encodeLE_mod])
  · have r16 := rd8 (by decide) s16
    refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, hM, hS0, hS0M, hr, hrS, hw, r8, r16, ↓rdN_fold, ↓loadI_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]
      post_simp
      all_goals try assumption
      all_goals try (rw [← hsx, hm, encodeLE_mod])

/-- 30250 … 30281: the writer `{cap, ptr, len}` at M + 24 is copied to the result at O (from M), ω₀, ω₅,
    ω₆ come back from M + 72, + 64, + 56, the frame is closed and the encoder returns. -/
theorem t5 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (M O cap ptr len ret t r5 r6 : Nat) (hM : M + 80 < 4294967296) (hO : O + 24 ≤ 4294967296)
    (hOM : O + 24 ≤ M + 56 ∨ M + 80 ≤ O)
    (h1 : ω[1] = UInt64.ofNat M) (s0 : μ.readN M 8 = Num.encodeLE 8 O)
    (sc : μ.readN (M + 24) 8 = Num.encodeLE 8 cap) (sp : μ.readN (M + 32) 8 = Num.encodeLE 8 ptr)
    (sl : μ.readN (M + 40) 8 = Num.encodeLE 8 len)
    (sr : μ.readN (M + 72) 8 = Num.encodeLE 8 ret) (s5 : μ.readN (M + 64) 8 = Num.encodeLE 8 r5)
    (s6 : μ.readN (M + 56) 8 = Num.encodeLE 8 r6)
    (hc : cap < 18446744073709551616) (hp : ptr < 18446744073709551616) (hl : len < 18446744073709551616)
    (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hr : ∀ a, M ≤ a → a < M + 80 → μ.readable a = true)
    (hw : ∀ a, O ≤ a → a < O + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 30250 ω μ x t ω' μ' x 14 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (M + 80) ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 ∧
      μ'.readN O 8 = Num.encodeLE 8 cap ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 ptr ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 len ∧
      (∀ a, a < 4294967296 → (a < O ∨ O + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r0 := rd8 (by omega) s0
  have rc := rd8 hc sc
  have rp := rd8 hp sp
  have rl := rd8 hl sl
  have rr := rd8 (by omega) sr
  have r5' := rd8 hr5 s5
  have r6' := rd8 hr6 s6
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hM, hO, hOM, hr, hw, r0, rc, rp, rl, rr, r5', r6', hret, hjt, hbt, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]
    post_simp
    all_goals try assumption
    all_goals try (congr 1; omega)

end Services.Bootstrap.Encode.Top
