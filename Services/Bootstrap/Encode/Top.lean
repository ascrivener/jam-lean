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

end Services.Bootstrap.Encode.Top
