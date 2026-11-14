import Services.Bootstrap.Refine.DecodeTail
import Services.Bootstrap.Decode.LoopAPass
import Services.Bootstrap.Decode.VecU8
import Services.Bootstrap.Decode.AllocOk

/-!
# `Vec<Instruction>::decode` (482 … its return), one batch

`Vec<Instruction>::decode` (482), called with the output at ω₇, the reader at ω₈ and the length n at ω₉,
opens a 552-octet frame S = ω₁ − 552, starts with an empty `Vec` `{0, 8, 0}` at S + 40 and decodes in batches
of min(n, 70) elements: it reserves each batch exactly (`finish_grow`, 32989; 232-octet elements at alignment
8), decodes it (the element loop 680 … 562, `Decode.LoopA.loopAF`), and after the last batch writes the `Vec`
`{cap, ptr, len}` to the output and returns. Here: one batch (1 ≤ n ≤ 70). GP v0.8.0 Appendix B.4 (Ψ_R running
bootstrap's code); `Spec.refine`'s `decode (Dec.payload C) y`.
-/

namespace Services.Bootstrap.Refine.DecodeVec

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Encode.Writer

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 482 … 530 (n ≠ 0): the frame S = ω₁ − 552 (return address, ω₅, ω₆ at S + 544, S + 536, S + 528), the
    reader at S + 24, the output at S, the empty `Vec` `{0, 8, 0}` at S + 40; on to 531 with ω₅ = n, ω₇ = 0
    (elements so far), ω₉ = 8, ω₁₂ = 70. Memory changes only in [S, S + 64) and [S + 528, S + 552). -/
theorem v1a {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S out rd n r0 v5 v6 : Nat) (hS : 65536 ≤ S ∧ S + 552 ≤ 4294967296 ∧ S % 8 = 0) (hn : n ≠ 0)
    (hn64 : n < 18446744073709551616) (hout : out < 18446744073709551616) (hrd : rd < 18446744073709551616)
    (hr0 : r0 < 18446744073709551616) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat (S + 552)) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat out) (h8 : ω[8] = UInt64.ofNat rd)
    (h9 : ω[9] = UInt64.ofNat n)
    (hw : ∀ a, S ≤ a → a < S + 552 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 482 ω μ x 531 ω' μ' x 20 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat n ∧
      ω'[7] = UInt64.ofNat 0 ∧ ω'[9] = UInt64.ofNat 8 ∧ ω'[12] = UInt64.ofNat 70 ∧
      μ'.readN S 8 = Num.encodeLE 8 out ∧ μ'.readN (S + 24) 8 = Num.encodeLE 8 rd ∧
      μ'.readN (S + 40) 8 = Num.encodeLE 8 0 ∧ μ'.readN (S + 48) 8 = Num.encodeLE 8 8 ∧
      μ'.readN (S + 56) 8 = Num.encodeLE 8 0 ∧ μ'.readN (S + 544) 8 = Num.encodeLE 8 r0 ∧
      μ'.readN (S + 536) 8 = Num.encodeLE 8 v5 ∧ μ'.readN (S + 528) 8 = Num.encodeLE 8 v6 ∧
      (∀ a, a < 4294967296 → (a < S ∨ (S + 64 ≤ a ∧ a < S + 528) ∨ S + 552 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hS0, hS1, hS8⟩ := hS
  have hn' : ¬ n = 0 := hn
  have hr : ∀ a, S ≤ a → a < S + 552 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, h9, hS0, hS1, hS8, hn', hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, Nat.mod_eq_of_lt hn64,
      Nat.mod_eq_of_lt hout, Nat.mod_eq_of_lt hrd, Nat.mod_eq_of_lt hr0, Nat.mod_eq_of_lt hv5,
      Nat.mod_eq_of_lt hv6]
    all_goals try (congr 1; omega)
    post_simp

/-- 531 … 602, the first batch (the `Vec` empty, 1 ≤ n ≤ 70): the batch n (= min(n, 70)) at S + 8 and S + 16, 70
    at S + 32, and `finish_grow` (32989) called for the capacity n (ω₁₀; old capacity ω₈ = 0, alignment 8,
    element size 232, result at S + 296; return address 14 → 607) with ω₅ = ω₆ = n. Memory changes only at
    S + 8 … S + 24 and S + 32 … S + 40. -/
theorem v1b {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S n : Nat)
    (hS : 65536 ≤ S ∧ S + 552 ≤ 4294967296 ∧ S % 8 = 0) (hn : 1 ≤ n ∧ n ≤ 70)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat n) (h7 : ω[7] = UInt64.ofNat 0)
    (h9 : ω[9] = UInt64.ofNat 8) (h12 : ω[12] = UInt64.ofNat 70)
    (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 0)
    (hw : ∀ a, S ≤ a → a < S + 64 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 531 ω μ x 32989 ω' μ' x 30 ∧ ω'[0] = UInt64.ofNat 14 ∧ ω'[1] = UInt64.ofNat S ∧
      ω'[5] = UInt64.ofNat n ∧ ω'[6] = UInt64.ofNat n ∧ ω'[7] = UInt64.ofNat (S + 296) ∧
      ω'[8] = UInt64.ofNat 0 ∧ ω'[9] = UInt64.ofNat 8 ∧ ω'[10] = UInt64.ofNat n ∧ ω'[11] = UInt64.ofNat 8 ∧
      ω'[12] = UInt64.ofNat 232 ∧
      μ'.readN (S + 8) 8 = Num.encodeLE 8 n ∧ μ'.readN (S + 16) 8 = Num.encodeLE 8 n ∧
      μ'.readN (S + 32) 8 = Num.encodeLE 8 70 ∧
      (∀ a, a < 4294967296 → (a < S + 8 ∨ (S + 24 ≤ a ∧ a < S + 32) ∨ S + 40 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hS0, hS1, hS8⟩ := hS
  have r40 := rd8 (by decide) s40
  have hr : ∀ a, S ≤ a → a < S + 64 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hmin : min n 70 = n := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h7, h9, h12, hS0, hS1, hS8, hn, hw, hr, r40, hmin, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, h9]
    all_goals try (congr 1; omega)
    post_simp

end Services.Bootstrap.Refine.DecodeVec
