import Services.Bootstrap.CodeAAll
import Services.Bootstrap.Alloc.Register
import PVM.Logic.Go

/-!
# `AccumulateItem::decode` (45126), the operand arm: the work result and the auth trace

After the gas, the work result l (GP v0.8.0 Appendix C, O(l)): its tag octet, then for tag 0 the
output as a `Vec<u8>` (39634), and for tags 1 … 6 nothing more (the error kinds ∞, ☇, ⊚, ⊖, BAD,
BIG); then the auth trace t, a `Vec<u8>`; then the 184-octet slot.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **46889 … 46914**, the gas decoded (ω₇ = 0, ω₈ = g): g kept in ω₅, a zero octet at b + 272 and the
    read of the work result's tag octet into it (ω₇ = rd, return address 2108). -/
theorem op_res {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (b rd g : Nat) (h1 : ω[1] = UInt64.ofNat b) (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (h8 : ω[8] = UInt64.ofNat g)
    (hb : 65536 ≤ b ∧ b + 424 < 4294967296) (hrd : rd < 18446744073709551616) (hg : g < 18446744073709551616)
    (hwf : ∀ a, b ≤ a → a < b + 424 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 46889 ω μ x 58434 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat 2108 ∧ ω'[1] = UInt64.ofNat b ∧ ω'[5] = UInt64.ofNat g ∧
      ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (b + 272) ∧
      ω'[9] = UInt64.ofNat 1 ∧
      (∀ a, a < 4294967296 → (a < b + 272 ∨ b + 273 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, b ≤ a → a < b + 424 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h6, h7, h8, hwf, hr, bitwise_and_m1, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h6, h8]
    all_goals try with_reducible rfl
    all_goals try first
      | (rd_simp []; done)
      | rd_simp []
    all_goals try first
      | with_reducible rfl
      | exact Nat.mod_eq_of_lt (by omega)
    all_goals first
      | (congr 1; omega)
      | rfl

/-- **46920 … 47080**, the tag octet 0 read (ω₇ = 0): the work output, a `Vec<u8>`, decoded by 39634
    into b + 272 (ω₇ = b + 272, ω₈ = the reader, return address 2114). -/
theorem op_t0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (b : Nat) (h1 : ω[1] = UInt64.ofNat b) (h7 : ω[7] = UInt64.ofNat 0) (mt : rdN μ (b + 272) 1 = 0)
    (hb : 65536 ≤ b ∧ b + 424 < 4294967296)
    (hrf : ∀ a, b ≤ a → a < b + 424 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 46920 ω μ x 39634 ω' μ x 20 ∧
      ω'[0] = UInt64.ofNat 2114 ∧ ω'[1] = UInt64.ofNat b ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (b + 272) ∧ ω'[8] = ω[6] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, h7, mt, hrf, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1]
    all_goals first
      | rfl
      | (congr 1; omega)

/-- 39708: the `Vec<u8>` decoder's return, through entry 1056 (2114), to 47086. -/
theorem op_ret1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (h0 : ω[0] = UInt64.ofNat 2114) : FreeStepsH p R 39708 ω μ x 47086 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0]

/-- 39708: the `Vec<u8>` decoder's return, through entry 1057 (2116), to 47158. -/
theorem op_ret2 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (h0 : ω[0] = UInt64.ofNat 2116) : FreeStepsH p R 39708 ω μ x 47158 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0]

/-- **47086 … 47152**, the work output decoded into b + 272 (cap c ≠ −1, ptr q, len n): n saved at b,
    c at b + 8 and q at b + 16, and the auth trace, a `Vec<u8>`, decoded by 39634 into b + 272
    (ω₇ = b + 272, ω₈ = the reader, return address 2116). -/
theorem op_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (b c q n : Nat) (h1 : ω[1] = UInt64.ofNat b)
    (m0 : rdN μ (b + 272) 8 = c) (m8 : rdN μ (b + 280) 8 = q) (m16 : rdN μ (b + 288) 8 = n)
    (hc : c < 18446744073709551615)
    (hb : 65536 ≤ b ∧ b + 424 < 4294967296)
    (hwf : ∀ a, b ≤ a → a < b + 424 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 47086 ω μ x 39634 ω' μ' x 30 ∧
      ω'[0] = UInt64.ofNat 2116 ∧ ω'[1] = UInt64.ofNat b ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (b + 272) ∧ ω'[8] = ω[6] ∧
      rdN μ' b 8 = n ∧ rdN μ' (b + 8) 8 = c ∧ rdN μ' (b + 16) 8 = q ∧
      (∀ a, a < 4294967296 → (a < b ∨ b + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, b ≤ a → a < b + 424 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have hc' : c % 18446744073709551616 ≠ 18446744073709551615 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, m0, m8, m16, hc', hwf, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1]
    all_goals try with_reducible rfl
    all_goals try first
      | (rd_simp []; done)
      | rd_simp []
    all_goals try first
      | with_reducible rfl
      | exact Nat.mod_eq_of_lt (by omega)
    trace_state
    all_goals sorry

end Services.Bootstrap.Acc
