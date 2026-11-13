import Services.Bootstrap.CodeAAll
import Services.Bootstrap.Alloc.Register
import Services.Bootstrap.Acc.Inputs.ItemOperand
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
      | exact UInt64.ofNat_toNat
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

/-- The `Vec`'s pointer word rebuilt from its octets (47098 … 47140): an or of disjoint shifted parts. -/
theorem repack (B0 U4 U2 U1 : Nat) (h0 : B0 < 256) (h4 : U4 < 4294967296) (h2 : U2 < 65536) (h1 : U1 < 256) :
    Exec.bitwise (fun x1 x2 => x1 || x2) (Exec.bitwise (fun x1 x2 => x1 && x2) (B0 % 18446744073709551616) 255 %
        18446744073709551616)
      (Exec.bitwise (fun x1 x2 => x1 || x2)
          (Exec.bitwise (fun x1 x2 => x1 || x2) (U2 % 18446744073709551616 * 4294967296 % 18446744073709551616)
            (U1 % 18446744073709551616 * 281474976710656 % 18446744073709551616) % 18446744073709551616)
          (U4 % 18446744073709551616) % 18446744073709551616 * 256 % 18446744073709551616) %
        18446744073709551616 % 2 ^ (8 * 8) =
    B0 + 256 * U4 + 1099511627776 * U2 + 72057594037927936 * U1 := by
  have e1 : Exec.bitwise (fun x1 x2 => x1 && x2) (B0 % 18446744073709551616) 255 = B0 := by
    rw [bitwise_and_low _ 255 8 (by decide) (by decide)]; omega
  have e2 : Exec.bitwise (fun x1 x2 => x1 || x2) (U2 % 18446744073709551616 * 4294967296 % 18446744073709551616)
      (U1 % 18446744073709551616 * 281474976710656 % 18446744073709551616) = U2 * 4294967296 + U1 * 2 ^ 48 := by
    rw [show U2 % 18446744073709551616 * 4294967296 % 18446744073709551616 = U2 * 4294967296 by omega,
      show U1 % 18446744073709551616 * 281474976710656 % 18446744073709551616 = U1 * 2 ^ 48 by
        rw [show (2 : Nat) ^ 48 = 281474976710656 by decide]; omega]
    exact bitwise_or_add _ _ 48 (by decide) (by rw [show (2 : Nat) ^ 48 = 281474976710656 by decide]; omega)
      (by rw [show (2 : Nat) ^ (64 - 48) = 65536 by decide]; omega)
  have e3 : Exec.bitwise (fun x1 x2 => x1 || x2) ((U2 * 4294967296 + U1 * 2 ^ 48) % 18446744073709551616)
      (U4 % 18446744073709551616) = U4 + (U2 + 65536 * U1) * 2 ^ 32 := by
    rw [bitwise_or_comm, show U4 % 18446744073709551616 = U4 by omega,
      show (U2 * 4294967296 + U1 * 2 ^ 48) % 18446744073709551616 = (U2 + 65536 * U1) * 2 ^ 32 by
        simp only [Nat.reducePow]; omega]
    exact bitwise_or_add _ _ 32 (by decide) (by simp only [Nat.reducePow]; omega)
      (by simp only [Nat.reducePow, Nat.reduceSub]; omega)
  have e4 : Exec.bitwise (fun x1 x2 => x1 || x2) B0 ((U4 + (U2 + 65536 * U1) * 2 ^ 32) % 18446744073709551616 * 256 %
      18446744073709551616) = B0 + (U4 + (U2 + 65536 * U1) * 2 ^ 32) * 2 ^ 8 := by
    rw [show (U4 + (U2 + 65536 * U1) * 2 ^ 32) % 18446744073709551616 * 256 % 18446744073709551616 =
      (U4 + (U2 + 65536 * U1) * 2 ^ 32) * 2 ^ 8 by simp only [Nat.reducePow]; omega]
    exact bitwise_or_add _ _ 8 (by decide) (by simp only [Nat.reducePow]; omega)
      (by simp only [Nat.reducePow, Nat.reduceSub]; omega)
  rw [e1, Nat.mod_eq_of_lt (by omega : B0 < 18446744073709551616), e2, e3, e4]
  simp only [Nat.reducePow, Nat.reduceMul]; omega

/-- A word as its octets 0, 1 … 4, 5 … 6 and 7. -/
theorem rd8_split (μ : Memory) (a : Nat) :
    rdN μ a 8 = rdN μ a 1 + 256 * rdN μ (a + 1) 4 + 1099511627776 * rdN μ (a + 5) 2 +
      72057594037927936 * rdN μ (a + 7) 1 := by
  unfold rdN
  rw [show (8 : Nat) = 1 + (4 + (2 + 1)) by rfl, PVM.Memory.readN_split, PVM.Memory.readN_split,
    PVM.Memory.readN_split, decodeLE_append, decodeLE_append, decodeLE_append]
  simp only [PVM.Memory.length_readN, show a + 1 + 4 = a + 5 by omega, show a + 5 + 2 = a + 7 by omega]
  omega

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
    all_goals first
      | (congr 1; omega)
      | (rw [← m16]; exact rd_mod64 μ _)
      | (rw [← m0]; exact rd_mod64 μ _)
      | (rw [repack _ _ _ _ (by have := rdN_lt μ (b + 280) 1; unfold rdN at this; simpa using this)
            (by have := rdN_lt μ (b + 281) 4; unfold rdN at this; simpa using this)
            (by have := rdN_lt μ (b + 285) 2; unfold rdN at this; simpa using this)
            (by have := rdN_lt μ (b + 287) 1; unfold rdN at this; simpa using this), ← m8, rd8_split]
         rfl)
      | rfl

end Services.Bootstrap.Acc
