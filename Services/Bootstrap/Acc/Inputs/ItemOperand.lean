import Services.Bootstrap.CodeAAll
import Services.Bootstrap.Alloc.Register
import PVM.Logic.Go

/-!
# `AccumulateItem::decode` (45126), the operand arm: the four hashes

Tag 0 is an operand (GP v0.8.0 §12, 𝕌): ℰ(p, e, a, y, g, l, t) — four hashes (the package hash p,
the segment root e, the authorizer hash a, the payload hash y), the gas g (ℰ, `cu_call`), the work
result l and the auth trace t. Each hash is read by `read_ok` into the zeroed buffer b + 272 and copied
to the frame: p to b + 32, e to b + 64, a to b + 96 and y to b + 136.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}


/-- **46300 … 58434**, the tag read (ω₇ = 0) and the tag 0 (an operand, at b + 272): `out` saved at
    b + 24, the 32-octet buffer b + 272 zeroed and the read of p into it (ω₇ = ω₅ = rd, ω₈ = b + 272,
    ω₉ = 32, return address 2084). -/
theorem op_h0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (b out rd : Nat) (h1 : ω[1] = UInt64.ofNat b) (h5 : ω[5] = UInt64.ofNat rd) (h6 : ω[6] = UInt64.ofNat out)
    (h7 : ω[7] = UInt64.ofNat 0) (mt : rdN μ (b + 272) 1 = 0)
    (hb : 65536 ≤ b ∧ b + 424 < 4294967296) (hout : out < 18446744073709551616) (hrd : rd < 18446744073709551616)
    (hwf : ∀ a, b ≤ a → a < b + 424 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 46300 ω μ x 58434 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat 2084 ∧ ω'[1] = UInt64.ofNat b ∧ ω'[5] = UInt64.ofNat rd ∧
      ω'[6] = UInt64.ofNat out ∧ ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (b + 272) ∧
      ω'[9] = UInt64.ofNat 32 ∧ rdN μ' (b + 24) 8 = out ∧
      (∀ a, a < 4294967296 → (a < b + 24 ∨ b + 32 ≤ a) → (a < b + 272 ∨ b + 304 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, b ≤ a → a < b + 424 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, h6, h7, mt, hwf, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h5, h6]
    all_goals try with_reducible rfl
    all_goals try first
      | (rd_simp []; done)
      | rd_simp []
    all_goals try first
      | with_reducible rfl
      | exact Nat.mod_eq_of_lt (by omega)
      | with_reducible exact Nat.mod_eq_of_lt (rdN_lt64 _ _)
    all_goals first
      | (congr 1; omega)
      | (simp only [Nat.reduceMul, Nat.reducePow, Nat.mod_mod]; exact Nat.mod_eq_of_lt (rdN_lt64 _ _))
      | rfl

/-- **46375 … 58434**, p read (ω₇ = 0): p copied from b + 272 to b + 32, the buffer zeroed and the read of e (return address 2086). -/
theorem op_h1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (b rd : Nat) (h1 : ω[1] = UInt64.ofNat b) (h5 : ω[5] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (hb : 65536 ≤ b ∧ b + 424 < 4294967296) (hrd : rd < 18446744073709551616)
    (hwf : ∀ a, b ≤ a → a < b + 424 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 46375 ω μ x 58434 ω' μ' x 40 ∧
      ω'[0] = UInt64.ofNat 2086 ∧ ω'[1] = UInt64.ofNat b ∧ ω'[5] = UInt64.ofNat rd ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (b + 272) ∧ ω'[9] = UInt64.ofNat 32 ∧
      rdN μ' (b + 32) 8 = rdN μ (b + 272) 8 ∧
      rdN μ' (b + 40) 8 = rdN μ (b + 280) 8 ∧
      rdN μ' (b + 48) 8 = rdN μ (b + 288) 8 ∧
      rdN μ' (b + 56) 8 = rdN μ (b + 296) 8 ∧
      (∀ a, a < 4294967296 → (a < b + 32 ∨ b + 64 ≤ a) → (a < b + 272 ∨ b + 304 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, b ≤ a → a < b + 424 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, h7, hwf, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h5]
    all_goals try with_reducible rfl
    all_goals try first
      | (rd_simp []; done)
      | rd_simp []
    all_goals try first
      | with_reducible rfl
      | exact Nat.mod_eq_of_lt (by omega)
      | with_reducible exact Nat.mod_eq_of_lt (rdN_lt64 _ _)
    all_goals first
      | (congr 1; omega)
      | (simp only [Nat.reduceMul, Nat.reducePow, Nat.mod_mod]; exact Nat.mod_eq_of_lt (rdN_lt64 _ _))
      | rfl

/-- **46442 … 58434**, e read (ω₇ = 0): the reader also in ω₆, e copied from b + 272 to b + 64, the buffer zeroed and the read of a (return address 2088). -/
theorem op_h2 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (b rd : Nat) (h1 : ω[1] = UInt64.ofNat b) (h5 : ω[5] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (hb : 65536 ≤ b ∧ b + 424 < 4294967296) (hrd : rd < 18446744073709551616)
    (hwf : ∀ a, b ≤ a → a < b + 424 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 46442 ω μ x 58434 ω' μ' x 40 ∧
      ω'[0] = UInt64.ofNat 2088 ∧ ω'[1] = UInt64.ofNat b ∧ ω'[5] = UInt64.ofNat rd ∧ ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (b + 272) ∧ ω'[9] = UInt64.ofNat 32 ∧
      rdN μ' (b + 64) 8 = rdN μ (b + 272) 8 ∧
      rdN μ' (b + 72) 8 = rdN μ (b + 280) 8 ∧
      rdN μ' (b + 80) 8 = rdN μ (b + 288) 8 ∧
      rdN μ' (b + 88) 8 = rdN μ (b + 296) 8 ∧
      (∀ a, a < 4294967296 → (a < b + 64 ∨ b + 96 ≤ a) → (a < b + 272 ∨ b + 304 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, b ≤ a → a < b + 424 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, h7, hwf, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h5]
    all_goals try with_reducible rfl
    all_goals try first
      | (rd_simp []; done)
      | rd_simp []
    all_goals try first
      | with_reducible rfl
      | exact Nat.mod_eq_of_lt (by omega)
      | with_reducible exact Nat.mod_eq_of_lt (rdN_lt64 _ _)
    all_goals first
      | (congr 1; omega)
      | (simp only [Nat.reduceMul, Nat.reducePow, Nat.mod_mod]; exact Nat.mod_eq_of_lt (rdN_lt64 _ _))
      | rfl

/-- **46508 … 58434**, a read (ω₇ = 0): a copied from b + 272 to b + 96, the buffer zeroed and the read of y (return address 2090). -/
theorem op_h3 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (b rd : Nat) (h1 : ω[1] = UInt64.ofNat b) (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (hb : 65536 ≤ b ∧ b + 424 < 4294967296) (hrd : rd < 18446744073709551616)
    (hwf : ∀ a, b ≤ a → a < b + 424 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 46508 ω μ x 58434 ω' μ' x 40 ∧
      ω'[0] = UInt64.ofNat 2090 ∧ ω'[1] = UInt64.ofNat b ∧ ω'[5] = ω[5] ∧ ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (b + 272) ∧ ω'[9] = UInt64.ofNat 32 ∧
      rdN μ' (b + 96) 8 = rdN μ (b + 272) 8 ∧
      rdN μ' (b + 104) 8 = rdN μ (b + 280) 8 ∧
      rdN μ' (b + 112) 8 = rdN μ (b + 288) 8 ∧
      rdN μ' (b + 120) 8 = rdN μ (b + 296) 8 ∧
      (∀ a, a < 4294967296 → (a < b + 96 ∨ b + 128 ≤ a) → (a < b + 272 ∨ b + 304 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, b ≤ a → a < b + 424 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h6, h7, hwf, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h6]
    all_goals try with_reducible rfl
    all_goals try first
      | (rd_simp []; done)
      | rd_simp []
    all_goals try first
      | with_reducible rfl
      | exact Nat.mod_eq_of_lt (by omega)
      | with_reducible exact Nat.mod_eq_of_lt (rdN_lt64 _ _)
    all_goals first
      | (congr 1; omega)
      | (simp only [Nat.reduceMul, Nat.reducePow, Nat.mod_mod]; exact Nat.mod_eq_of_lt (rdN_lt64 _ _))
      | rfl

/-- **46571 … 46852**, y read (ω₇ = 0): y copied from b + 272 to b + 136 and the call of the gas's decoder 46856 (ω₇ = rd, return address 2106). -/
theorem op_h4 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (b rd : Nat) (h1 : ω[1] = UInt64.ofNat b) (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (hb : 65536 ≤ b ∧ b + 424 < 4294967296) (hrd : rd < 18446744073709551616)
    (hwf : ∀ a, b ≤ a → a < b + 424 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 46571 ω μ x 46856 ω' μ' x 40 ∧
      ω'[0] = UInt64.ofNat 2106 ∧ ω'[1] = UInt64.ofNat b ∧ ω'[5] = ω[5] ∧ ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat rd ∧
      rdN μ' (b + 136) 8 = rdN μ (b + 272) 8 ∧
      rdN μ' (b + 144) 8 = rdN μ (b + 280) 8 ∧
      rdN μ' (b + 152) 8 = rdN μ (b + 288) 8 ∧
      rdN μ' (b + 160) 8 = rdN μ (b + 296) 8 ∧
      (∀ a, a < 4294967296 → (a < b + 136 ∨ b + 168 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, b ≤ a → a < b + 424 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h6, h7, hwf, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h6]
    all_goals try with_reducible rfl
    all_goals try first
      | (rd_simp []; done)
      | rd_simp []
    all_goals try first
      | with_reducible rfl
      | exact Nat.mod_eq_of_lt (by omega)
      | with_reducible exact Nat.mod_eq_of_lt (rdN_lt64 _ _)
    all_goals first
      | (congr 1; omega)
      | (simp only [Nat.reduceMul, Nat.reducePow, Nat.mod_mod]; exact Nat.mod_eq_of_lt (rdN_lt64 _ _))
      | rfl

end Services.Bootstrap.Acc
