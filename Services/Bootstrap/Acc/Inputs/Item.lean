import Services.Bootstrap.CodeAAll
import Services.Bootstrap.Alloc.AllocWrap
import Services.Bootstrap.Memzero
import Services.Bootstrap.MemcpyBig
import Services.Bootstrap.Acc.Inputs.ReadVec
import PVM.Logic.Go

/-!
# `AccumulateItem::decode` (45126), the transfer arm

45126 decodes one accumulation input (GP v0.8.0 §12, 𝕌 ∪ 𝕏) from a reader into a 184-octet slot.
The tag octet comes first. Tag 1 is a deferred transfer, ℰ(1, ℰ₄(s), ℰ₄(d), ℰ₈(a), m, ℰ₈(g))
(GP Appendix C): the slot gets −1 at + 0 (the transfer's niche), the memo at + 8 … + 136, a at
+ 136, g at + 144, s at + 152 and d at + 156. Tag 0 is an operand (see `ItemOperand.lean`); any
other tag writes −2 (an error) at + 0.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **45126 … 58434**: the 424-octet frame (ω₀, ω₅, ω₆ at sp − 8, − 16, − 24), the slot `out`
    (ω₇) kept in ω₆ and the reader (ω₈) in ω₅ and ω₁₀, a zero octet at sp − 152, and the read of the
    tag octet into it (return address 2082). -/
theorem it_pre {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp out rd : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat out) (h8 : ω[8] = UInt64.ofNat rd)
    (hsp : 65536 + 424 ≤ sp ∧ sp < 4294967296) (hout : out < 18446744073709551616) (hrd : rd < 18446744073709551616)
    (hwf : ∀ a, sp - 424 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 45126 ω μ x 58434 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat 2082 ∧ ω'[1] = UInt64.ofNat (sp - 424) ∧ ω'[5] = UInt64.ofNat rd ∧
      ω'[6] = UInt64.ofNat out ∧ ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (sp - 152) ∧
      ω'[9] = UInt64.ofNat 1 ∧ ω'[10] = UInt64.ofNat rd ∧
      rdN μ' (sp - 8) 8 = ω[0].toNat ∧ rdN μ' (sp - 16) 8 = ω[5].toNat ∧ rdN μ' (sp - 24) 8 = ω[6].toNat ∧
      (∀ a, a < 4294967296 → (a < sp - 424 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 424 ≤ a → a < sp → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h7, h8, hwf, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h7, h8]
    all_goals try with_reducible rfl
    all_goals try simp only [show sp - 424 + 416 = sp - 8 from by omega, show sp - 424 + 408 = sp - 16 from by omega,
      show sp - 424 + 400 = sp - 24 from by omega]
    all_goals try first
      | (rd_simp []; done)
      | rd_simp []
    all_goals try first
      | with_reducible rfl
      | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)
    all_goals first
      | (congr 1; omega)
      | rfl
      | rw [Nat.mod_eq_of_lt (by omega)]
      | (congr 1; rw [Nat.mod_eq_of_lt (by omega)])


/-- **46300 … 58434**, the tag read (ω₇ = 0) and the tag 1 (a transfer, at b + 272, b the frame's
    base): `out` saved at b + 24, a zero word at b + 272, and the read of ℰ₄(s) into it (ω₇ = ω₆ = rd,
    ω₈ = b + 272, ω₉ = 4, return address 2092). -/
theorem it_tr_src {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (b out rd : Nat) (h1 : ω[1] = UInt64.ofNat b) (h5 : ω[5] = UInt64.ofNat rd) (h6 : ω[6] = UInt64.ofNat out)
    (h7 : ω[7] = UInt64.ofNat 0) (mt : rdN μ (b + 272) 1 = 1)
    (hb : 65536 ≤ b ∧ b + 424 < 4294967296) (hout : out < 18446744073709551616) (hrd : rd < 18446744073709551616)
    (hwf : ∀ a, b ≤ a → a < b + 424 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 46300 ω μ x 58434 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat 2092 ∧ ω'[1] = UInt64.ofNat b ∧ ω'[5] = UInt64.ofNat rd ∧
      ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (b + 272) ∧
      ω'[9] = UInt64.ofNat 4 ∧ rdN μ' (b + 24) 8 = out ∧
      (∀ a, a < 4294967296 → (a < b + 24 ∨ b + 32 ≤ a) → (a < b + 272 ∨ b + 276 ≤ a) → μ'.read a = μ.read a) ∧
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
    all_goals first
      | (congr 1; omega)
      | rfl

end Services.Bootstrap.Acc
