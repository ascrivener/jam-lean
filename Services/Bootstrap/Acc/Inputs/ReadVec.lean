import Services.Bootstrap.CodeAAll
import Services.Bootstrap.Alloc.AllocWrap
import PVM.Logic.Go

/-!
# Accumulate's `Vec<u8>` body reader (45643), for a length of at most 16 KiB

45643 reads `len` octets (ω₉) from a reader (ω₈) into a fresh `Vec<u8>` written at `out` (ω₇),
16384 octets at a time: each chunk grows the vector by `finish_grow` (40852; align 1, element 1)
and copies the chunk by the reader (58434). A reader with fewer than `len` octets left gives an
error (−1 at `out`); `len` = 0 gives the empty vector. For 0 < len ≤ 16384 there is one chunk, and
the growth starts from no block.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **45643 … 40852**, 0 < len ≤ 16384 and the reader (`rd`, its length at rd + 8) holding at least
    `len` octets: the 96-octet frame (ω₀, ω₅, ω₆ at sp − 8, − 16, − 24; `out` at sp − 88, `rd` at
    sp − 80), the empty vector's capacity 0 and pointer 1 at sp − 64 and sp − 72, `len` at sp − 56,
    and the call of `finish_grow` for `len` octets with no current block: ω₇ = sp − 48, ω₈ = 0,
    ω₉ = 1, ω₁₀ = len, ω₁₁ = ω₁₂ = 1, return address 2058. -/
theorem rv_entry {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp out rd rlen len : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat out)
    (h8 : ω[8] = UInt64.ofNat rd) (h9 : ω[9] = UInt64.ofNat len)
    (mr : rdN μ (rd + 8) 8 = rlen) (hlen : 0 < len ∧ len ≤ 16384) (hrl : len ≤ rlen)
    (hrl64 : rlen < 18446744073709551616) (hout : out < 18446744073709551616)
    (hsp : 65536 + 96 ≤ sp ∧ sp < 4294967296) (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296)
    (hrr : ∀ a, rd ≤ a → a < rd + 16 → μ.readable a = true)
    (dr : rd + 16 ≤ sp - 96 ∨ sp ≤ rd)
    (hwf : ∀ a, sp - 96 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 45643 ω μ x 40852 ω' μ' x 40 ∧
      ω'[1] = UInt64.ofNat (sp - 96) ∧ ω'[7] = UInt64.ofNat (sp - 48) ∧ ω'[8] = UInt64.ofNat 0 ∧
      ω'[9] = UInt64.ofNat 1 ∧ ω'[10] = UInt64.ofNat len ∧ ω'[11] = UInt64.ofNat 1 ∧
      ω'[12] = UInt64.ofNat 1 ∧ ω'[0] = UInt64.ofNat 2058 ∧
      rdN μ' (sp - 8) 8 = ω[0].toNat ∧ rdN μ' (sp - 16) 8 = ω[5].toNat ∧ rdN μ' (sp - 24) 8 = ω[6].toNat ∧
      rdN μ' (sp - 88) 8 = out ∧ rdN μ' (sp - 80) 8 = rd ∧
      (∀ a, a < 4294967296 → (a < sp - 96 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 96 ≤ a → a < sp → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have z : ∀ μ0 : Memory, rdN (μ0.writeN (sp - 96 + 32) [UInt8.ofNat 0, UInt8.ofNat 0, UInt8.ofNat 0,
      UInt8.ofNat 0, UInt8.ofNat 0, UInt8.ofNat 0, UInt8.ofNat 0, UInt8.ofNat 0]) (sp - 96 + 32) 8 = 0 := by
    intro μ0; unfold rdN
    rw [PVM.Memory.readN_writeN_same μ0 (sp - 96 + 32) 8 _ rfl (by unfold PVM.two32; omega)]; rfl
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h7, h8, h9, mr, hrr, hwf, hr, Nat.mod_eq_of_lt hrl64, z, show (0 : Nat) < len by omega,
    show ¬ rlen < len by omega, show len ≠ 0 by omega, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h9]
    all_goals try with_reducible rfl
    all_goals try simp only [show sp - 96 + 88 = sp - 8 from by omega, show sp - 96 + 80 = sp - 16 from by omega,
      show sp - 96 + 72 = sp - 24 from by omega, show sp - 96 + 8 = sp - 88 from by omega,
      show sp - 96 + 16 = sp - 80 from by omega]
    all_goals try first
      | (rd_simp []; done)
      | rd_simp []
    all_goals try first
      | with_reducible rfl
      | exact Nat.mod_eq_of_lt (by omega)
      | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)
    all_goals first
      | (congr 1; omega)
      | rfl

end Services.Bootstrap.Acc
