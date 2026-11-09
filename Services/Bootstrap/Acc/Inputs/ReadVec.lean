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


/-- **41175 … 58434**, after `finish_grow` wrote `Ok(ptr, len)` at b + 48 (b the frame's base):
    `finish_grow`'s return through entry 1028 (2058) to 45773, the block and its capacity stored at
    b + 24 and b + 32, and the reader call for the chunk: ω₇ = rd (from b + 16), ω₈ = ptr,
    ω₉ = len, return address 2060. -/
theorem rv_mid {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (b rd ptr len : Nat) (h0 : ω[0] = UInt64.ofNat 2058) (h1 : ω[1] = UInt64.ofNat b)
    (h5 : ω[5] = UInt64.ofNat 0) (h6 : ω[6] = UInt64.ofNat len)
    (m0 : rdN μ b 8 = len) (m16 : rdN μ (b + 16) 8 = rd) (m48 : rdN μ (b + 48) 8 = 0)
    (m56 : rdN μ (b + 56) 8 = ptr)
    (hb : 65536 ≤ b ∧ b + 96 < 4294967296) (hptr : ptr < 18446744073709551616) (hlen : len < 4294967296)
    (hrd : rd < 18446744073709551616)
    (hwf : ∀ a, b ≤ a → a < b + 96 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 41175 ω μ x 58434 ω' μ' x 30 ∧
      ω'[0] = UInt64.ofNat 2060 ∧ ω'[1] = UInt64.ofNat b ∧ ω'[5] = UInt64.ofNat 0 ∧
      ω'[6] = UInt64.ofNat len ∧ ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat ptr ∧
      ω'[9] = UInt64.ofNat len ∧
      rdN μ' (b + 24) 8 = ptr ∧ rdN μ' (b + 32) 8 = len ∧
      (∀ a, a < 4294967296 → (a < b + 24 ∨ b + 40 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, b ≤ a → a < b + 96 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h0, h1, h5, h6, m0, m16, m48, m56, hwf, hr, Nat.mod_eq_of_lt hptr,
    Nat.mod_eq_of_lt hrd, Nat.mod_eq_of_lt (show len < 18446744073709551616 by omega),
    rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h0, h1, h5, h6]
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


/-- **45809 … 45950**, the chunk read (ω₇ = 0) and nothing left: `Vec { cap: len, ptr, len }`
    stored at `out` (from b + 8; capacity b + 32, pointer b + 24), ω₀, ω₅, ω₆ restored from
    b + 88, + 80, + 72 and the frame popped, at the return's `jumpInd`. -/
theorem rv_exit {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (b out ptr len r0 r5 r6 : Nat) (h1 : ω[1] = UInt64.ofNat b)
    (h5 : ω[5] = UInt64.ofNat 0) (h6 : ω[6] = UInt64.ofNat len) (h7 : ω[7] = UInt64.ofNat 0)
    (m8 : rdN μ (b + 8) 8 = out) (m24 : rdN μ (b + 24) 8 = ptr) (m32 : rdN μ (b + 32) 8 = len)
    (m40 : rdN μ (b + 40) 8 = len) (m72 : rdN μ (b + 72) 8 = r6) (m80 : rdN μ (b + 80) 8 = r5)
    (m88 : rdN μ (b + 88) 8 = r0)
    (hb : 65536 ≤ b ∧ b + 96 < 4294967296) (hout : 65536 ≤ out ∧ out + 24 < 4294967296)
    (hptr : ptr < 18446744073709551616) (hlen : len < 4294967296)
    (dbo : out + 24 ≤ b ∨ b + 96 ≤ out)
    (hrb : ∀ a, b ≤ a → a < b + 96 → μ.readable a = true)
    (hwo : ∀ a, out ≤ a → a < out + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 45809 ω μ x 45950 ω' μ' x 30 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (b + 96) ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 ∧
      rdN μ' out 8 = len ∧ rdN μ' (out + 8) 8 = ptr ∧ rdN μ' (out + 16) 8 = len ∧
      (∀ a, a < 4294967296 → (a < out ∨ out + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hro : ∀ a, out ≤ a → a < out + 24 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwo a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, h6, h7, m8, m24, m32, m40, m72, m80, m88, hrb, hro, hwo,
    Nat.mod_eq_of_lt (show len < 18446744073709551616 by omega), rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h5, h6]
    all_goals try with_reducible rfl
    all_goals try simp only [show 16 + out = out + 16 from Nat.add_comm _ _, show 8 + out = out + 8 from Nat.add_comm _ _]
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
