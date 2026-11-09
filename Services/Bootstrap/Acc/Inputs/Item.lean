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
      | exact UInt64.ofNat_toNat
      | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)


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

/-- **46624 … 58434**: ℰ₄(s) read; s (from b + 272, sign-extended) saved at b + 16, `out` (b + 24) in ω₅, a zero word at b + 272 and the read of ℰ₄(d) (return address 2094). -/
theorem it_tr_dst {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (b out rd v : Nat)
    (h1 : ω[1] = UInt64.ofNat b) (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (hb : 65536 ≤ b ∧ b + 424 < 4294967296) (hrd : rd < 18446744073709551616)
    (hrf : ∀ a, b ≤ a → a < b + 424 → μ.readable a = true) (hwf : ∀ a, b ≤ a → a < b + 424 → μ.writable a = true)
    (m24 : rdN μ (b + 24) 8 = out) (mv : rdN μ (b + 272) 4 = v) (hv : v < 4294967296) (hout : out < 18446744073709551616) :
    ∃ ω' μ', FreeStepsH p R 46624 ω μ x 58434 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat 2094 ∧ ω'[1] = UInt64.ofNat b ∧ ω'[5] = UInt64.ofNat out ∧ ω'[6] = UInt64.ofNat rd ∧
      ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (b + 272) ∧ ω'[9] = UInt64.ofNat 4 ∧
      rdN μ' (b + 16) 8 = sxw 4 v % 18446744073709551616 ∧
      (∀ a, a < 4294967296 → (a < b ∨ b + 424 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h6, h7, m24, mv, hrf, hwf, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h6]
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
      | (congr 1; rw [Nat.mod_eq_of_lt (by omega)])
      | exact UInt64.ofNat_toNat
      | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)

/-- **46658 … 58434**: ℰ₄(d) read; d saved at b + 8, a zero word at b + 272 and the read of ℰ₈(a) (return address 2096). -/
theorem it_tr_amt {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (b rd v : Nat)
    (h1 : ω[1] = UInt64.ofNat b) (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (hb : 65536 ≤ b ∧ b + 424 < 4294967296) (hrd : rd < 18446744073709551616)
    (hrf : ∀ a, b ≤ a → a < b + 424 → μ.readable a = true) (hwf : ∀ a, b ≤ a → a < b + 424 → μ.writable a = true)
    (mv : rdN μ (b + 272) 4 = v) (hv : v < 4294967296) :
    ∃ ω' μ', FreeStepsH p R 46658 ω μ x 58434 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat 2096 ∧ ω'[1] = UInt64.ofNat b ∧ ω'[6] = UInt64.ofNat rd ∧
      ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (b + 272) ∧ ω'[9] = UInt64.ofNat 8 ∧ ω'[5] = ω[5] ∧
      rdN μ' (b + 8) 8 = sxw 4 v % 18446744073709551616 ∧
      (∀ a, a < 4294967296 → (a < b ∨ b + 424 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h6, h7, mv, hrf, hwf, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h6]
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
      | (congr 1; rw [Nat.mod_eq_of_lt (by omega)])
      | exact UInt64.ofNat_toNat
      | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)

/-- **46688 … 70133**: ℰ₈(a) read; a saved at b + 0, and the memo's buffer b + 272 … + 400 zeroed by `memzero` (return address 2098). -/
theorem it_tr_memo0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (b rd v : Nat)
    (h1 : ω[1] = UInt64.ofNat b) (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (hb : 65536 ≤ b ∧ b + 424 < 4294967296) (hrd : rd < 18446744073709551616)
    (hrf : ∀ a, b ≤ a → a < b + 424 → μ.readable a = true) (hwf : ∀ a, b ≤ a → a < b + 424 → μ.writable a = true)
    (mv : rdN μ (b + 272) 8 = v) (hv : v < 18446744073709551616) :
    ∃ ω' μ', FreeStepsH p R 46688 ω μ x 70133 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat 2098 ∧ ω'[1] = UInt64.ofNat b ∧ ω'[6] = UInt64.ofNat rd ∧
      ω'[7] = UInt64.ofNat (b + 272) ∧ ω'[8] = UInt64.ofNat 0 ∧ ω'[9] = UInt64.ofNat 128 ∧ ω'[5] = ω[5] ∧
      rdN μ' b 8 = v ∧
      (∀ a, a < 4294967296 → (a < b ∨ b + 424 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h6, h7, mv, hrf, hwf, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h6]
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
      | (congr 1; rw [Nat.mod_eq_of_lt (by omega)])
      | exact UInt64.ofNat_toNat
      | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)

/-- **46714 … 58434**: the read of the memo m (128 octets) into b + 272 (return address 2100). -/
theorem it_tr_memo {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (b rd : Nat) (h1 : ω[1] = UInt64.ofNat b) (h6 : ω[6] = UInt64.ofNat rd)
    (hb : 65536 ≤ b ∧ b + 424 < 4294967296) (hrd : rd < 18446744073709551616) :
    ∃ ω' μ', FreeStepsH p R 46714 ω μ x 58434 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat 2100 ∧ ω'[1] = UInt64.ofNat b ∧ ω'[6] = UInt64.ofNat rd ∧
      ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (b + 272) ∧ ω'[9] = UInt64.ofNat 128 ∧ ω'[5] = ω[5] ∧
      μ' = μ := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h6, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h6]
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
      | (congr 1; rw [Nat.mod_eq_of_lt (by omega)])
      | exact UInt64.ofNat_toNat
      | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)

/-- **46730 … 68729**: the memo read; its copy from b + 272 to b + 136 (`memcpy`, 128 octets, return address 2102). -/
theorem it_tr_memocp {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (b : Nat) (h1 : ω[1] = UInt64.ofNat b) (h7 : ω[7] = UInt64.ofNat 0) (hb : 65536 ≤ b ∧ b + 424 < 4294967296) :
    ∃ ω' μ', FreeStepsH p R 46730 ω μ x 68729 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat 2102 ∧ ω'[1] = UInt64.ofNat b ∧ ω'[7] = UInt64.ofNat (b + 136) ∧
      ω'[8] = UInt64.ofNat (b + 272) ∧ ω'[9] = UInt64.ofNat 128 ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ μ' = μ := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h7, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
      | rfl
      | (congr 1; rw [Nat.mod_eq_of_lt (by omega)])
      | exact UInt64.ofNat_toNat
      | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)

/-- **46751 … 46040**: the call of the `u64` reader on the reader (ω₇ = ω₆, return address 2104). -/
theorem it_tr_gas {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (b : Nat) (h1 : ω[1] = UInt64.ofNat b) :
    ∃ ω' μ', FreeStepsH p R 46751 ω μ x 46040 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat 2104 ∧ ω'[1] = UInt64.ofNat b ∧ ω'[7] = ω[6] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ μ' = μ := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
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
      | rfl
      | (congr 1; rw [Nat.mod_eq_of_lt (by omega)])
      | exact UInt64.ofNat_toNat
      | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)

/-- **46040 … 58434**, the `u64` reader: the 16-octet frame (ω₀ at sp − 8), a zero word at sp − 16 and the read of 8 octets into it (return address 2068). -/
theorem u64_pre {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : 65536 + 16 ≤ sp ∧ sp < 4294967296)
    (hwf : ∀ a, sp - 16 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 46040 ω μ x 58434 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat 2068 ∧ ω'[1] = UInt64.ofNat (sp - 16) ∧ ω'[8] = UInt64.ofNat (sp - 16) ∧
      ω'[9] = UInt64.ofNat 8 ∧ ω'[7] = ω[7] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      rdN μ' (sp - 8) 8 = ω[0].toNat ∧
      (∀ a, a < 4294967296 → (a < sp - 16 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, hwf, Memory.readable_of_writable, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1]
    all_goals try with_reducible rfl
    all_goals try simp only [show sp - 16 + 8 = sp - 8 from by omega]
    all_goals try first
      | (rd_simp []; done)
      | rd_simp []
    all_goals try first
      | with_reducible rfl
      | exact Nat.mod_eq_of_lt (by omega)
    all_goals first
      | (congr 1; omega)
      | rfl
      | (congr 1; rw [Nat.mod_eq_of_lt (by omega)])
      | exact UInt64.ofNat_toNat
      | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)

/-- **46059 … 46067**: the word read (at sp, the frame's base) in ω₈, ω₀ restored from sp + 8, the frame popped, at the return's `jumpInd`. -/
theorem u64_post {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v r0 : Nat) (h1 : ω[1] = UInt64.ofNat sp) (m0 : rdN μ sp 8 = v) (m8 : rdN μ (sp + 8) 8 = r0)
    (hsp : 65536 ≤ sp ∧ sp + 16 < 4294967296)
    (hrf : ∀ a, sp ≤ a → a < sp + 16 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 46059 ω μ x 46067 ω' μ' x 20 ∧
      ω'[8] = UInt64.ofNat v ∧ ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (sp + 16) ∧ ω'[7] = ω[7] ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ μ' = μ := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, m0, m8, hrf, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1]
    all_goals try with_reducible rfl
    all_goals try simp only [Nat.add_zero]
    all_goals try first
      | (rd_simp []; done)
      | rd_simp []
    all_goals try first
      | with_reducible rfl
      | exact Nat.mod_eq_of_lt (by omega)
    all_goals first
      | (congr 1; omega)
      | rfl
      | (congr 1; rw [Nat.mod_eq_of_lt (by omega)])
      | exact UInt64.ofNat_toNat
      | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)

/-- **46759 … 68729**: the gas g read (ω₇ = 0, g in ω₈): g kept in ω₆, and the memo's copy from b + 136 to out + 8 (`memcpy`, 128 octets, return address 2112). -/
theorem it_tr_cp {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (b out g : Nat) (h1 : ω[1] = UInt64.ofNat b) (h5 : ω[5] = UInt64.ofNat out) (h7 : ω[7] = UInt64.ofNat 0)
    (h8 : ω[8] = UInt64.ofNat g) (hb : b + 424 < 4294967296) (hout : out + 8 < 18446744073709551616)
    (hg : g < 18446744073709551616) :
    ∃ ω' μ', FreeStepsH p R 46759 ω μ x 68729 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat 2112 ∧ ω'[1] = UInt64.ofNat b ∧ ω'[5] = UInt64.ofNat out ∧ ω'[6] = UInt64.ofNat g ∧
      ω'[7] = UInt64.ofNat (out + 8) ∧ ω'[8] = UInt64.ofNat (b + 136) ∧ ω'[9] = UInt64.ofNat 128 ∧ μ' = μ := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, h7, h8, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h5, h8]
    all_goals try with_reducible rfl
    all_goals try simp only [Nat.add_zero]
    all_goals try first
      | (rd_simp []; done)
      | rd_simp []
    all_goals try first
      | with_reducible rfl
      | exact Nat.mod_eq_of_lt (by omega)
    all_goals first
      | (congr 1; omega)
      | rfl
      | (congr 1; rw [Nat.mod_eq_of_lt (by omega)])
      | exact UInt64.ofNat_toNat
      | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)

/-- **47029 … 47072**, the transfer's slot filled: −1 at out + 0, a (from b) at + 136, g (ω₆) at + 144,
    s (b + 16) as a `u32` at + 152 and d (b + 8) at + 156; ω₀, ω₅, ω₆ restored from b + 416, + 408,
    + 400 and the frame popped, at the return's `jumpInd`. -/
theorem it_tr_fill {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (b out g am sv dv r0 r5 r6 : Nat) (h1 : ω[1] = UInt64.ofNat b) (h5 : ω[5] = UInt64.ofNat out)
    (h6 : ω[6] = UInt64.ofNat g)
    (m0 : rdN μ b 8 = am) (m8 : rdN μ (b + 8) 8 = dv) (m16 : rdN μ (b + 16) 8 = sv)
    (m400 : rdN μ (b + 400) 8 = r6) (m408 : rdN μ (b + 408) 8 = r5) (m416 : rdN μ (b + 416) 8 = r0)
    (hb : 65536 ≤ b ∧ b + 424 < 4294967296) (hout : 65536 ≤ out ∧ out + 184 < 4294967296)
    (dbo : out + 184 ≤ b ∨ b + 424 ≤ out) (hg : g < 18446744073709551616)
    (ham : am < 18446744073709551616) (hsv : sv < 18446744073709551616) (hdv : dv < 18446744073709551616)
    (hr0 : r0 < 18446744073709551616) (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hrf : ∀ a, b ≤ a → a < b + 424 → μ.readable a = true)
    (hwo : ∀ a, out ≤ a → a < out + 184 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 47029 ω μ x 47072 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (b + 424) ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 ∧
      rdN μ' out 8 = 18446744073709551615 ∧ rdN μ' (out + 136) 8 = am ∧ rdN μ' (out + 144) 8 = g ∧
      rdN μ' (out + 152) 4 = sv % 4294967296 ∧ rdN μ' (out + 156) 4 = dv % 4294967296 ∧
      (∀ a, a < 4294967296 → (a < out ∨ out + 8 ≤ a) → (a < out + 136 ∨ out + 160 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hro : ∀ a, out ≤ a → a < out + 184 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwo a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, h6, m0, m8, m16, m400, m408, m416, hrf, hro, hwo, rdN_writeN_disjoint, ↓rdN_fold,
    ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1]
    all_goals try with_reducible rfl
    all_goals try simp only [show 136 + out = out + 136 from Nat.add_comm _ _, show 144 + out = out + 144 from Nat.add_comm _ _,
      show 152 + out = out + 152 from Nat.add_comm _ _, show 156 + out = out + 156 from Nat.add_comm _ _]
    all_goals try first
      | (rd_simp []; done)
      | rd_simp []
    all_goals try first
      | with_reducible rfl
      | exact Nat.mod_eq_of_lt (by omega)
    all_goals first
      | (congr 1; omega)
      | rfl
      | (congr 1; rw [Nat.mod_eq_of_lt (by omega)])

end Services.Bootstrap.Acc
