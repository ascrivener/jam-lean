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
      (∀ a, a < 4294967296 → (a < b + 16 ∨ b + 24 ≤ a) → (a < b + 272 ∨ b + 276 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h6, h7, m24, mv, hrf, hwf, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_, fun a => ?_⟩
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
      (∀ a, a < 4294967296 → (a < b + 8 ∨ b + 16 ≤ a) → (a < b + 272 ∨ b + 280 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h6, h7, mv, hrf, hwf, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_, fun a => ?_⟩
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
      (∀ a, a < 4294967296 → (a < b ∨ b + 8 ≤ a) → μ'.read a = μ.read a) ∧
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

/-- **Stage 1 of the transfer arm, 45126 … 46624**: the frame (base b = sp − 424), the tag octet 1
    read, and ℰ₄(s) read into b + 272; the reader `rd` (in the caller's frame) advanced by 5. -/
theorem tr_s1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp out rd ip rlen : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat out)
    (h8 : ω[8] = UInt64.ofNat rd)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ip) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 rlen)
    (hrl : 5 ≤ rlen) (hrl32 : rlen < 4294967296) (htag : rdN μ ip 1 = 1)
    (hip : 65536 ≤ ip ∧ ip + 160 < 2147483648) (hra : ∀ a, ip ≤ a → a < ip + 5 → μ.readable a = true)
    (hsp : 2147483648 + 512 ≤ sp ∧ sp < 4294967296 ∧ sp % 8 = 0) (hout : sp ≤ out ∧ out < 18446744073709551616)
    (hrd : sp ≤ rd ∧ rd + 16 < 4294967296)
    (hwf : ∀ a, sp - 512 ≤ a → a < sp → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 45126 ω μ x 46624 ω' μ' x 300 ∧
      ω'[1] = UInt64.ofNat (sp - 424) ∧ ω'[5] = UInt64.ofNat rd ∧ ω'[6] = UInt64.ofNat rd ∧
      ω'[7] = UInt64.ofNat 0 ∧
      rdN μ' (sp - 424 + 24) 8 = out ∧ rdN μ' (sp - 424 + 272) 4 = rdN μ (ip + 1) 4 ∧
      rdN μ' (sp - 8) 8 = ω[0].toNat ∧ rdN μ' (sp - 16) 8 = ω[5].toNat ∧ rdN μ' (sp - 24) 8 = ω[6].toNat ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ip + 5) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (rlen - 5) ∧
      (∀ a, a < 4294967296 → (a < sp - 512 ∨ sp ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hrd64 : rd < 18446744073709551616 := by omega
  obtain ⟨ω1, μ1, r1, a0, a1, a5, a6, a7, a8, a9, a10, s8, s16, s24, fr1, rd1, wr1⟩ :=
    it_pre (p := p) (P := P) (R := R) x ω μ sp out rd h1 h7 h8 ⟨by omega, hsp.2.1⟩ hout.2 hrd64
      (fun a h1 h2 => hwf a (by omega) h2)
  have m1 : ∀ a, a < 4294967296 → (a < sp - 424 ∨ sp ≤ a) → μ1.read a = μ.read a := fr1
  have hR0' : μ1.readN rd 8 = Num.encodeLE 8 ip := by
    rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => m1 _ (by omega) (Or.inr (by omega)))]; exact hR0
  have hR8' : μ1.readN (rd + 8) 8 = Num.encodeLE 8 rlen := by
    rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => m1 _ (by omega) (Or.inr (by omega)))]; exact hR8
  obtain ⟨ω2, μ2, r2, e0, e1, -, -, -, e5, e6, -, e7, q0, q8, qb, fr2, rd2, wr2⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω1 μ1 2082 46300 (sp - 424) rd (sp - 152) ip rlen 1 a0 a1 a7 a8 a9
      (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_1040]) bs_46300
      ⟨by omega, by omega⟩ ⟨by omega, hrd.2⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide) (by omega) hrl32
      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
      (fun a h1 h2 => by rw [wr1]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr1]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [wr1]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [rd1]; exact hra a h1 (by omega)) hR0' hR8'
  have mt : rdN μ2 (sp - 424 + 272) 1 = 1 := by
    unfold rdN at htag ⊢
    rw [show sp - 424 + 272 = sp - 152 by omega, qb,
      PVM.Memory.readN_congr (μ := μ) (fun j hj => m1 _ (by omega) (Or.inl (by omega)))]; exact htag
  obtain ⟨ω3, μ3, r3, c0, c1, c5, c6, c7, c8, c9, k24, fr3, rd3, wr3⟩ :=
    it_tr_src (p := p) (P := P) (R := R) x ω2 μ2 (sp - 424) out rd (by rw [e1, a1]) (by rw [e5, a5])
      (by rw [e6, a6]) e7 mt ⟨by omega, by omega⟩ hout.2 hrd64
      (fun a h1 h2 => by rw [wr2, wr1]; exact hwf a (by omega) (by omega))
  have m32 : ∀ a, a < 4294967296 → (a < sp - 424 + 24 ∨ sp - 424 + 32 ≤ a) → (a < sp - 424 + 272 ∨ sp - 424 + 276 ≤ a) →
      μ3.read a = μ2.read a := fr3
  have k3 : ∀ (o : Nat) {l : List UInt8}, sp ≤ o → o + 8 < 4294967296 → μ2.readN o 8 = l → μ3.readN o 8 = l :=
    fun o l h1 h2 h => by
      rw [PVM.Memory.readN_congr (μ := μ2) (fun j hj => m32 _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)))]
      exact h
  obtain ⟨ω4, μ4, r4, d0, d1, -, -, -, d5, d6, -, d7, p0, p8, pb, fr4, rd4, wr4⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω3 μ3 2092 46624 (sp - 424) rd (sp - 424 + 272) (ip + 1) (rlen - 1) 4
      c0 c1 c7 c8 c9
      (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_1045]) bs_46624
      ⟨by omega, by omega⟩ ⟨by omega, hrd.2⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide) (by omega) (by omega)
      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
      (fun a h1 h2 => by rw [wr3, wr2, wr1]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr3, wr2, wr1]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [wr3, wr2, wr1]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [rd3, rd2, rd1]; exact hra a (by omega) (by omega))
      (k3 rd hrd.1 (by omega) q0) (k3 (rd + 8) (by omega) (by omega) q8)
  -- the frame from b up to sp, kept by the second read
  have f4 : ∀ a, sp - 424 ≤ a → a < sp → (a < sp - 424 + 272 ∨ sp - 424 + 276 ≤ a) → μ4.read a = μ3.read a :=
    fun a h1 h2 h3 => fr4 a (by omega) (Or.inr h1) (Or.inl (by omega)) h3
  have l4 : ∀ o v, sp - 424 ≤ o → o + 8 ≤ sp → (o + 8 ≤ sp - 424 + 272 ∨ sp - 424 + 276 ≤ o) →
      rdN μ3 o 8 = v → rdN μ4 o 8 = v := fun o v h1 h2 h3 hv => by
    rw [rdN_frame fun j hj => f4 _ (by omega) (by omega) (by omega)]; exact hv
  have l31 : ∀ o v, sp - 424 + 32 ≤ o → o + 8 ≤ sp → (o + 8 ≤ sp - 152 ∨ sp - 151 ≤ o) →
      (o + 8 ≤ sp - 424 + 272 ∨ sp - 424 + 276 ≤ o) → rdN μ1 o 8 = v → rdN μ3 o 8 = v := fun o v h1 h2 h3 h4 hv => by
    rw [rdN_frame fun j hj => m32 _ (by omega) (Or.inr (by omega)) (by omega),
      rdN_frame fun j hj => fr2 _ (by omega) (Or.inr (by omega)) (Or.inl (by omega)) (by omega)]; exact hv
  refine ⟨ω4, μ4, (((r1.trans r2).trans r3).trans r4).mono (by omega), by rw [d1, c1], by rw [d5, c5],
    by rw [d6, c6], d7, l4 _ _ (by omega) (by omega) (by omega) k24, ?_,
    l4 _ _ (by omega) (by omega) (by omega) (l31 _ _ (by omega) (by omega) (by omega) (by omega) s8),
    l4 _ _ (by omega) (by omega) (by omega) (l31 _ _ (by omega) (by omega) (by omega) (by omega) s16),
    l4 _ _ (by omega) (by omega) (by omega) (l31 _ _ (by omega) (by omega) (by omega) (by omega) s24),
    p0, p8, ?_, fun a => by rw [rd4, rd3, rd2, rd1], fun a => by rw [wr4, wr3, wr2, wr1]⟩
  · unfold rdN; rw [pb, PVM.Memory.readN_congr (μ := μ) (fun j hj => by
      rw [m32 _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)),
        fr2 _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)), m1 _ (by omega) (Or.inl (by omega))])]
  · intro a h0 hs hr
    rw [fr4 a h0 (by omega) hr (by omega), m32 a h0 (by omega) (by omega),
      fr2 a h0 (by omega) hr (by omega), m1 a h0 (by omega)]

/-- **Stage 2 of the transfer arm, 46624 … 46688**: s (at b + 272) saved sign-extended at b + 16,
    ℰ₄(d) read and d saved at b + 8, ℰ₈(a) read into b + 272; the reader advanced by 12. -/
theorem tr_s2 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (b out rd ip rlen : Nat) (h1 : ω[1] = UInt64.ofNat b) (h5 : ω[5] = UInt64.ofNat rd)
    (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (m24 : rdN μ (b + 24) 8 = out) (hout : out < 18446744073709551616)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ip) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 rlen)
    (hrl : 12 ≤ rlen) (hrl32 : rlen < 4294967296)
    (hip : 65536 ≤ ip ∧ ip + 160 < 2147483648) (hra : ∀ a, ip ≤ a → a < ip + 12 → μ.readable a = true)
    (hb : 2147483648 + 88 ≤ b ∧ b + 424 < 4294967296 ∧ b % 8 = 0) (hrd : b + 424 ≤ rd ∧ rd + 16 < 4294967296)
    (hwf : ∀ a, b - 88 ≤ a → a < b + 424 → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 46624 ω μ x 46688 ω' μ' x 300 ∧
      ω'[1] = UInt64.ofNat b ∧ ω'[5] = UInt64.ofNat out ∧ ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat 0 ∧
      rdN μ' (b + 16) 8 = sxw 4 (rdN μ (b + 272) 4) % 18446744073709551616 ∧
      rdN μ' (b + 8) 8 = sxw 4 (rdN μ ip 4) % 18446744073709551616 ∧
      rdN μ' (b + 272) 8 = rdN μ (ip + 4) 8 ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ip + 12) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (rlen - 12) ∧
      (∀ a, a < 4294967296 → (a < b - 88 ∨ b + 32 ≤ a) → (a < b + 272 ∨ b + 280 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hrd64 : rd < 18446744073709551616 := by omega
  obtain ⟨ω1, μ1, r1, a0, a1, a5, a6, a7, a8, a9, s16, fr1, rd1, wr1⟩ :=
    it_tr_dst (p := p) (P := P) (R := R) x ω μ b out rd (rdN μ (b + 272) 4) h1 h6 h7 ⟨by omega, by omega⟩ hrd64
      (fun a h1 h2 => Memory.readable_of_writable (hwf a (by omega) h2))
      (fun a h1 h2 => hwf a (by omega) h2) m24 rfl (rdN_lt μ _ 4) hout
  have m1 : ∀ a, a < 4294967296 → (a < b ∨ b + 424 ≤ a) → μ1.read a = μ.read a := fun a h0 h =>
    fr1 a h0 (by omega) (by omega)
  have k1 : ∀ (o : Nat) {l : List UInt8}, b + 424 ≤ o → o + 8 < 4294967296 → μ.readN o 8 = l → μ1.readN o 8 = l :=
    fun o l h1 h2 h => by rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => m1 _ (by omega) (Or.inr (by omega)))]; exact h
  obtain ⟨ω2, μ2, r2, e0, e1, -, -, -, e5, e6, -, e7, q0, q8, qb, fr2, rd2, wr2⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω1 μ1 2094 46658 b rd (b + 272) ip rlen 4 a0 a1 a7 a8 a9
      (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_1046]) bs_46658
      ⟨by omega, by omega⟩ ⟨by omega, hrd.2⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide) (by omega) hrl32
      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
      (fun a h1 h2 => by rw [wr1]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr1]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [wr1]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [rd1]; exact hra a h1 (by omega))
      (k1 rd (by omega) (by omega) hR0) (k1 (rd + 8) (by omega) (by omega) hR8)
  have mv : rdN μ2 (b + 272) 4 = rdN μ ip 4 := by
    unfold rdN; rw [qb, PVM.Memory.readN_congr (μ := μ) (fun j hj => m1 _ (by omega) (Or.inl (by omega)))]
  obtain ⟨ω3, μ3, r3, c0, c1, c6, c7, c8, c9, c5, s8, fr3, rd3, wr3⟩ :=
    it_tr_amt (p := p) (P := P) (R := R) x ω2 μ2 b rd (rdN μ ip 4) (by rw [e1, a1]) (by rw [e6, a6]) e7
      ⟨by omega, by omega⟩ hrd64
      (fun a h1 h2 => by rw [rd2, rd1]; exact Memory.readable_of_writable (hwf a (by omega) h2))
      (fun a h1 h2 => by rw [wr2, wr1]; exact hwf a (by omega) h2) mv (rdN_lt μ _ 4)
  have m3 : ∀ a, a < 4294967296 → (a < b ∨ b + 424 ≤ a) → μ3.read a = μ2.read a := fun a h0 h =>
    fr3 a h0 (by omega) (by omega)
  have k3 : ∀ (o : Nat) {l : List UInt8}, b + 424 ≤ o → o + 8 < 4294967296 → μ2.readN o 8 = l → μ3.readN o 8 = l :=
    fun o l h1 h2 h => by rw [PVM.Memory.readN_congr (μ := μ2) (fun j hj => m3 _ (by omega) (Or.inr (by omega)))]; exact h
  obtain ⟨ω4, μ4, r4, d0, d1, -, -, -, d5, d6, -, d7, p0, p8, pb, fr4, rd4, wr4⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω3 μ3 2096 46688 b rd (b + 272) (ip + 4) (rlen - 4) 8 c0 c1 c7 c8 c9
      (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_1047]) bs_46688
      ⟨by omega, by omega⟩ ⟨by omega, hrd.2⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide) (by omega) (by omega)
      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
      (fun a h1 h2 => by rw [wr3, wr2, wr1]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr3, wr2, wr1]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [wr3, wr2, wr1]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [rd3, rd2, rd1]; exact hra a (by omega) (by omega))
      (k3 rd (by omega) (by omega) q0) (k3 (rd + 8) (by omega) (by omega) q8)
  -- words of the frame from b up: kept by the second read (outside its buffer b + 272 … + 280)
  have f4 : ∀ a, b ≤ a → a < b + 424 → (a < b + 272 ∨ b + 280 ≤ a) → μ4.read a = μ3.read a :=
    fun a h1 h2 h3 => fr4 a (by omega) (Or.inr h1) (Or.inl (by omega)) h3
  have l2 : ∀ o v, b ≤ o → o + 8 ≤ b + 272 → rdN μ1 o 8 = v → rdN μ2 o 8 = v := fun o v h1 h2 hv => by
    rw [rdN_frame fun j hj => fr2 _ (by omega) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))]; exact hv
  refine ⟨ω4, μ4, (((r1.trans r2).trans r3).trans r4).mono (by omega), by rw [d1, c1],
    by rw [d5, c5, e5, a5], by rw [d6, c6], d7, ?_, ?_, ?_, p0, p8, ?_,
    fun a => by rw [rd4, rd3, rd2, rd1], fun a => by rw [wr4, wr3, wr2, wr1]⟩
  · rw [rdN_frame fun j hj => f4 _ (by omega) (by omega) (Or.inl (by omega)),
      rdN_frame fun j hj => fr3 _ (by omega) (Or.inr (by omega)) (Or.inl (by omega))]
    exact l2 _ _ (by omega) (by omega) s16
  · rw [rdN_frame fun j hj => f4 _ (by omega) (by omega) (Or.inl (by omega))]
    rw [s8]
  · unfold rdN; rw [pb]; congr 1
    exact PVM.Memory.readN_congr fun j hj => by
      rw [m3 _ (by omega) (Or.inl (by omega)), fr2 _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)),
        m1 _ (by omega) (Or.inl (by omega))]
  · intro a h0 hs hb2 hr
    rw [fr4 a h0 (by omega) hr (by omega), fr3 a h0 (by omega) (by omega), fr2 a h0 (by omega) hr (by omega),
      fr1 a h0 (by omega) (by omega)]

/-- **Stage 3 of the transfer arm, 46688 … 46751**: a (at b + 272) saved at b, the memo buffer
    zeroed, the memo m (128 octets) read into it and copied to b + 136; the reader advanced by 128. -/
theorem tr_s3 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (b rd ip rlen : Nat) (h1 : ω[1] = UInt64.ofNat b) (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ip) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 rlen)
    (hrl : 128 ≤ rlen) (hrl32 : rlen < 4294967296)
    (hip : 65536 ≤ ip ∧ ip + 160 < 2147483648) (hra : ∀ a, ip ≤ a → a < ip + 128 → μ.readable a = true)
    (hb : 2147483648 + 88 ≤ b ∧ b + 424 < 4294967296 ∧ b % 8 = 0) (hrd : b + 424 ≤ rd ∧ rd + 16 < 4294967296)
    (hwf : ∀ a, b - 88 ≤ a → a < b + 424 → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 46688 ω μ x 46751 ω' μ' x 2400 ∧
      ω'[1] = UInt64.ofNat b ∧ ω'[5] = ω[5] ∧ ω'[6] = UInt64.ofNat rd ∧
      rdN μ' b 8 = rdN μ (b + 272) 8 ∧ μ'.readN (b + 136) 128 = μ.readN ip 128 ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ip + 128) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (rlen - 128) ∧
      (∀ a, a < 4294967296 → (a < b - 88 ∨ b + 8 ≤ a) → (a < b + 136 ∨ b + 400 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hrd64 : rd < 18446744073709551616 := by omega
  obtain ⟨ω1, μ1, r1, a0, a1, a6, a7, a8, a9, a5, s0, fr1, rd1, wr1⟩ :=
    it_tr_memo0 (p := p) (P := P) (R := R) x ω μ b rd (rdN μ (b + 272) 8) h1 h6 h7 ⟨by omega, by omega⟩ hrd64
      (fun a h1 h2 => Memory.readable_of_writable (hwf a (by omega) h2)) (fun a h1 h2 => hwf a (by omega) h2)
      rfl (rdN_lt64 μ _)
  obtain ⟨ω2, μ2, r2, b0, b1, b5, b6, bz, bfr, brd, bwr⟩ :=
    Services.Bootstrap.Memzero.memzero (p := p) (P := P) (R := R) x ω1 μ1 (b + 272) 128 2098 46714 (by omega) (by decide) (by omega) a0 a7 a8 a9
      (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_1048]) bs_46714
      (fun a h1 h2 => by rw [wr1]; exact hwf a (by omega) (by omega))
  obtain ⟨ω3, μ3, r3, c0, c1, c6, c7, c8, c9, c5, ec⟩ :=
    it_tr_memo (p := p) (P := P) (R := R) x ω2 μ2 b rd (by rw [b1, a1]) (by rw [b6, a6]) ⟨by omega, by omega⟩ hrd64
  rw [ec] at r3
  have m12 : ∀ a, a < 4294967296 → (a < b ∨ b + 8 ≤ a) → (a < b + 272 ∨ b + 400 ≤ a) → μ2.read a = μ.read a :=
    fun a h0 h1 h2 => by rw [bfr a h0 h2, fr1 a h0 h1]
  have k2 : ∀ (o : Nat) {l : List UInt8}, b + 424 ≤ o → o + 8 < 4294967296 → μ.readN o 8 = l → μ2.readN o 8 = l :=
    fun o l h1 h2 h => by rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => m12 _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)))]; exact h
  obtain ⟨ω4, μ4, r4, d0, d1, d5, d6, d7, q0, q8, qb, fr4, rd4, wr4⟩ :=
    read_any (p := p) (P := P) (R := R) x ω3 μ2 2100 46730 b rd (b + 272) ip rlen 128 c0 c1 c7 c8 c9
      (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_1049]) bs_46730
      ⟨by omega, by omega, hb.2.2⟩ ⟨by omega, hrd.2⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hrl hrl32
      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
      (fun a h1 h2 => by rw [bwr, wr1]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [bwr, wr1]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [bwr, wr1]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [brd, rd1]; exact hra a h1 h2)
      (k2 rd (by omega) (by omega) hR0) (k2 (rd + 8) (by omega) (by omega) hR8)
  obtain ⟨ω5, μ5, r5, e0, e1, e7, e8, e9, e5, e6, ee⟩ :=
    it_tr_memocp (p := p) (P := P) (R := R) x ω4 μ4 b (by rw [d1, c1]) d7 ⟨by omega, by omega⟩
  rw [ee] at r5
  obtain ⟨ω6, μ6, r6, g0, g1, g5, g6, gc, gfr, grd, gwr⟩ :=
    memcpy_big_aligned (p := p) (P := P) (R := R) x ω5 μ4 2102 46751 b (b + 136) (b + 272) 128 e0 e1 e7 e8 e9
      (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_1050]) bs_46751 ⟨by omega, by omega, hb.2.2⟩
      (by decide) (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
      (fun a h1 h2 => by rw [rd4, brd, rd1]; exact Memory.readable_of_writable (hwf a (by omega) (by omega)))
      (fun a h1 h2 => by rw [wr4, bwr, wr1]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr4, bwr, wr1]; exact hwf a (by omega) (by omega))
  refine ⟨ω6, μ6, ?_, by rw [g1], ?_, by rw [g6, e6, d6, c6], ?_, ?_, ?_, ?_, ?_,
    fun a => by rw [grd, rd4, brd, rd1], fun a => by rw [gwr, wr4, bwr, wr1]⟩
  · exact (((((r1.trans r2).trans r3).trans r4).trans r5).trans r6).mono (by omega)
  · rw [g5, e5, d5, c5, b5, a5]
  · rw [rdN_frame fun j hj => gfr _ (by omega) (Or.inl (by omega)) (Or.inr (by omega)),
      rdN_frame fun j hj => fr4 _ (by omega) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)),
      rdN_frame fun j hj => bfr _ (by omega) (Or.inl (by omega))]
    exact s0
  · rw [gc, qb]
    exact PVM.Memory.readN_congr fun j hj => m12 _ (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  · rw [PVM.Memory.readN_congr (μ := μ4) (fun j hj => gfr _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)))]; exact q0
  · rw [PVM.Memory.readN_congr (μ := μ4) (fun j hj => gfr _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)))]; exact q8
  · intro a h0 h1 h2 h3
    rw [gfr a h0 (by omega) (by omega), fr4 a h0 (by omega) h3 (by omega), m12 a h0 (by omega) (by omega)]

/-- 46067: the `u64` reader's return, through entry 1051 (2104), to 46759. -/
theorem u64_ret {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (h0 : ω[0] = UInt64.ofNat 2104) : FreeStepsH p R 46067 ω μ x 46759 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0]

/-- **Stage 4 of the transfer arm, 46751 … 47029**: ℰ₈(g) read by the `u64` reader (g kept in ω₆),
    and the memo copied from b + 136 to out + 8 (128 octets); the reader advanced by 8. -/
theorem tr_s4 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (b out rd ip rlen : Nat) (h1 : ω[1] = UInt64.ofNat b) (h5 : ω[5] = UInt64.ofNat out)
    (h6 : ω[6] = UInt64.ofNat rd)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ip) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 rlen)
    (hrl : 8 ≤ rlen) (hrl32 : rlen < 4294967296)
    (hip : 65536 ≤ ip ∧ ip + 160 < 2147483648) (hra : ∀ a, ip ≤ a → a < ip + 8 → μ.readable a = true)
    (hb : 2147483648 + 112 ≤ b ∧ b + 424 < 4294967296 ∧ b % 8 = 0) (hrd : b + 424 ≤ rd ∧ rd + 16 < 4294967296)
    (hout : b + 424 ≤ out ∧ out + 184 < 4294967296 ∧ out % 8 = 0) (dor : out + 184 ≤ rd ∨ rd + 16 ≤ out)
    (hwf : ∀ a, b - 112 ≤ a → a < b + 424 → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hwo : ∀ a, out ≤ a → a < out + 184 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 46751 ω μ x 47029 ω' μ' x 800 ∧
      ω'[1] = UInt64.ofNat b ∧ ω'[5] = UInt64.ofNat out ∧ ω'[6] = UInt64.ofNat (rdN μ ip 8) ∧
      μ'.readN (out + 8) 128 = μ.readN (b + 136) 128 ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ip + 8) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (rlen - 8) ∧
      (∀ a, a < 4294967296 → (a < b - 112 ∨ b ≤ a) → (a < out + 8 ∨ out + 136 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨ω1, μ1, r1, a0, a1, a7, a5, a6, ea⟩ := it_tr_gas (p := p) (P := P) (R := R) x ω μ b h1
  rw [ea] at r1
  obtain ⟨ω2, μ2, r2, b0, b1, b8, b9, b7, b5, b6, s8, fr2, rd2, wr2⟩ :=
    u64_pre (p := p) (P := P) (R := R) x ω1 μ b a1 ⟨by omega, by omega⟩ (fun a h1 h2 => hwf a (by omega) (by omega))
  have k2 : ∀ (o : Nat) {l : List UInt8}, b ≤ o → o + 8 < 4294967296 → μ.readN o 8 = l → μ2.readN o 8 = l :=
    fun o l h1 h2 h => by rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => fr2 _ (by omega) (Or.inr (by omega)))]; exact h
  obtain ⟨ω3, μ3, r3, c0, c1, -, -, -, c5, c6, -, c7, q0, q8, qb, fr3, rd3, wr3⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω2 μ2 2068 46059 (b - 16) rd (b - 16) ip rlen 8 b0 b1
      (by rw [b7, a7, h6]) b8 b9
      (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, Services.Bootstrap.Code.jte_1033])
      Services.Bootstrap.Code.bs_46059
      ⟨by omega, by omega⟩ ⟨by omega, hrd.2⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide) hrl hrl32
      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
      (fun a h1 h2 => by rw [wr2]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr2]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [wr2]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [rd2]; exact hra a h1 h2)
      (k2 rd (by omega) (by omega) hR0) (k2 (rd + 8) (by omega) (by omega) hR8)
  have mv : rdN μ3 (b - 16) 8 = rdN μ ip 8 := by
    unfold rdN; rw [qb, PVM.Memory.readN_congr (μ := μ) (fun j hj => fr2 _ (by omega) (Or.inl (by omega)))]
  have m8 : rdN μ3 (b - 16 + 8) 8 = 2104 := by
    rw [rdN_frame fun j hj => fr3 _ (by omega) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inr (by omega)),
      show b - 16 + 8 = b - 8 by omega, s8, a0]
    simp
  obtain ⟨ω4, μ4, r4, d8, d0, d1, d7, d5, d6, ed⟩ :=
    u64_post (p := p) (P := P) (R := R) x ω3 μ3 (b - 16) (rdN μ ip 8) 2104 (by rw [c1, b1]) mv m8
      ⟨by omega, by omega⟩ (fun a h1 h2 => by rw [rd3, rd2]; exact Memory.readable_of_writable (hwf a (by omega) (by omega)))
  rw [ed] at r4
  have rj := u64_ret (p := p) (P := P) (R := R) x ω4 μ3 d0
  have e1' : ω4[1] = UInt64.ofNat b := by rw [d1]; congr 1; omega
  obtain ⟨ω5, μ5, r5, e0, e1, e5, e6, e7, e8, e9, ee⟩ :=
    it_tr_cp (p := p) (P := P) (R := R) x ω4 μ3 b out (rdN μ ip 8) e1' (by rw [d5, c5, b5, a5, h5])
      (by rw [d7, c7]) d8 (by omega) (by omega) (rdN_lt64 μ _)
  rw [ee] at r5
  obtain ⟨ω6, μ6, r6, g0, g1, g5, g6, gc, gfr, grd, gwr⟩ :=
    memcpy_big_aligned (p := p) (P := P) (R := R) x ω5 μ3 2112 47029 b (out + 8) (b + 136) 128 e0 e1 e7 e8 e9
      (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_1055]) bs_47029 ⟨by omega, by omega, hb.2.2⟩
      (by decide) (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
      (fun a h1 h2 => by rw [rd3, rd2]; exact Memory.readable_of_writable (hwf a (by omega) (by omega)))
      (fun a h1 h2 => by rw [wr3, wr2]; exact hwo a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr3, wr2]; exact hwf a (by omega) (by omega))
  refine ⟨ω6, μ6, (((((r1.trans r2).trans r3).trans r4).trans rj).trans r5 |>.trans r6).mono (by omega),
    by rw [g1], by rw [g5, e5], by rw [g6, e6], ?_, ?_, ?_, ?_,
    fun a => by rw [grd, rd3, rd2], fun a => by rw [gwr, wr3, wr2]⟩
  · rw [gc]
    exact PVM.Memory.readN_congr fun j hj => by
      rw [fr3 _ (by omega) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inr (by omega)), fr2 _ (by omega) (Or.inr (by omega))]
  · rw [PVM.Memory.readN_congr (μ := μ3) (fun j hj => gfr _ (by omega) (by omega) (Or.inr (by omega)))]; exact q0
  · rw [PVM.Memory.readN_congr (μ := μ3) (fun j hj => gfr _ (by omega) (by omega) (Or.inr (by omega)))]; exact q8
  · intro a h0 hs ho hr
    rw [gfr a h0 ho (by omega), fr3 a h0 (by omega) hr (by omega), fr2 a h0 (by omega)]


/-- A sign-extended `u32` word cut back to 32 bits is the word. -/
theorem sxw4_cut (v : Nat) (hv : v < 4294967296) : sxw 4 v % 18446744073709551616 % 4294967296 = v := by
  rw [Nat.mod_mod_of_dvd _ (by decide)]
  have := sxw_mod 4 v (Or.inr rfl) (by simpa using hv)
  simp only [Nat.reducePow] at this
  rw [this, Nat.mod_eq_of_lt hv]

/-- **The transfer arm, 45126 … 47072**: one deferred transfer ℰ(1, ℰ₄(s), ℰ₄(d), ℰ₈(a), m, ℰ₈(g))
    (GP v0.8.0 §12 𝕏, Appendix C) read from the reader's 153 octets at ip into the slot out: −1 at
    + 0, m at + 8, a at + 136, g at + 144, s at + 152 and d at + 156; ω₀, ω₁, ω₅, ω₆ kept, the
    reader advanced by 153, at the return's `jumpInd`. -/
theorem tr_call {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp out rd ip rlen : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat out)
    (h8 : ω[8] = UInt64.ofNat rd)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ip) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 rlen)
    (hrl : 153 ≤ rlen) (hrl32 : rlen < 4294967296) (htag : rdN μ ip 1 = 1)
    (hip : 65536 ≤ ip ∧ ip + 305 < 2147483648) (hra : ∀ a, ip ≤ a → a < ip + 153 → μ.readable a = true)
    (hsp : 2147483648 + 536 ≤ sp ∧ sp < 4294967296 ∧ sp % 8 = 0)
    (hout : sp ≤ out ∧ out + 184 < 4294967296 ∧ out % 8 = 0)
    (hrd : sp ≤ rd ∧ rd + 16 < 4294967296) (dor : out + 184 ≤ rd ∨ rd + 16 ≤ out)
    (hwf : ∀ a, sp - 536 ≤ a → a < sp → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hwo : ∀ a, out ≤ a → a < out + 184 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 45126 ω μ x 47072 ω' μ' x 3820 ∧
      ω'[0] = ω[0] ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      rdN μ' out 8 = 18446744073709551615 ∧ μ'.readN (out + 8) 128 = μ.readN (ip + 17) 128 ∧
      rdN μ' (out + 136) 8 = rdN μ (ip + 9) 8 ∧ rdN μ' (out + 144) 8 = rdN μ (ip + 145) 8 ∧
      rdN μ' (out + 152) 4 = rdN μ (ip + 1) 4 ∧ rdN μ' (out + 156) 4 = rdN μ (ip + 5) 4 ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ip + 153) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (rlen - 153) ∧
      (∀ a, a < 4294967296 → (a < sp - 536 ∨ sp ≤ a) → (a < out ∨ out + 160 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨ω1, μ1, r1, a1, a5, a6, a7, s24, s272, s8, s16, s24', R0, R8, fr1, rd1, wr1⟩ :=
    tr_s1 (p := p) (P := P) (R := R) x ω μ sp out rd ip rlen h1 h7 h8 hR0 hR8 (by omega) hrl32 htag
      ⟨hip.1, by omega⟩ (fun a h1 h2 => hra a h1 (by omega)) ⟨by omega, hsp.2.1, hsp.2.2⟩ ⟨hout.1, by omega⟩ hrd
      (fun a h1 h2 => hwf a (by omega) h2) hwr
  obtain ⟨ω2, μ2, r2, b1, b5, b6, b7, w16, w8, w272, R0, R8, fr2, rd2, wr2⟩ :=
    tr_s2 (p := p) (P := P) (R := R) x ω1 μ1 (sp - 424) out rd (ip + 5) (rlen - 5) a1 a5 a6 a7 s24 (by omega)
      R0 R8 (by omega) (by omega) ⟨by omega, by omega⟩
      (fun a h1 h2 => by rw [rd1]; exact hra a (by omega) (by omega)) ⟨by omega, by omega, by omega⟩
      ⟨by omega, by omega⟩ (fun a h1 h2 => by rw [wr1]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr1]; exact hwr a h1 h2)
  obtain ⟨ω3, μ3, r3, c1, c5, c6, wb, wm, R0, R8, fr3, rd3, wr3⟩ :=
    tr_s3 (p := p) (P := P) (R := R) x ω2 μ2 (sp - 424) rd (ip + 5 + 12) (rlen - 5 - 12) b1 b6 b7
      R0 R8 (by omega) (by omega) ⟨by omega, by omega⟩
      (fun a h1 h2 => by rw [rd2, rd1]; exact hra a (by omega) (by omega)) ⟨by omega, by omega, by omega⟩
      ⟨by omega, by omega⟩ (fun a h1 h2 => by rw [wr2, wr1]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr2, wr1]; exact hwr a h1 h2)
  obtain ⟨ω4, μ4, r4, d1, d5, d6, mo, R0, R8, fr4, rd4, wr4⟩ :=
    tr_s4 (p := p) (P := P) (R := R) x ω3 μ3 (sp - 424) out rd (ip + 5 + 12 + 128) (rlen - 5 - 12 - 128) c1
      (c5.trans b5) c6 R0 R8 (by omega) (by omega) ⟨by omega, by omega⟩
      (fun a h1 h2 => by rw [rd3, rd2, rd1]; exact hra a (by omega) (by omega)) ⟨by omega, by omega, by omega⟩
      ⟨by omega, by omega⟩ ⟨by omega, hout.2.1, hout.2.2⟩ dor
      (fun a h1 h2 => by rw [wr3, wr2, wr1]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr3, wr2, wr1]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [wr3, wr2, wr1]; exact hwo a h1 h2)
  obtain ⟨ω5, μ5, r5, e0, e1, e5, e6, f0, f136, f144, f152, f156, fr5, rd5, wr5⟩ :=
    it_tr_fill (p := p) (P := P) (R := R) x ω4 μ4 (sp - 424) out _ _ _ _ _ _ _ d1 d5 d6 rfl rfl rfl rfl rfl rfl
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (rdN_lt64 _ _) (rdN_lt64 _ _) (rdN_lt64 _ _)
      (rdN_lt64 _ _) (rdN_lt64 _ _) (rdN_lt64 _ _) (rdN_lt64 _ _)
      (fun a h1 h2 => by
        rw [rd4, rd3, rd2, rd1]; exact Memory.readable_of_writable (hwf a (by omega) (by omega)))
      (fun a h1 h2 => by rw [wr4, wr3, wr2, wr1]; exact hwo a h1 h2)
  -- the frame, from the input, through each stage
  have k : ∀ a, a < 4294967296 → (a < sp - 536 ∨ sp ≤ a) → (a < out ∨ out + 160 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
      μ5.read a = μ.read a := fun a h0 hs ho hr => by
    rw [fr5 a h0 (by omega) (by omega), fr4 a h0 (by omega) (by omega) hr, fr3 a h0 (by omega) (by omega) hr,
      fr2 a h0 (by omega) (by omega) hr, fr1 a h0 (by omega) hr]
  -- the frame words saved by stage 1, unchanged until the fill
  have q : ∀ o, sp - 424 + 400 ≤ o → o + 8 ≤ sp → rdN μ4 o 8 = rdN μ1 o 8 := fun o h1 h2 => by
    rw [rdN_frame fun j hj => fr4 _ (by omega) (by omega) (by omega) (by omega),
      rdN_frame fun j hj => fr3 _ (by omega) (by omega) (Or.inr (by omega)) (by omega),
      rdN_frame fun j hj => fr2 _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (by omega)]
  -- the input's octets at ip, unchanged until stage k
  have i1 : ∀ o n, ip ≤ o → o + n ≤ ip + 153 → rdN μ1 o n = rdN μ o n := fun o n h1 h2 =>
    rdN_frame fun j hj => fr1 _ (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  have i2 : ∀ o n, ip ≤ o → o + n ≤ ip + 153 → rdN μ2 o n = rdN μ o n := fun o n h1 h2 => by
    rw [rdN_frame fun j hj => fr2 _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))]
    exact i1 o n h1 h2
  have i3 : ∀ o n, ip ≤ o → o + n ≤ ip + 153 → rdN μ3 o n = rdN μ o n := fun o n h1 h2 => by
    rw [rdN_frame fun j hj => fr3 _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))]
    exact i2 o n h1 h2
  -- the words stages 2 and 3 saved in the frame, unchanged until the fill
  have v0 : rdN μ4 (sp - 424) 8 = rdN μ (ip + 9) 8 := by
    rw [rdN_frame fun j hj => fr4 _ (by omega) (Or.inr (by omega)) (by omega) (by omega), wb, w272]
    exact i1 _ _ (by omega) (by omega)
  have v8 : rdN μ4 (sp - 424 + 8) 8 = sxw 4 (rdN μ (ip + 5) 4) % 18446744073709551616 := by
    rw [rdN_frame fun j hj => fr4 _ (by omega) (Or.inr (by omega)) (by omega) (by omega),
      rdN_frame fun j hj => fr3 _ (by omega) (Or.inr (by omega)) (Or.inl (by omega)) (by omega), w8,
      i1 _ _ (by omega) (by omega)]
  have v16 : rdN μ4 (sp - 424 + 16) 8 = sxw 4 (rdN μ (ip + 1) 4) % 18446744073709551616 := by
    rw [rdN_frame fun j hj => fr4 _ (by omega) (Or.inr (by omega)) (by omega) (by omega),
      rdN_frame fun j hj => fr3 _ (by omega) (Or.inr (by omega)) (Or.inl (by omega)) (by omega), w16, s272]
  refine ⟨ω5, μ5, ((((r1.trans r2).trans r3).trans r4).trans r5).mono (by omega), ?_,
    by rw [e1, show sp - 424 + 424 = sp by omega], ?_, ?_, f0, ?_, by rw [f136, v0], by rw [f144, i3 _ _ (by omega) (by omega)], ?_, ?_, ?_, ?_, k,
    fun a => by rw [rd5, rd4, rd3, rd2, rd1], fun a => by rw [wr5, wr4, wr3, wr2, wr1]⟩
  · rw [e0, q _ (by omega) (by omega), show sp - 424 + 416 = sp - 8 by omega, s8]; exact UInt64.ofNat_toNat
  · rw [e5, q _ (by omega) (by omega), show sp - 424 + 408 = sp - 16 by omega, s16]; exact UInt64.ofNat_toNat
  · rw [e6, q _ (by omega) (by omega), show sp - 424 + 400 = sp - 24 by omega, s24']; exact UInt64.ofNat_toNat
  · rw [PVM.Memory.readN_congr (μ := μ4) (fun j hj => fr5 _ (by omega) (Or.inr (by omega)) (Or.inl (by omega))),
      mo, wm]
    exact PVM.Memory.readN_congr fun j hj => by
      rw [fr2 _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)),
        fr1 _ (by omega) (Or.inl (by omega)) (Or.inl (by omega))]
  · rw [f152, v16]; exact sxw4_cut _ (rdN_lt μ _ 4)
  · rw [f156, v8]; exact sxw4_cut _ (rdN_lt μ _ 4)
  · rw [PVM.Memory.readN_congr (μ := μ4) (fun j hj => fr5 _ (by omega) (by omega) (by omega)), R0,
      show ip + 153 = ip + 5 + 12 + 128 + 8 by omega]
  · rw [PVM.Memory.readN_congr (μ := μ4) (fun j hj => fr5 _ (by omega) (by omega) (by omega)), R8,
      show rlen - 153 = rlen - 5 - 12 - 128 - 8 by omega]

end Services.Bootstrap.Acc
