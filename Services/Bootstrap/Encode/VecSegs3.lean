import Services.Bootstrap.Encode.EncMD

/-!
# `Instruction::encode_to`: `Provide`'s pieces up to its preimage

`Provide`'s arm (18990, see `VecSegs2.seg_tag5` for its tag) keeps S in ω₅ and the writer v in ω₆: it
appends the service's 4 octets (S + 48, 19013), then reads the preimage's tag octet at S + 8; for
`Hash` (0) it appends 0 and the 32 octets of the hash at S + 9 (20169 … 20197) and leaves through the
shared end at 20204. (For `Inline` (1) it appends 1 and calls a helper at 3716 for the bytes; no code
facts for 3716 … 3790 are in `Code`, `CodeX`, `CodeA`, `CodeF` or `CodeR`.)
-/

namespace Services.Bootstrap.Encode.Enc

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.Encode.Writer

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {X : Type} {R : HostRel X}

/-- 19013 … 19027: the 4 octets at S + 48 (ω₅ = S) to sp + 24 and the call for them (return 808 →
    19034), the writer from ω₆. -/
theorem seg_19013 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hS : S + 232 ≤ 4294967296)
    (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat S) (h6 : ω[6] = UInt64.ofNat v)
    (hr : ∀ a, S + 48 ≤ a → a < S + 48 + 4 → μ.readable a = true)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 24 + 4 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 19013 ω μ x 58508 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 808 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 4 ∧
      μ'.readN (sp + 24) 4 = μ.readN (S + 48) 4 ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 24 + 4 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hsx : Num.encodeLE 4 (sxw 4 (rdN μ (S + 48) 4)) = μ.readN (S + 48) 4 := by
    rw [encodeLE_sxw 4 _ (Or.inr rfl) (rdN_lt μ _ 4), encodeLE_rdN]
  have hm : ∀ w : Nat, w % 18446744073709551616 % 4294967296 = w % 256 ^ 4 := fun w => by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hsp, hS, hr, hw, ↓rdN_fold, ↓loadI_fold, rdN_mod64]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, h6, Nat.mod_eq_of_lt hv]
    post_simp
    all_goals try assumption
    all_goals try (rw [← hsx, hm, encodeLE_mod])

/-- 19034 … 19037, 20169 … 20183 (`Provide { preimage: Hash(_) }`): the tag octet at S + 8 is 0; ω₅ =
    S + 9, the octet 0 at sp + 24 and the call for it (return 906 → 20190), the writer from ω₆. -/
theorem seg_19034_hash {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hS : S + 232 ≤ 4294967296)
    (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat S) (h6 : ω[6] = UInt64.ofNat v)
    (s8 : rdN μ (S + 8) 1 = 0)
    (hr : ∀ a, S + 8 ≤ a → a < S + 9 → μ.readable a = true)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 25 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 19034 ω μ x 58508 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 906 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat (S + 9) ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (sp + 24) 1 = [UInt8.ofNat 0] ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 25 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hsp, hS, hr, hw, s8, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, h6, Nat.mod_eq_of_lt hv]
    post_simp
    all_goals try assumption

/-- 20190 … 20197: the call appending the 32 octets at ω₅ (return 908 → 20204), the writer from ω₆. -/
theorem seg_20190 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (v s : Nat) (hv : v < 18446744073709551616) (hs : s < 18446744073709551616)
    (h5 : ω[5] = UInt64.ofNat s) (h6 : ω[6] = UInt64.ofNat v) :
    ∃ ω', FreeStepsH p R 20190 ω μ x 58508 ω' μ x 6 ∧
      ω'[0] = UInt64.ofNat 908 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat s ∧ ω'[9] = UInt64.ofNat 32 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h5, h6]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h5, h6, Nat.mod_eq_of_lt hv,
      Nat.mod_eq_of_lt hs]
    all_goals try (congr 1; omega)

end Services.Bootstrap.Encode.Enc
