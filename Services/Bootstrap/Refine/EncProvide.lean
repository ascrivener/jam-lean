import Services.Bootstrap.Refine.EncRSA
import Services.Bootstrap.Decode.LookupProvideElem

/-!
# `Provide` with an inline preimage (17) in refine's output encoder, with growth (`EncOkMH`)

The arm at 18990 (dispatch index 17, `Instruction::encode_to`) for `Provide { service, preimage: Inline(bytes) }`: the
tag octet 17, the service's four octets (S + 48), the octet 1 (the octet at S + 8 is 1; 0, by hash, is 20169,
`GrowH.provide_hashH`), then `<[u8] as Encode>::encode_to` (3716, its own frame at sp − 40): the length prefix ℰ(n) (n at
S + 32, a 32-bit word: n ≥ 2^32 traps at 3779) and the n octets from q (S + 24) on the heap; it returns to 19074, the
arm's tail. `provide_inlineH` composes them (`EncOkMH 232`). GP v0.8.0
Appendix C, B.7.
-/

namespace Services.Bootstrap.Refine.EncProvide

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX
  Services.Bootstrap.CodeA Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Encode.WriterGrow Services.Bootstrap.Encode.Enc
  Services.Bootstrap.Encode.EncMD Services.Bootstrap.Encode.GrowH

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

section
variable {X : Type} {R : HostRel X}

/-- 18990 … 19006 (`Provide`, tag 17): the octet 17 at sp + 24 and the call for it (return 806 → 19013), with S
    (ω₁₁) in ω₅ and the writer v (ω₁₀) in ω₆. -/
theorem seg_18990 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616) (hS : S < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h10 : ω[10] = UInt64.ofNat v) (h11 : ω[11] = UInt64.ofNat S)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 25 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 18990 ω μ x 58508 ω' μ' x 7 ∧
      ω'[0] = UInt64.ofNat 806 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat S ∧ ω'[6] = UInt64.ofNat v ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (sp + 24) 1 = [UInt8.ofNat 17] ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 25 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h10, h11, hsp, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h10, h11, Nat.mod_eq_of_lt hv,
      Nat.mod_eq_of_lt hS]
    post_simp
    all_goals try assumption

/-- 19013 … 19027 (`Provide`, the service): the `u32` at S + 48 (ω₅ = S) to sp + 24 and the call appending its 4
    octets (return 808 → 19034), the writer from ω₆. -/
theorem seg_19013 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hS : S + 232 ≤ 4294967296) (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat S) (h6 : ω[6] = UInt64.ofNat v)
    (hr : ∀ a, S + 48 ≤ a → a < S + 48 + 4 → μ.readable a = true)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 28 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 19013 ω μ x 58508 ω' μ' x 6 ∧
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
  · pvm_go [h1, h5, h6, hsp, hS, hr, hw, ↓rdN_fold, ↓loadI_fold, rdN_mod64, rdN_writeN_disjoint]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, h6, Nat.mod_eq_of_lt hv]
    post_simp
    all_goals try assumption
    all_goals try (rw [← hsx, hm, encodeLE_mod])

/-- 19034 … 19053 (`Provide`, inline): the octet at S + 8 is 1: the octet 1 at sp + 24 and the call for it (return
    810 → 19060), the writer from ω₆. -/
theorem seg_19034 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hS : S + 16 ≤ 4294967296) (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat S) (h6 : ω[6] = UInt64.ofNat v)
    (s8 : μ.readN (S + 8) 1 = [1])
    (hrS : ∀ a, S + 8 ≤ a → a < S + 9 → μ.readable a = true)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 25 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 19034 ω μ x 58508 ω' μ' x 7 ∧
      ω'[0] = UInt64.ofNat 810 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (sp + 24) 1 = [UInt8.ofNat 1] ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 25 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rb : rdN μ (S + 8) 1 = 1 := by show Num.decodeLE _ = _; rw [s8]; rfl
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hsp, hS, hw, hrS, rb, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, h6, Nat.mod_eq_of_lt hv]
    post_simp
    all_goals try assumption

/-- 19060 … 19068 (`Provide`, inline): q (S + 24) in ω₇, n (S + 32) in ω₈, the writer in ω₉; the call of the `[u8]`
    encoder 3716 (return 812 → 19074). -/
theorem seg_19060 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (S v q n : Nat) (hS : S + 40 ≤ 4294967296) (hv : v < 18446744073709551616) (hq : q < 18446744073709551616)
    (hn : n < 18446744073709551616)
    (h5 : ω[5] = UInt64.ofNat S) (h6 : ω[6] = UInt64.ofNat v)
    (s24 : μ.readN (S + 24) 8 = Num.encodeLE 8 q) (s32 : μ.readN (S + 32) 8 = Num.encodeLE 8 n)
    (hrS : ∀ a, S + 24 ≤ a → a < S + 40 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 19060 ω μ x 3716 ω' μ x 4 ∧
      ω'[0] = UInt64.ofNat 812 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat q ∧ ω'[8] = UInt64.ofNat n ∧ ω'[9] = UInt64.ofNat v := by
  have rq := rd8 hq s24
  have rn := rd8 hn s32
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h5, h6, hS, hrS, rq, rn, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h5, h6, Nat.mod_eq_of_lt hv,
      Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hn]

/-- 3716 … 3725 (the `[u8]` encoder's frame): sp' = sp − 40, ω₀, ω₅, ω₆ saved at sp' + 32, sp' + 24, sp' + 16. -/
theorem seg_3716 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp r0 r5 r6 : Nat) (hsp : 40 ≤ sp ∧ sp ≤ 4294967296) (hr0 : r0 < 18446744073709551616)
    (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat r5)
    (h6 : ω[6] = UInt64.ofNat r6)
    (hw : ∀ a, sp - 24 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 3716 ω μ x 3728 ω' μ' x 4 ∧
      ω'[0] = ω[0] ∧ ω'[1] = UInt64.ofNat (sp - 40) ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = ω[7] ∧
      ω'[8] = ω[8] ∧ ω'[9] = ω[9] ∧
      μ'.readN (sp - 8) 8 = Num.encodeLE 8 r0 ∧ μ'.readN (sp - 16) 8 = Num.encodeLE 8 r5 ∧
      μ'.readN (sp - 24) 8 = Num.encodeLE 8 r6 ∧
      (∀ a, a < 4294967296 → (a < sp - 24 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have e40 : (sp + 18446744073709551576) % 18446744073709551616 = sp - 40 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, hsp, hw, e40]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h0, h1, h5, h6, e40,
      Nat.mod_eq_of_lt hr0, Nat.mod_eq_of_lt hr5, Nat.mod_eq_of_lt hr6]
    all_goals try (simp only [show sp - 40 + 32 = sp - 8 by omega, show sp - 40 + 24 = sp - 16 by omega,
      show sp - 40 + 16 = sp - 24 by omega])
    post_simp
    all_goals try assumption

/-- 3728 … 3748 (the `[u8]` encoder, n < 2^32, frame at F): n as a 32-bit word at F + 12 and q at F; the call of the
    length prefix with ω₇ = F + 12, the writer in ω₈ and ω₆, n in ω₅ (return 94 → 3753). -/
theorem seg_3728 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (F v q n : Nat) (hF : F + 16 ≤ 4294967296) (hv : v < 18446744073709551616)
    (hq : q < 18446744073709551616) (hn : n < 4294967296)
    (h1 : ω[1] = UInt64.ofNat F) (h7 : ω[7] = UInt64.ofNat q) (h8 : ω[8] = UInt64.ofNat n)
    (h9 : ω[9] = UInt64.ofNat v)
    (hw : ∀ a, F ≤ a → a < F + 16 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 3728 ω μ x 30977 ω' μ' x 9 ∧
      ω'[0] = UInt64.ofNat 94 ∧ ω'[1] = UInt64.ofNat F ∧ ω'[5] = UInt64.ofNat n ∧
      ω'[6] = UInt64.ofNat v ∧ ω'[7] = UInt64.ofNat (F + 12) ∧ ω'[8] = UInt64.ofNat v ∧
      rdN μ' (F + 12) 4 = n ∧ μ'.readN F 8 = Num.encodeLE 8 q ∧
      (∀ a, a < 4294967296 → (a < F ∨ F + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hsh : n >>> 32 = 0 := by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt hn
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, h8, h9, hF, hw, hsh]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h7, h8, h9,
      Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt (show n < 18446744073709551616 by omega)]
    post_simp
    all_goals try assumption
    all_goals try (show Num.decodeLE _ = _
                   rw [Memory.readN_writeN_disjoint _ _ _ _ _ (Or.inl (by simp)) (by simp [two32]; omega)
                     (by simp [two32]; omega),
                     Memory.readN_writeN_same _ _ _ _ (by simp) (by simp [two32]), Num.decodeLE_encodeLE]
                   exact Nat.mod_eq_of_lt (by omega))

/-- 3753 … 3759 (the `[u8]` encoder, after the prefix): the writer (ω₆) in ω₇, q (from F) in ω₈, n (ω₅) in ω₉; the
    call appending the n octets (return 96 → 3765). -/
theorem seg_3753 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (F v q n : Nat) (hF : F + 8 ≤ 4294967296) (hv : v < 18446744073709551616) (hq : q < 18446744073709551616)
    (hn : n < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat F) (h5 : ω[5] = UInt64.ofNat n) (h6 : ω[6] = UInt64.ofNat v)
    (s0 : μ.readN F 8 = Num.encodeLE 8 q) (hr : ∀ a, F ≤ a → a < F + 8 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 3753 ω μ x 58508 ω' μ x 4 ∧
      ω'[0] = UInt64.ofNat 96 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat q ∧ ω'[9] = UInt64.ofNat n := by
  have rq := rd8 hq s0
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, h6, hF, hr, rq, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, h6, Nat.mod_eq_of_lt hv,
      Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hn]

/-- 3765 … 3777, then 19074 … 19086: the `[u8]` encoder's frame closed (return 812 → 19074), then `encode_to`'s own
    frame at sp: ω₀, ω₅, ω₆ from sp + 48, sp + 40, sp + 32, ω₁ = sp + 56, and the return to `ret` (→ t). -/
theorem seg_3765 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp a5 a6 ret t r5 r6 : Nat) (hsp : 40 ≤ sp ∧ sp + 56 < 4294967296) (ha5 : a5 < 18446744073709551616)
    (ha6 : a6 < 18446744073709551616) (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat (sp - 40))
    (i0 : μ.readN (sp - 8) 8 = Num.encodeLE 8 812) (i5 : μ.readN (sp - 16) 8 = Num.encodeLE 8 a5)
    (i6 : μ.readN (sp - 24) 8 = Num.encodeLE 8 a6)
    (s0 : μ.readN (sp + 48) 8 = Num.encodeLE 8 ret)
    (s5 : μ.readN (sp + 40) 8 = Num.encodeLE 8 r5) (s6 : μ.readN (sp + 32) 8 = Num.encodeLE 8 r6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hr : ∀ a, sp - 24 ≤ a → a < sp → μ.readable a = true)
    (hr' : ∀ a, sp + 32 ≤ a → a < sp + 56 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 3765 ω μ x t ω' μ x 10 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (sp + 56) ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 := by
  have j0 := rd8 (by decide) i0
  have j5 := rd8 ha5 i5
  have j6 := rd8 ha6 i6
  have r0 := rd8 (by omega) s0
  have r5' := rd8 hr5 s5
  have r6' := rd8 hr6 s6
  have e32 : sp - 40 + 32 = sp - 8 := by omega
  have e24 : sp - 40 + 24 = sp - 16 := by omega
  have e16 : sp - 40 + 16 = sp - 24 := by omega
  have e40 : sp - 40 + 40 = sp := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hsp, hr, hr', j0, j5, j6, r0, r5', r6', e32, e24, e16, e40, hret, hjt, hbt, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, Nat.mod_eq_of_lt hr5,
      Nat.mod_eq_of_lt hr6, Nat.mod_eq_of_lt (show ret < 18446744073709551616 by omega)]
    all_goals try (congr 1; omega)

end

/-- `Provide { service, preimage: Inline(bytes) }`'s slot, the octets at q (`Decode.ProvideInlineRep` with its q
    given): tag word 2^63 + 16, the octet 1 at 8, capacity n at 16, q at 24, length n at 32, the service s at 48. -/
def ProvideInlineRepAt (s : List UInt8) (n q : Nat) (bytes : List UInt8) (bs : List UInt8) (μ : Memory) : Prop :=
  bs.take 8 = Num.encodeLE 8 9223372036854775824 ∧ (bs.drop 8).take 1 = [1] ∧ (bs.drop 48).take 4 = s ∧
    (bs.drop 16).take 8 = Num.encodeLE 8 n ∧ (bs.drop 24).take 8 = Num.encodeLE 8 q ∧
    (bs.drop 32).take 8 = Num.encodeLE 8 n ∧ μ.readN q n = bytes

/-- The decode side's `ProvideInlineRep` is `ProvideInlineRepAt` for some q. -/
theorem provideInlineRep_iff (s : List UInt8) (n : Nat) (bytes bs : List UInt8) (μ : Memory) :
    Decode.LookupProvideElem.ProvideInlineRep s n bytes bs μ ↔ ∃ q, ProvideInlineRepAt s n q bytes bs μ := by
  constructor
  · rintro ⟨h0, h1, h2, q, h3, h4, h5, h6⟩; exact ⟨q, h0, h1, h2, h3, h4, h5, h6⟩
  · rintro ⟨q, h0, h1, h2, h3, h4, h5, h6⟩; exact ⟨h0, h1, h2, q, h3, h4, h5, h6⟩

theorem BufH.cast {env : RefineHost.Env} {pb S0 S1 B v len ptr0 : Nat} {s0 : State} {μ0 : Memory}
    {pre pre' : List UInt8} {cap ptr : Nat} {s : State} {μ : Memory}
    (W : BufH env pb S0 S1 B v len ptr0 s0 μ0 pre cap ptr s μ) (h : pre = pre') :
    BufH env pb S0 S1 B v len ptr0 s0 μ0 pre' cap ptr s μ := h ▸ W

/-- **`Provide` with an inline preimage (index 17), with growth**: `ProvideInlineRepAt s n q bytes` (n < 2^32) encodes
    to 17 :: s ++ 1 :: ℰ(n) ++ bytes, the heap octets the stretch (q, n) when n > 0. The `[u8]` encoder (3716) runs in its
    own frame at F − 96, so the depth is 232. -/
theorem provide_inlineH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (s4 : List UInt8) (n q : Nat) (bytes : List UInt8) (hs4 : s4.length = 4) (hby : bytes.length = n)
    (hn : n < 4294967296) (hq64 : q < 18446744073709551616) :
    EncOkMH env K pb p P 232 (17 :: (s4 ++ 1 :: (Blob.encodeNat n ++ bytes))) (ProvideInlineRepAt s4 n q bytes)
      (SrcAtP q n) := by
  intro x ω μ s S0 S1 F S v cap ptr len ret t h0 h1 h7 h8 rep L hlen tab hrt hsrc
  obtain ⟨r0, r8, r48, r16, r24, r32, rby⟩ := rep
  have hD8 : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 17) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact r0
  have c8 : μ.readN (S + 8) 1 = [1] := by rw [← slot_take μ S 8 1 (by decide)]; exact r8
  have c48 : μ.readN (S + 48) 4 = s4 := by rw [← slot_take μ S 48 4 (by decide)]; exact r48
  have c24 : μ.readN (S + 24) 8 = Num.encodeLE 8 q := by rw [← slot_take μ S 24 8 (by decide)]; exact r24
  have c32 : μ.readN (S + 32) 8 = Num.encodeLE 8 n := by rw [← slot_take μ S 32 8 (by decide)]; exact r32
  have Fr := L.fr
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := L.nums
  have hS := L.hS; have hS' := L.hS'
  have hE := encodeNat_pos n
  have hFv := Fr.hFv; have hS1 := Fr.hS1; have hFS0 := Fr.hFS0; have hF2 := Fr.hF2
  have hN : (17 :: (s4 ++ 1 :: (Blob.encodeNat n ++ bytes)) : List UInt8).length =
      6 + (Blob.encodeNat n).length + n := by simp [hs4, hby]; omega
  rw [hN] at hlen
  have gas : ∀ k, k ≤ 2000 * 6 + 4000 + growGas * (6 + (Blob.encodeNat n).length + n) →
      k ≤ encGas (17 :: (s4 ++ 1 :: (Blob.encodeNat n ++ bytes))) := fun k hk => by
    unfold encGas growGas at *; rw [hN]; omega
  obtain ⟨ω1, μ1, run1, st1, a10, a11⟩ := startDH (p := p) (P := P) K x ω μ L (by decide) 17
    ⟨by decide, by decide⟩ h0 h1 h7 h8 hD8 tab hrt
  rw [show arm 17 = 18990 from rfl] at run1
  -- the tag
  obtain ⟨cap1, ptr1, s1, W1⟩ := st1.buf
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bt, bfr, brd, bwr⟩ := seg_18990 (p := p) (P := P)
    (R := refineContractK K env) x ω1 μ1 (F - 56) v S (by omega) (by omega) (by omega) st1.h1 a10 a11
    (fun a h1 h2 => W1.H.st a (by omega) (by omega))
  have st2 := st1.scratch Fr b1 (fun a h0 h1 => bfr a h0 (by omega)) brd bwr
  rcases scratchDH (p := p) (P := P) env K hK1 hK x ω2 μ2 Fr (by decide) st2 [UInt8.ofNat 17] 1 806 19013 rfl
      (by decide) b0 b7 b8 b9 ⟨by decide, by decide, by decide⟩ jte_402 bs_19013 (by simp; omega) bt with
    ⟨ω3, μ3, run3, st3, c5, c6, -⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans run2) hx).mono (gas _ (by unfold stepGas growGas; omega)))
  -- the service
  obtain ⟨cap3, ptr3, s3, W3⟩ := st3.buf
  obtain ⟨ω4, μ4, run4, d0, d1, d5, d6, d7, d8, d9, dt, dfr, drd, dwr⟩ := seg_19013 (p := p) (P := P)
    (R := refineContractK K env) x ω3 μ3 (F - 56) v S (by omega) (by omega) (by omega) st3.h1
    (by rw [c5, b5]) (by rw [c6, b6])
    (fun a h1 h2 => W3.safe_readable (by omega) (W3.safe L.slot) a (by omega) (by omega))
    (fun a h1 h2 => W3.H.st a (by omega) (by omega))
  have st4 := st3.scratch Fr d1 (fun a h0 h1 => dfr a h0 (by omega)) drd dwr
  rcases scratchDH (p := p) (P := P) env K hK1 hK x ω4 μ4 Fr (by decide) st4 s4 4 808 19034 hs4
      (by decide) d0 d7 d8 d9 ⟨by decide, by decide, by decide⟩ jte_403 bs_19034 (by simp; omega)
      (by rw [dt, st3.slot L.slot (by decide), c48]) with
    ⟨ω5, μ5, run5, st5, e5, e6, -⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans run4))) hx).mono
      (gas _ (by unfold stepGas growGas; omega)))
  -- the octet 1 (inline)
  obtain ⟨cap5, ptr5, s5, W5⟩ := st5.buf
  obtain ⟨ω6, μ6, run6, f0, f1, f5, f6, f7, f8, f9, ft, ffr, frd, fwr⟩ := seg_19034 (p := p) (P := P)
    (R := refineContractK K env) x ω5 μ5 (F - 56) v S (by omega) (by omega) (by omega) st5.h1
    (by rw [e5, d5, c5, b5]) (by rw [e6, d6, c6, b6])
    (by rw [st5.slot L.slot (by decide)]; exact c8)
    (fun a h1 h2 => W5.safe_readable (by omega) (W5.safe L.slot) a (by omega) (by omega))
    (fun a h1 h2 => W5.H.st a (by omega) (by omega))
  have st6 := st5.scratch Fr f1 (fun a h0 h1 => ffr a h0 (by omega)) frd fwr
  rcases scratchDH (p := p) (P := P) env K hK1 hK x ω6 μ6 Fr (by decide) st6 [UInt8.ofNat 1] 1 810 19060 rfl
      (by decide) f0 f7 f8 f9 ⟨by decide, by decide, by decide⟩ jte_404 bs_19060 (by simp [hs4]; omega) ft with
    ⟨ω7, μ7, run7, st7, g5, g6, -⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))) hx).mono
      (gas _ (by unfold stepGas growGas; omega)))
  have h7S : ω7[5] = UInt64.ofNat S := by rw [g5, f5, e5, d5, c5, b5]
  have h7v : ω7[6] = UInt64.ofNat v := by rw [g6, f6, e6, d6, c6, b6]
  -- the call of the `[u8]` encoder
  obtain ⟨cap7, ptr7, s7, W7⟩ := st7.buf
  obtain ⟨ω8, run8, k0, k1, k5, k6, k7, k8, k9⟩ := seg_19060 (p := p) (P := P) (R := refineContractK K env) x ω7
    μ7 S v q n (by omega) (by omega) hq64 (by omega) h7S h7v
    (by rw [st7.slot L.slot (by decide)]; exact c24) (by rw [st7.slot L.slot (by decide)]; exact c32)
    (fun a h1 h2 => W7.safe_readable (by omega) (W7.safe L.slot) a (by omega) (by omega))
  obtain ⟨ω9, μ9, run9, m0, m1, m5, m6, m7, m8, m9, i0, i5, i6, mfr, mrd, mwr⟩ := seg_3716 (p := p) (P := P)
    (R := refineContractK K env) x ω8 μ7 (F - 56) 812 S v ⟨by omega, by omega⟩ (by decide) (by omega) (by omega)
    k0 (k1.trans st7.h1) (k5.trans h7S) (k6.trans h7v) (fun a h1 h2 => W7.H.st a (by omega) (by omega))
  have W9 := W7.frame (F - 80) (F - 56) (by omega) (by omega) (Or.inl (by omega))
    (fun a h0 h => mfr a h0 (by omega)) mrd mwr
  obtain ⟨ω10, μ10, run10, o0, o1, o5, o6, o7, o8, on, oq, ofr, ord, owr⟩ := seg_3728 (p := p) (P := P)
    (R := refineContractK K env) x ω9 μ9 (F - 96) v q n (by omega) (by omega) hq64 hn
    (by rw [m1]; congr 1) (by rw [m7, k7]) (by rw [m8, k8]) (by rw [m9, k9])
    (fun a h1 h2 => by rw [mwr]; exact W7.H.st a (by omega) (by omega))
  have W10 := W9.frame (F - 96) (F - 80) (by omega) (by omega) (Or.inl (by omega))
    (fun a h0 h => ofr a h0 (by omega)) ord owr
  -- the length prefix
  have hpre7 : ([] ++ [UInt8.ofNat 17] ++ s4 ++ [UInt8.ofNat 1] : List UInt8).length = 6 := by simp [hs4]
  rcases prefix_anyH (p := p) (P := P) K hK1 hK x ω10 μ10 W10 (F - 96) (F - 84) 94 3753 n v n
      ⟨by omega, by omega, by omega⟩ (by omega) (by omega) hS1 o0 o1 o5 o6 (by rw [o7]; congr 1; omega) o8 (by omega) (by omega)
      (by omega) (Or.inr (by omega)) (by rw [show F - 84 = F - 96 + 12 by omega]; exact on)
      (fun a h1 h2 => by rw [ord, mrd]; exact Memory.readable_of_writable (W7.H.st a (by omega) (by omega)))
      ⟨by decide, by decide, by decide⟩ jte_46 bs_3753 (by rw [hpre7]; omega) with
    ⟨cap11, ptr11, s11, ω11, μ11, run11, p0, p1, p5, p6, W11, pkp⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans (run8.trans (run9.trans run10))))))))) hx).mono
      (gas _ (by unfold stepGas prefixGas growGas; omega)))
  -- the octets
  obtain ⟨ω12, run12, q0, q1, q5, q6, q7, q8, q9⟩ := seg_3753 (p := p) (P := P) (R := refineContractK K env) x
    ω11 μ11 (F - 96) v q n (by omega) (by omega) hq64 (by omega) p1 p5 p6
    (by rw [Memory.readN_congr (fun j hj => pkp _ (by omega) (by omega) (Or.inl (by omega)))]; exact oq)
    (fun a h1 h2 => Memory.readable_of_writable (W11.H.st a (by omega) (by omega)))
  have hsrcE : n = 0 ∨ (F - 96 ≤ q ∧ q + n ≤ S1 ∧ (q + n ≤ v ∨ v + 24 ≤ q)) ∨ HeapSrc s ptr q n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exact Or.inl h
    · rcases hsrc q n ⟨h, rfl, rfl⟩ with ⟨h1, h2, h3⟩ | h
      · exact Or.inr (Or.inl ⟨by omega, h2, h3⟩)
      · exact Or.inr (Or.inr h)
  have hby11 : μ11.readN q n = bytes := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      have hb0 : bytes = [] := List.eq_nil_of_length_eq_zero hby
      subst hb0; simp [Memory.readN]
    · rw [W11.readN_safe (hsrc q n ⟨h, rfl, rfl⟩), rby]
  rcases extendH (p := p) (P := P) env K hK1 hK x ω12 μ11 W11 (F - 96) q n 96 3765 ⟨by omega, by omega, by omega⟩
      (by omega) (by omega) hS1 q0 (q1.trans p1) q7 q8 q9 ⟨by decide, by decide, by decide⟩ jte_47 bs_3765
      (by simp [hpre7]; omega) hsrcE with
    ⟨cap13, ptr13, s13, ω13, μ13, run13, z0, z1, z5, z6, W13, zkp⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans (run8.trans (run9.trans (run10.trans (run11.trans run12))))))))))) hx).mono
      (gas _ (by unfold stepGas prefixGas growGas; omega)))
  -- the helper's frame and the arm's tail
  have kp : ∀ a, a < 4294967296 → F - 80 ≤ a → a < F → μ13.read a = μ9.read a := fun a h0 h1 h2 => by
    rw [zkp a h0 (by omega) (Or.inl (by omega)), pkp a h0 (by omega) (Or.inl (by omega)),
      ofr a h0 (Or.inr (by omega))]
  have kp7 : ∀ a, a < 4294967296 → F - 56 ≤ a → a < F → μ13.read a = μ7.read a := fun a h0 h1 h2 => by
    rw [kp a h0 (by omega) h2, mfr a h0 (Or.inr (by omega))]
  obtain ⟨ω14, run14, y0, y1, y5, y6⟩ := seg_3765 (p := p) (P := P) (R := refineContractK K env) x ω13 μ13
    (F - 56) S v ret t ω[5].toNat ω[6].toNat ⟨by omega, by omega⟩ (by omega) (by omega) (UInt64.toNat_lt _)
    (UInt64.toNat_lt _) (by rw [z1]; congr 1)
    (by rw [Memory.readN_congr (fun j hj => kp _ (by omega) (by omega) (by omega))]; exact i0)
    (by rw [Memory.readN_congr (fun j hj => kp _ (by omega) (by omega) (by omega))]; exact i5)
    (by rw [Memory.readN_congr (fun j hj => kp _ (by omega) (by omega) (by omega))]; exact i6)
    (by rw [Memory.readN_congr (fun j hj => kp7 _ (by omega) (by omega) (by omega)),
      show F - 56 + 48 = F - 8 by omega]; exact st7.w0)
    (by rw [Memory.readN_congr (fun j hj => kp7 _ (by omega) (by omega) (by omega)),
      show F - 56 + 40 = F - 16 by omega]; exact st7.w5)
    (by rw [Memory.readN_congr (fun j hj => kp7 _ (by omega) (by omega) (by omega)),
      show F - 56 + 32 = F - 24 by omega]; exact st7.w6)
    L.hret L.hjt L.hbt
    (fun a h1 h2 => Memory.readable_of_writable (W13.H.st a (by omega) (by omega)))
    (fun a h1 h2 => Memory.readable_of_writable (W13.H.st a (by omega) (by omega)))
  have henc : [] ++ [UInt8.ofNat 17] ++ s4 ++ [UInt8.ofNat 1] ++ Blob.encodeNat n ++ μ11.readN q n =
      (17 :: (s4 ++ 1 :: (Blob.encodeNat n ++ bytes)) : List UInt8) := by
    rw [hby11]; simp only [List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] <;> rfl
  refine Or.inl ⟨ω14, μ13, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans (run8.trans (run9.trans (run10.trans (run11.trans (run12.trans (run13.trans run14))))))))))))).mono
    (gas _ (by unfold stepGas prefixGas growGas; omega)), y0, by rw [y1]; congr 1; omega,
    by rw [y5]; exact UInt64.ofNat_toNat, by rw [y6]; exact UInt64.ofNat_toNat, cap13, ptr13, s13, W13.cast henc⟩


end Services.Bootstrap.Refine.EncProvide
