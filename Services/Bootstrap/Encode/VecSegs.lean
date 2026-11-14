import Services.Bootstrap.Encode.EncMD

/-!
# `Instruction::encode_to`: the straight-line pieces of the arms holding a `Vec`

The arms of `Provide` (17, at 18990), `LookedUp` (18, at 19538) and `Imported` (19, at 19983), from
one call to the next, one theorem each (as `Encode.Segs` for the fixed-width arms). Unlike those arms,
17 and 19 keep the value S in ω₅ and the writer v in ω₆; 18 keeps S in ω₆ and compares the word at
S + 8 with ω₅ = 2^64 − 1, which the dispatch sets (`dispatchV`), the `None` niche of `Option<Vec<u8>>`.
A `Vec`'s length is stored as a 32-bit word at sp + 24 and passed to the length-prefix function
(30977); the code traps (20397) when the length is 2^32 or more. `Imported`'s elements are encoded by
a loop (20058 … 20115) over its `Vec<Vec<u8>>`'s 24-octet elements.
-/

namespace Services.Bootstrap.Encode.Enc

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.Encode.Writer

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {X : Type} {R : HostRel X}

/-- `dispatch` for the variants 18 and 19, also giving ω₅ = 2^64 − 1 (set at 30161). -/
theorem dispatchV {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (F S v ret r5 r6 t : Nat) (ht : t = 18 ∨ t = 19) (hF : 67476 + 56 ≤ F ∧ F < 4294967296)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat F) (h5 : ω[5] = UInt64.ofNat r5)
    (h6 : ω[6] = UInt64.ofNat r6) (h7 : ω[7] = UInt64.ofNat S) (h8 : ω[8] = UInt64.ofNat v)
    (hret : ret < 18446744073709551616) (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hv : v < 18446744073709551616)
    (hS : S + 8 ≤ 4294967296) (hSF : S + 8 ≤ F - 56 ∨ F ≤ S)
    (hD : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + t))
    (tab : μ.readN 67376 100 = table) (hrt : ∀ a, 67376 ≤ a → a < 67476 → μ.readable a = true)
    (hrS : ∀ a, S ≤ a → a < S + 8 → μ.readable a = true)
    (hw : ∀ a, F - 56 ≤ a → a < F → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 30145 ω μ x (arm t) ω' μ' x 24 ∧
      ω'[1] = UInt64.ofNat (F - 56) ∧ ω'[5] = UInt64.ofNat 18446744073709551615 ∧
      ω'[10] = UInt64.ofNat v ∧ ω'[11] = UInt64.ofNat S ∧
      μ'.readN (F - 8) 8 = Num.encodeLE 8 ret ∧ μ'.readN (F - 16) 8 = Num.encodeLE 8 r5 ∧
      μ'.readN (F - 24) 8 = Num.encodeLE 8 r6 ∧ μ'.readN (F - 40) 8 = Num.encodeLE 8 v ∧
      (∀ a, a < 4294967296 → (a < F - 56 ∨ F ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rD := rd8 (by omega) hD
  have hrt' : ∀ a, 67376 + 4 * t ≤ a → a < 67376 + 4 * t + 4 → μ.readable a = true :=
    fun a h1 h2 => hrt a (by omega) (by omega)
  have rt : rdN μ (67376 + 4 * t) 4 = ents.getD t 0 := by
    show Num.decodeLE (μ.readN _ 4) = _
    rw [table_entry tab t (by omega)]
    exact table_val t (by omega)
  have hsx := sxw_table t (by omega)
  have hr : ∀ a, F - 56 ≤ a → a < F → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  rcases ht with h | h <;>
  subst h <;>
  · simp only [ents, List.getD_cons_succ, List.getD_cons_zero, Nat.reduceMul, Nat.reduceAdd] at rt hrt' hsx
    simp only [arm, List.getD_cons_succ, List.getD_cons_zero]
    refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · pvm_go [h0, h1, h5, h6, h7, h8, hF, hS, hSF, hw, hr, hrS, rD, rt, hrt', hsx, rdN_writeN_disjoint,
        ↓rdN_fold, ↓loadI_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
      all_goals try simp only [show F - 56 + 48 = F - 8 by omega, show F - 56 + 40 = F - 16 by omega,
        show F - 56 + 32 = F - 24 by omega, show F - 56 + 16 = F - 40 by omega]
      post_simp
      all_goals try assumption

/-- 19538 … 19552 (`LookedUp`, tag 18): the octet 18 at sp + 24 and the call for it (return 856 →
    19559), with S (ω₁₁) in ω₆ and ω₅ kept. -/
theorem seg_19538 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616) (hS : S < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h10 : ω[10] = UInt64.ofNat v) (h11 : ω[11] = UInt64.ofNat S)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 25 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 19538 ω μ x 58508 ω' μ' x 10 ∧
      ω'[0] = UInt64.ofNat 856 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = UInt64.ofNat S ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (sp + 24) 1 = [UInt8.ofNat 18] ∧
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

/-- 19559 … 20359 (`LookedUp { data: None }`): the word at S + 8 is the niche 2^64 − 1 = ω₅; the octet 0
    at sp + 24 and the call for it (return 918 → 20383), the writer reloaded from sp + 16. -/
theorem seg_19559_none {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616)
    (hS : S + 16 ≤ 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat 18446744073709551615) (h6 : ω[6] = UInt64.ofNat S)
    (s8 : μ.readN (S + 8) 8 = Num.encodeLE 8 18446744073709551615)
    (s16 : μ.readN (sp + 16) 8 = Num.encodeLE 8 v)
    (hrS : ∀ a, S + 8 ≤ a → a < S + 16 → μ.readable a = true)
    (hw : ∀ a, sp + 16 ≤ a → a < sp + 25 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 19559 ω μ x 58508 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 918 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (sp + 24) 1 = [UInt8.ofNat 0] ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 25 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r8 := rd8 (by decide) s8
  have r16 := rd8 hv s16
  have hr : ∀ a, sp + 16 ≤ a → a < sp + 25 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hsp, hS, hw, hr, hrS, r8, r16, ↓rdN_fold, rdN_writeN_disjoint]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, h6, Nat.mod_eq_of_lt hv]
    post_simp
    all_goals try assumption


/-- 19559 … 19579 (`LookedUp { data: Some(_) }`): the word w at S + 8 (the `Vec`'s capacity) is not the
    niche; the octet 1 at sp + 24 and the call for it (return 858 → 19586). -/
theorem seg_19559_some {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (sp v S w : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616)
    (hS : S + 16 ≤ 4294967296) (hw64 : w < 18446744073709551615)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat 18446744073709551615) (h6 : ω[6] = UInt64.ofNat S)
    (s8 : μ.readN (S + 8) 8 = Num.encodeLE 8 w)
    (s16 : μ.readN (sp + 16) 8 = Num.encodeLE 8 v)
    (hrS : ∀ a, S + 8 ≤ a → a < S + 16 → μ.readable a = true)
    (hw : ∀ a, sp + 16 ≤ a → a < sp + 25 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 19559 ω μ x 58508 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 858 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (sp + 24) 1 = [UInt8.ofNat 1] ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 25 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r8 := rd8 (by omega) s8
  have r16 := rd8 hv s16
  have hne : ¬ w = 18446744073709551615 := by omega
  have hr : ∀ a, sp + 16 ≤ a → a < sp + 25 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hsp, hS, hw, hr, hrS, r8, r16, hne, ↓rdN_fold, rdN_writeN_disjoint]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, h6, Nat.mod_eq_of_lt hv]
    post_simp
    all_goals try assumption

/-- 19586 … 19616 (`LookedUp { data: Some(_) }`): the `Vec`'s pointer q (S + 16) to sp + 8 and its
    length n < 2^32 (S + 24) as a 32-bit word to sp + 24; the call of the length prefix with ω₇ = sp + 24
    and the writer (from sp + 16) in ω₈ and ω₅, n in ω₆ (return 860 → 19622). -/
theorem seg_19586 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (sp v S q n : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616)
    (hS : S + 32 ≤ 4294967296) (hq : q < 18446744073709551616) (hn : n < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h6 : ω[6] = UInt64.ofNat S)
    (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 q) (s24 : μ.readN (S + 24) 8 = Num.encodeLE 8 n)
    (v16 : μ.readN (sp + 16) 8 = Num.encodeLE 8 v)
    (hrS : ∀ a, S + 16 ≤ a → a < S + 32 → μ.readable a = true)
    (hw : ∀ a, sp + 8 ≤ a → a < sp + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 19586 ω μ x 30977 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat 860 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v ∧ ω'[6] = UInt64.ofNat n ∧
      ω'[7] = UInt64.ofNat (sp + 24) ∧ ω'[8] = UInt64.ofNat v ∧
      μ'.readN (sp + 8) 8 = Num.encodeLE 8 q ∧ rdN μ' (sp + 24) 4 = n ∧
      μ'.readN (sp + 16) 8 = Num.encodeLE 8 v ∧
      (∀ a, a < 4294967296 → (a < sp + 8 ∨ sp + 16 ≤ a) → (a < sp + 24 ∨ sp + 28 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r16 := rd8 hq s16
  have r24 := rd8 (by omega) s24
  have rv := rd8 hv v16
  have hsh : n >>> 32 = 0 := by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt hn
  have hr : ∀ a, sp + 8 ≤ a → a < sp + 32 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, hsp, hS, hw, hr, hrS, r16, r24, rv, hsh, ↓rdN_fold, rdN_writeN_disjoint]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h6, Nat.mod_eq_of_lt hv]
    post_simp
    all_goals try assumption
    all_goals try (show Num.decodeLE _ = _; rw [Memory.readN_writeN_same _ _ _ _ (by simp) (by simp [two32] <;> omega),
      Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt (by omega))

end Services.Bootstrap.Encode.Enc
