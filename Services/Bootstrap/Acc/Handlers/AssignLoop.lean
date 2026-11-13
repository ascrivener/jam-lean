import Services.Bootstrap.Acc.Handlers.DesignateLoop

/-!
# `Assign`'s copy loop (40336 … 40365)

40215 (`Assign`'s callee, its frame at S = ω₁) builds the authorizer queue's serialisation (GP §B.7
Ω_A: 32-octet hashes one after another) in a `Vec<u8>` `{cap, ptr, len}` at S + 32. Each turn of the
loop:
* stores the next hash's address s + 32 at S + 24;
* appends the 32 octets at s with `extend_from_slice` (58508, `extend_ok`), return 1978 (40356);
* steps ω₅ (the octets left) down by 32, reloads ω₆ := s + 32, and goes round again while ω₅ ≠ 0.
-/

namespace Services.Bootstrap.Acc.Handlers.AssignLoop

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.Acc.Handlers.DesignateLoop

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 40336 … 58508: s + 32 stored at S + 24, the call `extend(S + 32, s, 32)`, return 1978. -/
theorem seg_head {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (S s : Nat) (h1 : ω[1] = UInt64.ofNat S) (h6 : ω[6] = UInt64.ofNat s)
    (hS : S + 56 < 4294967296) (hs : s + 32 < 4294967296)
    (hw : ∀ a, S + 24 ≤ a → a < S + 32 → μ.writable a = true) :
    ∃ ω', FreeStepsH p R 40336 ω μ x 58508 ω' (μ.writeN (S + 24) (Num.encodeLE 8 (s + 32))) x 6 ∧
      ω'[0] = UInt64.ofNat 1978 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = ω[5] ∧ ω'[6] = UInt64.ofNat s ∧
      ω'[7] = UInt64.ofNat (S + 32) ∧ ω'[8] = UInt64.ofNat s ∧ ω'[9] = UInt64.ofNat 32 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h6, hS, hs, hw, bs_58508]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h6]
    all_goals try (congr 1; omega)

/-- 40356 … 40362: ω₅ := ω₅ − 32, ω₆ := the word at S + 24; round again (40336) while ω₅ ≠ 0,
    else on to 40365. -/
theorem tail_gen {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (S r s' : Nat) (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat r) (hr : 32 ≤ r)
    (hr64 : r < 18446744073709551616) (hS : S + 56 < 4294967296) (hs' : s' < 18446744073709551616)
    (m : μ.readN (S + 24) 8 = Num.encodeLE 8 s')
    (hrd : ∀ a, S + 24 ≤ a → a < S + 32 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 40356 ω μ x (if r = 32 then 40365 else 40336) ω' μ x 3 ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat (r - 32) ∧ ω'[6] = UInt64.ofNat s' := by
  have m' := Services.Bootstrap.Encode.Writer.rd8 hs' m
  rw [show ω = regsNF ω [] from rfl]
  rcases Nat.eq_or_lt_of_le hr with he | hlt
  · subst he
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · simp only [↓reduceIte]
      pvm_go [h1, h5, hS, m', hrd, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_⟩
      all_goals simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5]
      all_goals try (congr 1; omega)
  · have hne : r ≠ 32 := by omega
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · simp only [hne, ↓reduceIte]
      pvm_go [h1, h5, hS, m', hrd, hr64, hne, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_⟩
      all_goals simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5]
      all_goals try (congr 1; omega)

end Services.Bootstrap.Acc.Handlers.AssignLoop
