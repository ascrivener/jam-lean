import Services.Bootstrap.Encode.Writer
import Services.Bootstrap.CodeA

/-!
# `Designate`'s copy loop (49775 … 49856)

49597 builds the validator keys' serialisation (GP §6.3 and §C, each key 336 octets: Bandersnatch 32,
Ed25519 32, BLS 144, metadata 128) in a `Vec<u8>` `{cap, ptr, len}` at S + 24, its frame base S
(ω₁). The keys are Rust structs of 336 octets whose fields lie in the order metadata (+ 0),
Bandersnatch (+ 128), Ed25519 (+ 160), BLS (+ 192). Each turn of the loop:
* stores the next key's address s + 336 at S + 16;
* appends the four fields in the serialisation's order with `extend_from_slice` (58508, `extend_ok`);
* steps ω₆ (the octets left) down by 336, reloads ω₅ := s + 336, and goes round again while ω₆ ≠ 0.

`seg_head`, `seg1`, `seg2`, `seg3` and `seg_tail` are the straight-line pieces between the calls.
-/

namespace Services.Bootstrap.Acc.Handlers.DesignateLoop

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- One key's serialisation (GP §6.3), read from the Rust struct at s. -/
def keyBytes (μ : Memory) (s : Nat) : List UInt8 :=
  μ.readN (s + 128) 32 ++ μ.readN (s + 160) 32 ++ μ.readN (s + 192) 144 ++ μ.readN s 128

/-- 49775 … 58508: s + 336 stored at S + 16, the first call `extend(S + 24, s + 128, 32)`, return 2204. -/
theorem seg_head {p : ByteArray} {P : Program} [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (S s : Nat) (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat s)
    (hS : S + 48 < 4294967296) (hs : s + 336 < 4294967296)
    (hw : ∀ a, S + 16 ≤ a → a < S + 24 → μ.writable a = true) :
    ∃ ω', FreeStepsH p R 49775 ω μ x 58508 ω' (μ.writeN (S + 16) (Num.encodeLE 8 (s + 336))) x 6 ∧
      ω'[0] = UInt64.ofNat 2204 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat s ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (S + 24) ∧ ω'[8] = UInt64.ofNat (s + 128) ∧ ω'[9] = UInt64.ofNat 32 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, hS, hs, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5]
    all_goals try (congr 1; omega)

/-- A call `extend(S + 24, s + o, n)` returning through `ret`, set up from 49798 / 49814 / 49831. -/
theorem seg_mid {p : ByteArray} {P : Program} [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (S s i o n ret : Nat) (hi : (i = 49798 ∧ o = 160 ∧ n = 32 ∧ ret = 2206) ∨
      (i = 49814 ∧ o = 192 ∧ n = 144 ∧ ret = 2208) ∨ (i = 49831 ∧ o = 0 ∧ n = 128 ∧ ret = 2210))
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat s)
    (hS : S + 48 < 4294967296) (hs : s + 336 < 4294967296) :
    ∃ ω', FreeStepsH p R i ω μ x 58508 ω' μ x 4 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat s ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (S + 24) ∧ ω'[8] = UInt64.ofNat (s + o) ∧ ω'[9] = UInt64.ofNat n := by
  rw [show ω = regsNF ω [] from rfl]
  rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  all_goals refine ⟨?_, ?_, ?_⟩
  all_goals rotate_left
  all_goals first
    | pvm_go [h1, h5, hS, hs]
    | (refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
       all_goals simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
         ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, Nat.add_zero]
       all_goals try (congr 1; omega))

/-- 49846 … 49853: ω₆ := ω₆ − 336, ω₅ := the word at S + 16; round again (49775) while ω₆ ≠ 0
    (`tail_again`), else on to 49856 (`tail_done`). -/
theorem tail_gen {p : ByteArray} {P : Program} [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (S r s' : Nat) (h1 : ω[1] = UInt64.ofNat S) (h6 : ω[6] = UInt64.ofNat r) (hr : 336 ≤ r)
    (hr64 : r < 18446744073709551616) (hS : S + 48 < 4294967296) (hs' : s' < 18446744073709551616)
    (m : μ.readN (S + 16) 8 = Num.encodeLE 8 s')
    (hrd : ∀ a, S + 16 ≤ a → a < S + 24 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 49846 ω μ x (if r = 336 then 49856 else 49775) ω' μ x 3 ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat s' ∧ ω'[6] = UInt64.ofNat (r - 336) := by
  have m' := Services.Bootstrap.Encode.Writer.rd8 hs' m
  rw [show ω = regsNF ω [] from rfl]
  rcases Nat.eq_or_lt_of_le hr with he | hlt
  · subst he
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · simp only [↓reduceIte]
      pvm_go [h1, h6, hS, m', hrd, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_⟩
      all_goals simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h6]
      all_goals try (congr 1; omega)
  · have hne : r ≠ 336 := by omega
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · simp only [hne, ↓reduceIte]
      pvm_go [h1, h6, hS, m', hrd, hr64, hne, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_⟩
      all_goals simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h6]
      all_goals try (congr 1; omega)

end Services.Bootstrap.Acc.Handlers.DesignateLoop
