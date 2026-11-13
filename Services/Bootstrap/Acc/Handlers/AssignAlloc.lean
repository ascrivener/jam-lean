import Services.Bootstrap.Acc.Inputs.FetchVec

/-!
# `Assign`'s buffer (40215 … 41177, 40302 … 40336)

40215 (`Assign`'s callee, its frame at S = ω₁, the queue's length n at S + 24 and ω₅ = 32 · n)
checks 32 · n + 3 ≤ 2³⁷ − 32, takes the allocator's lock and calls `alloc_impl` (41177) for n + 1
units of alignment 1, not zeroed, return address 1976 (40302). There the lock is cleared and the
vector `{cap: 32 · n + 3, ptr, len: 0}` set up at S + 32 for the copy loop (40336).
-/

namespace Services.Bootstrap.Acc.Handlers.AssignAlloc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- A word read back from its encoding. -/
theorem rd8 {μ : Memory} {a w : Nat} (hw : w < 2 ^ 64) (h : μ.readN a 8 = Num.encodeLE 8 w) : rdN μ a 8 = w := by
  show Num.decodeLE _ = _
  rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hw]

/-- **40215 … 41177**, n hashes, 32 · n + 3 ≤ 2³⁷ − 32 and n + 1 < 2³¹: the lock taken (the scratch
    at 196608 … 196616 used), 196792 at S + 16, and the call of `alloc_impl` with ω₇ = 196792,
    ω₈ = 1 (alignment), ω₉ = n + 1 units, ω₁₀ = 0 (not zeroed), return address 1976; ω₅ kept. -/
theorem lock {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (S n : Nat) (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat (32 * n))
    (hn : 32 * n + 3 ≤ 137438953440) (hn1 : n + 1 < 2147483648)
    (m24 : μ.readN (S + 24) 8 = Num.encodeLE 8 n)
    (hl : rdN μ 206848 1 = 0) {HT S0 S1 : Nat} (hH : 206864 ≤ HT) (hwr : WrAt μ HT S0 S1)
    (hS : S0 ≤ S ∧ S + 32 ≤ S1 ∧ HT ≤ S ∧ S1 < 4294967296) :
    ∃ ω' μ', FreeStepsH p R 40215 ω μ x 41177 ω' μ' x 40 ∧
      ω'[7] = UInt64.ofNat 196792 ∧ ω'[8] = UInt64.ofNat 1 ∧ ω'[9] = UInt64.ofNat (n + 1) ∧
      ω'[10] = UInt64.ofNat 0 ∧ ω'[0] = UInt64.ofNat 1976 ∧ ω'[5] = ω[5] ∧ ω'[1] = ω[1] ∧
      μ'.readN (S + 16) 8 = Num.encodeLE 8 196792 ∧
      (∀ a, a < 4294967296 → (a < 196608 ∨ 196616 ≤ a) → (a < 206848 ∨ 206852 ≤ a) →
        (a < S + 16 ∨ S + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) := by
  have hr := hwr.rd
  have hand := lock_test (w := rdN μ 206848 4) (by rw [rdN4_mod]; exact hl)
  have r24 := rd8 (by omega) m24
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, hn, hn1, r24, hand, hwr, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, by reg_val, by reg_val, by reg_val, by reg_val, ?_, ?_, ?_,
      fun a ha h1 h2 h3 => ?_, fun a => ?_⟩
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']
      rd_simp []
      rfl
    · simp [PVM.getElem_regsNF, PVM.lookup_cons_nat]
    · simp [PVM.getElem_regsNF, PVM.lookup_cons_nat]
    all_goals rd_simp []
    all_goals try rfl

end Services.Bootstrap.Acc.Handlers.AssignAlloc
