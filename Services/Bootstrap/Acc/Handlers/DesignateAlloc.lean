import Services.Bootstrap.Acc.Inputs.FetchVec

/-!
# `Designate`'s buffer (49597 … 41177)

49597 (`Designate`'s callee, its frame at S = ω₁) sizes the keys' serialisation, L = 336 · n for n
keys (GP §6.3), saves the source `Vec`'s address (ω₅) at S + 16 and n at S + 8, checks
L ≤ 2³⁷ − 32, takes the allocator's lock (the word at 206848) and calls `alloc_impl` (41177) for
⌈L/32⌉ units of alignment 1, not zeroed, return address 2202 (49733).
-/

namespace Services.Bootstrap.Acc.Handlers.DesignateAlloc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **49597 … 41177**, n > 0 keys, L = 336 · n ≤ 2³⁷ − 32: the source `Vec`'s address v at S + 16,
    n at S + 8, the lock taken (the scratch at 196608 … 196616 used), 196792 at S, and the call of
    `alloc_impl` with ω₇ = 196792, ω₈ = 1 (alignment), ω₉ = ⌈L/32⌉, ω₁₀ = 0 (not zeroed), return
    address 2202; ω₅ = L. -/
theorem lock {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (S v n : Nat) (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat v)
    (h6 : ω[6] = UInt64.ofNat n) (hn : 0 < n) (hL : 336 * n + 31 < 68719476736)
    (hv : v < 18446744073709551616)
    (hl : rdN μ 206848 1 = 0) {HT S0 S1 : Nat} (hH : 206864 ≤ HT) (hwr : WrAt μ HT S0 S1)
    (hS : S0 ≤ S ∧ S + 24 ≤ S1 ∧ HT ≤ S ∧ S1 < 4294967296) :
    ∃ ω' μ', FreeStepsH p R 49597 ω μ x 41177 ω' μ' x 40 ∧
      ω'[7] = UInt64.ofNat 196792 ∧ ω'[8] = UInt64.ofNat 1 ∧
      ω'[9] = UInt64.ofNat ((336 * n + 31) / 32) ∧ ω'[10] = UInt64.ofNat 0 ∧ ω'[0] = UInt64.ofNat 2202 ∧
      ω'[6] = UInt64.ofNat 1 ∧ ω'[5] = UInt64.ofNat (336 * n) ∧ ω'[1] = ω[1] ∧
      μ'.readN (S + 16) 8 = Num.encodeLE 8 v ∧ μ'.readN (S + 8) 8 = Num.encodeLE 8 n ∧
      μ'.readN S 8 = Num.encodeLE 8 196792 ∧
      (∀ a, a < 4294967296 → (a < 196608 ∨ 196616 ≤ a) → (a < 206848 ∨ 206852 ≤ a) →
        (a < S ∨ S + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) := by
  have hr := hwr.rd
  have hand := lock_test (w := rdN μ 206848 4) (by rw [rdN4_mod]; exact hl)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, h6, hn, hv, hand, show 137438953440 ≥ 336 * n by omega, hwr, hr,
    rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, by reg_val, by reg_val, by reg_val, ?_, ?_, ?_,
      ?_, fun a ha h1 h2 h3 => ?_, fun a => ?_⟩
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
        List.lookup_nil, Option.getD_none]
    all_goals rd_simp []
    all_goals try rfl

end Services.Bootstrap.Acc.Handlers.DesignateAlloc
