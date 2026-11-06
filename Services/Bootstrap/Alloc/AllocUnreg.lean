import Services.Bootstrap.Alloc.AllocSplit

/-!
# The binary's `alloc_impl`: the chunk leaves its bin

41589 … 41726: `unregister_free_space_first_chunk` — the bin's head becomes the chunk's successor
(whose back link is cleared), or, the bin now empty, its bits are cleared.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **41589 … 41726**, the chunk C has a successor `nxt`: the bin's slot holds `nxt`, whose back
    link becomes 0; C's `prev` saved; ω₈ = 32·c. -/
theorem au_head {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp C c slot nxt pv : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h10 : ω[10] = UInt64.ofNat C)
    (h3 : ω[3] = UInt64.ofNat c) (hsl : rdN μ (sp + 64) 8 = slot) (hn : rdN μ (C + 8) 4 = nxt)
    (hp : rdN μ C 4 = pv) (hpv : pv < 2147483648) (hn0 : nxt ≠ 0)
    (hC : C + 16 < 2147483648) (hna : 206864 ≤ nxt) (hn1 : nxt + 16 < 2147483648) (hsl1 : slot + 4 ≤ 206864)
    (hc : c < 33554432) (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) (hwr : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 41589 ω μ x 41726 ω' μ' x 10 ∧
      rdN μ' slot 4 = nxt ∧ rdN μ' (nxt + 12) 4 = 0 ∧ rdN μ' (sp + 48) 8 = pv ∧ ω'[8] = UInt64.ofNat (32 * c) ∧
      (∀ a, a < 4294967296 → (a < slot ∨ slot + 4 ≤ a) → (a < nxt + 12 ∨ nxt + 16 ≤ a) →
        (a < sp + 48 ∨ sp + 56 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) ∧ ∀ j : Fin 13, j.val ∉ [8, 10, 12] → ω'[j] = ω[j] := by
  have hr : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hwr a)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h10, h3, hsl, hn, hp, sxw4_small hpv, hn0, hwr, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, fun a ha h1 h2 h3 => ?_, fun a => ?_, by reg_frame⟩
    all_goals try rd_simp [hwr]
    all_goals try rd_finish
    all_goals try reg_val

/-- **41589 … 41671**, the chunk C last in its bin: the bin's slot holds 0; C's `prev` saved. -/
theorem au_last {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp C c slot pv : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h10 : ω[10] = UInt64.ofNat C)
    (h3 : ω[3] = UInt64.ofNat c) (hsl : rdN μ (sp + 64) 8 = slot) (hn : rdN μ (C + 8) 4 = 0)
    (hp : rdN μ C 4 = pv) (hpv : pv < 2147483648)
    (hC : C + 16 < 2147483648) (hsl1 : slot + 4 ≤ 206864)
    (hc : c < 33554432) (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) (hwr : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 41589 ω μ x 41671 ω' μ' x 8 ∧
      rdN μ' slot 4 = 0 ∧ rdN μ' (sp + 48) 8 = pv ∧ ω'[8] = UInt64.ofNat (32 * c) ∧
      (∀ a, a < 4294967296 → (a < slot ∨ slot + 4 ≤ a) → (a < sp + 48 ∨ sp + 56 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) ∧ ∀ j : Fin 13, j.val ∉ [8, 10, 12] → ω'[j] = ω[j] := by
  have hr : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hwr a)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h10, h3, hsl, hn, hp, sxw4_small hpv, hwr, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_, by reg_frame⟩
    all_goals try rd_simp [hwr]
    all_goals try rd_finish
    all_goals try reg_val

/-- `clear_word` with the operands the other way round, as `alloc_impl` has them. -/
theorem clear_word' (k w : Nat) (hk : k < 64) (hw : w < 2 ^ 64) :
    Exec.bitwise (· && ·) w (Num.rotl 64 18446744073709551614 k % 18446744073709551616) % 18446744073709551616 =
      w &&& ((2 ^ 64 - 1) ^^^ 2 ^ k) := by
  have hm : (2 ^ 64 - 1) ^^^ 2 ^ k < 2 ^ 64 :=
    Nat.xor_lt_two_pow (by decide) (Nat.pow_lt_pow_right (by decide) hk)
  rw [rotl_clear k hk, Nat.mod_eq_of_lt hm, bitwise_and_land _ _ hm]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left hw)

theorem au_clear {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp q b w pri : Nat) (h1 : ω[1] = UInt64.ofNat sp)
    (hq : rdN μ (sp + 40) 8 = q) (hb : rdN μ (sp + 32) 8 = b) (h88 : rdN μ (sp + 88) 8 = 204984)
    (h120 : rdN μ (sp + 120) 8 = 204984) (hq1 : q < 38) (hb1 : b < 64)
    (hw : rdN μ (q * 8 + 204984 + 1544) 8 = w) (hp : rdN μ 206832 8 = pri)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) (hwr : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 41671 ω μ x 41726 ω' μ' x 20 ∧
      rdN μ' (q * 8 + 204984 + 1544) 8 = w &&& ((2 ^ 64 - 1) ^^^ 2 ^ b) ∧
      rdN μ' 206832 8 = (if w &&& ((2 ^ 64 - 1) ^^^ 2 ^ b) = 0 then pri &&& ((2 ^ 64 - 1) ^^^ 2 ^ q) else pri) ∧
      (∀ a, a < 4294967296 → (a < q * 8 + 204984 + 1544 ∨ q * 8 + 204984 + 1552 ≤ a) →
        (a < 206832 ∨ 206840 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) ∧ ∀ j : Fin 13, j.val ∉ [2, 5, 6, 10, 11, 12] → ω'[j] = ω[j] := by
  have hr : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hwr a)
  have hw64 : w < 2 ^ 64 := by rw [← hw]; exact rdN_lt64 μ _
  have hp64 : pri < 2 ^ 64 := by rw [← hp]; exact rdN_lt64 μ _
  have hc1 := clear_word' b w hb1 hw64
  have hc2 := clear_word' q pri (by omega) hp64
  rw [← hw] at hc1
  rw [← hp] at hc2
  rw [show ω = regsNF ω [] from rfl]
  by_cases hz : w &&& ((2 ^ 64 - 1) ^^^ 2 ^ b) = 0
  · have hz' : rdN μ (q * 8 + 204984 + 1544) 8 &&& ((2 ^ 64 - 1) ^^^ 2 ^ b) = 0 := by rw [hw]; exact hz
    refine ⟨?ω', ?μ', ?run, ?post⟩
    case run => pvm_go [h1, hq, hb, h88, h120, hwr, hr, hc1, hc2, hz', rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
    case post =>
      refine ⟨?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_, by reg_frame⟩
      all_goals try rd_simp [hwr, hz, hw, hp]
      all_goals try (simp [Num.decodeLE]; done)
      all_goals try rw [show Num.decodeLE (μ.readN 206832 8) = pri from hp]
      all_goals try rw [show Num.decodeLE (μ.readN (q * 8 + 204984 + 1544) 8) = w from hw]
      all_goals try rw [show (18446744073709551615 : Nat) = 2 ^ 64 - 1 from rfl]
      all_goals try simp only [if_true, if_false, ite_true, ite_false]
      all_goals try exact Nat.mod_eq_of_lt (clear_lt _ _ hp64)
      all_goals try exact Nat.mod_eq_of_lt (clear_lt _ _ hw64)
      all_goals try rfl
  · have hz' : ¬ rdN μ (q * 8 + 204984 + 1544) 8 &&& ((2 ^ 64 - 1) ^^^ 2 ^ b) = 0 := by rw [hw]; exact hz
    refine ⟨?ω'', ?μ'', ?run', ?post'⟩
    case run' => pvm_go [h1, hq, hb, h88, h120, hwr, hr, hc1, hz', rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
    case post' =>
      refine ⟨?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_, by reg_frame⟩
      all_goals try rd_simp [hwr, hz, hw, hp]
      all_goals try (simp [Num.decodeLE]; done)
      all_goals try rw [show Num.decodeLE (μ.readN 206832 8) = pri from hp]
      all_goals try rw [show Num.decodeLE (μ.readN (q * 8 + 204984 + 1544) 8) = w from hw]
      all_goals try rw [show (18446744073709551615 : Nat) = 2 ^ 64 - 1 from rfl]
      all_goals try simp only [if_true, if_false, ite_true, ite_false]
      all_goals try exact Nat.mod_eq_of_lt (clear_lt _ _ hp64)
      all_goals try exact Nat.mod_eq_of_lt (clear_lt _ _ hw64)
      all_goals try rfl

end Services.Bootstrap.Alloc
