import Services.Bootstrap.Alloc.ReallocGrow

/-!
# The binary's `grow_inplace`: the old next chunk leaves its bin

43933 … 44030: the old next chunk nc (at sp + 80) leaves its bin's list — the head case (43933),
the middle case (43950), and the bin's bits cleared when its list empties (43971). ω₁₁ = the head
slot (head case), ω₁₀ = the bin (clear case), ω₇ = the allocator, ω₃ = 204984.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **43933 … 44030**, nc its bin's head with a successor `nxt`: the bin's head becomes `nxt`,
    whose back link is cleared. -/
theorem rg_unlink_head {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp nc slot nxt : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h11 : ω[11] = UInt64.ofNat slot)
    (h80 : rdN μ (sp + 80) 8 = nc) (hn : rdN μ (nc + 8) 4 = nxt)
    (hnc : nc + 16 < 2147483648) (hn0 : nxt ≠ 0) (hn1 : nxt + 16 < 2147483648) (hsl : slot + 4 ≤ 206864)
    (hna : 206864 ≤ nxt) (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296) (hw : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 43933 ω μ x 44030 ω' μ' x 7 ∧
      rdN μ' slot 4 = nxt ∧ rdN μ' (nxt + 12) 4 = 0 ∧
      (∀ a, a < 4294967296 → (a < slot ∨ slot + 4 ≤ a) → (a < nxt + 12 ∨ nxt + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) ∧ ∀ j : Fin 13, j.val ∉ [9, 12] → ω'[j] = ω[j] := by
  have hr : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hw a)
  have hn32 : nxt < 4294967296 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h11, h80, hn, hn0, hw, hr, ↓rdN_fold]
  case post =>
    refine ⟨?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_, by reg_frame⟩
    all_goals try rd_simp [hw]
    all_goals try rd_finish

/-- **43933 … 43971**, nc its bin's head and last: the bin's head becomes 0. -/
theorem rg_unlink_head0 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp nc slot : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h11 : ω[11] = UInt64.ofNat slot)
    (h80 : rdN μ (sp + 80) 8 = nc) (hn : rdN μ (nc + 8) 4 = 0) (hnc : nc + 16 < 2147483648)
    (hsl : slot + 4 ≤ 206864) (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296)
    (hw : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 43933 ω μ x 43971 ω' μ' x 6 ∧ rdN μ' slot 4 = 0 ∧
      (∀ a, a < 4294967296 → (a < slot ∨ slot + 4 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) ∧ ∀ j : Fin 13, j.val ∉ [9, 12] → ω'[j] = ω[j] := by
  have hr : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hw a)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h11, h80, hn, hw, hr, ↓rdN_fold]
  case post =>
    refine ⟨?_, fun a ha h1 => ?_, fun a => ?_, by reg_frame⟩
    all_goals try rd_simp [hw]
    all_goals try rd_finish

/-- **43950 … 44030**, nc inside its bin's list, between `prv` and `nxt` (0 if last): `prv`'s next
    becomes `nxt`, and `nxt`'s back link `prv`. -/
theorem rg_unlink_mid {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp nc prv nxt : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h80 : rdN μ (sp + 80) 8 = nc)
    (hn : rdN μ (nc + 8) 4 = nxt) (hp : rdN μ (nc + 12) 4 = prv) (hnc : nc + 16 < 2147483648)
    (hn1 : nxt + 16 < 2147483648) (hp1 : prv + 16 < 2147483648) (hna : nxt ≠ 0 → (nxt + 16 ≤ prv ∨ prv + 16 ≤ nxt))
    (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296) (hw : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 43950 ω μ x 44030 ω' μ' x 8 ∧
      rdN μ' (prv + 8) 4 = nxt ∧ (nxt ≠ 0 → rdN μ' (nxt + 12) 4 = prv) ∧
      (∀ a, a < 4294967296 → (a < prv + 8 ∨ prv + 12 ≤ a) → (nxt = 0 ∨ a < nxt + 12 ∨ nxt + 16 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) ∧ ∀ j : Fin 13, j.val ∉ [9, 10, 11] → ω'[j] = ω[j] := by
  have hr : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hw a)
  rw [show ω = regsNF ω [] from rfl]
  by_cases hn0 : nxt = 0
  · subst hn0
    refine ⟨?ω', ?μ', ?run, ?post⟩
    case run => pvm_go [h1, h80, hn, hp, hw, hr, ↓rdN_fold]
    case post =>
      refine ⟨?_, fun h => absurd rfl h, fun a ha h1 h2 => ?_, fun a => ?_, by reg_frame⟩
      all_goals try rd_simp [hw]
      all_goals try rd_finish
  · have hd := hna hn0
    refine ⟨?ω'', ?μ'', ?run', ?post'⟩
    case run' => pvm_go [h1, h80, hn, hp, hn0, hw, hr, ↓rdN_fold]
    case post' =>
      refine ⟨?_, fun _ => ?_, fun a ha h1 h2 => ?_, fun a => ?_, by reg_frame⟩
      all_goals try rd_simp [hw]
      all_goals try rd_finish

/-- **43971 … 44030**, the bin's list now empty: its bit is cleared in its secondary word w, and if
    that leaves the word 0, the word's bit in the primary word; ω₂ = X + 32·n (sp + 64),
    ω₅ = n (sp + 112). -/
theorem rg_clear {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp bin w pri n N : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h10 : ω[10] = UInt64.ofNat bin)
    (h7 : ω[7] = UInt64.ofNat 196792) (h3 : ω[3] = UInt64.ofNat 204984)
    (hb : bin < 2432) (hw : rdN μ (bin / 64 * 8 + 204984 + 1544) 8 = w) (hp : rdN μ 206832 8 = pri)
    (h64 : rdN μ (sp + 64) 8 = N) (h112 : rdN μ (sp + 112) 8 = n)
    (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296) (hwr : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 43971 ω μ x 44030 ω' μ' x 21 ∧
      rdN μ' (bin / 64 * 8 + 204984 + 1544) 8 = w &&& ((2 ^ 64 - 1) ^^^ 2 ^ (bin % 64)) ∧
      rdN μ' 206832 8 = (if w &&& ((2 ^ 64 - 1) ^^^ 2 ^ (bin % 64)) = 0 then
        pri &&& ((2 ^ 64 - 1) ^^^ 2 ^ (bin / 64)) else pri) ∧
      (∀ a, a < 4294967296 → (a < bin / 64 * 8 + 204984 + 1544 ∨ bin / 64 * 8 + 204984 + 1552 ≤ a) →
        (a < 206832 ∨ 206840 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) ∧ ω'[2] = UInt64.ofNat N ∧ ω'[5] = UInt64.ofNat n ∧
      ∀ j : Fin 13, j.val ∉ [2, 5, 9, 10, 11, 12] → ω'[j] = ω[j] := by
  have hr : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hwr a)
  have hw64 : w < 2 ^ 64 := by rw [← hw]; exact rdN_lt64 μ _
  have hp64 : pri < 2 ^ 64 := by rw [← hp]; exact rdN_lt64 μ _
  have hc1 := clear_word' (bin % 64) w (Nat.mod_lt _ (by decide)) hw64
  have hc2 := clear_word (bin / 64) pri (by omega) hp64
  rw [← hw] at hc1
  rw [← hp, rdN_mod64] at hc2
  have hp' : rdN μ (204984 + 1848) 8 = pri := hp
  rw [show ω = regsNF ω [] from rfl]
  by_cases hz : w &&& ((2 ^ 64 - 1) ^^^ 2 ^ (bin % 64)) = 0
  · have hz' : rdN μ (bin / 64 * 8 + 204984 + 1544) 8 &&& ((2 ^ 64 - 1) ^^^ 2 ^ (bin % 64)) = 0 := by
      rw [hw]; exact hz
    refine ⟨?ω', ?μ', ?run, ?post⟩
    case run => pvm_go [h1, h10, h7, h3, h64, h112, hwr, hr, bitwise_and_m63, rdN_mod64, hc1, hc2, hz',
      rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
    case post =>
      refine ⟨?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_, ?_, ?_, by reg_frame⟩
      all_goals try rd_simp [hwr, hz, hw, hp]
      all_goals try (simp [Num.decodeLE]; done)
      all_goals try reg_val
      all_goals try rw [show Num.decodeLE (μ.readN (sp + 112) 8) = n from h112]
      all_goals try rw [show Num.decodeLE (μ.readN (sp + 64) 8) = N from h64]
      all_goals try rw [show Num.decodeLE (μ.readN 206832 8) = pri from hp]
      all_goals try rw [show Num.decodeLE (μ.readN (204984 + 1848) 8) = pri from hp]
      all_goals try rw [show Num.decodeLE (μ.readN (bin / 64 * 8 + 204984 + 1544) 8) = w from hw]
      all_goals try rw [show (18446744073709551615 : Nat) = 2 ^ 64 - 1 from rfl]
      all_goals try rw [Nat.mod_eq_of_lt (show _ < 18446744073709551616 from clear_lt _ _ hp64)]
      all_goals try rw [Nat.mod_eq_of_lt (show _ < 18446744073709551616 from clear_lt _ _ hw64)]
      all_goals try rw [Nat.mod_eq_of_lt (show _ < 2 ^ (8 * 8) from clear_lt _ _ hp64)]
      all_goals try rw [Nat.mod_eq_of_lt (show _ < 2 ^ (8 * 8) from clear_lt _ _ hw64)]
  · have hz' : ¬ rdN μ (bin / 64 * 8 + 204984 + 1544) 8 &&& ((2 ^ 64 - 1) ^^^ 2 ^ (bin % 64)) = 0 := by
      rw [hw]; exact hz
    refine ⟨?ω'', ?μ'', ?run', ?post'⟩
    case run' => pvm_go [h1, h10, h7, h3, h64, h112, hwr, hr, bitwise_and_m63, rdN_mod64, hc1, hz',
      rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
    case post' =>
      refine ⟨?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_, ?_, ?_, by reg_frame⟩
      all_goals try rd_simp [hwr, hz, hw, hp]
      all_goals try (simp [Num.decodeLE]; done)
      all_goals try reg_val
      all_goals try rw [show Num.decodeLE (μ.readN (sp + 112) 8) = n from h112]
      all_goals try rw [show Num.decodeLE (μ.readN (sp + 64) 8) = N from h64]
      all_goals try rw [show Num.decodeLE (μ.readN 206832 8) = pri from hp]
      all_goals try rw [show Num.decodeLE (μ.readN (bin / 64 * 8 + 204984 + 1544) 8) = w from hw]
      all_goals try rw [show (18446744073709551615 : Nat) = 2 ^ 64 - 1 from rfl]
      all_goals try rw [Nat.mod_eq_of_lt (show _ < 18446744073709551616 from clear_lt _ _ hp64)]
      all_goals try rw [Nat.mod_eq_of_lt (show _ < 18446744073709551616 from clear_lt _ _ hw64)]
      all_goals try rw [Nat.mod_eq_of_lt (show _ < 2 ^ (8 * 8) from clear_lt _ _ hp64)]
      all_goals try rw [Nat.mod_eq_of_lt (show _ < 2 ^ (8 * 8) from clear_lt _ _ hw64)]

end Services.Bootstrap.Alloc
