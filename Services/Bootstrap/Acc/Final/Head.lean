import Services.Bootstrap.Acc.Items.Head
import Services.Bootstrap.Acc.Items.End
import Services.Bootstrap.Acc.Items.Exit

/-!
# The items loop's head, for T2's composition

- `il_head2`: `Acc.il_head` (6674 … 6782, n > 0 items) with a finer frame: sp + 128 … 144 (the
  formatter word at sp + 136 the transfer arm reads) is kept.
- `il_head0` / `items_none_halt`: with no items (n = 0, GP v0.8.0 §12: nothing to accumulate), 6674
  jumps to 15215, finds the cursor at the end (15316), frees nothing (capacity 0) and returns
  (ω₇, ω₈) = (0, 0): the run halts with an empty output.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **6674 … 6782**, as `il_head`, with sp + 128 … 144 kept. -/
theorem il_head2 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp n q c : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : 65536 ≤ sp ∧ sp + 1600 < 4294967296)
    (m0 : rdN μ (sp + 1568) 8 = c) (m8 : rdN μ (sp + 1576) 8 = q) (m16 : rdN μ (sp + 1584) 8 = n)
    (hn : 0 < n ∧ n ≤ 89) (hq : q + 184 * n < 2147483648)
    (hwf : ∀ a, sp ≤ a → a < sp + 1600 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 6674 ω μ x 6782 ω' μ' x 30 ∧
      ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat q ∧ ω'[11] = UInt64.ofNat q ∧
      rdN μ' (sp + 144) 8 = q + 184 * n ∧ rdN μ' (sp + 16) 8 = q ∧ rdN μ' (sp + 32) 8 = c ∧
      rdN μ' (sp + 184) 8 = 9223372036854775808 ∧ rdN μ' (sp + 216) 8 = 9223372036854775809 ∧
      (∀ a, a < 4294967296 → (a < sp + 16 ∨ sp + 48 ≤ a) → (a < sp + 112 ∨ sp + 128 ≤ a) →
        (a < sp + 144 ∨ sp + 152 ≤ a) →
        (a < sp + 184 ∨ sp + 192 ≤ a) → (a < sp + 216 ∨ sp + 224 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp ≤ a → a < sp + 1600 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have hn' : n % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hc : c < 18446744073709551616 := by rw [← m0]; exact rdN_lt64 _ _
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, m0, m8, m16, hn', hwf, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val; simp [h1], by reg_val, by reg_val, ?_, ?_, ?_, ?_, ?_,
      fun a ha h1 h2 h3 h4 h5 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try (rd_simp []; done)
    all_goals try rd_simp []
    all_goals try with_reducible rfl
    all_goals try decide
    all_goals try (simp only [Nat.reduceMul, Nat.reducePow]; exact Nat.mod_eq_of_lt (by omega))
    all_goals try exact Nat.mod_eq_of_lt (by omega)
    all_goals try omega

/-- **6674 … 15215**, no items (the word at sp + 1584 is 0): the capacity c (sp + 1568) stored at
    sp + 32, the end q at sp + 144, q at sp + 16 and in ω₁₁. -/
theorem il_head0a {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp q c : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : 65536 ≤ sp ∧ sp + 1600 < 4294967296)
    (m0 : rdN μ (sp + 1568) 8 = c) (m8 : rdN μ (sp + 1576) 8 = q) (m16 : rdN μ (sp + 1584) 8 = 0)
    (hwf : ∀ a, sp ≤ a → a < sp + 1600 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 6674 ω μ x 15215 ω' μ' x 20 ∧
      ω'[1] = UInt64.ofNat sp ∧ ω'[11] = UInt64.ofNat q ∧ rdN μ' (sp + 32) 8 = c ∧
      rdN μ' (sp + 144) 8 = q ∧
      (∀ a, a < 4294967296 → (a < sp + 16 ∨ sp + 24 ≤ a) → (a < sp + 32 ∨ sp + 40 ≤ a) →
        (a < sp + 144 ∨ sp + 152 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp ≤ a → a < sp + 1600 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have hc : c < 18446744073709551616 := by rw [← m0]; exact rdN_lt64 _ _
  have hq : q < 18446744073709551616 := by rw [← m8]; exact rdN_lt64 _ _
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, m0, m8, m16, hwf, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val; simp [h1], by reg_val, ?_, ?_, fun a ha h1 h2 h3 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try (rd_simp []; done)
    all_goals try rd_simp []
    all_goals try with_reducible rfl
    all_goals try exact Nat.mod_eq_of_lt (by omega)
    all_goals try omega

/-- **15215 … 15316**: the cursor ω₁₁ is the end (sp + 144). -/
theorem il_15215_end {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp q : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : 65536 ≤ sp ∧ sp + 1600 < 4294967296)
    (h11 : ω[11] = UInt64.ofNat q) (m144 : rdN μ (sp + 144) 8 = q)
    (hr : ∀ a, sp ≤ a → a < sp + 1600 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 15215 ω μ x 15316 ω' μ x 3 ∧ ω'[1] = ω[1] := by
  have hq : q < 18446744073709551616 := by rw [← m144]; exact rdN_lt64 _ _
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, h11, m144, hr, ↓rdN_fold, ↓loadI_fold]
  case post => reg_val

/-- **No items: the run halts** from 6674 with an empty output (ω₈ = 0), given the saved return
    address 2³² − 2¹⁶ at sp + 1848 and the decoded `Vec { 0, q, 0 }` at sp + 1568. -/
theorem items_none_halt {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp q : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : 65536 ≤ sp ∧ sp + 1856 < 4294967296)
    (m0 : rdN μ (sp + 1568) 8 = 0) (m8 : rdN μ (sp + 1576) 8 = q) (m16 : rdN μ (sp + 1584) 8 = 0)
    (m1848 : rdN μ (sp + 1848) 8 = 4294901760)
    (hwf : ∀ a, sp ≤ a → a < sp + 1856 → μ.writable a = true) :
    ∃ ω' μ', FreeRunH p R 6674 ω μ x .halt ω' μ' x ∧ (ω'.get 8).toNat = 0 := by
  obtain ⟨ω0, μ1, run0, a1', a11, a32, a144, fr1, rd1, wr1⟩ := il_head0a (p := p) (P := P) (R := R) x ω μ sp q 0 h1
    ⟨hsp.1, by omega⟩ m0 m8 m16 (fun a h1 h2 => hwf a h1 (by omega))
  obtain ⟨ω1, run1', e1⟩ := il_15215_end (p := p) (P := P) (R := R) x ω0 μ1 sp q a1' ⟨hsp.1, by omega⟩ a11 a144
    (fun a h1 h2 => by rw [rd1]; exact Memory.readable_of_writable (hwf a h1 (by omega)))
  have a1 : ω1[1] = UInt64.ofNat sp := e1.trans a1'
  have run1 := run0.trans run1'
  have hrf : ∀ a, sp ≤ a → a < sp + 1856 → μ1.readable a = true := fun a h1 h2 => by
    rw [rd1]; exact Memory.readable_of_writable (hwf a h1 h2)
  obtain ⟨ω2, run2, f2⟩ := il_end_nofree (p := p) (P := P) (R := R) x ω1 μ1 sp a1 hsp a32 hrf
  obtain ⟨ω3, run3, g7, g8, -, g0, -⟩ := il_ret (p := p) (P := P) (R := R) x ω2 μ1 sp
    ((f2 1 (by decide)).trans a1) hsp hrf
  have k : rdN μ1 (sp + 1848) 8 = 4294901760 := by
    rw [rdN_frame fun j hj => fr1 _ (by omega) (.inr (by omega)) (.inr (by omega)) (.inr (by omega))]
    exact m1848
  refine ⟨ω3, μ1, (run1.trans (run2.trans run3)).run
    (.exit (.exit (halt_15359 (P := P) ω3 μ1 (by rw [g0, k]))) (by simp)), ?_⟩
  show (ω3[8]).toNat = 0
  rw [g8]; rfl

end Services.Bootstrap.Acc
