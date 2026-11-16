import PVM.SymExec.Sound

/-!
# One-operation values (symexec)

The value of one ALU operation (§A.5.10, §A.5.13) on named naturals, under the bounds that make it
exact: shifts, multiplications and subtractions that neither overflow nor sign-extend, `and` with
2046, and the sign-extended u32 (𝒳_4) at or above 2^31. A check's rewrites (`Static.rw`) replace
such an operation by a fresh named natural; these lemmas prove each rewrite (`RwHold`).
-/

namespace PVM.SymExec

open Num Exec


theorem op_shloL {E : Env} {a s : Nat} (hs : s < 64) (h : E.ρ a * 2 ^ s < 2 ^ 63) :
    (SVal.alu2i .shloLImm64 (.const 0) (.var a) s).eval E = E.ρ a * 2 ^ s := by
  rw [SVal.eval, alu_shloL, Option.getD_some, SVal.eval, Nat.mod_eq_of_lt hs,
    Nat.mod_eq_of_lt (by simp only [two64]; omega), sext8_id (by simp only [two64]; omega)]

theorem op_shloLm {E : Env} {a s : Nat} (hs : s < 64) (h : E.ρ a * 2 ^ s % 2 ^ 64 < 2 ^ 63) :
    (SVal.alu2i .shloLImm64 (.const 0) (.var a) s).eval E = E.ρ a * 2 ^ s % 2 ^ 64 := by
  rw [SVal.eval, alu_shloL, Option.getD_some, SVal.eval, Nat.mod_eq_of_lt hs,
    sext8_id (by simp only [two64]; omega)]

theorem op_shloR {E : Env} {a s : Nat} (hs : 0 < s ∧ s < 64) (h : E.ρ a < 2 ^ 64) :
    (SVal.alu2i .shloRImm64 (.const 0) (.var a) s).eval E = E.ρ a / 2 ^ s := by
  rw [SVal.eval, alu_shloR, Option.getD_some, SVal.eval, Nat.mod_eq_of_lt hs.2]
  have : E.ρ a / 2 ^ s ≤ E.ρ a / 2 := Nat.div_le_div_left (Nat.le_trans (by decide) (Nat.pow_le_pow_right (by decide) hs.1)) (by decide)
  rw [sext8_id (by simp only [two64]; omega)]

theorem op_mulU {E : Env} {a c : Nat} :
    (SVal.alu3 .mulUpperUU (.var a) (.const c) (.const 0)).eval E = E.ρ a * c / 2 ^ 64 := by
  simp only [SVal.eval, threeRegAlu, two64]

theorem op_mul {E : Env} {a c : Nat} (h : E.ρ a * c < 2 ^ 64) :
    (SVal.alu3 .mul64 (.var a) (.const c) (.const 0)).eval E = E.ρ a * c := by
  simp only [SVal.eval, threeRegAlu]; exact Nat.mod_eq_of_lt (by simp only [two64]; omega)

theorem alu_mulImm64 (a b x : Nat) : twoRegImmAlu .mulImm64 a b x = some ((b * x) % two64) := rfl

theorem op_mulI {E : Env} {a c : Nat} (h : E.ρ a * c < 2 ^ 64) :
    (SVal.alu2i .mulImm64 (.const 0) (.var a) c).eval E = E.ρ a * c := by
  rw [SVal.eval, alu_mulImm64, Option.getD_some, SVal.eval]
  exact Nat.mod_eq_of_lt (by simp only [two64]; omega)

theorem op_sub {E : Env} {a b : Nat} (h : E.ρ b ≤ E.ρ a) (ha : E.ρ a < 2 ^ 64) :
    (SVal.alu3 .sub64 (.var a) (.var b) (.const 0)).eval E = E.ρ a - E.ρ b := by
  simp only [SVal.eval, threeRegAlu, two64]; omega


theorem bitwise_and_2046 (x : Nat) : bitwise (· && ·) x 2046 = x / 2 % 1024 * 2 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [bitwise, Num.testBit_ofBits, Num.bit_eq_testBit]
  simp only [Nat.testBit_eq_decide_div_mod_eq]
  rcases (show i < 11 ∨ 11 ≤ i by omega) with hi | hi
  · rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i
    all_goals simp only [← Bool.decide_and, decide_eq_decide, Nat.reduceAdd, Nat.reducePow, Nat.reduceDiv, Nat.reduceMod, and_true, Nat.reduceLT, true_and]
    all_goals omega
  · have h1 : (2046 : Nat) / 2 ^ i = 0 := Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) hi))
    have h2 : x / 2 % 1024 * 2 / 2 ^ i = 0 := Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (by omega) (Nat.pow_le_pow_right (by decide) hi))
    simp [h1, h2]

theorem op_and2046 {E : Env} {a : Nat} :
    (SVal.alu2i .andImm (.const 0) (.var a) 2046).eval E = E.ρ a / 2 % 1024 * 2 := by
  rw [SVal.eval, alu_andImm, Option.getD_some, SVal.eval, bitwise_and_2046]

theorem alu_shloL32 (a b x : Nat) :
    twoRegImmAlu .shloLImm32 a b x = some (sext 4 ((b * 2 ^ (x % 32)) % two32)) := rfl

theorem op_shloL32 {E : Env} {a : Nat} (h : E.ρ a < 2 ^ 30) :
    (SVal.alu2i .shloLImm32 (.const 0) (.var a) 1).eval E = 2 * E.ρ a := by
  rw [SVal.eval, alu_shloL32, Option.getD_some, SVal.eval, show (2 : Nat) ^ (1 % 32) = 2 from rfl,
    Nat.mod_eq_of_lt (by simp only [two32]; omega), sext4_small (by omega)]; omega



theorem sx4_big {x : Nat} (h1 : 2 ^ 31 ≤ x) (h2 : x < 2 ^ 32) : u64 (signed 4 x) = x + 18446744069414584320 := by
  unfold u64 unsigned signed
  rw [if_neg (by show ¬ x < 2 ^ 31; omega)]
  show ((2 ^ 64 + ((x : Int) - 2 ^ 32)) % (2 ^ 64 : Int)).toNat = _
  omega

theorem op_shloL_sx {E : Env} {a : Nat} (h1 : 2 ^ 31 ≤ E.ρ a) (h2 : E.ρ a < 2 ^ 32) :
    (SVal.alu2i .shloLImm64 (.const 0) (.sx 4 (.var a)) 32).eval E = E.ρ a * 4294967296 := by
  rw [SVal.eval, alu_shloL, Option.getD_some, SVal.eval, SVal.eval, sx4_big h1 h2,
    show (2 : Nat) ^ (32 % 64) = 4294967296 from rfl]
  rw [sext8_id (by simp only [two64]; omega)]
  simp only [two64]; omega

theorem op_sub_sx {E : Env} {a b : Nat} (h1 : 2 ^ 31 ≤ E.ρ a) (h2 : E.ρ a < 2 ^ 32) (hb : E.ρ b ≤ E.ρ a) :
    (SVal.alu3 .sub64 (.sx 4 (.var a)) (.var b) (.const 0)).eval E = E.ρ a + 18446744069414584320 - E.ρ b := by
  have e : (SVal.sx 4 (.var a)).eval E = E.ρ a + 18446744069414584320 := by
    rw [SVal.eval, SVal.eval, sx4_big h1 h2]
  rw [SVal.eval, e, SVal.eval, SVal.eval]
  simp only [threeRegAlu, two64]; omega

/-- The high-pair offset of a four-digit block r: (r/4 · 5243 / 2^16) & 2046 = 2 · (r / 100). -/
theorem idx_hi (r : Nat) (h : r < 10000) : r / 4 * 5243 / 65536 / 2 % 1024 * 2 = 2 * (r / 100) := by
  have e1 : r / 4 * 5243 / 65536 / 2 = r / 4 * 5243 / 131072 := by rw [Nat.div_div_eq_div_mul]
  have e2 : r / 4 * 5243 / 131072 = r / 100 := by omega
  rw [e1, e2, Nat.mod_eq_of_lt (by omega)]; omega

end PVM.SymExec
