import PVM.SymExec.Sound
open PVM PVM.SymExec Num Exec
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
