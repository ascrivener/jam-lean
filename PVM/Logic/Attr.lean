import Lean

/-!
# The `pvm_code` simp set

Facts about one specific program (its decoded instructions, block starts, jump-table entries),
proved from a `checkCode` hypothesis and tagged `@[pvm_code]` so the stepper can use them.
-/

/-- Code facts about a specific program, for `simp`. -/
register_simp_attr pvm_code
