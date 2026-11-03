import PVM.Logic.Steps

/-!
# Chasing facts through composed runs

Composing proved pieces of a run (segments, summaries) means proving each piece's hypotheses
from what the earlier pieces guarantee: register equations, octets they leave, frames
`∀ a, cond a = true → μ'.read a = μ.read a`, and unchanged page access. `chase` does this with
`simp`, using every hypothesis in the context as a (conditional) rewrite: an octet read of the
last memory steps back through the frames whose condition holds at that address (decided for
concrete addresses, by `omega` for symbolic ones) until a fact states it. `chase_prep` first
splits word facts `μ.readN a n = bs` into octet facts.
-/

namespace PVM

theorem Memory.readN_succ' (μ : Memory) (a n : Nat) :
    μ.readN a (n + 1) = μ.read a :: μ.readN (a + 1) n := by
  simp only [Memory.readN, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro j _
  simp [Function.comp, Nat.add_assoc, Nat.add_comm 1 j]

theorem Memory.readN_zero' (μ : Memory) (a : Nat) : μ.readN a 0 = [] := rfl

/-- An octet of a copy: inside `μ.writeN a (μ'.readN b n)`, the octet copied from `b`. -/
theorem Memory.read_writeN_readN (μ μ' : Memory) (a b n c : Nat) (h1 : a ≤ c) (h2 : c < a + n)
    (hn : n ≤ two32) : (μ.writeN a (μ'.readN b n)).read c = μ'.read (b + (c - a)) := by
  have h := Memory.read_writeN_at μ a (μ'.readN b n) (by simp [Memory.length_readN]; omega) (c - a)
    (by simp [Memory.length_readN]; omega)
  rw [show a + (c - a) = c by omega] at h
  rw [h]
  simp [Memory.readN]

/-- The side conditions of `chase`'s rewrites: a frame condition at a concrete address by
    evaluation, at a symbolic one by `omega`; arithmetic by `omega`. -/
macro "chase_disch" : tactic => `(tactic| first
  | decide
  | (simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
      not_and, Nat.not_lt, Memory.length_readN, Num.length_encodeLE, List.length_cons,
      List.length_nil, two32] <;> omega)
  | omega)

/-- Split word facts `μ.readN a n = bs` into octet facts: in the goal, or at the given
    hypotheses (once, when they are introduced, so later goals find them split). -/
syntax "chase_prep" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| chase_prep $[$loc]?) => `(tactic|
      try simp only [Memory.readN_succ', Memory.readN_zero', Num.encodeLE, List.cons.injEq, and_true,
        Nat.reduceAdd, Nat.add_zero] $[$loc]?)

/-- Close an octet equation `UInt8.ofNat e = c` by arithmetic on `e mod 2^8`. -/
macro "chase_octet" : tactic => `(tactic| first
  | rfl
  | decide
  | (apply UInt8.toNat_inj.mp
     simp only [UInt8.toNat_ofNat', UInt8.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
     omega))

/-- Prove a register, octet, word or access fact of the last state from the facts in context. -/
macro "chase" : tactic => `(tactic| first
  | assumption
  | (simp (disch := chase_disch) only [*, Memory.readN_succ', Memory.readN_zero', Num.encodeLE,
      List.cons.injEq, and_true, Nat.reduceAdd, Nat.add_zero, Memory.writable_writeN,
      Memory.readable_writeN, Memory.read_writeN_disjoint, Memory.read_writeN_readN,
      Num.length_encodeLE, Memory.length_readN, Nat.reduceSub, UInt64.toNat_ofNat',
      Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.mod_eq_of_lt, Nat.div_eq_of_lt, Nat.zero_div,
      UInt8.reduceOfNat, List.length_cons, List.length_nil, two32] <;> chase_octet)
  | chase_octet
  | (intro a h1 h2; simp (disch := chase_disch) only [*, Memory.writable_writeN,
      Memory.readable_writeN]; done)
  | (intro a h1 h2; simp (disch := chase_disch) only [*, Memory.writable_writeN,
      Memory.readable_writeN]
     first | exact Memory.readable_of_writable (by simp (disch := chase_disch) only [*]) | done))

end PVM
