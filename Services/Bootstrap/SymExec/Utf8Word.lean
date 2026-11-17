import Services.Bootstrap.SymExec.ProgU
import Services.Bootstrap.SymExec.Utf8Byte
import PVM.SymExec.Loop

/-!
# `core::str::from_utf8` (60681): the word loop 60759 (symexec, loops)

EXPERIMENTAL (see `Services/Bootstrap/SymExec/README.md`). The aligned fast path of Rust's
`run_utf8_validation` checks 16 octets per iteration (GP v0.8.0 §A.5.13 `add_64`, `or`, `and`;
§A.5.10 `load_ind_u64`; §A.5.8 `branch_ne_imm`; §A.5.11 `branch_lt_u`):

    60759: r10 := r8 + r5; r6 := ℰ₈⁻¹(μ[r10..+8]); r10 := ℰ₈⁻¹(μ[r10+8..+8])
           r12 := 0x8080…80; r10 := r6 | r10; r10 := r12 & r10
           if r10 ≠ 0 goto 60793; r5 := r5 + 16; if r5 <ᵤ r4 goto 60759; goto 60793

Here r8 = p (the input), r5 = i (the index), r9 = len, and r4 = len − 15 (the case len ≥ 15 of the
pre-loop segment). `word_loop` proves, by one forking check and loop induction
(`loop_fork_soundX`), that from the header (with i + 16 ≤ len) the machine reaches 60793 with
i ≤ len, changing no register but r5, r6, r10 and r12, and no memory; either len ≤ i + 15, or the
16 octets at q = p + i (in the start memory) have a set top bit (`maskV` ≠ 0).

Named naturals as in `Utf8Byte`: 0 p, 1 len, 2 i, 3 q, 4 sp, 5 the alignment offset (r0), 6 (unused),
7 r11, 8 the saved return address, 9 and 10 the saved r5 and r6, 11 r7, 12 e = p + len, 13 and 14
(unused).
-/

namespace Services.Bootstrap.SymExec.Utf8

open PVM PVM.SymExec Num Exec

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- Upper bounds of the named naturals: q + 31 < 2^32 inside the loop. -/
def ub2 : List Nat :=
  [2^32, 2^32, 2^32, 2^32 - 15, 2^32 - 32, 8, 2^32, 2^64, 2^64, 2^64, 2^64, 2^32, 2^32 + 1, 2^64, 2^32]
/-- The bounds at the loop's exit: q may reach 2^32. -/
def ub2x : List Nat :=
  [2^32, 2^32, 2^32, 2^32 + 1, 2^32 - 32, 8, 2^32, 2^64, 2^64, 2^64, 2^64, 2^32, 2^32 + 1, 2^64, 2^32]
/-- Lower bounds: len ≥ 15 (so r4 = len − 15 does not wrap). -/
def lb2 : List Nat := [0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The header cut at 60759: registers (r4 = len − 15), the four saved stack words, the frame
    (sp, 32). r6, r10 and r12 are scratch. -/
def H2 : Cut :=
  ⟨[(0, vr 5), (1, vr 4), (3, .const 1), (4, .addr (af 1 (-15))), (5, vr 2), (7, vr 11), (8, vr 0),
    (9, vr 1), (11, vr 7)],
   [(af 4 24, 8, vr 8), (af 4 16, 8, vr 9), (af 4 8, 8, vr 10), (af 4 0, 8, .const 71078)],
   [], [], [(af 4 0, 32)]⟩

/-- q = p + i, i + 16 ≤ len, e = p + len, [p, e) readable. -/
def asm2 : List Fact := [.sum 0 2 3, .le (af 2 1) (af 1 (-15)), .sum 0 1 12, .rd (af 0 0) (af 12 0)]

/-- The top bits of the 16 octets at q: (w₀ | w₁) & 0x8080…80, w₀ and w₁ the two words at q, q + 8. -/
def maskV : SVal :=
  .mod (.alu3 .and (.mod (.alu3 .or (.mem0 (af 3 8) 8) (.mem0 (af 3 0) 8) (.const 0)) (2^64))
    (.const 9259542123273814144) (.const 0)) (2^64)

/-- The next iteration's named naturals: i + 16, q + 16. -/
def nxt2 : List SVal :=
  [vr 0, vr 1, .addr (af 2 16), .addr (af 3 16), vr 4, vr 5, vr 6, vr 7, vr 8, vr 9, vr 10, vr 11,
    vr 12, vr 13, vr 14]

/-- The leaves of the body: a set top bit, the back edge, and the end (i + 16 ≥ len − 15). -/
def leaves2 : List Leaf :=
  [⟨60793, [.ne maskV 0], H2, idsub15⟩,
   ⟨60759, [.le (af 2 17) (af 1 (-15)), .ge maskV 0, .lt maskV 1], H2, nxt2⟩,
   ⟨60793, [.le (af 1 (-15)) (af 2 16), .ge maskV 0, .lt maskV 1], H2, nxt2⟩]

theorem check2 : forkCheck progU ub2 lb2 [] H2 asm2 leaves2 60759 100 = true := by
  decide +kernel

/-- The named naturals the word loop does not change (all but i and q). -/
def keep2 : List Nat := [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]

/-- What the loop keeps that the executor does not track: r11 = 2^64 − len, and the input
    [p, p + len) apart from the stack frame [sp, sp + 32); and, against the named naturals `v₀` at
    the loop's start (a ghost), every named natural but i and q unchanged and i not below its
    start. -/
def I2 (v₀ vals : List Nat) : Prop :=
  vals.getD 7 0 + vals.getD 1 0 = 2 ^ 64 ∧
  (vals.getD 0 0 + vals.getD 1 0 ≤ vals.getD 4 0 ∨ vals.getD 4 0 + 32 ≤ vals.getD 0 0) ∧
  Keep keep2 v₀ vals ∧ v₀.getD 2 0 ≤ vals.getD 2 0

/-- The measure: len − i. -/
def meas2 (vals : List Nat) : Nat := vals.getD 1 0 - vals.getD 2 0

/-- Where the loop ends: at 60793, the header cut with some named naturals satisfying `I2`, the
    bounds `ub2x`, q = p + i, e = p + len and i ≤ len; either len ≤ i + 15, or i + 16 ≤ len and the
    16 octets at q in the start memory μ₀ have a set top bit. -/
def Q2 (μ₀ : Memory) (v₀ : List Nat) (pc : Nat) (ω : Regs) (μ : Memory) : Prop :=
  ∃ vals, H2.Holds vals μ₀ ω μ ∧ BHold vals ub2x ∧ LBHold vals lb2 ∧ I2 v₀ vals ∧
    vals.getD 0 0 + vals.getD 2 0 = vals.getD 3 0 ∧ vals.getD 0 0 + vals.getD 1 0 = vals.getD 12 0 ∧
    pc = 60793 ∧ vals.getD 2 0 ≤ vals.getD 1 0 ∧
    (vals.getD 1 0 ≤ vals.getD 2 0 + 15 ∨
     (vals.getD 2 0 + 16 ≤ vals.getD 1 0 ∧ maskV.eval (env vals ω μ₀) ≠ 0))

theorem readN_frame {μ μ₀ : Memory} {a n : Nat} (h : ∀ k, k < n → μ.read (a + k) = μ₀.read (a + k)) :
    μ.readN a n = μ₀.readN a n := by
  simp only [Memory.readN]
  exact List.map_congr_left (fun k hk => h k (List.mem_range.mp hk))

theorem obl2 (μ₀ : Memory) (v₀ : List Nat) :
    ∀ ℓ ∈ leaves2, LoopOblX ub2 lb2 H2 asm2 μ₀ (I2 v₀) meas2 60759 (Q2 μ₀ v₀) ℓ := by
  simp only [leaves2, List.mem_cons, List.not_mem_nil, or_false]
  rintro ℓ (rfl | rfl | rfl) <;> intro vals ω μ hI hB hLB hF hH hf <;>
    rcases vals with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8, _ | ⟨a9, _ | ⟨a10, _ | ⟨a11, _ | ⟨a12, _ | ⟨a13, _ | ⟨a14, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    (try (simp [BHold, ub2] at hB; done)) <;> simp only [BHold, ub2] at hB <;>
    simp only [LBHold, lb2] at hLB <;>
    simp only [I2, List.getD_cons_succ, List.getD_cons_zero] at hI <;>
    simp only [asm2, FactsHold, Fact.Holds, Aff.eval, env, List.getD_cons_succ,
      List.getD_cons_zero, af] at hF
  all_goals
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, -⟩ := hB
    obtain ⟨-, l1, -⟩ := hLB
    obtain ⟨h2, h3, hK, h5⟩ := hI
    obtain ⟨f1, f2, f3, f4, -⟩ := hF
  · -- a set top bit
    simp only [FactsHold, Fact.Holds] at hf
    obtain ⟨g1, -⟩ := hf
    right
    intro ω' μ' hB'
    refine ⟨_, hB', ?_⟩
    have hm : maskV.eval (env (svals (env [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13,
        a14] ω μ) idsub15) ω' μ₀) = maskV.eval (env [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11,
        a12, a13, a14] ω μ) := by
      have hfr : ∀ t, a3 ≤ t → t < a3 + 16 → μ.read t = μ₀.read t := fun t ht1 ht2 =>
        (hH.2.2.2.2.1 t (by simp only [two32]; omega) (by
          simp only [H2, List.mem_cons, List.not_mem_nil, or_false, forall_eq, InReg, Aff.eval, env,
            List.getD_cons_succ, List.getD_cons_zero, af]
          omega)).symm ▸ rfl
      simp only [maskV, svals, idsub15, List.map, SVal.eval, Aff.eval, env, List.getD_cons_succ,
        List.getD_cons_zero, af]
      rw [readN_frame (μ := μ) (μ₀ := μ₀) (a := ((a3 : Int) + 8).toNat) (n := 8) (fun k hk =>
            hfr _ (by omega) (by omega)),
          readN_frame (μ := μ) (μ₀ := μ₀) (a := ((a3 : Int) + 0).toNat) (n := 8) (fun k hk =>
            hfr _ (by omega) (by omega))]
    rw [hm]
    simp only [svals, idsub15, List.map, SVal.eval, I2, BHold, ub2x, LBHold, lb2, env,
      List.getD_cons_succ, List.getD_cons_zero]
    exact ⟨⟨b0, b1, b2, by omega, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, trivial⟩,
      ⟨Nat.zero_le _, l1, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
        Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
        Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, trivial⟩,
      ⟨h2, h3, keep_of hK (by simp [keep2]), by omega⟩, f1, f3, trivial, by omega, Or.inr ⟨by omega, g1⟩⟩
  · -- the back edge
    simp only [FactsHold, Fact.Holds, Aff.eval, env, List.getD_cons_succ, List.getD_cons_zero] at hf
    obtain ⟨g1, -⟩ := hf
    left
    refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [svals, nxt2, List.map, SVal.eval, Aff.eval, af, I2, BHold, ub2, LBHold, lb2, asm2,
        FactsHold, Fact.Holds, env, meas2, List.getD_cons_succ, List.getD_cons_zero]
    · exact ⟨h2, h3, keep_of hK (by simp [keep2]), by omega⟩
    · exact ⟨b0, b1, by omega, by omega, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, trivial⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> omega
    · exact ⟨by omega, by omega, f3, f4, trivial⟩
    · omega
  · -- the end: i + 16 ≥ len − 15
    simp only [FactsHold, Fact.Holds, Aff.eval, env, List.getD_cons_succ, List.getD_cons_zero] at hf
    obtain ⟨g1, -⟩ := hf
    right
    intro ω' μ' hB'
    refine ⟨_, hB', ?_⟩
    simp only [svals, nxt2, List.map, SVal.eval, Aff.eval, af, I2, BHold, ub2x, LBHold, lb2, env,
      List.getD_cons_succ, List.getD_cons_zero]
    refine ⟨⟨b0, b1, by omega, by omega, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, trivial⟩,
      ?_, ⟨h2, h3, keep_of hK (by simp [keep2]), by omega⟩, by omega, f3, trivial, by omega, Or.inl (by omega)⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> omega

/-- **The word loop of `from_utf8`** (60759): from its header (with i + 16 ≤ len) the machine reaches
    60793 with i ≤ len, and either len ≤ i + 15 or the 16 octets at q have a set top bit (`Q2`). -/
theorem word_loop {X : Type} {p : ByteArray} {R : HostRel X} {P : Program}
    [Services.Bootstrap.CodeF.HasCodeF p P] [Services.Bootstrap.Code.HasCode p P]
    {μ₀ : Memory} (v₀ : List Nat) (x : X) :
    ∀ vals ω μ, I2 v₀ vals → BHold vals ub2 → LBHold vals lb2 → FactsHold (env vals ω μ) asm2 →
      H2.Holds vals μ₀ ω μ →
      ∃ xpc k ω' μ', FreeStepsH p R 60759 ω μ x xpc ω' μ' x k ∧ Q2 μ₀ v₀ xpc ω' μ' :=
  loop_fork_soundX check2 (by decide) (hypU (p := p) (P := P)) trivial (fun _ _ _ _ => trivial)
    (obl2 μ₀ v₀) x

end Services.Bootstrap.SymExec.Utf8
