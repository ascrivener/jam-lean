import Services.Bootstrap.SymExec.ProgU
import PVM.SymExec.Loop

/-!
# `core::str::from_utf8` (60681): the byte loop 60803 (symexec, loops)

EXPERIMENTAL (see `Services/Bootstrap/SymExec/README.md`). The tail loop of Rust's
`run_utf8_validation` checks one octet per iteration (GP v0.8.0 §A.5.10 `load_ind_i8`, §A.5.8
`branch_lt_s_imm`, §A.5.11 `branch_ne`):

    60803: r12 := 𝒳₁(μ[r10]); if r12 <ₛ 0 goto 60943
           r6 := r6 − 1; r10 := r10 + 1; if r11 ≠ r6 goto 60803; goto 61086

With p the input, len its length, i the index and q = p + i, the loop keeps r10 = q and
r6 = 2^64 − i, and r11 = 2^64 − len. `byte_loop` proves, by one forking check and loop induction
(`loop_fork_soundX`), that from the header the machine reaches 61086 with i = len, or 60943 at an
index i < len whose octet is at least 0x80, in both cases changing no register but r6, r10 and r12,
and no memory.

Named naturals: 0 p, 1 len, 2 i, 3 q, 4 sp, 5 the alignment offset (r0), 6 r4, 7 r11, 8 the saved
return address, 9 and 10 the saved r5 and r6, 11 r7, 12 e = p + len, 13 r6, 14 r5.
-/

namespace Services.Bootstrap.SymExec.Utf8

open PVM PVM.SymExec Num Exec

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- The named natural `k`. -/
abbrev vr (k : Nat) : SVal := .var k
/-- ρ_k + o. -/
abbrev af (k : Nat) (o : Int) : Aff := ⟨some k, o⟩

/-- The identity substitution on the 15 named naturals. -/
def idsub15 : List SVal :=
  [vr 0, vr 1, vr 2, vr 3, vr 4, vr 5, vr 6, vr 7, vr 8, vr 9, vr 10, vr 11, vr 12, vr 13, vr 14]

/-- The octet at q, sign-extended (the path facts' value). -/
def byteQ : SVal := .sx 1 (.mem0 (af 3 0) 1)

/-- Upper bounds of the named naturals. -/
def ub3 : List Nat :=
  [2^32, 2^32, 2^32, 2^32, 2^32 - 32, 8, 2^32, 2^64, 2^64, 2^64, 2^64, 2^32, 2^32 + 1, 2^64, 2^32]
/-- Lower bounds: r6 = 2^64 − i is at least 2^64 − 2^32. -/
def lb3 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2^64 - 2^32, 0]

/-- The header cut at 60803: registers, the four saved stack words, the frame (sp, 32). -/
def H3 : Cut :=
  ⟨[(0, vr 5), (1, vr 4), (3, .const 1), (4, vr 6), (5, vr 14), (6, vr 13), (7, vr 11), (8, vr 0),
    (9, vr 1), (10, vr 3), (11, vr 7)],
   [(af 4 24, 8, vr 8), (af 4 16, 8, vr 9), (af 4 8, 8, vr 10), (af 4 0, 8, .const 71078)],
   [], [], [(af 4 0, 32)]⟩

/-- q = p + i, e = p + len, [p, e) readable, i < len. -/
def asm3 : List Fact := [.sum 0 2 3, .le (af 2 1) (af 1 0), .sum 0 1 12, .rd (af 0 0) (af 12 0)]

/-- The next iteration's named naturals: i + 1, q + 1, r6 − 1. -/
def nxt3 : List SVal :=
  [vr 0, vr 1, .addr (af 2 1), .addr (af 3 1), vr 4, vr 5, vr 6, vr 7, vr 8, vr 9, vr 10, vr 11, vr 12,
    .addr (af 13 (-1)), vr 14]

/-- The leaves of the body: the back edge, the end (r11 = r6), and an octet ≥ 0x80. -/
def leaves3 : List Leaf :=
  [⟨60803, [.neA (af 7 0) (af 13 (-1)), .lt byteQ (2^63)], H3, nxt3⟩,
   ⟨61086, [.le (af 7 0) (af 13 (-1)), .le (af 13 (-1)) (af 7 0), .lt byteQ (2^63)], H3, nxt3⟩,
   ⟨60943, [.ge byteQ (2^63)], H3, idsub15⟩]

theorem check3 : forkCheck progU ub3 lb3 [] H3 asm3 leaves3 60803 100 = true := by
  decide +kernel

/-- What the loop keeps that the executor does not track: r6 = 2^64 − i, r11 = 2^64 − len, and the
    input [p, p + len) apart from the stack frame [sp, sp + 32). -/
def I3 (vals : List Nat) : Prop :=
  vals.getD 13 0 + vals.getD 2 0 = 2 ^ 64 ∧ vals.getD 7 0 + vals.getD 1 0 = 2 ^ 64 ∧
  (vals.getD 0 0 + vals.getD 1 0 ≤ vals.getD 4 0 ∨ vals.getD 4 0 + 32 ≤ vals.getD 0 0)

/-- The measure: len − i. -/
def meas3 (vals : List Nat) : Nat := vals.getD 1 0 - vals.getD 2 0

/-- Where the loop ends: the header cut with some named naturals satisfying `I3`, the bounds and
    q = p + i, e = p + len; at 61086 with i = len, at 60943 with i < len and the octet at q (in the
    start memory μ₀) at least 0x80. -/
def Q3 (μ₀ : Memory) (pc : Nat) (ω : Regs) (μ : Memory) : Prop :=
  ∃ vals, H3.Holds vals μ₀ ω μ ∧ BHold vals ub3 ∧ LBHold vals lb3 ∧ I3 vals ∧
    vals.getD 0 0 + vals.getD 2 0 = vals.getD 3 0 ∧ vals.getD 0 0 + vals.getD 1 0 = vals.getD 12 0 ∧
    ((pc = 61086 ∧ vals.getD 2 0 = vals.getD 1 0) ∨
     (pc = 60943 ∧ vals.getD 2 0 < vals.getD 1 0 ∧ 128 ≤ decodeLE (μ₀.readN (vals.getD 3 0) 1)))

theorem sx1_ge {b : Nat} (hb : b < 256) (h : 2 ^ 63 ≤ u64 (signed 1 b)) : 128 ≤ b := by
  simp only [u64, unsigned, signed] at h
  split at h <;> omega

theorem decodeLE_one_lt (μ : Memory) (a : Nat) : decodeLE (μ.readN a 1) < 256 := by
  have := decodeLE_lt (μ.readN a 1); simpa [Memory.length_readN] using this

theorem readN_one_frame {μ μ₀ : Memory} {a : Nat} (h : μ.read a = μ₀.read a) :
    μ.readN a 1 = μ₀.readN a 1 := by
  simp [Memory.readN, h]

theorem obl3 (μ₀ : Memory) : ∀ ℓ ∈ leaves3, LoopOblX ub3 lb3 H3 asm3 μ₀ I3 meas3 60803 (Q3 μ₀) ℓ := by
  simp only [leaves3, List.mem_cons, List.not_mem_nil, or_false]
  rintro ℓ (rfl | rfl | rfl) <;> intro vals ω μ hI hB hLB hF hH hf <;>
    rcases vals with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8, _ | ⟨a9, _ | ⟨a10, _ | ⟨a11, _ | ⟨a12, _ | ⟨a13, _ | ⟨a14, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    (try (simp [BHold, ub3] at hB; done)) <;> simp only [BHold, ub3] at hB <;>
    simp only [LBHold, lb3] at hLB <;>
    simp only [I3, List.getD_cons_succ, List.getD_cons_zero] at hI <;>
    simp only [asm3, FactsHold, Fact.Holds, Aff.eval, env, List.getD_cons_succ,
      List.getD_cons_zero, af] at hF <;>
    simp only [FactsHold, Fact.Holds, Aff.eval, env, List.getD_cons_succ, List.getD_cons_zero, af,
      byteQ, SVal.eval] at hf
  · -- the back edge
    left
    refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [svals, nxt3, List.map, SVal.eval, Aff.eval, af, I3, BHold, ub3, LBHold, lb3, asm3,
        FactsHold, Fact.Holds, env, meas3, List.getD_cons_succ, List.getD_cons_zero] <;> omega
  · -- the end: i + 1 = len
    right
    intro ω' μ' hB'
    refine ⟨_, hB', ?_⟩
    simp only [svals, nxt3, List.map, SVal.eval, Aff.eval, af, I3, BHold, ub3, LBHold, lb3,
      List.getD_cons_succ, List.getD_cons_zero]
    omega
  · -- an octet ≥ 0x80
    right
    intro ω' μ' hB'
    refine ⟨_, hB', ?_⟩
    have hb := sx1_ge (decodeLE_one_lt μ _) hf
    have hfr := hH.2.2.2.2.1 a3 (by omega) (by
      simp only [H3, List.mem_cons, List.not_mem_nil, or_false, forall_eq, InReg, Aff.eval, env,
        List.getD_cons_succ, List.getD_cons_zero, af]
      omega)
    rw [readN_one_frame (show μ.read _ = μ₀.read _ from by simpa using hfr)] at hb
    simp only [svals, idsub15, List.map, SVal.eval, I3, BHold, ub3, LBHold, lb3,
      List.getD_cons_succ, List.getD_cons_zero]
    omega

/-- **The byte loop of `from_utf8`** (60803): from its header the machine reaches 61086 with
    i = len, or 60943 at an index i < len whose octet is at least 0x80 (`Q3`). -/
theorem byte_loop {X : Type} {p : ByteArray} {R : HostRel X} {P : Program}
    [Services.Bootstrap.CodeF.HasCodeF p P] [Services.Bootstrap.Code.HasCode p P]
    {μ₀ : Memory} (x : X) :
    ∀ vals ω μ, I3 vals → BHold vals ub3 → LBHold vals lb3 → FactsHold (env vals ω μ) asm3 →
      H3.Holds vals μ₀ ω μ →
      ∃ xpc k ω' μ', FreeStepsH p R 60803 ω μ x xpc ω' μ' x k ∧ Q3 μ₀ xpc ω' μ' :=
  loop_fork_soundX check3 (by decide) (hypU (p := p) (P := P)) trivial (fun _ _ _ _ => trivial) (obl3 μ₀) x

end Services.Bootstrap.SymExec.Utf8
