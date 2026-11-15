import Services.Bootstrap.SymExec.Utf8Outer

/-!
# `core::str::from_utf8` (60681): the outer loop 60738 (symexec, loops)

EXPERIMENTAL, WORK IN PROGRESS (see `Services/Bootstrap/SymExec/README.md`). The outer loop of
Rust's `run_utf8_validation` (GP v0.8.0 §A.5), proved by loop induction (`loop_soundX`) with a
hand-composed body: the forking checks of `Utf8Outer` and the inner loops `word_loop` and
`byte_loop'`. From the header 60738 the machine reaches the Ok exit 61086 or the error exit 61138
(`QO`); at the error exit, i < len, the octet at p + i (in the start memory) is at least 0x80, and
(r2, r3) is (0, 1) (error_len none) or (1, k), k ∈ {1, 2, 3}.

Named naturals as in `Utf8Byte` (0 p, 1 len, 2 i, 3 q, 4 sp, 5 align, 6 m = max(len, 15) − 15,
7 r11 = 2^64 − len, 8 ret, 9/10 saved r5/r6, 11 r7, 12 e = p + len).
-/

namespace Services.Bootstrap.SymExec.Utf8

open PVM PVM.SymExec Num Exec

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- The named naturals the outer loop does not change. -/
def keepO : List Nat := [0, 1, 4, 8, 9, 10, 11, 12]

/-- What the outer loop keeps that the executor does not track: r11 = 2^64 − len, the input apart
    from the stack frame, m + 15 = max(len, 15), and (against the loop's start `v₀`) `keepO`. -/
def I1 (v₀ vals : List Nat) : Prop :=
  vals.getD 7 0 + vals.getD 1 0 = 2 ^ 64 ∧
  (vals.getD 0 0 + vals.getD 1 0 ≤ vals.getD 4 0 ∨ vals.getD 4 0 + 32 ≤ vals.getD 0 0) ∧
  vals.getD 6 0 + 15 = max (vals.getD 1 0) 15 ∧ Keep keepO v₀ vals

/-- The invariant at the header 60738. -/
def Inv1 (μ₀ : Memory) (v₀ vals : List Nat) (ω : Regs) (μ : Memory) : Prop :=
  I1 v₀ vals ∧ BHold vals ub1 ∧ LBHold vals lb1 ∧ FactsHold (env vals ω μ) asm1 ∧
    H1.Holds vals μ₀ ω μ

/-- The measure: len − i. -/
def meas1 (vals : List Nat) : Nat := vals.getD 1 0 - vals.getD 2 0

/-- Where the outer loop ends: at 61086 (Ok), or at 61138 (Err) with i < len, the octet at p + i
    in μ₀ at least 0x80, and (r2, r3) ∈ {(0, 1), (1, 1), (1, 2), (1, 3)}. -/
def QO (μ₀ : Memory) (v₀ : List Nat) (pc : Nat) (ω : Regs) (μ : Memory) : Prop :=
  (pc = 61086 ∧ ∃ vals, HOk.Holds vals μ₀ ω μ ∧ Keep keepO v₀ vals) ∨
  (pc = 61138 ∧ ∃ vals c2 c3, (HE c2 c3).Holds vals μ₀ ω μ ∧ Keep keepO v₀ vals ∧
    ((c2 = 0 ∧ c3 = 1) ∨ (c2 = 1 ∧ (c3 = 1 ∨ c3 = 2 ∨ c3 = 3))) ∧
    vals.getD 2 0 < vals.getD 1 0 ∧
    128 ≤ decodeLE (μ₀.readN (vals.getD 0 0 + vals.getD 2 0) 1))

/-- The regions the loop reads, readable in μ₀: the input [p, e), the table [71078, 71334), the
    stack frame [sp, sp + 32) (p, e, sp from the loop's start `v₀`). -/
def RdO (μ₀ : Memory) (v₀ : List Nat) : Prop :=
  (∀ t, v₀.getD 0 0 ≤ t → t < v₀.getD 12 0 → μ₀.readable t = true) ∧
  (∀ t, 71078 ≤ t → t < 71334 → μ₀.readable t = true) ∧
  (∀ t, v₀.getD 4 0 ≤ t → t < v₀.getD 4 0 + 32 → μ₀.readable t = true)

theorem keepO_get {v₀ vals : List Nat} (h : Keep keepO v₀ vals) :
    vals.getD 0 0 = v₀.getD 0 0 ∧ vals.getD 1 0 = v₀.getD 1 0 ∧ vals.getD 4 0 = v₀.getD 4 0 ∧
    vals.getD 12 0 = v₀.getD 12 0 :=
  ⟨h 0 (by decide), h 1 (by decide), h 4 (by decide), h 12 (by decide)⟩

/-- `asm1` from the arithmetic facts and `RdO`. -/
theorem asm1_of {μ₀ μ : Memory} {ω : Regs} {v₀ vals : List Nat} (hR : RdO μ₀ v₀)
    (hK : Keep keepO v₀ vals) (hp : μ.pages = μ₀.pages)
    (h1 : vals.getD 0 0 + vals.getD 2 0 = vals.getD 3 0) (h2 : vals.getD 2 0 + 1 ≤ vals.getD 1 0)
    (h3 : vals.getD 0 0 + vals.getD 1 0 = vals.getD 12 0) : FactsHold (env vals ω μ) asm1 := by
  obtain ⟨k0, -, k4, k12⟩ := keepO_get hK
  obtain ⟨r1, r2, r3⟩ := hR
  simp only [asm1, FactsHold, Fact.Holds, Aff.eval, env, af, readable_pages hp]
  refine ⟨h1, by omega, h3, fun t ht1 ht2 => r1 t (by omega) (by omega),
    fun t ht1 ht2 => r2 t (by omega) (by omega), fun t ht1 ht2 => r3 t (by omega) (by omega),
    trivial⟩

/-- 60943 → 60946 (as `check5a`, without the lower bound on r6: r6 = 0 when the byte loop was
    entered at i = 0). -/
theorem check5a' : forkCheckW progU ub3x lb1 [] H3 asm3 [⟨60946, [], H5a, idsub15⟩] 60943 100 = true := by
  decide +kernel

/-- `H5a` (r5 = 2^64 − r6 mod 2^64) is `H1` when r6 + i ≡ 0. -/
theorem h5a_h1 {vals : List Nat} {μ₀ μ : Memory} {ω : Regs} (h : H5a.Holds vals μ₀ ω μ)
    (hm : (vals.getD 13 0 + vals.getD 2 0) % 2 ^ 64 = 0) (h13 : vals.getD 13 0 < 2 ^ 64)
    (h2 : vals.getD 2 0 < 2 ^ 32) : H1.Holds vals μ₀ ω μ := by
  obtain ⟨hr, hc, hrd, hwr, hf, hp⟩ := h
  refine ⟨?_, hc, hrd, hwr, hf, hp⟩
  simp only [H5a, H1, regs1, RegsHold, SVal.eval, twoRegImmAlu, Option.getD_some, env] at hr ⊢
  obtain ⟨r0, r1, r3, r4, r5, -, r7, r8, r9, -, r11, -⟩ := hr
  refine ⟨r0, r1, r3, r4, ?_, r7, r8, r9, r11, trivial⟩
  rw [r5]; congr 1; simp only [two64]; omega

theorem lb1_of {vals : List Nat} (h : vals.length = 15) : LBHold vals lb1 := by
  rcases vals with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8, _ | ⟨a9, _ | ⟨a10, _ | ⟨a11, _ | ⟨a12, _ | ⟨a13, _ | ⟨a14, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp at h
  simp [LBHold, lb1]

theorem asm3_of {E : Env} (h : FactsHold E asm1) : FactsHold E asm3 :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, trivial⟩

theorem asm4_of {E : Env} (h : FactsHold E asm1) : FactsHold E asm4 := by
  obtain ⟨f1, f2, f3, f4, -⟩ := h
  simp only [asm4, FactsHold, Fact.Holds, Aff.eval, af] at f2 ⊢
  exact ⟨f1, by omega, f3, f4, trivial⟩

/-- Fifteen omega goals. -/
macro "omega15" : tactic =>
  `(tactic| exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, trivial⟩)

theorem ub1_of_ub3x {vals : List Nat} (hB : BHold vals ub3x) (h3 : vals.getD 3 0 < 2 ^ 32) :
    BHold vals ub1 := by
  rcases vals with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8, _ | ⟨a9, _ | ⟨a10, _ | ⟨a11, _ | ⟨a12, _ | ⟨a13, _ | ⟨a14, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp only [BHold, ub3x] at hB <;> (try exact hB.elim) <;> (try simp_all; done)
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h3
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, -⟩ := hB
  simp only [BHold, ub1]
  omega15

/-- An entry of a bounded list is below its bound. -/
theorem bget0 : ∀ {vals ub : List Nat}, BHold vals ub → ∀ k, vals.getD k 0 < ub.getD k 0 ∨ ub.length ≤ k
  | [], [], _, k => Or.inr (Nat.zero_le _)
  | _ :: _, _ :: _, h, 0 => Or.inl (by simpa using h.1)
  | _ :: _, _ :: _, h, k + 1 => by
    simpa [List.getD_cons_succ] using bget0 h.2 k
  | [], _ :: _, h, _ => h.elim
  | _ :: _, [], h, _ => h.elim

theorem bget {vals ub : List Nat} (h : BHold vals ub) (k : Nat) (hk : k < ub.length := by decide) :
    vals.getD k 0 < ub.getD k 0 := (bget0 h k).resolve_right (by omega)

/-- A cut with fewer registers (same cells, regions and frame) holds when the bigger one does. -/
theorem cut_sub {A B : Cut} {vals : List Nat} {μ₀ μ : Memory} {ω : Regs}
    (hr : ∀ r ∈ A.regs, r ∈ B.regs) (hc : A.cells = B.cells) (hrd : A.rd = B.rd) (hwr : A.wr = B.wr)
    (hf : A.frame = B.frame) (h : B.Holds vals μ₀ ω μ) : A.Holds vals μ₀ ω μ := by
  obtain ⟨r, c, rd, wr, f, pg⟩ := h
  exact ⟨regsHold_of_mem fun x hx => regsHold_mem r x (hr x hx), hc ▸ c, hrd ▸ rd, hwr ▸ wr,
    hf ▸ f, pg⟩

theorem keep_trans {ks ks' : List Nat} {v₀ v₁ vals : List Nat} (hs : ∀ k ∈ ks, k ∈ ks')
    (h1 : Keep ks' v₁ vals) (h0 : Keep ks v₀ v₁) : Keep ks v₀ vals :=
  fun k hk => (h1 k (hs k hk)).trans (h0 k hk)

/-! ## Two more checks -/

/-- (align − i) mod 8 (the alignment test at 60738). -/
def alignV : SVal :=
  .alu2i .andImm (.const 0) (.mod (.alu3 .sub64 (vr 5) (vr 2) (.const 0)) (2^64)) 7

/-- `check1` with the path facts: the misaligned and aligned leaves know the octet is < 0x80, the
    multi-octet leaf that it is ≥ 0x80. -/
def leaves1F : List Leaf :=
  [⟨60731, [.ne alignV 0, .lt byteQ (2^63)], H1, idsub15⟩,
   ⟨60756, [.ge alignV 0, .lt alignV 1, .lt byteQ (2^63)], H1, idsub15⟩,
   ⟨60829, [.ge byteQ (2^63)], H1b, sub1b⟩]

theorem check1F : forkCheck progU ub1 lb1 [] H1 asm1 leaves1F 60738 300 = true := by
  decide +kernel

/-- The byte loop's header entered at i = 0, where r6 = 0 (not 2^64 − i). -/
def H3z : Cut :=
  ⟨[(0, vr 5), (1, vr 4), (3, .const 1), (4, vr 6), (5, vr 14), (6, .const 0), (7, vr 11), (8, vr 0),
    (9, vr 1), (10, vr 3), (11, vr 7)],
   [(af 4 24, 8, vr 8), (af 4 16, 8, vr 9), (af 4 8, 8, vr 10), (af 4 0, 8, .const 71078)],
   [], [], [(af 4 0, 32)]⟩

/-- i ↦ i + 1, q ↦ q + 1, r6 ↦ 2^64 − 1. -/
def nxt3z : List SVal :=
  [vr 0, vr 1, .addr (af 2 1), .addr (af 3 1), vr 4, vr 5, vr 6, vr 7, vr 8, vr 9, vr 10, vr 11, vr 12,
    .const (2^64 - 1), vr 14]

/-- r6 ↦ 0. -/
def sub3z : List SVal :=
  [vr 0, vr 1, vr 2, vr 3, vr 4, vr 5, vr 6, vr 7, vr 8, vr 9, vr 10, vr 11, vr 12, .const 0, vr 14]

def leaves3z : List Leaf :=
  [⟨60803, [.ne (vr 7) (2^64 - 1), .lt byteQ (2^63)], H3, nxt3z⟩,
   ⟨61086, [.ge (vr 7) (2^64 - 1), .lt (vr 7) (2^64), .lt byteQ (2^63)], H3, nxt3z⟩,
   ⟨60943, [.ge byteQ (2^63)], H3, sub3z⟩]

/-- The first iteration of the byte loop from i = 0 (r6 = 0). -/
theorem check3z : forkCheck progU ub3 lb1 [] H3z asm3 leaves3z 60803 100 = true := by
  decide +kernel

theorem sx1_lt {b : Nat} (hb : b < 256) (h : u64 (signed 1 b) < 2 ^ 63) : b < 128 := by
  simp only [u64, unsigned, signed] at h
  split at h <;> omega

/-- The octet at q is the same in μ and μ₀ when q lies outside the frame [sp, sp + 32). -/
theorem octet_frame {H : Cut} {vals : List Nat} {μ₀ μ : Memory} {ω : Regs}
    (hH : H.Holds vals μ₀ ω μ) (hfr : H.frame = [(af 4 0, 32)]) {q : Nat} (hq : q < 2 ^ 32)
    (hd : q < vals.getD 4 0 ∨ vals.getD 4 0 + 32 ≤ q) :
    decodeLE (μ.readN q 1) = decodeLE (μ₀.readN q 1) := by
  rw [readN_one_frame (hH.2.2.2.2.1 q (by simp only [two32]; omega) (by
    rw [hfr]
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, InReg, Aff.eval, env, af]
    omega))]

/-- `H3` with r6 = 0 is `H3z`. -/
theorem h3_h3z {vals : List Nat} {μ₀ μ : Memory} {ω : Regs} (h : H3.Holds vals μ₀ ω μ)
    (h13 : vals.getD 13 0 = 0) : H3z.Holds vals μ₀ ω μ := by
  obtain ⟨hr, hc, hrd, hwr, hf, hp⟩ := h
  refine ⟨?_, hc, hrd, hwr, hf, hp⟩
  simp only [H3, H3z, RegsHold, SVal.eval, env] at hr ⊢
  obtain ⟨r0, r1, r3, r4, r5, r6, r7, r8, r9, r10, r11, -⟩ := hr
  exact ⟨r0, r1, r3, r4, r5, by rw [r6, h13], r7, r8, r9, r10, r11, trivial⟩

section
variable {X : Type} {p : ByteArray} {R : HostRel X}

/-- From `pc`, the outer body's goal: back at the header with a measure below `n`, or an exit. -/
def Reach (p : ByteArray) (R : HostRel X) (x : X) (μ₀ : Memory) (v₀ : List Nat) (n pc : Nat)
    (ω : Regs) (μ : Memory) : Prop :=
  ∃ k ω' μ', (FreeStepsH p R pc ω μ x 60738 ω' μ' x k ∧
      ∃ vals', meas1 vals' < n ∧ Inv1 μ₀ v₀ vals' ω' μ') ∨
    (∃ xpc, FreeStepsH p R pc ω μ x xpc ω' μ' x k ∧ QO μ₀ v₀ xpc ω' μ')

theorem reach_pre {x : X} {μ₀ : Memory} {v₀ : List Nat} {n pc pc' : Nat} {ω ω₁ : Regs}
    {μ μ₁ : Memory} {k : Nat} (h : FreeStepsH p R pc ω μ x pc' ω₁ μ₁ x k)
    (hr : Reach p R x μ₀ v₀ n pc' ω₁ μ₁) : Reach p R x μ₀ v₀ n pc ω μ := by
  obtain ⟨k', ω', μ', hr | ⟨xpc, hs, hq⟩⟩ := hr
  · exact ⟨_, ω', μ', Or.inl ⟨h.trans hr.1, hr.2⟩⟩
  · exact ⟨_, ω', μ', Or.inr ⟨xpc, h.trans hs, hq⟩⟩

theorem reach_q {x : X} {μ₀ : Memory} {v₀ : List Nat} {n pc xpc : Nat} {ω ω' : Regs}
    {μ μ' : Memory} {k : Nat} (h : FreeStepsH p R pc ω μ x xpc ω' μ' x k)
    (hq : QO μ₀ v₀ xpc ω' μ') : Reach p R x μ₀ v₀ n pc ω μ :=
  ⟨k, ω', μ', Or.inr ⟨xpc, h, hq⟩⟩

theorem reach_back {x : X} {μ₀ : Memory} {v₀ : List Nat} {n pc : Nat} {ω ω' : Regs}
    {μ μ' : Memory} {k : Nat} (h : FreeStepsH p R pc ω μ x 60738 ω' μ' x k) (vals' : List Nat)
    (hm : meas1 vals' < n) (hi : Inv1 μ₀ v₀ vals' ω' μ') : Reach p R x μ₀ v₀ n pc ω μ :=
  ⟨k, ω', μ', Or.inl ⟨h, vals', hm, hi⟩⟩

theorem bhold_length : ∀ {vals ub : List Nat}, BHold vals ub → vals.length = ub.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp only [List.length_cons, bhold_length h.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem svals_idsub15 {vals : List Nat} {ω : Regs} {μ : Memory} (h : vals.length = 15) :
    svals (env vals ω μ) idsub15 = vals := by
  rcases vals with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8, _ | ⟨a9, _ | ⟨a10, _ | ⟨a11, _ | ⟨a12, _ | ⟨a13, _ | ⟨a14, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp at h
  simp [svals, idsub15, SVal.eval, env]

theorem pages_of {vals vals' : List Nat} {μ₀ : Memory} {A B : Cut} {ω ω' : Regs} {μ μ' : Memory}
    (hA : A.Holds vals μ₀ ω μ) (hB : B.Holds vals' μ₀ ω' μ') : μ.pages = μ'.pages :=
  hA.2.2.2.2.2.trans hB.2.2.2.2.2.symm

/-- 60946 → 60738 (the end of the path through the byte loop). -/
theorem seg5b {P : Program} [Services.Bootstrap.CodeF.HasCodeF p P]
    [Services.Bootstrap.Code.HasCode p P] {x : X} {μ₀ : Memory} {v₀ : List Nat} {n : Nat}
    {vals : List Nat} {ω : Regs} {μ : Memory} (hI : I1 v₀ vals) (hB : BHold vals ub1)
    (hLB : LBHold vals lb1) (hF : FactsHold (env vals ω μ) asm1) (hH : H1.Holds vals μ₀ ω μ)
    (hm : meas1 vals < n) : Reach p R x μ₀ v₀ n 60946 ω μ := by
  obtain ⟨ℓ, hℓ, k, ω', μ', hrun, -, hBℓ⟩ :=
    fork_sound check5b (hypU (p := p) (P := P)) trivial hB hLB (fun _ _ => trivial) hH hF x
  simp only [List.mem_singleton] at hℓ; subst hℓ
  rw [show svals (env vals ω μ) idsub15 = vals from svals_idsub15 (bhold_length hB)] at hBℓ
  exact reach_back hrun vals hm
    ⟨hI, hB, hLB, factsHold_env (pages_of hH hBℓ) (by decide) hF, hBℓ⟩

/-- 60943 (the byte loop found an octet ≥ 0x80 at i < len) → 60946 → 60738. -/
theorem seg5a {P : Program} [Services.Bootstrap.CodeF.HasCodeF p P]
    [Services.Bootstrap.Code.HasCode p P] {x : X} {μ₀ : Memory} {v₀ : List Nat} {n : Nat}
    {vals : List Nat} {ω : Regs} {μ : Memory} (hR : RdO μ₀ v₀) (hH : H3.Holds vals μ₀ ω μ)
    (hB : BHold vals ub3x) (hmod : (vals.getD 13 0 + vals.getD 2 0) % 2 ^ 64 = 0)
    (hI : I1 v₀ vals) (h1 : vals.getD 0 0 + vals.getD 2 0 = vals.getD 3 0)
    (h3 : vals.getD 0 0 + vals.getD 1 0 = vals.getD 12 0) (hlt : vals.getD 2 0 < vals.getD 1 0)
    (hm : meas1 vals < n) : Reach p R x μ₀ v₀ n 60943 ω μ := by
  have hl := bhold_length hB
  have hLB := lb1_of hl
  have hb12 : vals.getD 12 0 < 2 ^ 32 + 1 := bget hB 12
  have hb13 : vals.getD 13 0 < 2 ^ 64 := bget hB 13
  have hb2 : vals.getD 2 0 < 2 ^ 32 := bget hB 2
  have hF := asm1_of (ω := ω) hR hI.2.2.2 hH.2.2.2.2.2 h1 hlt h3
  obtain ⟨ℓ, hℓ, k, ω', μ', hrun, hBℓ⟩ :=
    fork_soundW check5a' (hypU (p := p) (P := P)) trivial hB hLB (fun _ _ => trivial) hH
      (asm3_of hF) x
  simp only [List.mem_singleton] at hℓ; subst hℓ
  rw [show svals (env vals ω μ) idsub15 = vals from svals_idsub15 hl] at hBℓ
  have hH1 := h5a_h1 hBℓ hmod hb13 hb2
  exact reach_pre hrun (seg5b (P := P) hI (ub1_of_ub3x hB (by omega)) hLB
    (asm1_of hR hI.2.2.2 hBℓ.2.2.2.2.2 h1 hlt h3) hH1 hm)

/-- Where the byte loop ends (`Q3`), the outer body's goal holds, given the outer invariant at the
    byte loop's start `v₁` and that the measure drops at every index ≥ i₁ with an octet ≥ 0x80. -/
theorem q3_reach {P : Program} [Services.Bootstrap.CodeF.HasCodeF p P]
    [Services.Bootstrap.Code.HasCode p P] {x : X} {μ₀ : Memory} {v₀ v₁ : List Nat} {n xpc : Nat}
    {ω : Regs} {μ : Memory} (hR : RdO μ₀ v₀) (hI : I1 v₀ v₁)
    (hprog : ∀ j, v₁.getD 2 0 ≤ j → 128 ≤ decodeLE (μ₀.readN (v₁.getD 0 0 + j) 1) →
      v₁.getD 1 0 - j < n)
    (hq : Q3 μ₀ v₁ xpc ω μ) : Reach p R x μ₀ v₀ n xpc ω μ := by
  obtain ⟨vals, hH, hB, ⟨hmod, h7, hdisj, hK, hge⟩, h1, h3, hx⟩ := hq
  have hKO : Keep keepO v₀ vals := keep_trans (by decide) hK hI.2.2.2
  rcases hx with ⟨rfl, -⟩ | ⟨rfl, hlt, hoct⟩
  · exact reach_q .refl (Or.inl ⟨rfl, vals, cut_sub (A := HOk) (B := H3) (by decide) rfl rfl rfl rfl hH, hKO⟩)
  · have k0 : vals.getD 0 0 = v₁.getD 0 0 := hK 0 (by decide)
    have k1 : vals.getD 1 0 = v₁.getD 1 0 := hK 1 (by decide)
    have k6 : vals.getD 6 0 = v₁.getD 6 0 := hK 6 (by decide)
    refine reach_pre .refl (seg5a (P := P) hR hH hB hmod ⟨h7, hdisj, by rw [k6, k1]; exact hI.2.2.1, hKO⟩
      h1 h3 hlt ?_)
    have := hprog (vals.getD 2 0) hge (by rw [← k0, h1]; exact hoct)
    simp only [meas1]; omega

/-- The hypotheses of the byte loop's entry 60803 (r6 = 2^64 − i mod 2^64, i < len). -/
structure ByteIn (μ₀ : Memory) (v₀ : List Nat) (vals : List Nat) (ω : Regs) (μ : Memory) : Prop where
  hH : H3.Holds vals μ₀ ω μ
  hB : BHold vals ub3
  hmod : (vals.getD 13 0 + vals.getD 2 0) % 2 ^ 64 = 0
  hI : I1 v₀ vals
  h1 : vals.getD 0 0 + vals.getD 2 0 = vals.getD 3 0
  h3 : vals.getD 0 0 + vals.getD 1 0 = vals.getD 12 0
  hlt : vals.getD 2 0 < vals.getD 1 0

/-- 60803 with i > 0: the byte loop, then `q3_reach`. -/
theorem segByte1 {P : Program} [Services.Bootstrap.CodeF.HasCodeF p P]
    [Services.Bootstrap.Code.HasCode p P] {x : X} {μ₀ : Memory} {v₀ : List Nat} {n : Nat}
    {vals : List Nat} {ω : Regs} {μ : Memory} (hR : RdO μ₀ v₀) (hin : ByteIn μ₀ v₀ vals ω μ)
    (hpos : 0 < vals.getD 2 0)
    (hprog : ∀ j, vals.getD 2 0 ≤ j → 128 ≤ decodeLE (μ₀.readN (vals.getD 0 0 + j) 1) →
      vals.getD 1 0 - j < n) : Reach p R x μ₀ v₀ n 60803 ω μ := by
  obtain ⟨hH, hB, hmod, hI, h1, h3, hlt⟩ := hin
  have hb13 : vals.getD 13 0 < 2 ^ 64 := bget hB 13
  have hb2 : vals.getD 2 0 < 2 ^ 32 := bget hB 2
  have hLB : LBHold vals lb3 := by
    have hl := bhold_length hB
    clear hH hB hI h1 h3 hlt hprog hR
    rcases vals with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8, _ | ⟨a9, _ | ⟨a10, _ | ⟨a11, _ | ⟨a12, _ | ⟨a13, _ | ⟨a14, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp [ub3] at hl
    simp only [List.getD_cons_succ, List.getD_cons_zero] at hb13 hb2 hmod hpos
    simp only [LBHold, lb3]
    omega15
  have hI3 : I3 vals vals := ⟨by omega, hI.1, hI.2.1, fun _ _ => rfl, Nat.le_refl _⟩
  obtain ⟨xpc, k, ω', μ', hrun, hq⟩ := byte_loop (p := p) (R := R) (P := P) (μ₀ := μ₀) vals x vals ω μ
    hI3 hB hLB (asm3_of (asm1_of hR hI.2.2.2 hH.2.2.2.2.2 h1 hlt h3)) hH
  exact reach_pre hrun (q3_reach (P := P) hR hI hprog hq)

/-- 60803 with i = 0 (r6 = 0): one iteration by `check3z`, then the byte loop from i = 1. -/
theorem segByte0 {P : Program} [Services.Bootstrap.CodeF.HasCodeF p P]
    [Services.Bootstrap.Code.HasCode p P] {x : X} {μ₀ : Memory} {v₀ : List Nat} {n : Nat}
    {vals : List Nat} {ω : Regs} {μ : Memory} (hR : RdO μ₀ v₀) (hin : ByteIn μ₀ v₀ vals ω μ)
    (h0 : vals.getD 2 0 = 0)
    (hprog : ∀ j, vals.getD 2 0 ≤ j → 128 ≤ decodeLE (μ₀.readN (vals.getD 0 0 + j) 1) →
      vals.getD 1 0 - j < n) : Reach p R x μ₀ v₀ n 60803 ω μ := by
  obtain ⟨hH, hB, hmod, hI, h1, h3, hlt⟩ := hin
  have hl := bhold_length hB
  have hb13 : vals.getD 13 0 < 2 ^ 64 := bget hB 13
  have h13 : vals.getD 13 0 = 0 := by omega
  have hF := asm1_of (ω := ω) hR hI.2.2.2 hH.2.2.2.2.2 h1 hlt h3
  obtain ⟨ℓ, hℓ, k, ω', μ', hrun, hf, hBℓ⟩ :=
    fork_sound check3z (hypU (p := p) (P := P)) trivial hB (lb1_of hl) (fun _ _ => trivial)
      (h3_h3z hH h13) (asm3_of hF) x
  refine reach_pre hrun ?_
  have hpg := hH.2.2.2.2.2
  have hpg' := hBℓ.2.2.2.2.2
  obtain ⟨i7, idj, i6, iK⟩ := hI
  clear hrun hF
  simp only [leaves3z, List.mem_cons, List.not_mem_nil, or_false] at hℓ
  rcases vals with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8, _ | ⟨a9, _ | ⟨a10, _ | ⟨a11, _ | ⟨a12, _ | ⟨a13, _ | ⟨a14, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp [ub3] at hl
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h0 h13 h1 h3 hlt hprog i7 idj i6
  subst h0 h13
  simp only [BHold, ub3] at hB
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, -⟩ := hB
  rcases hℓ with rfl | rfl | rfl <;>
    simp only [FactsHold, Fact.Holds, Aff.eval, env, List.getD_cons_succ, List.getD_cons_zero, af,
      byteQ, SVal.eval] at hf
  · -- back edge: i = 1, r6 = 2^64 − 1, then the byte loop
    obtain ⟨g1, g2, -⟩ := hf
    simp only [svals, nxt3z, List.map, SVal.eval, Aff.eval, env, List.getD_cons_succ,
      List.getD_cons_zero, af] at hBℓ
    refine segByte1 (P := P) hR ⟨hBℓ, ?_, ?_, ⟨?_, ?_, ?_, keep_of iK (by simp [keepO])⟩, ?_, ?_, ?_⟩
      ?_ ?_ <;> simp only [BHold, ub3, List.getD_cons_succ, List.getD_cons_zero]
    · omega15
    all_goals first | omega | (intro j hj; exact hprog j (by omega))
  · -- 61086: len = 1
    simp only [svals, nxt3z, List.map, SVal.eval, Aff.eval, env, List.getD_cons_succ,
      List.getD_cons_zero, af] at hBℓ
    exact reach_q .refl (Or.inl ⟨rfl, _, cut_sub (A := HOk) (B := H3) (by decide) rfl rfl rfl rfl hBℓ,
      keep_of iK (by simp [keepO])⟩)
  · -- 60943: the octet at i = 0 is ≥ 0x80
    obtain ⟨g1, -⟩ := hf
    simp only [svals, sub3z, List.map, SVal.eval, env, List.getD_cons_succ,
      List.getD_cons_zero] at hBℓ
    have hb := sx1_ge (decodeLE_one_lt μ _) g1
    have hd : a3 < [a0, a1, 0, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, 0, a14].getD 4 0 ∨
        [a0, a1, 0, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, 0, a14].getD 4 0 + 32 ≤ a3 := by
      simp only [List.getD_cons_succ, List.getD_cons_zero]; omega
    rw [show ((a3 : Int) + 0).toNat = a3 by omega, octet_frame hH rfl (q := a3) (by omega) hd] at hb
    have hm := hprog 0 (Nat.le_refl _) (by rw [h1]; exact hb)
    exact seg5a (P := P) hR hBℓ (by simp only [BHold, ub3x]; omega15) (by simp)
      ⟨i7, idj, i6, iK⟩ h1 h3 hlt (by simp only [meas1, List.getD_cons_succ, List.getD_cons_zero]; omega)

/-- 60793 (i ≤ len) → 61086, or the byte loop 60803. -/
theorem seg4 {P : Program} [Services.Bootstrap.CodeF.HasCodeF p P]
    [Services.Bootstrap.Code.HasCode p P] {x : X} {μ₀ : Memory} {v₀ : List Nat} {n : Nat}
    {vals : List Nat} {ω : Regs} {μ : Memory} (hR : RdO μ₀ v₀) (hH : H1.Holds vals μ₀ ω μ)
    (hB : BHold vals ub4) (hI : I1 v₀ vals) (hF : FactsHold (env vals ω μ) asm4)
    (hprog : ∀ j, vals.getD 2 0 ≤ j → 128 ≤ decodeLE (μ₀.readN (vals.getD 0 0 + j) 1) →
      vals.getD 1 0 - j < n) : Reach p R x μ₀ v₀ n 60793 ω μ := by
  have hl := bhold_length hB
  obtain ⟨ℓ, hℓ, k, ω', μ', hrun, hf, hBℓ⟩ :=
    fork_sound check4 (hypU (p := p) (P := P)) trivial hB (lb1_of hl) (fun _ _ => trivial) hH hF x
  simp only [leaves4, List.mem_cons, List.not_mem_nil, or_false] at hℓ
  rcases hℓ with rfl | rfl
  · rw [show svals (env vals ω μ) idsub15 = vals from svals_idsub15 hl] at hBℓ
    exact reach_q hrun (Or.inl ⟨rfl, vals, hBℓ, hI.2.2.2⟩)
  · refine reach_pre hrun ?_
    have hpg := hH.2.2.2.2.2
    clear hrun
    rcases vals with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8, _ | ⟨a9, _ | ⟨a10, _ | ⟨a11, _ | ⟨a12, _ | ⟨a13, _ | ⟨a14, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp [ub4] at hl
    simp only [BHold, ub4] at hB
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, -⟩ := hB
    simp only [asm4, FactsHold, Fact.Holds, Aff.eval, env, List.getD_cons_succ,
      List.getD_cons_zero, af] at hF
    obtain ⟨f1, f2, f3, -⟩ := hF
    simp only [FactsHold, Fact.Holds, Aff.eval, env, List.getD_cons_succ, List.getD_cons_zero,
      af] at hf
    simp only [svals, sub4, List.map, SVal.eval, env, List.getD_cons_succ, List.getD_cons_zero,
      twoRegImmAlu, Option.getD_some] at hBℓ
    simp only [List.getD_cons_succ, List.getD_cons_zero] at hprog
    obtain ⟨i7, idj, i6, iK⟩ := hI
    simp only [List.getD_cons_succ, List.getD_cons_zero] at i7 idj i6
    have hi : a2 + 1 ≤ a1 := by omega
    by_cases h0 : a2 = 0
    · simp only [two64, h0] at hBℓ ⊢
      refine segByte0 (P := P) hR ⟨hBℓ, ?_, ?_, ⟨i7, idj, i6, keep_of iK (by simp [keepO])⟩, ?_, ?_, ?_⟩
        ?_ ?_ <;> simp only [BHold, ub3, List.getD_cons_succ, List.getD_cons_zero]
      · omega15
      all_goals first | omega | (subst h0; exact hprog)
    · refine segByte1 (P := P) hR ⟨hBℓ, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ ?_ ?_ <;>
        simp only [BHold, ub3, List.getD_cons_succ, List.getD_cons_zero, two64]
      · omega15
      · omega
      · exact i7
      · exact idj
      · exact i6
      · exact keep_of iK (by simp [keepO])
      · omega
      · omega
      · omega
      · omega
      · exact hprog

end

end Services.Bootstrap.SymExec.Utf8
