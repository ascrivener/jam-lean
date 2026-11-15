import Services.Bootstrap.BParamsHdr
import Services.Bootstrap.StartMemZ
import Services.Bootstrap.StartupConsts
import Services.Bootstrap.Alloc.AfterStart

/-!
# The allocator's words when refine starts decoding (pc 4642)

From Y's state (`StartMem`, `StartMemZ`), the start-up (the prefix to 38875, `Prefix.prefix_run`,
then the parameter chain to 4642, `BParamsHdr.run_hdr`) leaves every allocator word that
`Alloc.AfterStart.rep_sStart` asks for:

- the heads: bin 2431's is 206880 (the parameter chain's `dealloc` writes it), bin 2430's is 0
  (written by the chain too), every other one is still Y's 0 (no step writes [196792, 206512));
- the secondary bitmap words: word 37 is 2⁶³ (written by the chain), every other one is still Y's 0
  (no step writes [206528, 206824));
- the primary word 2³⁷, `next` 0 and the size word 2²⁶ of the header at 206880 (the chain's post);
- the base 206880 and the allocated space 6 (the prefix's post, kept by the chain);
- the header's `prev` 0 (the chain's post) and `prevL` 0 (`BParamsHdr`: `dealloc`'s
  `register_free_space` in segments 160 … 173).

`alloc_words_4642` states them in `rep_sStart`'s form, and `Rep μ' sStart`.
-/

namespace Services.Bootstrap.AllocStart

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Prefix
open Services.Bootstrap.Alloc Services.Bootstrap.Alloc.AfterStart

set_option maxHeartbeats 100000000
set_option maxRecDepth 100000

/-- The allocator's words that `rep_sStart` asks for. -/
structure AllocWords (μ : Memory) : Prop where
  heads : ∀ b, b < binCount → rdN μ (A0 + 4 * b) 4 = if b = 2431 then 206880 else 0
  sec : ∀ p, p < 38 → rdN μ (A0 + 9736 + 8 * p) 8 = if p = 37 then 2 ^ 63 else 0
  pri : rdN μ 206832 8 = 2 ^ 37
  base : rdN μ 206520 8 = 206880
  alloc : rdN μ 206840 4 = 6
  h0 : rdN μ 206880 4 = 0
  h1 : rdN μ 206884 4 = 2 ^ 26
  h2 : rdN μ 206888 4 = 0
  h3 : rdN μ 206892 4 = 0

theorem AllocWords.rep {μ : Memory} (h : AllocWords μ) : Rep μ sStart :=
  rep_sStart h.heads h.sec h.pri h.base h.alloc h.h0 h.h1 h.h2 h.h3

theorem rdN4_of {μ : Memory} {a : Nat} {x0 x1 x2 x3 : UInt8} (h0 : μ.read a = x0)
    (h1 : μ.read (a + 1) = x1) (h2 : μ.read (a + 2) = x2) (h3 : μ.read (a + 3) = x3) :
    rdN μ a 4 = Num.decodeLE [x0, x1, x2, x3] := by
  unfold rdN
  rw [show μ.readN a 4 = [μ.read (a + 0), μ.read (a + 1), μ.read (a + 2), μ.read (a + 3)] from rfl,
    Nat.add_zero, h0, h1, h2, h3]

theorem rdN8_of {μ : Memory} {a : Nat} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt8} (h0 : μ.read a = x0)
    (h1 : μ.read (a + 1) = x1) (h2 : μ.read (a + 2) = x2) (h3 : μ.read (a + 3) = x3)
    (h4 : μ.read (a + 4) = x4) (h5 : μ.read (a + 5) = x5) (h6 : μ.read (a + 6) = x6)
    (h7 : μ.read (a + 7) = x7) :
    rdN μ a 8 = Num.decodeLE [x0, x1, x2, x3, x4, x5, x6, x7] := by
  unfold rdN
  rw [show μ.readN a 8 = [μ.read (a + 0), μ.read (a + 1), μ.read (a + 2), μ.read (a + 3),
    μ.read (a + 4), μ.read (a + 5), μ.read (a + 6), μ.read (a + 7)] from rfl,
    Nat.add_zero, h0, h1, h2, h3, h4, h5, h6, h7]

theorem rdN4_zero {μ : Memory} {a : Nat} (h : ∀ j, j < 4 → μ.read (a + j) = 0) : rdN μ a 4 = 0 := by
  have h0 := h 0 (by omega); rw [Nat.add_zero] at h0
  rw [rdN4_of h0 (h 1 (by omega)) (h 2 (by omega)) (h 3 (by omega))]; rfl

theorem rdN8_zero {μ : Memory} {a : Nat} (h : ∀ j, j < 8 → μ.read (a + j) = 0) : rdN μ a 8 = 0 := by
  have h0 := h 0 (by omega); rw [Nat.add_zero] at h0
  rw [rdN8_of h0 (h 1 (by omega)) (h 2 (by omega)) (h 3 (by omega)) (h 4 (by omega))
    (h 5 (by omega)) (h 6 (by omega)) (h 7 (by omega))]; rfl

/-- **The allocator's words at 4642.** From Y's state, for an argument of any length 1 … 2²⁴ and a
    refine environment whose `fetch` returns the full chain's constants, the first 3429 steps of
    refine reach 4642 with every allocator word `rep_sStart` asks for (so `Rep μ' sStart`), and
    ℰ₂(𝖢) at 196616 and ℰ₈(𝖰) at 196680 as in `StartupConsts.startup_consts`. -/
theorem alloc_words_4642 (p : ByteArray) (P : Program) [HasCode p P] (env : RefineHost.Env)
    (henv : heapBounds env.code = (48, 1044430)) (hpar : env.fetch.params = Params.full) (μ : Memory)
    (L : Nat) (hL : 0 < L ∧ L ≤ 16777216) (hμ : StartMem μ) (hz : StartMemZ μ) :
    ∃ ω' μ', FreeStepsH p (refineContract env) 0 (initRegs L) μ ((∅, []) : RefineCtx) 4642 ω' μ'
      ((∅, []) : RefineCtx) 3429 ∧
      AllocWords μ' ∧ Rep μ' sStart ∧
      μ'.readN 196616 2 = Codec.fixed 2 Params.full.coreCount ∧
      μ'.readN 196680 8 = Codec.fixed 8 Params.full.authQueueSize := by
  obtain ⟨ω1, μ1, x1, run1, post1⟩ := prefix_run p P env henv hpar μ L hL hμ
  obtain ⟨r1_0, r1_1, r1_2, r1_3, r1_4, r1_5, r1_6, r1_7, r1_8, r1_9, r1_12⟩ := post1.regs
  have hx1 := post1.ctx
  subst hx1
  have pbr := post1.bytes
  have fr1 := post1.frame
  have hst1 := post1.stack
  have hhp1 := post1.heap
  have hfr1 := post1.frame
  have hro1 := post1.ro
  have hlw1 := post1.lenWords
  simp only [lenAt, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hlw1
  have pb1 := post1.bytes
  simp only [postBytes, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true] at pb1
  have ib0 : ∀ q ∈ baseBytes, μ.read q.1 = q.2 := fun q hq => hμ.bytes q.1 q.2 hq
  simp only [baseBytes, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true] at ib0
  have ip0 : ∀ q ∈ pathBytes, μ.read q.1 = q.2 := fun q hq => hμ.path q.1 q.2 hq
  simp only [pathBytes, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true] at ip0
  refine (fun h2 => ?_) (BParamsHdr.run_hdr p P env ω1 μ1 ((∅, []) : RefineCtx) L ⟨by omega, by omega⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  · obtain ⟨ω2, μ2, run2, -, ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63⟩, -, fr2, -, -, hC, hQ, hZ⟩ := h2
    -- octets no step writes: Y's zeros
    have z : ∀ a, (196792 ≤ a ∧ a < 206512 ∨ 206528 ≤ a ∧ a < 206824) → μ2.read a = 0 := by
      intro a ha
      rw [fr2 a (by simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
            decide_eq_false_iff_not, not_and, Nat.not_lt]; omega),
        fr1 a (by simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
            decide_eq_false_iff_not, not_and, Nat.not_lt]; omega)]
      exact hz.zero a (by omega) (by omega)
    -- octets the prefix leaves and the chain keeps
    have k : ∀ a, (206520 ≤ a ∧ a < 206528 ∨ 206840 ≤ a ∧ a < 206844) → μ2.read a = μ1.read a := by
      intro a ha
      exact fr2 a (by simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
            decide_eq_false_iff_not, not_and, Nat.not_lt]; omega)
    have hw : AllocWords μ2 := by
      refine ⟨fun b hb => ?_, fun q hq => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · unfold A0; unfold binCount at hb
        by_cases e1 : b = 2431
        · subst e1; simp only [↓reduceIte]; show rdN μ2 206516 4 = 206880; rw [rdN4_of b4 b5 b6 b7]; rfl
        · simp only [e1, ↓reduceIte]
          by_cases e0 : b = 2430
          · subst e0; show rdN μ2 206512 4 = 0; rw [rdN4_of b0 b1 b2 b3]; rfl
          · exact rdN4_zero fun j hj => z _ (by omega)
      · unfold A0
        by_cases e1 : q = 37
        · subst e1; simp only [↓reduceIte]; show rdN μ2 206824 8 = 2 ^ 63; rw [rdN8_of b8 b9 b10 b11 b12 b13 b14 b15]; rfl
        · simp only [e1, ↓reduceIte]; exact rdN8_zero fun j hj => z _ (by omega)
      · rw [rdN8_of b16 b17 b18 b19 b20 b21 b22 b23]; rfl
      · rw [rdN8_of ((k 206520 (by omega)).trans (pbr (206520, 32) (by decide)))
          ((k 206521 (by omega)).trans (pbr (206521, 40) (by decide)))
          ((k 206522 (by omega)).trans (pbr (206522, 3) (by decide)))
          ((k 206523 (by omega)).trans (pbr (206523, 0) (by decide)))
          ((k 206524 (by omega)).trans (pbr (206524, 0) (by decide)))
          ((k 206525 (by omega)).trans (pbr (206525, 0) (by decide)))
          ((k 206526 (by omega)).trans (pbr (206526, 0) (by decide)))
          ((k 206527 (by omega)).trans (pbr (206527, 0) (by decide)))]; rfl
      · rw [rdN4_of ((k 206840 (by omega)).trans (pbr (206840, 6) (by decide)))
          ((k 206841 (by omega)).trans (pbr (206841, 0) (by decide)))
          ((k 206842 (by omega)).trans (pbr (206842, 0) (by decide)))
          ((k 206843 (by omega)).trans (pbr (206843, 0) (by decide)))]; rfl
      · rw [rdN4_of b28 b29 b30 b31]; rfl
      · rw [rdN4_of b32 b33 b34 b35]; rfl
      · rw [rdN4_of b36 b37 b38 b39]; rfl
      · unfold rdN; rw [hZ]; rfl
    exact ⟨ω2, μ2, run1.trans run2, hw, hw.rep, hC.trans StartupConsts.coreCount_full.symm,
      hQ.trans StartupConsts.authQueueSize_full.symm⟩
  all_goals first
    | chase
    | (intro a h1 h2; first
        | exact Memory.readable_of_writable (hhp1 a (by omega) (by omega))
        | exact Memory.readable_of_writable (hst1 a (by omega) (by omega)))

end Services.Bootstrap.AllocStart
