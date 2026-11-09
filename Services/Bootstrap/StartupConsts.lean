import Services.Bootstrap.Prefix
import Services.Bootstrap.BParamsConsts
import PVM.Logic.Words

/-!
# Bootstrap's start-up leaves 𝖢 at 196616 and 𝖰 at 196680

From Y's state (GP eq. `registers`, `conditions`), in every refine environment whose `fetch` case 0
returns the full chain's constants (`env.fetch.params = Params.full`, the assumption `PrefixC` and
`Prefix.prefix_run` already make; GP v0.8.0 Appendix B, Ω_Y), the first 3429 steps of refine (the
prefix to 38875 and the parameter chain to 4642) leave:

- at 196616 … 196618, ℰ₂(𝖢), the octets 24 … 26 of `fetch`'s reply (`Params.encode`);
- at 196680 … 196688, ℰ₈(𝖰), 𝖰 being the octets 82 … 84 of the reply, widened to a word.

`startup_consts` is that statement. The corollaries put it in the forms the decoders assume: the
16-bit word `rdN μ 196616 2` is 𝖢 (`coreCount_rdN`, `Decode.Designate`'s bound 3·𝖢), and the word at
196680 is a G < 2⁶⁴ with G mod 2³² = 𝖰 ∈ 1 … 512 (`authQueue_word`, `Decode.Assign`'s queue length).
-/

namespace Services.Bootstrap.StartupConsts

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Prefix

set_option maxHeartbeats 100000000
set_option maxRecDepth 100000

/-! ## The reply's fields (GP v0.8.0 Appendix B, Ω_Y case 0) -/

/-- Dropping k ≥ n octets past an n-octet field. -/
theorem drop_fixed {n k : Nat} (x : Nat) (l : List UInt8) (h : n ≤ k) :
    (Codec.fixed n x ++ l).drop k = l.drop (k - n) := by
  rw [List.drop_append, Codec.fixed, PVM.Num.length_encodeLE,
    List.drop_eq_nil_of_le (by rw [PVM.Num.length_encodeLE]; exact h), List.nil_append]

/-- The first n octets of an n-octet field and what follows are the field. -/
theorem take_fixed (n x : Nat) (l : List UInt8) : (Codec.fixed n x ++ l).take n = Codec.fixed n x :=
  List.take_left' (PVM.Num.length_encodeLE _ _)

/-- ℰ₂(𝖢) is octets 24 … 26 of `fetch` case 0's reply: after ℰ₈(𝖡_I), ℰ₈(𝖡_L), ℰ₈(𝖡_S)
    (GP v0.8.0 Appendix B, Ω_Y). -/
theorem coreCount_octets (c : Params) : (c.encode.drop 24).take 2 = Codec.fixed 2 c.coreCount := by
  unfold Params.encode
  simp only [List.append_assoc]
  repeat (rw [drop_fixed _ _ (by decide)]; simp only [Nat.reduceSub])
  rw [List.drop_zero, take_fixed]

/-- ℰ₂(𝖰) is octets 82 … 84 of `fetch` case 0's reply: after ℰ₈(𝖡_I, 𝖡_L, 𝖡_S), ℰ₂(𝖢),
    ℰ₄(𝖣, 𝖤), ℰ₈(𝖦_A, 𝖦_I, 𝖦_R, 𝖦_T), ℰ₂(𝖧, 𝖨, 𝖩, 𝖪), ℰ₄(𝖫), ℰ₂(𝖮, 𝖯) (GP v0.8.0 Appendix B,
    Ω_Y). -/
theorem authQueueSize_octets (c : Params) :
    (c.encode.drop 82).take 2 = Codec.fixed 2 c.authQueueSize := by
  unfold Params.encode
  simp only [List.append_assoc]
  repeat (rw [drop_fixed _ _ (by decide)]; simp only [Nat.reduceSub])
  rw [List.drop_zero, take_fixed]

/-- The full chain's 𝖢 = 341 encodes as [85, 1]. -/
theorem coreCount_full : Codec.fixed 2 Params.full.coreCount = [85, 1] := by decide

/-- The full chain's 𝖰 = 80 widened to a word encodes as [80, 0, 0, 0, 0, 0, 0, 0]. -/
theorem authQueueSize_full : Codec.fixed 8 Params.full.authQueueSize = [80, 0, 0, 0, 0, 0, 0, 0] := by
  decide

/-! ## From Y -/

/-- **Bootstrap's start-up stores 𝖢 and 𝖰.** From Y's state, for an argument of any length
    1 … 2²⁴ and a refine environment whose `fetch` returns the full chain's constants, the first
    3429 steps of refine reach 4642 (where the core index's decode begins) with ℰ₂(𝖢) at 196616 and
    ℰ₈(𝖰) at 196680 (GP v0.8.0 Appendix B, Ω_Y case 0; `Params.full`). -/
theorem startup_consts (p : ByteArray) (P : Program) [HasCode p P] (env : RefineHost.Env)
    (henv : heapBounds env.code = (48, 1044430)) (hpar : env.fetch.params = Params.full) (μ : Memory)
    (L : Nat) (hL : 0 < L ∧ L ≤ 16777216) (hμ : StartMem μ) :
    ∃ ω' μ', FreeStepsH p (refineContract env) 0 (initRegs L) μ ((∅, []) : RefineCtx) 4642 ω' μ'
      ((∅, []) : RefineCtx) 3429 ∧
      μ'.readN 196616 2 = Codec.fixed 2 Params.full.coreCount ∧
      μ'.readN 196680 8 = Codec.fixed 8 Params.full.authQueueSize := by
  obtain ⟨ω1, μ1, x1, run1, post1⟩ := prefix_run p P env henv hpar μ L hL hμ
  obtain ⟨r1_0, r1_1, r1_2, r1_3, r1_4, r1_5, r1_6, r1_7, r1_8, r1_9, r1_12⟩ := post1.regs
  have hx1 := post1.ctx
  subst hx1
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
  refine (fun h2 => ?_) (BParamsConsts.run_consts p P env ω1 μ1 ((∅, []) : RefineCtx) L ⟨by omega, by omega⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  · obtain ⟨ω2, μ2, run2, -, -, -, -, -, -, hC, hQ⟩ := h2
    exact ⟨ω2, μ2, run1.trans run2, hC.trans coreCount_full.symm, hQ.trans authQueueSize_full.symm⟩
  all_goals first
    | chase
    | (intro a h1 h2; first
        | exact Memory.readable_of_writable (hhp1 a (by omega) (by omega))
        | exact Memory.readable_of_writable (hst1 a (by omega) (by omega)))

/-! ## The decoders' hypotheses -/

/-- **`Designate`'s 𝖢**: in a memory holding ℰ₂(𝖢) at 196616, as `startup_consts` leaves it, the
    16-bit word `rdN μ 196616 2` is the core count 𝖢 = 341. -/
theorem coreCount_rdN {μ : Memory} (h : μ.readN 196616 2 = Codec.fixed 2 Params.full.coreCount) :
    rdN μ 196616 2 = Params.full.coreCount := by
  rw [rdN, h, coreCount_full]; decide

/-- **`Assign`'s queue length**: in a memory holding ℰ₈(𝖰) at 196680, as `startup_consts` leaves
    it, the octets there are ℰ₈(G) for G = 𝖰 = 80, and G < 2⁶⁴ with 1 ≤ G mod 2³² ≤ 512 (and
    G mod 2³² = 𝖰). The octets are given both as `readN` and octet by octet (the form of
    `Decode.Assign`'s globals `gl`). -/
theorem authQueue_word {μ : Memory} (h : μ.readN 196680 8 = Codec.fixed 8 Params.full.authQueueSize) :
    μ.readN 196680 8 = Num.encodeLE 8 Params.full.authQueueSize ∧
      (List.range 8).map (fun k => μ.read (196680 + k)) = Num.encodeLE 8 Params.full.authQueueSize ∧
      Params.full.authQueueSize < 18446744073709551616 ∧
      Params.full.authQueueSize % 4294967296 = Params.full.authQueueSize ∧
      1 ≤ Params.full.authQueueSize % 4294967296 ∧ Params.full.authQueueSize % 4294967296 ≤ 512 := by
  refine ⟨h, ?_, by decide, by decide, by decide, by decide⟩
  exact (show (List.range 8).map (fun k => μ.read (196680 + k)) = μ.readN 196680 8 from rfl).trans h

/-- `startup_consts`, with the decoders' forms: after the start-up, `rdN μ' 196616 2 = 𝖢` and the
    word at 196680 is 𝖰, with 1 ≤ 𝖰 mod 2³² ≤ 512. -/
theorem startup_decoder_facts (p : ByteArray) (P : Program) [HasCode p P] (env : RefineHost.Env)
    (henv : heapBounds env.code = (48, 1044430)) (hpar : env.fetch.params = Params.full) (μ : Memory)
    (L : Nat) (hL : 0 < L ∧ L ≤ 16777216) (hμ : StartMem μ) :
    ∃ ω' μ', FreeStepsH p (refineContract env) 0 (initRegs L) μ ((∅, []) : RefineCtx) 4642 ω' μ'
      ((∅, []) : RefineCtx) 3429 ∧
      rdN μ' 196616 2 = Params.full.coreCount ∧
      μ'.readN 196680 8 = Num.encodeLE 8 Params.full.authQueueSize ∧
      1 ≤ Params.full.authQueueSize % 4294967296 ∧ Params.full.authQueueSize % 4294967296 ≤ 512 := by
  obtain ⟨ω', μ', hrun, hC, hQ⟩ := startup_consts p P env henv hpar μ L hL hμ
  obtain ⟨hQ', -, -, -, h1, h2⟩ := authQueue_word hQ
  exact ⟨ω', μ', hrun, coreCount_rdN hC, hQ', h1, h2⟩

end Services.Bootstrap.StartupConsts
