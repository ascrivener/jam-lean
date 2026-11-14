import Services.Bootstrap.Refine.ArgsRun
import Services.Bootstrap.AllocStart
import Services.Bootstrap.Decode.HeapCtx

/-!
# The allocator's context at 35130, in refine's argument parse

`ArgsRun.run_args_gen` runs refine from Y's state to 35130 (the payload's Vec read) for any payload
length. Here its post is named `ArgsPost`, and `args_ctx` adds, given `StartMemZ`, the allocator's
context `HeapCtx env 1044430 4278050816 4278059008 μ' sStart` there.

`run_args_hdr` is `run_args_gen` re-proved with `BParamsHdr.run_hdr` in place of `BParams.run`, so
that it also states the first chunk's `prevL` (206892 … 206896) is 0 at 35130; the rest of the
allocator's words come from the post's reads and its frame over Y's zeros (`StartMemZ.zero`), the
stack's writability and the read-only region from `FreeStepsH.keepRO` over the whole run.
-/

namespace Services.Bootstrap.Refine.ArgsCtx

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Prefix
open Services.Bootstrap.NoInstrArgs (prefix_run_pages heapPages_of_writable)

set_option maxHeartbeats 100000000
set_option maxRecDepth 100000

/-- **`run_args_gen`'s post** at 35130 (registers, memory facts and frame clauses). -/
def ArgsPost (p : ByteArray) (env : RefineHost.Env) (μ : Memory) (C I S Y : Nat) (y : List UInt8) (L : Nat)
    (ω' : Regs) (μ' : Memory) : Prop :=
      (ω'[1] = UInt64.ofNat 4278058264) ∧
      (ω'[4] = UInt64.ofNat 8) ∧
      (ω'[5] = UInt64.ofNat 4278058544) ∧
      (ω'[6] = UInt64.ofNat 4278124544) ∧
      (ω'[7] = UInt64.ofNat 0) ∧
      (ω'[8] = UInt64.ofNat Y) ∧
      (μ'.readN 206512 8 = [0, 0, 0, 0, 32, 40, 3, 0]) ∧
      (μ'.readN 206520 8 = [32, 40, 3, 0, 0, 0, 0, 0]) ∧
      (μ'.readN 206824 8 = [0, 0, 0, 0, 0, 0, 0, 128]) ∧
      (μ'.readN 206832 8 = [0, 0, 0, 0, 32, 0, 0, 0]) ∧
      (μ'.readN 206840 4 = [6, 0, 0, 0]) ∧
      (μ'.readN 206848 4 = [0, 0, 0, 0]) ∧
      (μ'.readN 206880 8 = [0, 0, 0, 0, 0, 0, 0, 4]) ∧
      (μ'.readN 206888 4 = [0, 0, 0, 0]) ∧
      (μ'.readN 4278058312 8 = Num.encodeLE 8 (Y + 32)) ∧
      (∀ a, 196608 ≤ a → a < 196616 → μ'.writable a = true) ∧
      (∀ a, 206512 ≤ a → a < 206520 → μ'.writable a = true) ∧
      (∀ a, 206824 ≤ a → a < 206840 → μ'.writable a = true) ∧
      (∀ a, 206848 ≤ a → a < 206852 → μ'.writable a = true) ∧
      (∀ a, 206880 ≤ a → a < 206888 → μ'.writable a = true) ∧
      (∀ a, 206976 ≤ a → a < 206992 → μ'.writable a = true) ∧
      (∀ a, 4278057992 ≤ a → a < 4278058264 → μ'.writable a = true) ∧
      (∀ a, 206512 ≤ a → a < 206528 → μ'.readable a = true) ∧
      (∀ a, 206824 ≤ a → a < 206844 → μ'.readable a = true) ∧
      (∀ a, 206848 ≤ a → a < 206852 → μ'.readable a = true) ∧
      (∀ a, 206880 ≤ a → a < 206892 → μ'.readable a = true) ∧
      (∀ a, 4278057992 ≤ a → a < 4278058016 → μ'.readable a = true) ∧
      (∀ a, 4278058024 ≤ a → a < 4278058128 → μ'.readable a = true) ∧
      (∀ a, 4278058136 ≤ a → a < 4278058176 → μ'.readable a = true) ∧
      (∀ a, 4278058184 ≤ a → a < 4278058200 → μ'.readable a = true) ∧
      (∀ a, 4278058224 ≤ a → a < 4278058232 → μ'.readable a = true) ∧
      (∀ a, 4278058312 ≤ a → a < 4278058320 → μ'.readable a = true) ∧
      (μ'.readN 66657 7 = [26, 66, 111, 111, 116, 115, 116]) ∧
      (μ'.readN 66664 8 = [114, 97, 112, 32, 83, 101, 114, 118]) ∧
      (μ'.readN 66672 8 = [105, 99, 101, 32, 82, 101, 102, 105]) ∧
      (μ'.readN 66680 8 = [110, 101, 44, 32, 192, 1, 104, 0]) ∧
      (μ'.readN 71060 4 = [48, 49, 50, 51]) ∧
      (μ'.readN 71064 8 = [52, 53, 54, 55, 56, 57, 97, 98]) ∧
      (μ'.readN 71072 4 = [99, 100, 101, 102]) ∧
      (μ'.readN 77040 8 = [36, 10, 0, 0, 0, 0, 0, 0]) ∧
      (μ'.readN 4278058352 8 = [0, 0, 255, 254, 0, 0, 0, 0]) ∧
      (μ'.readN 4278058368 8 = [152, 0, 0, 0, 0, 0, 0, 0]) ∧
      (μ'.readN 4278058360 8 = Num.encodeLE 8 L) ∧
      (∀ a, 206512 ≤ a → a < 206516 → μ'.writable a = true) ∧
      (∀ a, 206824 ≤ a → a < 206844 → μ'.writable a = true) ∧
      (∀ a, 207008 ≤ a → a < 207036 → μ'.writable a = true) ∧
      (∀ a, 207072 ≤ a → a < 207088 → μ'.writable a = true) ∧
      (∀ a, 4278057712 ≤ a → a < 4278057720 → μ'.writable a = true) ∧
      (∀ a, 4278057728 ≤ a → a < 4278057752 → μ'.writable a = true) ∧
      (∀ a, 4278057984 ≤ a → a < 4278058000 → μ'.writable a = true) ∧
      (∀ a, 4278058064 ≤ a → a < 4278058088 → μ'.writable a = true) ∧
      (∀ a, 4278058104 ≤ a → a < 4278058376 → μ'.writable a = true) ∧
      (∀ a, 4278058456 ≤ a → a < 4278058472 → μ'.writable a = true) ∧
      (∀ a, 4278058488 ≤ a → a < 4278058496 → μ'.writable a = true) ∧
      (∀ a, 4278058544 ≤ a → a < 4278058610 → μ'.writable a = true) ∧
      (∀ a, 4278058620 ≤ a → a < 4278058624 → μ'.writable a = true) ∧
      (∀ a, 4278058648 ≤ a → a < 4278058664 → μ'.writable a = true) ∧
      (∀ a, 66657 ≤ a → a < 66688 → μ'.readable a = true) ∧
      (∀ a, 71060 ≤ a → a < 71076 → μ'.readable a = true) ∧
      (∀ a, 77040 ≤ a → a < 77048 → μ'.readable a = true) ∧
      (∀ a, 206512 ≤ a → a < 206516 → μ'.readable a = true) ∧
      (∀ a, 206520 ≤ a → a < 206528 → μ'.readable a = true) ∧
      (∀ a, 206884 ≤ a → a < 206888 → μ'.readable a = true) ∧
      (∀ a, 206912 ≤ a → a < 206913 → μ'.readable a = true) ∧
      (∀ a, 206976 ≤ a → a < 206988 → μ'.readable a = true) ∧
      (∀ a, 207076 ≤ a → a < 207084 → μ'.readable a = true) ∧
      (∀ a, 4278058064 ≤ a → a < 4278058072 → μ'.readable a = true) ∧
      (∀ a, 4278058104 ≤ a → a < 4278058120 → μ'.readable a = true) ∧
      (∀ a, 4278058128 ≤ a → a < 4278058376 → μ'.readable a = true) ∧
      (∀ a, 4278058488 ≤ a → a < 4278058496 → μ'.readable a = true) ∧
      (∀ a, 4278058544 ≤ a → a < 4278058568 → μ'.readable a = true) ∧
      (∀ a, 4278058600 ≤ a → a < 4278058604 → μ'.readable a = true) ∧
      (∀ a, 4278058620 ≤ a → a < 4278058624 → μ'.readable a = true) ∧
      (∀ a, 4278058648 ≤ a → a < 4278058664 → μ'.readable a = true) ∧
      (JAM.HeapPages μ' 48 1044430 51) ∧
      (∀ a, 207008 ≤ a → a < 207037 → μ'.writable a = true) ∧
      (∀ a, 4278057744 ≤ a → a < 4278057752 → μ'.readable a = true) ∧
      (∀ a, 4278058072 ≤ a → a < 4278058088 → μ'.readable a = true) ∧
      (∀ a, 4278058104 ≤ a → a < 4278058376 → μ'.readable a = true) ∧
      (∀ a, 207008 ≤ a → a < 207038 → μ'.writable a = true) ∧
      (∀ a, 4278057736 ≤ a → a < 4278057752 → μ'.readable a = true) ∧
      (∀ a, 4278058064 ≤ a → a < 4278058088 → μ'.readable a = true) ∧
      (∀ a, 207008 ≤ a → a < 207039 → μ'.writable a = true) ∧
      (∀ a, 207008 ≤ a → a < 207040 → μ'.writable a = true) ∧
      (∀ a, 207008 ≤ a → a < 207041 → μ'.writable a = true) ∧
      (∀ a, 207008 ≤ a → a < 207042 → μ'.writable a = true) ∧
      (∀ a, 4278057736 ≤ a → a < 4278057744 → μ'.readable a = true) ∧
      (∀ a, 207008 ≤ a → a < 207043 → μ'.writable a = true) ∧
      (∀ a, 196608 ≤ a → a < 196616 → μ'.readable a = true) ∧
      (μ'.readN 4278058280 8 = Num.encodeLE 8 S) ∧
      (μ'.readN 4278058288 8 = Num.encodeLE 8 I) ∧
      (μ'.readN 4278058296 8 = Num.encodeLE 8 C) ∧
      (μ'.readN 4278058304 8 = Num.encodeLE 8 (4278124544 + (Blob.encodeNat C).length + (Blob.encodeNat I).length + (Blob.encodeNat S).length + (Blob.encodeNat Y).length)) ∧
      (μ'.readN (4278124544 + (Blob.encodeNat C).length + (Blob.encodeNat I).length + (Blob.encodeNat S).length + (Blob.encodeNat Y).length) Y = y) ∧
      (∀ a, 4278124544 ≤ a → a < 4278124544 + L → μ'.readable a = true) ∧
      (∀ a, 4278057688 ≤ a → a < 4278059008 → μ'.writable a = true) ∧
      (∀ a, 196608 ≤ a → a < 208896 → μ'.writable a = true) ∧
      (μ'.readN 66099 5 = [10, 82, 101, 116, 117]) ∧
      (μ'.readN 66104 8 = [114, 110, 105, 110, 103, 32, 192, 16]) ∧
      (μ'.readN 66112 8 = [32, 105, 110, 116, 111, 32, 97, 99]) ∧
      (μ'.readN 66120 8 = [99, 117, 109, 117, 108, 97, 116, 101]) ∧
      (μ'.readN 66128 1 = [0]) ∧
      (μ'.readN 72826 1 = [93]) ∧
      (μ'.readN 72829 1 = [91]) ∧
      (μ'.readN 196800 4 = [0, 0, 0, 0]) ∧
      (μ'.readN 206528 8 = [0, 0, 0, 0, 0, 0, 0, 0]) ∧
      (μ'.readN 4278058984 8 = [0, 0, 0, 0, 0, 0, 0, 0]) ∧
      (μ'.readN 4278058992 8 = [0, 0, 0, 0, 0, 0, 0, 0]) ∧
      (μ'.readN 4278059000 8 = [0, 0, 255, 255, 0, 0, 0, 0]) ∧
      (∀ a, 196800 ≤ a → a < 196804 → μ'.writable a = true) ∧
      (∀ a, 206528 ≤ a → a < 206536 → μ'.writable a = true) ∧
      (∀ a, 206880 ≤ a → a < 206896 → μ'.writable a = true) ∧
      (∀ a, 207040 ≤ a → a < 207056 → μ'.writable a = true) ∧
      (∀ a, 4278058064 ≤ a → a < 4278058376 → μ'.writable a = true) ∧
      (∀ a, 4278058496 ≤ a → a < 4278058504 → μ'.writable a = true) ∧
      (∀ a, 4278058544 ≤ a → a < 4278058600 → μ'.writable a = true) ∧
      (∀ a, 4278058624 ≤ a → a < 4278058680 → μ'.writable a = true) ∧
      (∀ a, 66099 ≤ a → a < 66129 → μ'.readable a = true) ∧
      (∀ a, 72826 ≤ a → a < 72827 → μ'.readable a = true) ∧
      (∀ a, 72829 ≤ a → a < 72830 → μ'.readable a = true) ∧
      (∀ a, 196800 ≤ a → a < 196804 → μ'.readable a = true) ∧
      (∀ a, 206520 ≤ a → a < 206536 → μ'.readable a = true) ∧
      (∀ a, 206880 ≤ a → a < 206888 → μ'.readable a = true) ∧
      (∀ a, 207008 ≤ a → a < 207011 → μ'.readable a = true) ∧
      (∀ a, 4278058064 ≤ a → a < 4278058376 → μ'.readable a = true) ∧
      (∀ a, 4278058456 ≤ a → a < 4278058472 → μ'.readable a = true) ∧
      (∀ a, 4278058544 ≤ a → a < 4278058570 → μ'.readable a = true) ∧
      (∀ a, 4278058624 ≤ a → a < 4278058680 → μ'.readable a = true) ∧
      (∀ a, 4278058984 ≤ a → a < 4278059008 → μ'.readable a = true) ∧
      -- frame: nothing at or above the stack's top (so nothing in the argument zone) changes
      (∀ a, 4278059008 ≤ a → a < 4294967296 → μ'.read a = μ.read a) ∧
      -- frame: below the stack's written part, only the prefix's and the parameter chain's
      -- globals/allocator words change
      (∀ a, a < 4278057688 → ¬(196608 ≤ a ∧ a < 196618) → ¬(196620 ≤ a ∧ a < 196668) →
        ¬(196672 ≤ a ∧ a < 196792) → ¬(206512 ≤ a ∧ a < 206528) → ¬(206824 ≤ a ∧ a < 206844) →
        ¬(206848 ≤ a ∧ a < 206852) → ¬(206880 ≤ a ∧ a < 206896) → ¬(206912 ≤ a ∧ a < 207034) →
        ¬(207040 ≤ a ∧ a < 207056) → μ'.read a = μ.read a) ∧
      -- the state at 4642 (the core index's decode), and from there to 35130 only the decodes'
      -- stack frames [4278058136, 4278058320) change
      (∃ ω₂ μ₂, FreeStepsH p (refineContract env) 0 (initRegs L) μ ((∅, []) : RefineCtx) 4642 ω₂ μ₂
          ((∅, []) : RefineCtx) 3429 ∧
        FreeStepsH p (refineContract env) 4642 ω₂ μ₂ ((∅, []) : RefineCtx) 35130 ω' μ'
          ((∅, []) : RefineCtx) 2016 ∧
        (∀ a, a < 4294967296 → (a < 4278058136 ∨ 4278058320 ≤ a) → μ'.read a = μ₂.read a) ∧
        (∀ a, μ'.readable a = μ₂.readable a) ∧ (∀ a, μ'.writable a = μ₂.writable a))

/-- `ArgsRun.run_args_gen`, with its post as `ArgsPost`, and in addition the first chunk's `prevL`
    (the octets 206892 … 206896) 0 at 35130 (via `BParamsHdr.run_hdr`). -/
theorem run_args_hdr (p : ByteArray) (P : Program) [HasCode p P] (env : RefineHost.Env)
    (henv : heapBounds env.code = (48, 1044430)) (hpar : env.fetch.params = Params.full) (μ : Memory)
    (hμ : StartMem μ) (C I S : Nat) (h : List UInt8) (hC : C < 65536) (hI : I < 65536)
    (hS : S < 4294967296) (Y : Nat) (hY1 : 1 ≤ Y) (hY : Y < 16777216) (y : List UInt8) (hy : y.length = Y)
    (hh : h.length = 32) (L : Nat)
    (hLdef : (Blob.encodeNat C).length + (Blob.encodeNat I).length + (Blob.encodeNat S).length +
      (Blob.encodeNat Y).length + Y + 32 = L) (hL : L < 16777217)
    (hmem : μ.readN 4278124544 L = Blob.encodeNat C ++ Blob.encodeNat I ++ Blob.encodeNat S ++
      Blob.encodeNat Y ++ y ++ h)
    (hrd : ∀ j, 4278124544 ≤ j → j < 4278124544 + L → μ.readable j = true) :
    ∃ ω' μ', FreeStepsH p (refineContract env) 0 (initRegs L) μ ((∅, []) : RefineCtx) 35130 ω' μ'
      ((∅, []) : RefineCtx) 6000 ∧ ArgsPost p env μ C I S Y y L ω' μ' ∧
      μ'.readN 206892 4 = [0, 0, 0, 0] := by
  have hwC := encodeNat_len_le3 C hC
  have hwI := encodeNat_len_le3 I hI
  have hwS := encodeNat_len_le5 S hS
  have hwY := encodeNat_len_le5 Y (by omega)
  obtain ⟨ω1, μ1, x1, run1, post1, hpg1⟩ := prefix_run_pages p P env henv hpar μ L ⟨by omega, by omega⟩ hμ
  obtain ⟨r1_0, r1_1, r1_2, r1_3, r1_4, r1_5, r1_6, r1_7, r1_8, r1_9, r1_12⟩ := post1.regs
  have hx1 := post1.ctx
  subst hx1
  have hst1 := post1.stack
  have hhp1 := post1.heap
  have hfr1 := post1.frame
  have hag1 := post1.args
  have har1 := post1.argsRd
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
  -- the parameter chain, to the core index's decode at 4642
  refine (fun h2 => ?_) (BParamsHdr.run_hdr p P env ω1 μ1 ((∅, []) : RefineCtx) L ⟨by omega, by omega⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  · obtain ⟨ω2, μ2, run2, g2, m2, s2, f2, rd2, wr2, -, -, hZ2⟩ := h2
    obtain ⟨g2_0, g2_1, g2_2, g2_3, g2_4, g2_5, g2_6, g2_7, g2_8, g2_10, g2_11, g2_12, g2_9⟩ := g2
    obtain ⟨s2a, s2b⟩ := s2
    -- the arguments, sliced
    have sC : μ.readN 4278124544 (Blob.encodeNat C).length = Blob.encodeNat C := by
      have := Memory.readN_mid μ 4278124544 [] (Blob.encodeNat C)
        (Blob.encodeNat I ++ Blob.encodeNat S ++ Blob.encodeNat Y ++ y ++ h)
        (by
          rw [show (([] : List UInt8) ++ Blob.encodeNat C ++ (Blob.encodeNat I ++ Blob.encodeNat S ++ Blob.encodeNat Y ++ y ++ h)).length = L by
            simp [hh, hy]; omega]
          simpa only [List.nil_append, List.append_assoc] using hmem)
      simpa using this
    -- the arguments are as they started, up to the core index's decode
    have arg2 : ∀ a, 4278124544 ≤ a → a < 4278124544 + L → μ2.read a = μ.read a := fun a h1 h2 =>
      (f2 a (by simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]; omega)).trans
        (hag1 a h1 h2)
    -- 4642: the return address of the inlined decode
    obtain ⟨ω3, run3, e3_0, e3fr⟩ : ∃ ω3, FreeStepsH p (refineContract env) 4642 ω2 μ2 ((∅, []) : RefineCtx) 4646 ω3 μ2
        ((∅, []) : RefineCtx) 1 ∧ ω3[0] = UInt64.ofNat 1634 ∧ ∀ j : Fin 13, j.val ≠ 0 → ω3[j] = ω2[j] := by
      rw [show ω2 = regsNF ω2 [] from rfl]
      refine ⟨?ω₃, ?r, ?e0, fun j hj => ?fr⟩
      case r => pvm_go []
      case e0 => simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, ↓reduceIte, PVM.getD_some']
      case fr =>
        simp only [Fin.getElem_fin]
        rw [PVM.getElem_regsNF _ _ _ j.isLt]
        simp [PVM.lookup_cons_nat, hj]
        rfl
    -- c
    obtain ⟨ω4, μ4, run4, d4_0, d4_1, d4_2, d4_3, d4_4, d4_5, d4_6, d4_12, d4_7, d4_8, d4_r0, d4_r8, d4_fr, d4_rd, d4_wr⟩ :=
      decodeU16 (p := p) (P := P) (R := refineContract env) ((∅, []) : RefineCtx) ω3 μ2 1634 35073 4278058264
        4278058304 4278124544 L e3_0 ((e3fr 1 (by decide)).trans g2_1) ((e3fr 7 (by decide)).trans g2_7) (by decide)
        (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_816]) bs_35073 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (fun a h1 h2 => by rw [wr2]; exact hst1 a (by omega) (by omega))
        (fun a h1 h2 => by rw [wr2]; exact hst1 a (by omega) (by omega))
        (by chase) (by chase) C hC ⟨by omega, by omega⟩
        (fun a h1 h2 => by rw [rd2, har1 a h1 (by omega)]; exact hrd a h1 (by omega))
        (by rw [Memory.readN_congr (fun j hj => arg2 _ (by omega) (by omega))]; exact sC)
    have arg4 : ∀ a, 4278124544 ≤ a → a < 4278124544 + L → μ4.read a = μ.read a := fun a h1 h2 =>
      (d4_fr a (by omega) (by omega) (by omega)).trans (arg2 a h1 h2)
    -- store c, call the decode of i
    obtain ⟨ω5, run5, e5_0, e5_1, e5_7, e5fr⟩ := glueC (p := p) (P := P) (R := refineContract env)
      ((∅, []) : RefineCtx) ω4 μ4 C (by omega) d4_7 d4_8 (d4_1.trans ((e3fr 1 (by decide)).trans g2_1))
      (fun a h1 h2 => by rw [d4_wr, wr2]; exact hst1 a (by omega) (by omega))
    have arg5 : ∀ a, 4278124544 ≤ a → a < 4278124544 + L →
        (μ4.writeN 4278058296 (Num.encodeLE 8 C)).read a = μ.read a := fun a h1 h2 => by
      rw [Memory.read_writeN_disjoint _ _ _ _ (by simp <;> omega) (by simp [two32]) (by simp [two32] <;> omega)]
      exact arg4 a h1 h2
    have sI : μ.readN (4278124544 + (Blob.encodeNat C).length) (Blob.encodeNat I).length = Blob.encodeNat I := by
      apply Memory.readN_mid μ 4278124544 (Blob.encodeNat C) (Blob.encodeNat I)
        (Blob.encodeNat S ++ Blob.encodeNat Y ++ y ++ h)
      rw [show (Blob.encodeNat C ++ Blob.encodeNat I ++ (Blob.encodeNat S ++ Blob.encodeNat Y ++ y ++ h)).length = L by
        simp [hh, hy]; omega]
      simpa only [List.append_assoc] using hmem
    -- i
    obtain ⟨ω6, μ6, run6, d6_0, d6_1, d6_2, d6_3, d6_4, d6_5, d6_6, d6_12, d6_7, d6_8, d6_r0, d6_r8, d6_fr, d6_rd, d6_wr⟩ :=
      decodeU32 (p := p) (P := P) (R := refineContract env) ((∅, []) : RefineCtx) ω5 (μ4.writeN 4278058296 (Num.encodeLE 8 C)) 1636 35092 4278058264
        4278058304 (4278124544 + (Blob.encodeNat C).length) (L - (Blob.encodeNat C).length) e5_0 e5_1 e5_7
        (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_817]) bs_35092 (by decide) (by decide)
        (by omega) (by omega) (by omega) (by omega)
        (fun a h1 h2 => by rw [Memory.writable_writeN, d4_wr, wr2]; exact hst1 a (by omega) (by omega))
        (fun a h1 h2 => by rw [Memory.writable_writeN, d4_wr, wr2]; exact hst1 a (by omega) (by omega))
        (by
          rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp) (by simp [two32]) (by simp [two32])]
          exact d4_r0)
        (by
          rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp) (by simp [two32]) (by simp [two32])]
          exact d4_r8)
        I (by omega) ⟨by omega, by omega⟩
        (fun a h1 h2 => by
          rw [Memory.readable_writeN, d4_rd, rd2, har1 a (by omega) (by omega)]; exact hrd a (by omega) (by omega))
        (by rw [Memory.readN_congr (fun j hj => arg5 _ (by omega) (by omega))]; exact sI)
    have arg6 : ∀ a, 4278124544 ≤ a → a < 4278124544 + L → μ6.read a = μ.read a := fun a h1 h2 =>
      (d6_fr a (by omega) (by omega) (by omega)).trans (arg5 a h1 h2)
    -- store i, call the decode of s
    obtain ⟨ω7, run7, e7_0, e7_1, e7_7, e7fr⟩ := glueI (p := p) (P := P) (R := refineContract env)
      ((∅, []) : RefineCtx) ω6 μ6 I (by omega) d6_7 d6_8 (d6_1.trans e5_1)
      (fun a h1 h2 => by rw [d6_wr, Memory.writable_writeN, d4_wr, wr2]; exact hst1 a (by omega) (by omega))
    have arg7 : ∀ a, 4278124544 ≤ a → a < 4278124544 + L →
        (μ6.writeN 4278058288 (Num.encodeLE 8 I)).read a = μ.read a := fun a h1 h2 => by
      rw [Memory.read_writeN_disjoint _ _ _ _ (by simp <;> omega) (by simp [two32]) (by simp [two32] <;> omega)]
      exact arg6 a h1 h2
    have sS : μ.readN (4278124544 + (Blob.encodeNat C).length + (Blob.encodeNat I).length) (Blob.encodeNat S).length =
        Blob.encodeNat S := by
      have := Memory.readN_mid μ 4278124544 (Blob.encodeNat C ++ Blob.encodeNat I) (Blob.encodeNat S)
        (Blob.encodeNat Y ++ y ++ h)
        (by
          rw [show (Blob.encodeNat C ++ Blob.encodeNat I ++ Blob.encodeNat S ++ (Blob.encodeNat Y ++ y ++ h)).length = L by
            simp [hh, hy]; omega]
          simpa only [List.append_assoc] using hmem)
      simpa [Nat.add_assoc] using this
    obtain ⟨ω8, μ8, run8, d8_0, d8_1, d8_2, d8_3, d8_4, d8_5, d8_6, d8_12, d8_7, d8_8, d8_r0, d8_r8, d8_fr, d8_rd, d8_wr⟩ :=
      decodeU32 (p := p) (P := P) (R := refineContract env) ((∅, []) : RefineCtx) ω7 (μ6.writeN 4278058288 (Num.encodeLE 8 I))
        1638 35111 4278058264 4278058304 (4278124544 + (Blob.encodeNat C).length + (Blob.encodeNat I).length)
        (L - (Blob.encodeNat C).length - (Blob.encodeNat I).length) e7_0 e7_1 e7_7
        (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_818]) bs_35111 (by decide) (by decide)
        (by omega) (by omega) (by omega) (by omega)
        (fun a h1 h2 => by rw [Memory.writable_writeN, d6_wr, Memory.writable_writeN, d4_wr, wr2]; exact hst1 a (by omega) (by omega))
        (fun a h1 h2 => by rw [Memory.writable_writeN, d6_wr, Memory.writable_writeN, d4_wr, wr2]; exact hst1 a (by omega) (by omega))
        (by
          rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp) (by simp [two32]) (by simp [two32]), d6_r0])
        (by
          rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp) (by simp [two32]) (by simp [two32]), d6_r8, Nat.sub_sub])
        S hS ⟨by omega, by omega⟩
        (fun a h1 h2 => by
          rw [Memory.readable_writeN, d6_rd, Memory.readable_writeN, d4_rd, rd2, har1 a (by omega) (by omega)]
          exact hrd a (by omega) (by omega))
        (by rw [Memory.readN_congr (fun j hj => arg7 _ (by omega) (by omega))]; exact sS)
    have arg8 : ∀ a, 4278124544 ≤ a → a < 4278124544 + L → μ8.read a = μ.read a := fun a h1 h2 =>
      (d8_fr a (by omega) (by omega) (by omega)).trans (arg7 a h1 h2)
    -- store s, call the decode of |y|
    obtain ⟨ω9, run9, e9_0, e9_1, e9_7, e9fr⟩ := glueS (p := p) (P := P) (R := refineContract env)
      ((∅, []) : RefineCtx) ω8 μ8 S (by omega) d8_7 d8_8 (d8_1.trans e7_1)
      (fun a h1 h2 => by rw [d8_wr, Memory.writable_writeN, d6_wr, Memory.writable_writeN, d4_wr, wr2]; exact hst1 a (by omega) (by omega))
    have arg9 : ∀ a, 4278124544 ≤ a → a < 4278124544 + L →
        (μ8.writeN 4278058280 (Num.encodeLE 8 S)).read a = μ.read a := fun a h1 h2 => by
      rw [Memory.read_writeN_disjoint _ _ _ _ (by simp <;> omega) (by simp [two32]) (by simp [two32] <;> omega)]
      exact arg8 a h1 h2
    have sY : μ.readN (4278124544 + (Blob.encodeNat C).length + (Blob.encodeNat I).length + (Blob.encodeNat S).length)
        (Blob.encodeNat Y).length = Blob.encodeNat Y := by
      have := Memory.readN_mid μ 4278124544 (Blob.encodeNat C ++ Blob.encodeNat I ++ Blob.encodeNat S) (Blob.encodeNat Y)
        (y ++ h)
        (by
          rw [show (Blob.encodeNat C ++ Blob.encodeNat I ++ Blob.encodeNat S ++ Blob.encodeNat Y ++ (y ++ h)).length = L by
            simp [hh, hy]; omega]
          simpa only [List.append_assoc] using hmem)
      simpa [Nat.add_assoc] using this
    obtain ⟨ω10, μ10, run10, d10_0, d10_1, d10_2, d10_3, d10_4, d10_5, d10_6, d10_12, d10_7, d10_8, d10_r0, d10_r8, d10_fr, d10_rd, d10_wr⟩ :=
      decodeU32 (p := p) (P := P) (R := refineContract env) ((∅, []) : RefineCtx) ω9 (μ8.writeN 4278058280 (Num.encodeLE 8 S))
        1640 35130 4278058264 4278058304
        (4278124544 + (Blob.encodeNat C).length + (Blob.encodeNat I).length + (Blob.encodeNat S).length)
        (L - (Blob.encodeNat C).length - (Blob.encodeNat I).length - (Blob.encodeNat S).length) e9_0 e9_1 e9_7
        (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_819]) bs_35130 (by decide) (by decide)
        (by omega) (by omega) (by omega) (by omega)
        (fun a h1 h2 => by rw [Memory.writable_writeN, d8_wr, Memory.writable_writeN, d6_wr, Memory.writable_writeN, d4_wr, wr2]; exact hst1 a (by omega) (by omega))
        (fun a h1 h2 => by rw [Memory.writable_writeN, d8_wr, Memory.writable_writeN, d6_wr, Memory.writable_writeN, d4_wr, wr2]; exact hst1 a (by omega) (by omega))
        (by rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp) (by simp [two32]) (by simp [two32]), d8_r0])
        (by rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp) (by simp [two32]) (by simp [two32]), d8_r8, Nat.sub_sub])
        Y (by omega) ⟨by omega, by omega⟩
        (fun a h1 h2 => by
          rw [Memory.readable_writeN, d8_rd, Memory.readable_writeN, d6_rd, Memory.readable_writeN, d4_rd, rd2,
            har1 a (by omega) (by omega)]
          exact hrd a (by omega) (by omega))
        (by rw [Memory.readN_congr (fun j hj => arg9 _ (by omega) (by omega))]; exact sY)
    have arg10 : ∀ a, 4278124544 ≤ a → a < 4278124544 + L → μ10.read a = μ.read a := fun a h1 h2 =>
      (d10_fr a (by omega) (by omega) (by omega)).trans (arg9 a h1 h2)
    have q10_4 : ω10[4] = UInt64.ofNat 8 := d10_4.trans ((e9fr 4 (by decide)).trans (d8_4.trans ((e7fr 4 (by decide)).trans (d6_4.trans ((e5fr 4 (by decide)).trans (d4_4.trans ((e3fr 4 (by decide)).trans g2_4)))))))
    have q10_5 : ω10[5] = UInt64.ofNat 4278058544 := d10_5.trans ((e9fr 5 (by decide)).trans (d8_5.trans ((e7fr 5 (by decide)).trans (d6_5.trans ((e5fr 5 (by decide)).trans (d4_5.trans ((e3fr 5 (by decide)).trans g2_5)))))))
    have q10_6 : ω10[6] = UInt64.ofNat 4278124544 := d10_6.trans ((e9fr 6 (by decide)).trans (d8_6.trans ((e7fr 6 (by decide)).trans (d6_6.trans ((e5fr 6 (by decide)).trans (d4_6.trans ((e3fr 6 (by decide)).trans g2_6)))))))
    have q10_r8 : μ10.readN 4278058312 8 = Num.encodeLE 8 (Y + 32) := by
      have := d10_r8
      rw [show L - (Blob.encodeNat C).length - (Blob.encodeNat I).length - (Blob.encodeNat S).length -
        (Blob.encodeNat Y).length = Y + 32 by omega] at this
      exact this
    -- the stored c, i, s and L, at μ10
    have p10S : μ10.readN 4278058280 8 = Num.encodeLE 8 S := by
      rw [Memory.readN_congr (fun j hj => d10_fr _ (by omega) (by omega) (by omega))]
      exact Memory.readN_writeN_same _ _ _ _ (Num.length_encodeLE _ _) (by simp [two32])
    have p10I : μ10.readN 4278058288 8 = Num.encodeLE 8 I := by
      rw [Memory.readN_congr (fun j hj => (d10_fr _ (by omega) (by omega) (by omega)).trans
        ((Memory.read_writeN_disjoint _ _ _ _ (by simp <;> omega) (by simp [two32]) (by simp [two32] <;> omega)).trans
        (d8_fr _ (by omega) (by omega) (by omega))))]
      exact Memory.readN_writeN_same _ _ _ _ (Num.length_encodeLE _ _) (by simp [two32])
    have p10C : μ10.readN 4278058296 8 = Num.encodeLE 8 C := by
      rw [Memory.readN_congr (fun j hj => (d10_fr _ (by omega) (by omega) (by omega)).trans
        ((Memory.read_writeN_disjoint _ _ _ _ (by simp <;> omega) (by simp [two32]) (by simp [two32] <;> omega)).trans
        ((d8_fr _ (by omega) (by omega) (by omega)).trans
        ((Memory.read_writeN_disjoint _ _ _ _ (by simp <;> omega) (by simp [two32]) (by simp [two32] <;> omega)).trans
        (d6_fr _ (by omega) (by omega) (by omega))))))]
      exact Memory.readN_writeN_same _ _ _ _ (Num.length_encodeLE _ _) (by simp [two32])
    have p10L : μ10.readN 4278058360 8 = Num.encodeLE 8 L := by
      rw [Memory.readN_congr (fun j hj => (d10_fr _ (by omega) (by omega) (by omega)).trans
        ((Memory.read_writeN_disjoint _ _ _ _ (by simp <;> omega) (by simp [two32]) (by simp [two32] <;> omega)).trans
        ((d8_fr _ (by omega) (by omega) (by omega)).trans
        ((Memory.read_writeN_disjoint _ _ _ _ (by simp <;> omega) (by simp [two32]) (by simp [two32] <;> omega)).trans
        ((d6_fr _ (by omega) (by omega) (by omega)).trans
        ((Memory.read_writeN_disjoint _ _ _ _ (by simp <;> omega) (by simp [two32]) (by simp [two32] <;> omega)).trans
        (d4_fr _ (by omega) (by omega) (by omega))))))))]
      exact s2b
    -- the payload, sliced
    have sP : μ.readN (4278124544 + (Blob.encodeNat C).length + (Blob.encodeNat I).length + (Blob.encodeNat S).length +
        (Blob.encodeNat Y).length) y.length = y := by
      have := Memory.readN_mid μ 4278124544 (Blob.encodeNat C ++ Blob.encodeNat I ++ Blob.encodeNat S ++ Blob.encodeNat Y)
        y h
        (by
          rw [show (Blob.encodeNat C ++ Blob.encodeNat I ++ Blob.encodeNat S ++ Blob.encodeNat Y ++ y ++ h).length = L by
            simp [hh, hy]; omega]
          exact hmem)
      simpa [Nat.add_assoc] using this
    have hrd10 : ∀ a, 4278124544 ≤ a → a < 4278124544 + L → μ10.readable a = true := fun a h1 h2 => by
      rw [d10_rd, Memory.readable_writeN, d8_rd, Memory.readable_writeN, d6_rd, Memory.readable_writeN, d4_rd,
        rd2, har1 a h1 h2]
      exact hrd a h1 h2
    have hwr10 : ∀ a, 4278057688 ≤ a → a < 4278059008 → μ10.writable a = true := fun a h1 h2 => by
      rw [d10_wr, Memory.writable_writeN, d8_wr, Memory.writable_writeN, d6_wr, Memory.writable_writeN, d4_wr, wr2]
      exact hst1 a (by omega) (by omega)
    have hwh10 : ∀ a, 196608 ≤ a → a < 208896 → μ10.writable a = true := fun a h1 h2 => by
      rw [d10_wr, Memory.writable_writeN, d8_wr, Memory.writable_writeN, d6_wr, Memory.writable_writeN, d4_wr, wr2]
      exact hhp1 a h1 h2
    have sP10 : μ10.readN (4278124544 + (Blob.encodeNat C).length + (Blob.encodeNat I).length +
        (Blob.encodeNat S).length + (Blob.encodeNat Y).length) Y = y := by
      rw [Memory.readN_congr (fun j hj => arg10 _ (by omega) (by omega))]
      have := sP
      rw [hy] at this
      exact this
    have r10 : μ10.readN 4278058304 8 = Num.encodeLE 8 (4278124544 + (Blob.encodeNat C).length +
        (Blob.encodeNat I).length + (Blob.encodeNat S).length + (Blob.encodeNat Y).length) := by
      rw [d10_r0]
    have hpg10 : JAM.HeapPages μ10 48 1044430 51 := heapPages_of_writable (fun x => by
      rw [d10_wr, Memory.writable_writeN, d8_wr, Memory.writable_writeN, d6_wr, Memory.writable_writeN, d4_wr, wr2]) hpg1
    -- frames
    have run12 := run1.trans run2
    have run3_10 := run3.trans (run4.trans (run5.trans (run6.trans (run7.trans (run8.trans (run9.trans run10))))))
    have fr4642 : ∀ a, a < 4294967296 → (a < 4278058136 ∨ 4278058320 ≤ a) → μ10.read a = μ2.read a :=
      fun a ha hb => by
        rw [d10_fr a ha (by omega) (by omega), Memory.read_writeN_disjoint _ _ _ _ (by simp <;> omega) (by simp [two32]) (by simp [two32] <;> omega),
          d8_fr a ha (by omega) (by omega), Memory.read_writeN_disjoint _ _ _ _ (by simp <;> omega) (by simp [two32]) (by simp [two32] <;> omega),
          d6_fr a ha (by omega) (by omega), Memory.read_writeN_disjoint _ _ _ _ (by simp <;> omega) (by simp [two32]) (by simp [two32] <;> omega),
          d4_fr a ha (by omega) (by omega)]
    have rd4642 : ∀ a, μ10.readable a = μ2.readable a := fun a => by
      rw [d10_rd, Memory.readable_writeN, d8_rd, Memory.readable_writeN, d6_rd, Memory.readable_writeN, d4_rd]
    have wr4642 : ∀ a, μ10.writable a = μ2.writable a := fun a => by
      rw [d10_wr, Memory.writable_writeN, d8_wr, Memory.writable_writeN, d6_wr, Memory.writable_writeN, d4_wr]
    have frSplit : ∃ ω₂ μ₂, FreeStepsH p (refineContract env) 0 (initRegs L) μ ((∅, []) : RefineCtx) 4642 ω₂ μ₂
          ((∅, []) : RefineCtx) 3429 ∧
        FreeStepsH p (refineContract env) 4642 ω₂ μ₂ ((∅, []) : RefineCtx) 35130 ω10 μ10
          ((∅, []) : RefineCtx) 2016 ∧
        (∀ a, a < 4294967296 → (a < 4278058136 ∨ 4278058320 ≤ a) → μ10.read a = μ₂.read a) ∧
        (∀ a, μ10.readable a = μ₂.readable a) ∧ (∀ a, μ10.writable a = μ₂.writable a) :=
      ⟨ω2, μ2, run12.mono (by omega), run3_10.mono (by omega), fr4642, rd4642, wr4642⟩
    have frTop : ∀ a, 4278059008 ≤ a → a < 4294967296 → μ10.read a = μ.read a := fun a h1 h2 => by
      rw [fr4642 a h2 (by omega)]
      refine (f2 a ?_).trans (hfr1 a ?_)
      · simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not, not_and,
          Nat.not_lt]
        omega
      · simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not, not_and,
          Nat.not_lt]
        omega
    have frLow : ∀ a, a < 4278057688 → ¬(196608 ≤ a ∧ a < 196618) → ¬(196620 ≤ a ∧ a < 196668) →
        ¬(196672 ≤ a ∧ a < 196792) → ¬(206512 ≤ a ∧ a < 206528) → ¬(206824 ≤ a ∧ a < 206844) →
        ¬(206848 ≤ a ∧ a < 206852) → ¬(206880 ≤ a ∧ a < 206896) → ¬(206912 ≤ a ∧ a < 207034) →
        ¬(207040 ≤ a ∧ a < 207056) → μ10.read a = μ.read a := fun a h0 n1 n2 n3 n4 n5 n6 n7 n8 n9 => by
      rw [fr4642 a (by omega) (by omega)]
      refine (f2 a ?_).trans (hfr1 a ?_)
      · simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not, not_and,
          Nat.not_lt]
        omega
      · simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not, not_and,
          Nat.not_lt]
        omega
    have z10 : μ10.readN 206892 4 = [0, 0, 0, 0] := by
      rw [Memory.readN_congr (fun j hj => fr4642 _ (by omega) (by omega))]; exact hZ2
    refine ⟨ω10, μ10, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans
      (run8.trans (run9.trans run10))))))))).mono (by omega), ?_, z10⟩
    unfold ArgsPost
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals tail_facts
  all_goals first
    | chase
    | (intro a h1 h2; first
        | exact Memory.readable_of_writable (hhp1 a (by omega) (by omega))
        | exact Memory.readable_of_writable (hst1 a (by omega) (by omega)))


open Picoalloc Services.Bootstrap.Alloc Services.Bootstrap.Alloc.AfterStart Services.Bootstrap.AllocStart
  Services.Bootstrap.Decode.HeapCtx

/-- **The allocator's context at 35130**: from Y's state (`StartMem`, `StartMemZ`) with the argument
    blob ℰ(c) ⌢ ℰ(i) ⌢ ℰ(s) ⌢ ℰ(|y|) ⌢ y ⌢ h, refine reaches 35130 with `run_args_gen`'s post
    (`ArgsPost`) and the allocator's context for picoalloc's start state `sStart`, heap bound
    1044430 and the stack [4278050816, 4278059008). -/
theorem args_ctx (p : ByteArray) (P : Program) [HasCode p P] (env : RefineHost.Env)
    (henv : heapBounds env.code = (48, 1044430)) (hpar : env.fetch.params = Params.full) (μ : Memory)
    (hμ : StartMem μ) (C I S : Nat) (h : List UInt8) (hC : C < 65536) (hI : I < 65536)
    (hS : S < 4294967296) (Y : Nat) (hY1 : 1 ≤ Y) (hY : Y < 16777216) (y : List UInt8) (hy : y.length = Y)
    (hh : h.length = 32) (L : Nat)
    (hLdef : (Blob.encodeNat C).length + (Blob.encodeNat I).length + (Blob.encodeNat S).length +
      (Blob.encodeNat Y).length + Y + 32 = L) (hL : L < 16777217)
    (hmem : μ.readN 4278124544 L = Blob.encodeNat C ++ Blob.encodeNat I ++ Blob.encodeNat S ++
      Blob.encodeNat Y ++ y ++ h)
    (hrd : ∀ j, 4278124544 ≤ j → j < 4278124544 + L → μ.readable j = true)
    (hz : StartMemZ μ) :
    ∃ ω' μ', FreeStepsH p (refineContract env) 0 (initRegs L) μ ((∅, []) : RefineCtx) 35130 ω' μ'
      ((∅, []) : RefineCtx) 6000 ∧ ArgsPost p env μ C I S Y y L ω' μ' ∧
      HeapCtx env 1044430 4278050816 4278059008 μ' sStart := by
  obtain ⟨ω', μ', run, post, z⟩ := run_args_hdr p P env henv hpar μ hμ C I S h hC hI hS Y hY1 hY y hy hh L
    hLdef hL hmem hrd
  refine ⟨ω', μ', run, post, ?_⟩
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56, c57, c58, c59, c60, c61, c62, c63, c64, c65, c66, c67, c68, c69, c70, c71, c72, c73, c74, c75, c76, c77, c78, c79, c80, c81, c82, c83, c84, c85, c86, c87, c88, c89, c90, c91, c92, c93, c94, c95, c96, c97, c98, c99, c100, c101, c102, c103, c104, c105, c106, c107, c108, c109, c110, c111, c112, c113, c114, c115, c116, c117, c118, c119, c120, c121, c122, c123, c124, c125, c126, c127, c128, c129, c130, c131⟩ := post
  obtain ⟨kp, -⟩ := FreeStepsH.keepRO (cap := hostCostMax) henv run
  -- Y's zeros, kept below the stack except at the prefix's and the chain's globals
  have zr : ∀ a, (196792 ≤ a ∧ a < 206512 ∨ 206528 ≤ a ∧ a < 206824) → μ'.read a = 0 := fun a ha =>
    (c130 a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)).trans (hz.zero a (by omega) (by omega))
  have hw : AllocWords μ' := by
    refine ⟨fun b hb => ?_, fun q hq => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold A0; unfold binCount at hb
      by_cases e1 : b = 2431
      · subst e1; simp only [↓reduceIte]; show rdN μ' 206516 4 = 206880
        rw [rdN4_of (a := 206516) (Memory.read_of_readN c6 4 (by decide)) (Memory.read_of_readN c6 5 (by decide))
          (Memory.read_of_readN c6 6 (by decide)) (Memory.read_of_readN c6 7 (by decide))]; rfl
      · simp only [e1, ↓reduceIte]
        by_cases e0 : b = 2430
        · subst e0; show rdN μ' 206512 4 = 0
          rw [rdN4_of (a := 206512) (Memory.read_of_readN c6 0 (by decide)) (Memory.read_of_readN c6 1 (by decide))
            (Memory.read_of_readN c6 2 (by decide)) (Memory.read_of_readN c6 3 (by decide))]; rfl
        · exact rdN4_zero fun j hj => zr _ (by omega)
    · unfold A0
      by_cases e1 : q = 37
      · subst e1; simp only [↓reduceIte]; show rdN μ' 206824 8 = 2 ^ 63
        unfold rdN; rw [c8]; rfl
      · simp only [e1, ↓reduceIte]; exact rdN8_zero fun j hj => zr _ (by omega)
    · unfold rdN; rw [c9]; rfl
    · unfold rdN; rw [c7]; rfl
    · unfold rdN; rw [c10]; rfl
    · rw [rdN4_of (a := 206880) (Memory.read_of_readN c12 0 (by decide)) (Memory.read_of_readN c12 1 (by decide))
        (Memory.read_of_readN c12 2 (by decide)) (Memory.read_of_readN c12 3 (by decide))]; rfl
    · rw [rdN4_of (a := 206884) (Memory.read_of_readN c12 4 (by decide)) (Memory.read_of_readN c12 5 (by decide))
        (Memory.read_of_readN c12 6 (by decide)) (Memory.read_of_readN c12 7 (by decide))]; rfl
    · unfold rdN; rw [c13]; rfl
    · unfold rdN; rw [z]; rfl
  refine ⟨sStart_wf, hw.rep, sStart_first, ?_, by rw [sStart_base]; omega, by rw [sStart_base]; omega,
    by rw [sStart_allocated]; omega, henv, ⟨51, by omega, by omega, c74, by omega,
      by rw [sStart_base, sStart_allocated]; omega⟩, by omega, by omega, fun a h1 h2 => ?_, fun a ha => ?_⟩
  · unfold rdN; rw [show μ'.readN 206848 1 = [μ'.read (206848 + 0)] from rfl, Memory.read_of_readN c11 0 (by decide)]; rfl
  · have e := kp (a / pageSize) (Or.inr (by unfold pageSize; omega))
    have := hμ.stack a (by omega) h2
    unfold Memory.writable at this ⊢
    rw [e]; exact this
  · have e := kp (a / pageSize) (Or.inl (by unfold pageSize; omega))
    have := hz.lowRO a ha
    unfold Memory.writable at this ⊢
    rw [e]; exact this

end Services.Bootstrap.Refine.ArgsCtx
