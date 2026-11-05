import Services.Bootstrap.Prefix
import Services.Bootstrap.BParams
import Services.Bootstrap.Glue
import Services.Bootstrap.BTail1
import Services.Bootstrap.BTail2
import Services.Bootstrap.BTail3
import Services.Bootstrap.BTail4
import Services.Bootstrap.BTail5
import Services.Bootstrap.BTail6
import Services.Bootstrap.BTail7
import Services.Bootstrap.BTail8

/-!
# Bootstrap's refine on an empty payload, end to end

From Y's state, for every core index c < 2^16, item index i < 2^16, service id s < 2^32 and
32-octet hash, with an empty payload: the prefix, the parameter chain `BParams`, the decodes of c
(`decodeU16`), i, s and |y| (`decodeU32`) with the steps between them (`Glue`), the hash's read
(`read_big`), and the tail for s's number of hex digits (`BTail1` … `BTail8`), to the trap at 6377.
-/

namespace Services.Bootstrap.EmptyPayload

macro "tail_facts" : tactic => `(tactic| first | assumption | chase)

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Prefix

set_option maxHeartbeats 100000000
set_option maxRecDepth 100000

theorem run_empty (p : ByteArray) (P : Program) [HasCode p P] (env : RefineHost.Env)
    (henv : heapBounds env.code = (48, 1044430)) (hpar : env.fetch.params = Params.full) (μ : Memory)
    (hμ : StartMem μ) (C I S : Nat) (h : List UInt8) (hC : C < 65536) (hI : I < 65536)
    (hS : S < 4294967296) (hh : h.length = 32)
    (hmem : μ.readN 4278124544 (Blob.encodeNat C ++ Blob.encodeNat I ++ Blob.encodeNat S ++
      Blob.encodeNat 0 ++ h).length = Blob.encodeNat C ++ Blob.encodeNat I ++ Blob.encodeNat S ++
      Blob.encodeNat 0 ++ h)
    (hrd : ∀ j, 4278124544 ≤ j → j < 4278124544 + (Blob.encodeNat C ++ Blob.encodeNat I ++
      Blob.encodeNat S ++ Blob.encodeNat 0 ++ h).length → μ.readable j = true) :
    ∃ ω' μ' x', FreeStepsH p (refineContract env) 0 (initRegs (Blob.encodeNat C ++ Blob.encodeNat I ++
      Blob.encodeNat S ++ Blob.encodeNat 0 ++ h).length) μ ((∅, []) : RefineCtx) 6377 ω' μ' x' 8000 := by
  have hwC := encodeNat_len_le3 C hC
  have hwI := encodeNat_len_le3 I hI
  have hwS := encodeNat_len_le5 S hS
  have hw0 : (Blob.encodeNat 0).length = 1 := by simp [Blob.encodeNat]
  have hlen : (Blob.encodeNat C ++ Blob.encodeNat I ++ Blob.encodeNat S ++ Blob.encodeNat 0 ++ h).length =
      (Blob.encodeNat C).length + (Blob.encodeNat I).length + (Blob.encodeNat S).length + 1 + 32 := by
    simp [hh, hw0]; omega
  rw [hlen] at hmem hrd ⊢
  generalize hLdef : (Blob.encodeNat C).length + (Blob.encodeNat I).length + (Blob.encodeNat S).length + 1 + 32
    = L at hmem hrd ⊢
  obtain ⟨ω1, μ1, x1, run1, post1⟩ := prefix_run p P env henv hpar μ L ⟨by omega, by omega⟩ hμ
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
  refine (fun h2 => ?_) (BParams.run p P env ω1 μ1 ((∅, []) : RefineCtx) L ⟨by omega, by omega⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  · obtain ⟨ω2, μ2, run2, g2, m2, s2, f2, rd2, wr2⟩ := h2
    obtain ⟨g2_0, g2_1, g2_2, g2_3, g2_4, g2_5, g2_6, g2_7, g2_8, g2_10, g2_11, g2_12, g2_9⟩ := g2
    obtain ⟨s2a, s2b⟩ := s2
    -- the arguments, sliced
    have sC : μ.readN 4278124544 (Blob.encodeNat C).length = Blob.encodeNat C := by
      have := Memory.readN_mid μ 4278124544 [] (Blob.encodeNat C)
        (Blob.encodeNat I ++ Blob.encodeNat S ++ Blob.encodeNat 0 ++ h)
        (by
          rw [show (([] : List UInt8) ++ Blob.encodeNat C ++ (Blob.encodeNat I ++ Blob.encodeNat S ++ Blob.encodeNat 0 ++ h)).length = L by
            simp [hh, hw0]; omega]
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
        (Blob.encodeNat S ++ Blob.encodeNat 0 ++ h)
      rw [show (Blob.encodeNat C ++ Blob.encodeNat I ++ (Blob.encodeNat S ++ Blob.encodeNat 0 ++ h)).length = L by
        simp [hh, hw0]; omega]
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
        (Blob.encodeNat 0 ++ h)
        (by
          rw [show (Blob.encodeNat C ++ Blob.encodeNat I ++ Blob.encodeNat S ++ (Blob.encodeNat 0 ++ h)).length = L by
            simp [hh, hw0]; omega]
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
        (Blob.encodeNat 0).length = Blob.encodeNat 0 := by
      have := Memory.readN_mid μ 4278124544 (Blob.encodeNat C ++ Blob.encodeNat I ++ Blob.encodeNat S) (Blob.encodeNat 0) h
        (by
          rw [show (Blob.encodeNat C ++ Blob.encodeNat I ++ Blob.encodeNat S ++ Blob.encodeNat 0 ++ h).length = L by
            simp [hh, hw0]; omega]
          exact hmem)
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
        0 (by omega) ⟨by omega, by omega⟩
        (fun a h1 h2 => by
          rw [Memory.readable_writeN, d8_rd, Memory.readable_writeN, d6_rd, Memory.readable_writeN, d4_rd, rd2,
            har1 a (by omega) (by omega)]
          exact hrd a (by omega) (by omega))
        (by rw [Memory.readN_congr (fun j hj => arg9 _ (by omega) (by omega))]; exact sY)
    have arg10 : ∀ a, 4278124544 ≤ a → a < 4278124544 + L → μ10.read a = μ.read a := fun a h1 h2 =>
      (d10_fr a (by omega) (by omega) (by omega)).trans (arg9 a h1 h2)
    -- the payload as an empty Vec, then the call reading the hash
    obtain ⟨ω11a, μ11a, run11a, v_0, v_1, v_5, v_6, v_7, v_8, v_9, v_m0, v_m8, v_fr, v_rd, v_wr⟩ :=
      glueVec (p := p) (P := P) (R := refineContract env) ((∅, []) : RefineCtx) ω10 μ10 d10_7
        (by rw [d10_8]) (d10_1.trans e9_1)
        (fun a h1 h2 => by rw [d10_wr, Memory.writable_writeN, d8_wr, Memory.writable_writeN, d6_wr,
          Memory.writable_writeN, d4_wr, wr2]; exact hst1 a (by omega) (by omega))
    have arg11a : ∀ a, 4278124544 ≤ a → a < 4278124544 + L → μ11a.read a = μ.read a := fun a h1 h2 =>
      (v_fr a (by omega) (by omega) (by omega)).trans (arg10 a h1 h2)
    have hrd11a : ∀ a, 4278124544 ≤ a → a < 4278124544 + L → μ11a.readable a = true := fun a h1 h2 => by
      rw [v_rd, d10_rd, Memory.readable_writeN, d8_rd, Memory.readable_writeN, d6_rd, Memory.readable_writeN, d4_rd,
        rd2, har1 a h1 h2]
      exact hrd a h1 h2
    have hwr11a : ∀ a, 4278057688 ≤ a → a < 4278059008 → μ11a.writable a = true := fun a h1 h2 => by
      rw [v_wr, d10_wr, Memory.writable_writeN, d8_wr, Memory.writable_writeN, d6_wr, Memory.writable_writeN, d4_wr, wr2]
      exact hst1 a (by omega) (by omega)
    obtain ⟨ω11, μ11, run11, k0, k1, k5, k6, k7, kR0, kR8, kbuf, kfr, krd, kwr⟩ :=
      read_big (p := p) (P := P) (R := refineContract env) ((∅, []) : RefineCtx) ω11a μ11a 1644 35202 4278058264
        4278058304 4278058320 (4278124544 + (Blob.encodeNat C).length + (Blob.encodeNat I).length +
          (Blob.encodeNat S).length + 1)
        (L - (Blob.encodeNat C).length - (Blob.encodeNat I).length - (Blob.encodeNat S).length - 1) 32
        v_0 v_1 v_7 v_8 v_9 (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_821]) bs_35202
        (by decide) (by decide) (by decide) (by omega) (by decide) (by omega) (by omega) (by decide)
        (by omega) (by omega) (by decide) (by omega)
        (fun a h1 h2 => hwr11a a (by omega) (by omega)) (fun a h1 h2 => hwr11a a (by omega) (by omega))
        (fun a h1 h2 => hwr11a a (by omega) (by omega)) (fun a h1 h2 => hrd11a a (by omega) (by omega))
        (by
          rw [Memory.readN_congr (fun j hj => v_fr _ (by omega) (by omega) (by omega)), d10_r0, hw0])
        (by
          rw [Memory.readN_congr (fun j hj => v_fr _ (by omega) (by omega) (by omega)), d10_r8, hw0, Nat.sub_sub])
    have arg11 : ∀ a, 4278124544 ≤ a → a < 4278124544 + L → μ11.read a = μ.read a := fun a h1 h2 =>
      (kfr a (by omega) (by omega) (by omega) (by omega)).trans (arg11a a h1 h2)
    -- what every tail needs that the pieces leave: the stored arguments, the empty Vec, L, ω₅
    have fk : ∀ a, a < 4294967296 → 4278058264 ≤ a → a < 4278058304 → μ11.read a = μ11a.read a :=
      fun a h0 h1 h2 => kfr a h0 (by omega) (by omega) (by omega)
    have fv : ∀ a, a < 4294967296 → 4278058280 ≤ a → a < 4278058304 → μ11a.read a = μ10.read a :=
      fun a h0 h1 h2 => v_fr a h0 (by omega) (by omega)
    have q5 : ω11[5] = UInt64.ofNat 4278058544 := k5.trans (v_5.trans (d10_5.trans ((e9fr 5 (by decide)).trans
      (d8_5.trans ((e7fr 5 (by decide)).trans (d6_5.trans ((e5fr 5 (by decide)).trans (d4_5.trans
      ((e3fr 5 (by decide)).trans g2_5)))))))))
    have q0 : μ11.readN 4278058264 8 = [0, 0, 0, 0, 0, 0, 0, 0] := by
      rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (by omega) (by omega) (by omega)), v_m0]; rfl
    have q8 : μ11.readN 4278058272 8 = [1, 0, 0, 0, 0, 0, 0, 0] := by
      rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (by omega) (by omega) (by omega)), v_m8]; rfl
    have qS : μ11.readN 4278058280 8 = Num.encodeLE 8 S := by
      rw [Memory.readN_congr (fun j hj => (fk _ (by omega) (by omega) (by omega)).trans ((fv _ (by omega) (by omega)
        (by omega)).trans (d10_fr _ (by omega) (by omega) (by omega))))]
      exact Memory.readN_writeN_same _ _ _ _ (Num.length_encodeLE _ _) (by simp [two32])
    have qI : μ11.readN 4278058288 8 = Num.encodeLE 8 I := by
      rw [Memory.readN_congr (fun j hj => (fk _ (by omega) (by omega) (by omega)).trans ((fv _ (by omega) (by omega)
        (by omega)).trans ((d10_fr _ (by omega) (by omega) (by omega)).trans
        ((Memory.read_writeN_disjoint _ _ _ _ (by simp <;> omega) (by simp [two32]) (by simp [two32] <;> omega)).trans
        (d8_fr _ (by omega) (by omega) (by omega))))))]
      exact Memory.readN_writeN_same _ _ _ _ (Num.length_encodeLE _ _) (by simp [two32])
    have qC : μ11.readN 4278058296 8 = Num.encodeLE 8 C := by
      rw [Memory.readN_congr (fun j hj => (fk _ (by omega) (by omega) (by omega)).trans ((fv _ (by omega) (by omega)
        (by omega)).trans ((d10_fr _ (by omega) (by omega) (by omega)).trans
        ((Memory.read_writeN_disjoint _ _ _ _ (by simp <;> omega) (by simp [two32]) (by simp [two32] <;> omega)).trans
        ((d8_fr _ (by omega) (by omega) (by omega)).trans
        ((Memory.read_writeN_disjoint _ _ _ _ (by simp <;> omega) (by simp [two32]) (by simp [two32] <;> omega)).trans
        (d6_fr _ (by omega) (by omega) (by omega))))))))]
      exact Memory.readN_writeN_same _ _ _ _ (Num.length_encodeLE _ _) (by simp [two32])
    have qL : μ11.readN 4278058360 8 = Num.encodeLE 8 L := by
      rw [Memory.readN_congr (fun j hj => (kfr _ (by omega) (by omega) (by omega) (by omega)).trans ((v_fr _ (by omega)
        (by omega) (by omega)).trans ((d10_fr _ (by omega) (by omega) (by omega)).trans
        ((Memory.read_writeN_disjoint _ _ _ _ (by simp <;> omega) (by simp [two32]) (by simp [two32] <;> omega)).trans
        ((d8_fr _ (by omega) (by omega) (by omega)).trans
        ((Memory.read_writeN_disjoint _ _ _ _ (by simp <;> omega) (by simp [two32]) (by simp [two32] <;> omega)).trans
        ((d6_fr _ (by omega) (by omega) (by omega)).trans
        ((Memory.read_writeN_disjoint _ _ _ _ (by simp <;> omega) (by simp [two32]) (by simp [two32] <;> omega)).trans
        (d4_fr _ (by omega) (by omega) (by omega))))))))))]
      exact s2b
    -- every tail's start facts, once
    have tfs : (ω11[1] = UInt64.ofNat 4278058264) ∧
        (ω11[5] = UInt64.ofNat 4278058544) ∧
        (ω11[6] = UInt64.ofNat 0) ∧
        (ω11[7] = UInt64.ofNat 0) ∧
        (μ11.readN 66657 7 = [26, 66, 111, 111, 116, 115, 116]) ∧
        (μ11.readN 66664 8 = [114, 97, 112, 32, 83, 101, 114, 118]) ∧
        (μ11.readN 66672 8 = [105, 99, 101, 32, 82, 101, 102, 105]) ∧
        (μ11.readN 66680 8 = [110, 101, 44, 32, 192, 1, 104, 0]) ∧
        (μ11.readN 71060 4 = [48, 49, 50, 51]) ∧
        (μ11.readN 71064 8 = [52, 53, 54, 55, 56, 57, 97, 98]) ∧
        (μ11.readN 71072 4 = [99, 100, 101, 102]) ∧
        (μ11.readN 77040 8 = [36, 10, 0, 0, 0, 0, 0, 0]) ∧
        (μ11.readN 206512 8 = [0, 0, 0, 0, 32, 40, 3, 0]) ∧
        (μ11.readN 206520 8 = [32, 40, 3, 0, 0, 0, 0, 0]) ∧
        (μ11.readN 206824 8 = [0, 0, 0, 0, 0, 0, 0, 128]) ∧
        (μ11.readN 206832 8 = [0, 0, 0, 0, 32, 0, 0, 0]) ∧
        (μ11.readN 206840 4 = [6, 0, 0, 0]) ∧
        (μ11.readN 206848 4 = [0, 0, 0, 0]) ∧
        (μ11.readN 206880 8 = [0, 0, 0, 0, 0, 0, 0, 4]) ∧
        (μ11.readN 206888 4 = [0, 0, 0, 0]) ∧
        (μ11.readN 4278058264 8 = [0, 0, 0, 0, 0, 0, 0, 0]) ∧
        (μ11.readN 4278058272 8 = [1, 0, 0, 0, 0, 0, 0, 0]) ∧
        (μ11.readN 4278058352 8 = [0, 0, 255, 254, 0, 0, 0, 0]) ∧
        (μ11.readN 4278058368 8 = [152, 0, 0, 0, 0, 0, 0, 0]) ∧
        (μ11.readN 4278058288 8 = Num.encodeLE 8 I) ∧
        (μ11.readN 4278058360 8 = Num.encodeLE 8 L) ∧
        (μ11.readN 4278058296 8 = Num.encodeLE 8 C) ∧
        (μ11.readN 4278058280 8 = Num.encodeLE 8 S) ∧
        (∀ a, 196608 ≤ a → a < 196616 → μ11.writable a = true) ∧
        (∀ a, 206512 ≤ a → a < 206520 → μ11.writable a = true) ∧
        (∀ a, 206824 ≤ a → a < 206840 → μ11.writable a = true) ∧
        (∀ a, 206848 ≤ a → a < 206852 → μ11.writable a = true) ∧
        (∀ a, 206880 ≤ a → a < 206896 → μ11.writable a = true) ∧
        (∀ a, 206912 ≤ a → a < 206940 → μ11.writable a = true) ∧
        (∀ a, 206976 ≤ a → a < 206992 → μ11.writable a = true) ∧
        (∀ a, 4278058064 ≤ a → a < 4278058088 → μ11.writable a = true) ∧
        (∀ a, 4278058104 ≤ a → a < 4278058376 → μ11.writable a = true) ∧
        (∀ a, 4278058456 ≤ a → a < 4278058472 → μ11.writable a = true) ∧
        (∀ a, 4278058488 ≤ a → a < 4278058496 → μ11.writable a = true) ∧
        (∀ a, 4278058544 ≤ a → a < 4278058610 → μ11.writable a = true) ∧
        (∀ a, 4278058620 ≤ a → a < 4278058624 → μ11.writable a = true) ∧
        (∀ a, 4278058648 ≤ a → a < 4278058664 → μ11.writable a = true) ∧
        (∀ a, 66657 ≤ a → a < 66688 → μ11.readable a = true) ∧
        (∀ a, 71060 ≤ a → a < 71076 → μ11.readable a = true) ∧
        (∀ a, 77040 ≤ a → a < 77048 → μ11.readable a = true) ∧
        (∀ a, 206512 ≤ a → a < 206528 → μ11.readable a = true) ∧
        (∀ a, 206824 ≤ a → a < 206844 → μ11.readable a = true) ∧
        (∀ a, 206848 ≤ a → a < 206852 → μ11.readable a = true) ∧
        (∀ a, 206880 ≤ a → a < 206892 → μ11.readable a = true) ∧
        (∀ a, 206980 ≤ a → a < 206988 → μ11.readable a = true) ∧
        (∀ a, 4278058064 ≤ a → a < 4278058088 → μ11.readable a = true) ∧
        (∀ a, 4278058104 ≤ a → a < 4278058376 → μ11.readable a = true) ∧
        (∀ a, 4278058488 ≤ a → a < 4278058496 → μ11.readable a = true) ∧
        (∀ a, 4278058544 ≤ a → a < 4278058568 → μ11.readable a = true) ∧
        (∀ a, 4278058600 ≤ a → a < 4278058604 → μ11.readable a = true) ∧
        (∀ a, 4278058620 ≤ a → a < 4278058624 → μ11.readable a = true) ∧
        (∀ a, 4278058648 ≤ a → a < 4278058664 → μ11.readable a = true) ∧
        (∀ a, 206912 ≤ a → a < 206941 → μ11.writable a = true) ∧
        (∀ a, 206912 ≤ a → a < 206942 → μ11.writable a = true) ∧
        (∀ a, 196608 ≤ a → a < 196616 → μ11.readable a = true) ∧
        (∀ a, 206912 ≤ a → a < 206943 → μ11.writable a = true) ∧
        (∀ a, 206912 ≤ a → a < 206944 → μ11.writable a = true) ∧
        (∀ a, 206912 ≤ a → a < 206945 → μ11.writable a = true) ∧
        (∀ a, 206912 ≤ a → a < 206946 → μ11.writable a = true) ∧
        (∀ a, 4278058064 ≤ a → a < 4278058080 → μ11.readable a = true) ∧
        (∀ a, 206912 ≤ a → a < 206947 → μ11.writable a = true) ∧
        (∀ a, 4278058080 ≤ a → a < 4278058088 → μ11.readable a = true) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals tail_facts
    obtain ⟨tf0, tf1, tf2, tf3, tf4, tf5, tf6, tf7, tf8, tf9, tf10, tf11, tf12, tf13, tf14, tf15, tf16, tf17, tf18, tf19, tf20, tf21, tf22, tf23, tf24, tf25, tf26, tf27, tf28, tf29, tf30, tf31, tf32, tf33, tf34, tf35, tf36, tf37, tf38, tf39, tf40, tf41, tf42, tf43, tf44, tf45, tf46, tf47, tf48, tf49, tf50, tf51, tf52, tf53, tf54, tf55, tf56, tf57, tf58, tf59, tf60, tf61, tf62, tf63, tf64, tf65, tf66⟩ := tfs
    -- the tail, by s's number of hex digits
    have : S < 16 ∨ (16 ≤ S ∧ S < 256) ∨ (256 ≤ S ∧ S < 4096) ∨ (4096 ≤ S ∧ S < 65536) ∨
        (65536 ≤ S ∧ S < 1048576) ∨ (1048576 ≤ S ∧ S < 16777216) ∨ (16777216 ≤ S ∧ S < 268435456) ∨
        268435456 ≤ S := by omega
    rcases this with hd | hd | hd | hd | hd | hd | hd | hd
    · -- 1 hex digit
      refine (fun hT => ?_) (BTail1.run p P env ω11 μ11 ((∅, []) : RefineCtx) S ⟨by omega, by omega⟩ C hC I hI L ⟨by omega, by omega⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      · obtain ⟨ω12, μ12, run12, -⟩ := hT
        exact ⟨ω12, μ12, _, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans
          (run8.trans (run9.trans (run10.trans (run11a.trans (run11.trans run12)))))))))))).mono (by omega)⟩
      all_goals assumption
    · -- 2 hex digits
      refine (fun hT => ?_) (BTail2.run p P env ω11 μ11 ((∅, []) : RefineCtx) S ⟨by omega, by omega⟩ C hC I hI L ⟨by omega, by omega⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      · obtain ⟨ω12, μ12, run12, -⟩ := hT
        exact ⟨ω12, μ12, _, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans
          (run8.trans (run9.trans (run10.trans (run11a.trans (run11.trans run12)))))))))))).mono (by omega)⟩
      all_goals assumption
    · -- 3 hex digits
      refine (fun hT => ?_) (BTail3.run p P env ω11 μ11 ((∅, []) : RefineCtx) S ⟨by omega, by omega⟩ C hC I hI L ⟨by omega, by omega⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      · obtain ⟨ω12, μ12, run12, -⟩ := hT
        exact ⟨ω12, μ12, _, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans
          (run8.trans (run9.trans (run10.trans (run11a.trans (run11.trans run12)))))))))))).mono (by omega)⟩
      all_goals assumption
    · -- 4 hex digits
      refine (fun hT => ?_) (BTail4.run p P env ω11 μ11 ((∅, []) : RefineCtx) S ⟨by omega, by omega⟩ C hC I hI L ⟨by omega, by omega⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      · obtain ⟨ω12, μ12, run12, -⟩ := hT
        exact ⟨ω12, μ12, _, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans
          (run8.trans (run9.trans (run10.trans (run11a.trans (run11.trans run12)))))))))))).mono (by omega)⟩
      all_goals assumption
    · -- 5 hex digits
      refine (fun hT => ?_) (BTail5.run p P env ω11 μ11 ((∅, []) : RefineCtx) S ⟨by omega, by omega⟩ C hC I hI L ⟨by omega, by omega⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      · obtain ⟨ω12, μ12, run12, -⟩ := hT
        exact ⟨ω12, μ12, _, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans
          (run8.trans (run9.trans (run10.trans (run11a.trans (run11.trans run12)))))))))))).mono (by omega)⟩
      all_goals assumption
    · -- 6 hex digits
      refine (fun hT => ?_) (BTail6.run p P env ω11 μ11 ((∅, []) : RefineCtx) S ⟨by omega, by omega⟩ C hC I hI L ⟨by omega, by omega⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      · obtain ⟨ω12, μ12, run12, -⟩ := hT
        exact ⟨ω12, μ12, _, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans
          (run8.trans (run9.trans (run10.trans (run11a.trans (run11.trans run12)))))))))))).mono (by omega)⟩
      all_goals assumption
    · -- 7 hex digits
      refine (fun hT => ?_) (BTail7.run p P env ω11 μ11 ((∅, []) : RefineCtx) S ⟨by omega, by omega⟩ C hC I hI L ⟨by omega, by omega⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      · obtain ⟨ω12, μ12, run12, -⟩ := hT
        exact ⟨ω12, μ12, _, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans
          (run8.trans (run9.trans (run10.trans (run11a.trans (run11.trans run12)))))))))))).mono (by omega)⟩
      all_goals assumption
    · -- 8 hex digits
      refine (fun hT => ?_) (BTail8.run p P env ω11 μ11 ((∅, []) : RefineCtx) S ⟨by omega, by omega⟩ C hC I hI L ⟨by omega, by omega⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      · obtain ⟨ω12, μ12, run12, -⟩ := hT
        exact ⟨ω12, μ12, _, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans
          (run8.trans (run9.trans (run10.trans (run11a.trans (run11.trans run12)))))))))))).mono (by omega)⟩
      all_goals assumption
  all_goals first
    | chase
    | (intro a h1 h2; first
        | exact Memory.readable_of_writable (hhp1 a (by omega) (by omega))
        | exact Memory.readable_of_writable (hst1 a (by omega) (by omega)))

end Services.Bootstrap.EmptyPayload
