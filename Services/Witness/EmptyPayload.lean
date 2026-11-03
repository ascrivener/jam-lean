import Services.Witness.Prefix
import Services.Witness.DecodeC
import Services.Witness.Front1
import Services.Witness.Front2
import Services.Witness.BadPayload
import Services.Witness.EFront3
import Services.Witness.EmptyTail

/-!
# Witness's refine on an empty payload, end to end

As `BadPayload.run_badTag`, for the empty payload: the decode of |y| = 0 returns to the same
point, and `EFront3` takes the 60 steps from there to `Op::decode`'s error jump at 74620 (no
allocation, no copy); the empty payload's tail `EmptyTail.run` leads to the halt with [12, 0] at
206752.
-/

namespace Services.Witness.EmptyPayload

open PVM JAM Services.Witness Services.Witness.Code Services.Witness.Prefix
  Services.Witness.BadPayload

set_option maxHeartbeats 100000000
set_option maxRecDepth 100000

/-- **Witness's refine rejects the empty payload.** As `BadPayload.run_badTag`, for the empty
    payload: the gas-free machine runs from Y's registers to the halting step at 43609 with
    ω₇ = 206752, ω₈ = 2 and the octets [12, 0] there, `Rejected(BadPayload)`. -/
theorem run_empty (p : ByteArray) (P : Program) [HasCode p P] (env : RefineHost.Env)
    (henv : heapBounds env.code = (48, 1044368)) (hpar : env.fetch.params = Params.full) (μ : Memory)
    (hμ : StartMem μ) (C I S : Nat) (y h : List UInt8) (hC : C < 65536) (hI : I < 65536)
    (hS : S < 4294967296) (hy : y.length = 0)
    (hh : h.length = 32)
    (hmem : μ.readN 4278124544 (Blob.encodeNat C ++ Blob.encodeNat I ++ Blob.encodeNat S ++
      Blob.encodeNat y.length ++ y ++ h).length = Blob.encodeNat C ++ Blob.encodeNat I ++
      Blob.encodeNat S ++ Blob.encodeNat y.length ++ y ++ h)
    (hrd : ∀ j, 4278124544 ≤ j → j < 4278124544 + (Blob.encodeNat C ++ Blob.encodeNat I ++
      Blob.encodeNat S ++ Blob.encodeNat y.length ++ y ++ h).length → μ.readable j = true) :
    ∃ ω' μ' x', FreeStepsH p (refineContract env) 0 (initRegs (Blob.encodeNat C ++ Blob.encodeNat I ++
      Blob.encodeNat S ++ Blob.encodeNat y.length ++ y ++ h).length) μ ((∅, []) : RefineCtx) 43609
      ω' μ' x' ∧ ω'[0] = UInt64.ofNat 4294901760 ∧ ω'[7] = UInt64.ofNat 206752 ∧
      ω'[8] = UInt64.ofNat 2 ∧ μ'.read 206752 = 12 ∧ μ'.read 206753 = 0 ∧
      μ'.readable 206752 = true ∧ μ'.readable 206753 = true := by
  have hwC := encodeNat_length_le3 C hC
  have hwI := encodeNat_length_le3 I hI
  have hwS := encodeNat_length_le5 S hS
  have hwY := encodeNat_length_le3 y.length (by omega)
  have hlen : (Blob.encodeNat C ++ Blob.encodeNat I ++ Blob.encodeNat S ++ Blob.encodeNat y.length ++
      y ++ h).length = (Blob.encodeNat C).length + (Blob.encodeNat I).length +
      (Blob.encodeNat S).length + (Blob.encodeNat y.length).length + y.length + 32 := by
    simp [hh]; omega
  -- the pieces of the arguments
  have sC : μ.readN 4278124544 (Blob.encodeNat C).length = Blob.encodeNat C := by
    have := Memory.readN_slice μ 4278124544 [] (Blob.encodeNat C)
      (Blob.encodeNat I ++ Blob.encodeNat S ++ Blob.encodeNat y.length ++ y ++ h)
      (by simpa only [List.nil_append, List.append_assoc] using hmem)
    simpa using this
  have sI : μ.readN (4278124544 + (Blob.encodeNat C).length) (Blob.encodeNat I).length =
      Blob.encodeNat I := Memory.readN_slice μ 4278124544 (Blob.encodeNat C) (Blob.encodeNat I)
      (Blob.encodeNat S ++ Blob.encodeNat y.length ++ y ++ h)
      (by simpa only [List.append_assoc] using hmem)
  have sS : μ.readN (4278124544 + ((Blob.encodeNat C).length + (Blob.encodeNat I).length))
      (Blob.encodeNat S).length = Blob.encodeNat S := by
    have := Memory.readN_slice μ 4278124544 (Blob.encodeNat C ++ Blob.encodeNat I)
      (Blob.encodeNat S) (Blob.encodeNat y.length ++ y ++ h)
      (by simpa only [List.append_assoc] using hmem)
    simpa using this
  have sY : μ.readN (4278124544 + ((Blob.encodeNat C).length + (Blob.encodeNat I).length +
      (Blob.encodeNat S).length)) (Blob.encodeNat y.length).length = Blob.encodeNat y.length := by
    have := Memory.readN_slice μ 4278124544 (Blob.encodeNat C ++ Blob.encodeNat I ++
      Blob.encodeNat S) (Blob.encodeNat y.length) (y ++ h)
      (by simpa only [List.append_assoc] using hmem)
    simpa [Nat.add_assoc] using this
  have sy : μ.readN (4278124544 + ((Blob.encodeNat C).length + (Blob.encodeNat I).length +
      (Blob.encodeNat S).length + (Blob.encodeNat y.length).length)) y.length = y := by
    have := Memory.readN_slice μ 4278124544 (Blob.encodeNat C ++ Blob.encodeNat I ++
      Blob.encodeNat S ++ Blob.encodeNat y.length) y h
      (by simpa only [List.append_assoc] using hmem)
    simpa [Nat.add_assoc] using this
  rw [hlen] at hmem hrd ⊢
  generalize hLdef : (Blob.encodeNat C).length + (Blob.encodeNat I).length +
      (Blob.encodeNat S).length + (Blob.encodeNat y.length).length + y.length + 32 = L at hmem hrd ⊢
  obtain ⟨ω1, μ1, x1, run1, post1⟩ := prefix_run p P env henv hpar μ L ⟨by omega, by omega⟩ hμ
  obtain ⟨r1_0, r1_1, r1_2, r1_3, r1_4, r1_5, r1_6, r1_7, r1_8, r1_9, r1_10, r1_11, r1_12⟩ := post1.regs
  have hx1 := post1.ctx
  subst hx1
  have hst1 := post1.stack
  have hhp1 := post1.heap
  have hfr1 := post1.frame
  have hag1 := post1.args
  have har1 := post1.argsRd
  have hro1 := post1.ro
  -- the octets the prefix leaves and the starting octets, as facts
  have pb1 := post1.bytes
  simp only [postBytes, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true] at pb1
  have ib0 : ∀ q ∈ baseBytes, μ.read q.1 = q.2 := fun q hq => hμ.bytes q.1 q.2 hq
  simp only [baseBytes, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true] at ib0
  have ip0 : ∀ q ∈ pathBytes, μ.read q.1 = q.2 := fun q hq => hμ.path q.1 q.2 hq
  simp only [pathBytes, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true] at ip0
  -- the core index
  obtain ⟨ω2, μ2, run2, d2_0, d2_1, d2_5, d2_7, d2_r0, d2_r8, d2_fr, d2_rd, d2_wr⟩ :=
    decodeC (p := p) (P := P) (R := refineContract env) ((∅, []) : RefineCtx) ω1 μ1 4278058816
      4278124544 L r1_1 r1_7 r1_8 (by decide) (by decide) (by decide)
      (fun a h1 h2 => hst1 a (by omega) (by omega)) C hC
      (fun a h1 h2 => by rw [har1 a h1 (by omega)]; exact hrd a h1 (by omega)) ⟨by omega, by omega⟩
      (by rw [Memory.readN_congr (fun j hj => hag1 (4278124544 + j) (by omega) (by omega))]; exact sC)
  have w2a := d2_r0
  have w2b := d2_r8
  chase_prep at w2a w2b
  -- i
  obtain ⟨ω3, μ3, run3, d3_0, d3_1, d3_5, d3_6, d3_7, d3_8, d3_r0, d3_r8, d3_fr, d3_rd, d3_wr⟩ :=
    decodeU32 (p := p) (P := P) (R := refineContract env) ((∅, []) : RefineCtx) ω2 μ2 842 43495
      4278058816 4278058832 (4278124544 + (Blob.encodeNat C).length) (L - (Blob.encodeNat C).length)
      d2_0 (by rw [d2_1, r1_1]) (by rw [d2_7]) (by decide)
      (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_420]) bs_43495
      (by decide) (by decide) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [d2_wr]; exact hst1 a (by omega) (by omega))
      (fun a h1 h2 => by rw [d2_wr]; exact hst1 a (by omega) (by omega))
      (by simpa using d2_r0) (by simpa using d2_r8) I (by omega) ⟨by omega, by omega⟩
      (fun a h1 h2 => by rw [d2_rd, har1 a (by omega) (by omega)]; exact hrd a (by omega) (by omega))
      (by
        rw [Memory.readN_congr (fun j hj => (d2_fr _ (by omega) (by omega)).trans
          (hag1 _ (by omega) (by omega)))]
        exact sI)
  have w3a := d3_r0
  have w3b := d3_r8
  chase_prep at w3a w3b
  -- Front1
  obtain ⟨ω4, μ4, run4, g4, _, f4, rd4, wr4⟩ := Front1.run p P env ω3 μ3 ((∅, []) : RefineCtx) I hI
    (by rw [d3_0, d2_0]) (by rw [d3_1, d2_1, r1_1]) d3_7 d3_8
  obtain ⟨g4_0, g4_1, g4_2, g4_3, g4_4, g4_6, g4_7, g4_8, g4_9, g4_10, g4_11, g4_12, g4_5⟩ := g4
  -- s
  obtain ⟨ω5, μ5, run5, d5_0, d5_1, d5_5, d5_6, d5_7, d5_8, d5_r0, d5_r8, d5_fr, d5_rd, d5_wr⟩ :=
    decodeU32 (p := p) (P := P) (R := refineContract env) ((∅, []) : RefineCtx) ω4 μ4 844 43514
      4278058816 4278058832 (4278124544 + (Blob.encodeNat C).length + (Blob.encodeNat I).length)
      (L - (Blob.encodeNat C).length - (Blob.encodeNat I).length)
      g4_0 (by rw [g4_1, d3_1, d2_1, r1_1]) g4_7 (by decide)
      (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_421]) bs_43514
      (by decide) (by decide) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [wr4, d3_wr, d2_wr]; exact hst1 a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr4, d3_wr, d2_wr]; exact hst1 a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => f4 _ (by simp; omega))]; simpa [Nat.add_assoc] using d3_r0)
      (by rw [Memory.readN_congr (fun j hj => f4 _ (by simp; omega))]; simpa [Nat.sub_sub] using d3_r8)
      S hS ⟨by omega, by omega⟩
      (fun a h1 h2 => by
        rw [rd4, d3_rd, d2_rd, har1 a (by omega) (by omega)]; exact hrd a (by omega) (by omega))
      (by
        rw [Memory.readN_congr (fun j hj => (f4 _ (by simp; omega)).trans
          ((d3_fr _ (by omega) (by omega) (by omega)).trans ((d2_fr _ (by omega) (by omega)).trans
          (hag1 _ (by omega) (by omega)))))]
        simpa [Nat.add_assoc] using sS)
  have w5a := d5_r0
  have w5b := d5_r8
  chase_prep at w5a w5b
  -- Front2
  obtain ⟨ω6, μ6, run6, g6, m6, s6, f6, rd6, wr6⟩ := Front2.run p P env ω5 μ5 ((∅, []) : RefineCtx) S hS
    I hI (by rw [d5_0, g4_0]) (by rw [d5_1, g4_1, d3_1, d2_1, r1_1]) d5_7 d5_8 (by rw [d5_5, g4_5])
    (fun a h1 h2 => by rw [d5_wr, wr4, d3_wr, d2_wr]; exact hst1 a (by omega) (by omega))
  obtain ⟨g6_0, g6_1, g6_2, g6_3, g6_4, g6_5, g6_6, g6_7, g6_8, g6_9, g6_10, g6_11, g6_12⟩ := g6
  chase_prep at s6
  -- |y|
  obtain ⟨ω7, μ7, run7, d7_0, d7_1, d7_5, d7_6, d7_7, d7_8, d7_r0, d7_r8, d7_fr, d7_rd, d7_wr⟩ :=
    decodeU32 (p := p) (P := P) (R := refineContract env) ((∅, []) : RefineCtx) ω6 μ6 490 23809
      4278058712 4278058832 (4278124544 + (Blob.encodeNat C).length + (Blob.encodeNat I).length +
        (Blob.encodeNat S).length)
      (L - (Blob.encodeNat C).length - (Blob.encodeNat I).length - (Blob.encodeNat S).length)
      g6_0 g6_1 g6_7 (by decide)
      (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_244]) bs_23809
      (by decide) (by decide) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [wr6, d5_wr, wr4, d3_wr, d2_wr]; exact hst1 a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr6, d5_wr, wr4, d3_wr, d2_wr]; exact hst1 a (by omega) (by omega))
      (by
        rw [Memory.readN_congr (fun j hj => f6 _ (by simp; omega))]
        simpa [Nat.add_assoc] using d5_r0)
      (by
        rw [Memory.readN_congr (fun j hj => f6 _ (by simp; omega))]
        simpa [Nat.sub_sub] using d5_r8)
      y.length (by omega) ⟨by omega, by omega⟩
      (fun a h1 h2 => by
        rw [rd6, d5_rd, rd4, d3_rd, d2_rd, har1 a (by omega) (by omega)]; exact hrd a (by omega) (by omega))
      (by
        rw [Memory.readN_congr (fun j hj => (f6 _ (by simp; omega)).trans
          ((d5_fr _ (by omega) (by omega) (by omega)).trans ((f4 _ (by simp; omega)).trans
          ((d3_fr _ (by omega) (by omega) (by omega)).trans ((d2_fr _ (by omega) (by omega)).trans
          (hag1 _ (by omega) (by omega)))))))]
        simpa [Nat.add_assoc] using sY)
  have w7a := d7_r0
  have w7b := d7_r8
  chase_prep at w7a w7b
  -- the 60 steps to Op::decode's error jump
  refine (fun h8 => ?_) (EFront3.run p P env ω7 μ7 ((∅, []) : RefineCtx) S hS I hI L (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  · obtain ⟨ω8, μ8, run8, g8, m8, s8, f8, rd8, wr8⟩ := h8
    chase_prep at s8
    -- the empty payload's tail
    refine (fun hT => ?_) (EmptyTail.run p P env ω8 μ8 ((∅, []) : RefineCtx) I hI S hS ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    · obtain ⟨ω9, μ9, run9, e0, e7, e8, eb0, eb1, er0, er1⟩ := hT
      exact ⟨ω9, μ9, _, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans
        (run7.trans (run8.trans run9))))))), e0, e7, e8, eb0, eb1, er0, er1⟩
    all_goals chase
  all_goals chase

end Services.Witness.EmptyPayload
