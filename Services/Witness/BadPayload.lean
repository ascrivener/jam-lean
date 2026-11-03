import Services.Witness.Prefix
import Services.Witness.DecodeC
import Services.Witness.Front1
import Services.Witness.Front2
import Services.Witness.Front3
import Services.Witness.Front4
import Services.Witness.ErrTail0
import Services.Witness.ErrTail1
import Services.Witness.ErrTail2
import Services.Witness.ErrTail3
import Services.Witness.ErrTail4
import Services.Witness.ErrTail5
import Services.Witness.Args

/-!
# Witness's refine on a payload with a bad tag, end to end

The prefix (`Prefix.prefix_run`), the core-index decode (`decodeC`), the `u32` decodes of i, s and
|y| (`decodeU32`), the front segments (`Front1` … `Front4`), the payload copy
(`memcpy_small_regs`) and the error tail (`ErrTail0` … `ErrTail5`), chained. Each piece's
hypotheses are proved by `chase` from what the pieces before it guarantee and from the start:
the prefix's post-state and frame, the starting octets (`StartMem`), and the arguments in memory.
-/

namespace Services.Witness.BadPayload

open PVM JAM Services.Witness Services.Witness.Code Services.Witness.Prefix

set_option maxHeartbeats 100000000
set_option maxRecDepth 100000

theorem encodeNat_length_le3 (n : Nat) (h : n < 65536) : (Blob.encodeNat n).length ≤ 3 ∧
    1 ≤ (Blob.encodeNat n).length := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; simp [Blob.encodeNat]
  rcases Nat.lt_or_ge n 128 with h1 | h1
  · rw [encodeNat_len1 n ⟨h0, h1⟩]; simp
  rcases Nat.lt_or_ge n 16384 with h2 | h2
  · rw [encodeNat_len2 n ⟨h1, h2⟩]; simp
  · rw [encodeNat_len3 n ⟨h2, by omega⟩]; simp

theorem encodeNat_length_le5 (n : Nat) (h : n < 4294967296) : (Blob.encodeNat n).length ≤ 5 ∧
    1 ≤ (Blob.encodeNat n).length := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; simp [Blob.encodeNat]
  rcases Nat.lt_or_ge n 128 with h1 | h1
  · rw [encodeNat_len1 n ⟨h0, h1⟩]; simp
  rcases Nat.lt_or_ge n 16384 with h2 | h2
  · rw [encodeNat_len2 n ⟨h1, h2⟩]; simp
  rcases Nat.lt_or_ge n 2097152 with h3 | h3
  · rw [encodeNat_len3 n ⟨h2, h3⟩]; simp
  rcases Nat.lt_or_ge n 268435456 with h4 | h4
  · rw [encodeNat_len4 n ⟨h3, h4⟩]; simp
  · rw [encodeNat_len5 n ⟨h4, by omega⟩]; simp

/-- **Witness's refine rejects a payload with a bad tag.** From any starting memory that meets the
    prefix's needs (`StartMem`; Y's RAM does, `startMem_initial`) and holds the arguments
    ℰ(c) ⌢ ℰ(i) ⌢ ℰ(s) ⌢ ↕y ⌢ h at `argStart`, readable, for every core index c < 2^16, item index
    i < 2^16, service id s < 2^32, payload y of 1 to 15 octets whose first octet (the `Op` tag) is
    at least 12, and 32-octet h: the gas-free machine runs from Y's registers to the halting step at
    43609 with ω₇ = 206816, ω₈ = 2 and the octets [12, 0] there, `Rejected(BadPayload)`. -/
theorem run_badTag (p : ByteArray) (P : Program) [HasCode p P] (env : RefineHost.Env)
    (henv : heapBounds env.code = (48, 1044368)) (hpar : env.fetch.params = Params.full) (μ : Memory)
    (hμ : StartMem μ) (C I S : Nat) (y h : List UInt8) (hC : C < 65536) (hI : I < 65536)
    (hS : S < 4294967296) (hy : 1 ≤ y.length ∧ y.length ≤ 15) (htag : 12 ≤ (y.headD 0).toNat)
    (hh : h.length = 32)
    (hmem : μ.readN 4278124544 (Blob.encodeNat C ++ Blob.encodeNat I ++ Blob.encodeNat S ++
      Blob.encodeNat y.length ++ y ++ h).length = Blob.encodeNat C ++ Blob.encodeNat I ++
      Blob.encodeNat S ++ Blob.encodeNat y.length ++ y ++ h)
    (hrd : ∀ j, 4278124544 ≤ j → j < 4278124544 + (Blob.encodeNat C ++ Blob.encodeNat I ++
      Blob.encodeNat S ++ Blob.encodeNat y.length ++ y ++ h).length → μ.readable j = true) :
    ∃ ω' μ' x', FreeStepsH p (refineContract env) 0 (initRegs (Blob.encodeNat C ++ Blob.encodeNat I ++
      Blob.encodeNat S ++ Blob.encodeNat y.length ++ y ++ h).length) μ ((∅, []) : RefineCtx) 43609
      ω' μ' x' ∧ ω'[0] = UInt64.ofNat 4294901760 ∧ ω'[7] = UInt64.ofNat 206816 ∧
      ω'[8] = UInt64.ofNat 2 ∧ μ'.read 206816 = 12 ∧ μ'.read 206817 = 0 ∧
      μ'.readable 206816 = true ∧ μ'.readable 206817 = true := by
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
  -- the tag: the payload's first octet
  have htagb : μ.read (4278124544 + (Blob.encodeNat C).length + (Blob.encodeNat I).length + (Blob.encodeNat S).length + (Blob.encodeNat y.length).length) = UInt8.ofNat (y.headD 0).toNat := by
    obtain ⟨b, ys, rfl⟩ : ∃ b ys, y = b :: ys := by
      cases y with
      | nil => simp at hy
      | cons b ys => exact ⟨b, ys, rfl⟩
    have := sy
    rw [show (b :: ys).length = ys.length + 1 by simp, Memory.readN_succ'] at this
    simp only [List.cons.injEq] at this
    simpa [Nat.add_assoc] using this.1
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
  -- Front3
  refine (fun h8 => ?_) (Front3.run p P env ω7 μ7 ((∅, []) : RefineCtx) (4278124544 + (Blob.encodeNat C).length + (Blob.encodeNat I).length + (Blob.encodeNat S).length + (Blob.encodeNat y.length).length) ⟨by omega, by omega⟩ y.length hy ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  · obtain ⟨ω8, μ8, run8, g8, m8, s8, f8, rd8, wr8⟩ := h8
    chase_prep at s8
    -- the payload copy
    obtain ⟨ω9, run9, g9_0, g9_1, g9_2, g9_3, g9_4, g9_5, g9_6, g9_7, g9_12⟩ := memcpy_small_regs
      (p := p) (P := P) (R := refineContract env) ((∅, []) : RefineCtx) ω8 μ8 492 23918 4278058712 206752
      (4278124544 + (Blob.encodeNat C).length + (Blob.encodeNat I).length + (Blob.encodeNat S).length + (Blob.encodeNat y.length).length) y.length (by chase) (by chase) (by chase) (by chase) (by chase)
      (by omega) (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_245]) bs_23918
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by intro a h1 h2; chase) (by intro a h1 h2; chase) (by intro a h1 h2; chase)
    -- Front4
    refine (fun h10 => ?_) (Front4.run p P env ω9
      ((memcpyFrame μ8 ω8 4278058712).writeN 206752 (μ8.readN (4278124544 + (Blob.encodeNat C).length + (Blob.encodeNat I).length + (Blob.encodeNat S).length + (Blob.encodeNat y.length).length) y.length))
      ((∅, []) : RefineCtx) (y.headD 0).toNat ⟨htag, UInt8.toNat_lt _⟩ S hS I hI y.length hy (4278124544 + (Blob.encodeNat C).length + (Blob.encodeNat I).length + (Blob.encodeNat S).length + (Blob.encodeNat y.length).length) ⟨by omega, by omega⟩ L (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    · obtain ⟨ω10, μ10, run10, g10, m10, s10, f10, rd10, wr10⟩ := h10
      chase_prep at s10
      simp only [memcpyFrame] at f10 rd10 wr10
      -- the error tail
      refine (fun hT0 => ?_) (ErrTail0.run p P env ω10 μ10 ((∅, []) : RefineCtx) (y.headD 0).toNat ⟨htag, UInt8.toNat_lt _⟩ y.length hy I hI ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      · obtain ⟨ω11, μ11, run11, post11⟩ := hT0
        chase_prep at post11
        refine (fun hT1 => ?_) (ErrTail1.run p P env ω11 μ11 ((∅, []) : RefineCtx) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        · obtain ⟨ω12, μ12, run12, post12⟩ := hT1
          chase_prep at post12
          refine (fun hT2 => ?_) (ErrTail2.run p P env ω12 μ12 ((∅, []) : RefineCtx) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
          · obtain ⟨ω13, μ13, run13, post13⟩ := hT2
            chase_prep at post13
            refine (fun hT3 => ?_) (ErrTail3.run p P env ω13 μ13 ((∅, []) : RefineCtx) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
            · obtain ⟨ω14, μ14, run14, post14⟩ := hT3
              chase_prep at post14
              refine (fun hT4 => ?_) (ErrTail4.run p P env ω14 μ14 ((∅, []) : RefineCtx) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
              · obtain ⟨ω15, μ15, run15, post15⟩ := hT4
                chase_prep at post15
                refine (fun hT5 => ?_) (ErrTail5.run p P env ω15 μ15 ((∅, []) : RefineCtx) S hS y.length hy ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
                · obtain ⟨ω16, μ16, run16, post16⟩ := hT5
                  chase_prep at post16
                  exact ⟨ω16, μ16, _, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans (run8.trans (run9.trans (run10.trans (run11.trans (run12.trans (run13.trans (run14.trans (run15.trans run16)))))))))))))), by chase, by chase, by chase, by chase, by chase,
                    Memory.readable_of_writable (by chase), Memory.readable_of_writable (by chase)⟩
                all_goals (try simp only [memcpyFrame])
                all_goals chase_prep
                all_goals chase
              all_goals (try simp only [memcpyFrame])
              all_goals chase_prep
              all_goals chase
            all_goals (try simp only [memcpyFrame])
            all_goals chase_prep
            all_goals chase
          all_goals (try simp only [memcpyFrame])
          all_goals chase_prep
          all_goals chase
        all_goals (try simp only [memcpyFrame])
        all_goals chase_prep
        all_goals chase
      all_goals (try simp only [memcpyFrame])
      all_goals chase_prep
      all_goals chase
    all_goals (try simp only [memcpyFrame])
    all_goals chase_prep
    all_goals chase
  all_goals chase_prep
  all_goals chase

end Services.Witness.BadPayload
