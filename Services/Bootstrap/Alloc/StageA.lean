import Services.Bootstrap.Alloc.Stages

/-!
# The binary's `free`: the merge with the previous chunk

`free_prev` (42369 … 42597) is the model's `mergePrev`.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- What `free_prev` needs of a free chunk Pa before X (the invariant gives it): a free chunk of
    pv units, X's `prev`, linked in its bin's list. -/
def PvFree (s : State) (F : Nat → Prop) (base Pa n pv : Nat) : Prop :=
  F Pa ∧ (s.hdr Pa).size = 2 * pv ∧ 1 ≤ pv ∧ pv ≤ 33554432 ∧ n + pv < 2147483648 ∧
    (s.hdr Pa).prev < 2147483648 ∧
    (s.heads (binDown pv) = 0 ∨ Al base (s.heads (binDown pv))) ∧
    ((s.hdr Pa).next ≠ 0 → F (s.hdr Pa).next) ∧
    (s.heads (binDown pv) ≠ Pa → F (s.hdr Pa).prevL ∧ ((s.hdr Pa).next ≠ 0 → (s.hdr Pa).next ≠ (s.hdr Pa).prevL))

/-- **`free`'s merge with the previous chunk, 42369 … 42597**: the memory holds the model's
    `mergePrev`, with the merged chunk in ω₈, its size in ω₂ and its `prev` in ω₃. -/
theorem free_prev {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (H F : Nat → Prop) (Xa n pv : Nat) (hrep : RepAt μ s H F)
    (h9 : ω[9] = UInt64.ofNat (Xa - s.base)) (h11 : ω[11] = UInt64.ofNat 31) (h8 : ω[8] = UInt64.ofNat Xa)
    (h3 : ω[3] = UInt64.ofNat pv) (h2 : ω[2] = UInt64.ofNat n) (h5 : ω[5] = UInt64.ofNat s.base)
    (h7 : ω[7] = UInt64.ofNat 196792) (h4 : ω[4] = UInt64.ofNat 204984)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hAX : Al s.base Xa)
    (hHF : ∀ a, H a ∨ F a → Al s.base a)
    (hpH : Xa ≠ s.base → 32 * pv ≤ Xa - s.base ∧ H (Xa - 32 * pv))
    (hfree : Xa ≠ s.base → (s.hdr (Xa - 32 * pv)).size % 2 = 0 → PvFree s F s.base (Xa - 32 * pv) n pv)
    {HT S0 S1 : Nat} (hHFT : ∀ a, H a ∨ F a → a + 32 ≤ HT) (hw : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 42369 ω μ x 42597 ω' μ' x 70 ∧
      RepAt μ' (mergePrev s Xa n pv).1 H F ∧
      ω'[8] = UInt64.ofNat (mergePrev s Xa n pv).2.1 ∧ ω'[2] = UInt64.ofNat (mergePrev s Xa n pv).2.2.1 ∧
      ω'[3] = UInt64.ofNat (mergePrev s Xa n pv).2.2.2 ∧ ω'[5] = UInt64.ofNat s.base ∧
      (∀ a, μ'.writable a = μ.writable a) ∧ (∀ a, a < 4294967296 → 2147483648 ≤ a → μ'.read a = μ.read a) ∧
      HKeepG μ μ' (fun a => H a ∨ F a) ∧
      ∀ j : Fin 13, j.val ∉ [0, 2, 3, 5, 6, 8, 9, 10, 11, 12] → ω'[j] = ω[j] := by
  have hr := hw.rd
  obtain ⟨hX1, hX2, hX3⟩ := hAX
  unfold mergePrev
  by_cases hXb : Xa = s.base
  · -- X is the first chunk
    rw [if_neg (fun h => h hXb)]
    have b := pv_br_first (p := p) (P := P) (R := R) x ω μ (Xa - s.base) h9 h11 (by omega)
    exact ⟨ω, μ, b.mono (by omega), hrep, h8, h2, h3, h5, fun _ => rfl, fun _ _ _ => rfl, HKeepG.refl μ _,
      fun _ _ => rfl⟩
  rw [if_pos hXb]
  dsimp only
  obtain ⟨hpv, hHP⟩ := hpH hXb
  have b1 := pv_br_has (p := p) (P := P) (R := R) x ω μ (Xa - s.base) h9 h11 (by
    have := hX2; omega) (by omega)
  have hAP := hHF _ (Or.inl hHP)
  have hPT := hHFT _ (Or.inl hHP)
  unfold Al at hAP
  have hsz : rdN μ (Xa - 32 * pv + 4) 4 = (s.hdr (Xa - 32 * pv)).size := hrep.size _ hHP
  obtain ⟨ω1, r1, c0, c12, c9, c11, g1⟩ := pv_hdr (p := p) (P := P) (R := R) x ω μ Xa pv
    (s.hdr (Xa - 32 * pv)).size h3 h8 (by omega) (by omega) hsz ⟨by omega, by omega⟩ hr
  generalize hPa : Xa - 32 * pv = Pa at *
  generalize hW : (s.hdr Pa).size = w at *
  by_cases hu : w % 2 = 1
  · have b2 := pv_br_used (p := p) (P := P) (R := R) x ω1 μ (w % 2) c12 (by omega) (by omega)
    have hwu : (!wordUsed w) = false := by simp [wordUsed, hu]
    rw [if_neg (by simp [hwu])]
    refine ⟨ω1, μ, ((b1.trans r1).trans b2).mono (by omega), hrep, ?_, ?_, ?_, ?_, fun _ => rfl, fun _ _ _ => rfl,
      HKeepG.refl μ _, fun j hj => g1 j (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega)⟩
    · rw [fget g1 8 (by decide) (by decide)]; exact h8
    · rw [fget g1 2 (by decide) (by decide)]; exact h2
    · rw [fget g1 3 (by decide) (by decide)]; exact h3
    · rw [fget g1 5 (by decide) (by decide)]; exact h5
  · have hu0 : w % 2 = 0 := by omega
    obtain ⟨hFn, hw2, hp1, hp2, hss, hpp, hhd, hnx, hmid⟩ := hfree hXb hu0
    rw [hW] at hw2
    have b2 := pv_br_free (p := p) (P := P) (R := R) x ω1 μ (by rw [c12, hu0])
    have hwu : (!wordUsed w) = true := by simp [wordUsed, hu0]
    rw [if_pos hwu]
    have hws : wordSize w = pv := by unfold wordSize; rw [hw2]; omega
    rw [hws]
    have h0' : ω1[0] = UInt64.ofNat (2 * pv) := by rw [c0, hw2]
    have hB : binDown pv < 2432 := toBin_lt false (Nat.min_le_right _ _)
    have hhd' : rdN μ (196792 + binDown pv * 4) 4 = s.heads (binDown pv) := by
      have := hrep.heads (binDown pv) (by unfold binCount; omega)
      unfold A0 at this; rw [show 196792 + binDown pv * 4 = 196792 + 4 * binDown pv by omega, this]
    have hpp' : rdN μ Pa 4 = (s.hdr Pa).prev := hrep.prev Pa hHP
    have e7 : ω1[7] = UInt64.ofNat 196792 := by rw [fget g1 7 (by decide) (by decide)]; exact h7
    -- the join, from either unlinking
    have join : ∀ (ω3 : Regs) (μ3 : Memory) (s3 : State), RepAt μ3 s3 H F → s3.base = s.base →
        RdAt μ3 HT S0 S1 →
        ω3[4] = UInt64.ofNat 204984 → ω3[10] = UInt64.ofNat pv → ω3[2] = UInt64.ofNat n →
        ω3[0] = UInt64.ofNat (2 * pv) → ω3[8] = UInt64.ofNat Xa →
        ∃ ω4, FreeStepsH p R 42583 ω3 μ3 x 42597 ω4 μ3 x 5 ∧ ω4[5] = UInt64.ofNat s.base ∧
          ω4[2] = UInt64.ofNat (n + pv) ∧ ω4[8] = UInt64.ofNat Pa ∧
          ∀ j : Fin 13, j.val ∉ [0, 2, 5, 8] → ω4[j] = ω3[j] := by
      intro ω3 μ3 s3 rep3 hb3 hw3 e4 e10 e2 e0 e8
      have hbase3 : rdN μ3 206520 8 = s.base := by have := rep3.base; unfold A0 at this; rw [← hb3]; exact this
      obtain ⟨ω4, r4, d5, d2, d8, g4⟩ := pv_join (p := p) (P := P) (R := R) x ω3 μ3 s.base pv n (2 * pv) Xa
        e4 e10 e2 e0 e8 hbase3 (by omega) (by omega) (by omega) (by omega) hw3
      exact ⟨ω4, r4, d5, by rw [d2]; congr 1; omega, by rw [d8, ← hPa]; congr 1; omega, g4⟩
    have hfr : ∀ (l1 l2 l3 l4 : List Nat) (ω2 ω3 ω4 : Regs),
        (∀ j : Fin 13, j.val ∉ l2 → ω2[j] = ω1[j]) → (∀ j : Fin 13, j.val ∉ l3 → ω3[j] = ω2[j]) →
        (∀ j : Fin 13, j.val ∉ l4 → ω4[j] = ω3[j]) → l1 = [0, 9, 11, 12] →
        (∀ j, j ∈ l2 → j ∈ [0, 2, 3, 5, 6, 8, 9, 10, 11, 12]) → (∀ j, j ∈ l3 → j ∈ [0, 2, 3, 5, 6, 8, 9, 10, 11, 12]) →
        (∀ j, j ∈ l4 → j ∈ [0, 2, 3, 5, 6, 8, 9, 10, 11, 12]) →
        ∀ j : Fin 13, j.val ∉ [0, 2, 3, 5, 6, 8, 9, 10, 11, 12] → ω4[j] = ω[j] := by
      intro l1 l2 l3 l4 ω2 ω3 ω4 f2 f3 f4 hl1 s2 s3 s4 j hj
      rw [f4 j (fun h => hj (s4 _ h)), f3 j (fun h => hj (s3 _ h)), f2 j (fun h => hj (s2 _ h)),
        g1 j (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega)]
    by_cases hh : s.heads (binDown pv) = Pa
    · obtain ⟨ω2, r2, d10, d5, d6, d3, g2⟩ := pv_lookup_head (p := p) (P := P) (R := R) x ω1 μ Pa pv
        (s.hdr Pa).prev h0' e7 c9 c11 hp1 hp2 (by rw [hhd', hh]) (by omega) hpp' hpp (by omega) ⟨by omega, by omega⟩ hr
      obtain ⟨ω3, μ3, r3, rep3, ww3, sf3, hk3, g3⟩ := pv_unreg_head (p := p) (P := P) (R := R) x ω2 μ s H F s.base
        Pa (binDown pv) hrep hh (by unfold binCount; omega) hFn hHF hnx hb0 hbT
        (by rw [fget g2 11 (by decide) (by decide)]; exact c11) d6 d5
        (by rw [fget g2 7 (by decide) (by decide)]; exact e7)
        (by rw [fget g2 4 (by decide) (by decide), fget g1 4 (by decide) (by decide)]; exact h4) hHFT hw
      obtain ⟨ω4, r4, j5, j2, j8, g4⟩ := join ω3 μ3 _ rep3 unregister_base (hw.of_eq ww3).rd
        (by rw [fget g3 4 (by decide) (by decide), fget g2 4 (by decide) (by decide),
          fget g1 4 (by decide) (by decide)]; exact h4)
        (by rw [fget g3 10 (by decide) (by decide)]; exact d10)
        (by rw [fget g3 2 (by decide) (by decide), fget g2 2 (by decide) (by decide),
          fget g1 2 (by decide) (by decide)]; exact h2)
        (by rw [fget g3 0 (by decide) (by decide), fget g2 0 (by decide) (by decide)]; exact h0')
        (by rw [fget g3 8 (by decide) (by decide), fget g2 8 (by decide) (by decide),
          fget g1 8 (by decide) (by decide)]; exact h8)
      refine ⟨ω4, μ3, (((((b1.trans r1).trans b2).trans r2).trans r3).trans r4).mono (by omega), rep3, j8, j2,
        by rw [fget g4 3 (by decide) (by decide), fget g3 3 (by decide) (by decide)]; exact d3, j5, ww3, sf3, hk3,
        hfr [0, 9, 11, 12] [3, 5, 6, 10, 12] [5, 6, 9, 11, 12] [0, 2, 5, 8] ω2 ω3 ω4 g2 g3 g4 rfl
          (by intro j h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega)
          (by intro j h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega)
          (by intro j h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega)⟩
    · obtain ⟨hFp, hpn⟩ := hmid hh
      have hhd1 : s.heads (binDown pv) < 2147483648 := by
        rcases hhd with h | h
        · omega
        · unfold Al at h; omega
      obtain ⟨ω2, r2, d10, d5, d3, g2⟩ := pv_lookup_mid (p := p) (P := P) (R := R) x ω1 μ Pa pv
        (s.hdr Pa).prev (s.heads (binDown pv)) h0' e7 c9 c11 hp1 hp2 hhd' hh hhd1 (by omega) hpp' hpp (by omega) ⟨by omega, by omega⟩ hr
      obtain ⟨ω3, μ3, r3, rep3, ww3, sf3, hk3, g3⟩ := pv_unreg_mid (p := p) (P := P) (R := R) x ω2 μ s H F s.base
        Pa (binDown pv) hrep hh hFn hHF hFp hnx hpn hb0 hbT
        (by rw [fget g2 11 (by decide) (by decide)]; exact c11) hHFT hw
      obtain ⟨ω4, r4, j5, j2, j8, g4⟩ := join ω3 μ3 _ rep3 unregister_base (hw.of_eq ww3).rd
        (by rw [fget g3 4 (by decide) (by decide), fget g2 4 (by decide) (by decide),
          fget g1 4 (by decide) (by decide)]; exact h4)
        (by rw [fget g3 10 (by decide) (by decide)]; exact d10)
        (by rw [fget g3 2 (by decide) (by decide), fget g2 2 (by decide) (by decide),
          fget g1 2 (by decide) (by decide)]; exact h2)
        (by rw [fget g3 0 (by decide) (by decide), fget g2 0 (by decide) (by decide)]; exact h0')
        (by rw [fget g3 8 (by decide) (by decide), fget g2 8 (by decide) (by decide),
          fget g1 8 (by decide) (by decide)]; exact h8)
      refine ⟨ω4, μ3, (((((b1.trans r1).trans b2).trans r2).trans r3).trans r4).mono (by omega), rep3, j8, j2,
        by rw [fget g4 3 (by decide) (by decide), fget g3 3 (by decide) (by decide)]; exact d3, j5, ww3, sf3, hk3,
        hfr [0, 9, 11, 12] [3, 5, 6, 10, 12] [9, 11] [0, 2, 5, 8] ω2 ω3 ω4 g2 g3 g4 rfl
          (by intro j h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega)
          (by intro j h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega)
          (by intro j h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega)⟩


/-- `RepAt` depends only on the octets below 2³¹ (for headers inside a heap below 2³¹). -/
theorem RepAt.congr_low {μ μ' : Memory} {t : State} {H F : Nat → Prop} (h : RepAt μ t H F)
    (wf : ∀ b, b < 2147483648 → μ'.read b = μ.read b)
    (hHa : ∀ b, H b ∨ F b → b + 16 < 2147483648) : RepAt μ' t H F := by
  refine ⟨fun b hb => ?_, fun q hq => ?_, ?_, ?_, ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_,
    fun b hb => ?_⟩
  · rw [← h.heads b hb]; unfold A0; unfold binCount at hb; exact rdN_frame fun j hj => wf _ (by omega)
  · rw [← h.sec q hq]; unfold A0; exact rdN_frame fun j hj => wf _ (by omega)
  · rw [← h.pri]; unfold A0; exact rdN_frame fun j hj => wf _ (by omega)
  · rw [← h.base]; unfold A0; exact rdN_frame fun j hj => wf _ (by omega)
  · rw [← h.alloc]; unfold A0; exact rdN_frame fun j hj => wf _ (by omega)
  · have := hHa b (Or.inl hb); rw [← h.prev b hb]; exact rdN_frame fun j hj => wf _ (by omega)
  · have := hHa b (Or.inl hb); rw [← h.size b hb]; exact rdN_frame fun j hj => wf _ (by omega)
  · have := hHa b (Or.inr hb); rw [← h.next b hb]; exact rdN_frame fun j hj => wf _ (by omega)
  · have := hHa b (Or.inr hb); rw [← h.prevL b hb]; exact rdN_frame fun j hj => wf _ (by omega)

end Services.Bootstrap.Alloc
