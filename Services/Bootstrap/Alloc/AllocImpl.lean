import Services.Bootstrap.Alloc.AllocTail

/-!
# The binary's `alloc_impl`, composed

The stages of `alloc_impl` (alignment one unit, the heap in use, no growth, not zeroing) put
together: the entry and the bin search to the chosen chunk (41177 … 41425), …
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

theorem binUp_small {x : Nat} (h1 : 1 ≤ x) (h2 : x ≤ 127) : binUp x = x - 1 := by
  unfold binUp toBin
  rw [maxSize_val]
  simp only [show min x 33554432 = x by omega, show x ≠ 0 by omega, ↓reduceIte, mantissaBits,
    show x < 2 ^ 7 by simp; omega]

/-- **41221 … 41297**, alignment one unit: ω₀ and ω₂ the request's bins rounded down and up. -/
theorem al_bins {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (req : Nat) (h9 : ω[9] = UInt64.ofNat req) (h8 : ω[8] = UInt64.ofNat 1)
    (h12 : ω[12] = UInt64.ofNat 1) (hm : req + 1 ≤ 33554432) :
    ∃ ω', FreeStepsH p R 41221 ω μ x 41297 ω' μ x 30 ∧
      ω'[0] = UInt64.ofNat (binDown (req + 1)) ∧ ω'[2] = UInt64.ofNat (binUp (req + 1)) ∧
      ω'[4] = UInt64.ofNat (req + 1) ∧ ω'[12] = UInt64.ofNat (req + 1) ∧
      ∀ j : Fin 13, j.val ∉ [0, 2, 3, 4, 5, 6, 11, 12] → ω'[j] = ω[j] := by
  by_cases hs : req + 1 < 128
  · obtain ⟨ω', r, a0, a2, a12, a4, g⟩ := al_bin_small (p := p) (P := P) (R := R) x ω μ req 1 h9 h8 h12 (Nat.le_refl 1) hs
    refine ⟨ω', r.mono (by omega), ?_, ?_, a4, a12, fun j hj => g j (by simp at hj ⊢; omega)⟩
    · rw [a0, binDown_small (by omega) (by omega)]
    · rw [a2, binUp_small (by omega) (by omega)]
  · exact al_bin_big (p := p) (P := P) (R := R) x ω μ req 1 h9 h8 h12 (Nat.le_refl 1) (by decide) (by omega) hm

/-- **41177 … 41425**, alignment one unit, the heap in use: the frame, the bins of `req + 1`, the
    search (the model's `findFirst`, rounded up, else rounded down) to `bin`, and its first chunk C,
    large enough. -/
theorem alloc_entry {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (sp req bin C w : Nat) (hbits : BitsOk s.secondary s.primary s.heads)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat 1)
    (h9 : ω[9] = UInt64.ofNat req) (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb : rdN μ 206520 8 = s.base) (hb0 : s.base ≠ 0)
    (hp : rdN μ 206832 8 = s.primary) (hs : ∀ q, q < 38 → rdN μ (q * 8 + 204984 + 1544) 8 = s.secondary q)
    (hm : req + 1 ≤ 33554432)
    (hbin : (findFirst s (binUp (req + 1))).or (findFirst s (binDown (req + 1))) = some bin)
    (hC : rdN μ (196792 + 4 * bin) 4 = C) (hw : rdN μ (C + 4) 4 = w) (hC1 : C + 8 < 2147483648)
    (hS : req + 1 ≤ w / 2) (hwr : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 41177 ω μ x 41425 ω' μ' x 120 ∧ ∃ q b, q * 64 + b = bin ∧ q < 38 ∧ b < 64 ∧
      ω'[1] = UInt64.ofNat (sp - 152) ∧ ω'[10] = UInt64.ofNat C ∧ ω'[11] = UInt64.ofNat (w / 2) ∧
      ω'[5] = UInt64.ofNat (196792 + 4 * bin) ∧ ω'[2] = UInt64.ofNat b ∧ ω'[6] = UInt64.ofNat q ∧
      ω'[3] = UInt64.ofNat 204984 ∧ ω'[8] = UInt64.ofNat 1 ∧ ω'[9] = UInt64.ofNat req ∧
      ω'[4] = UInt64.ofNat (req + 1) ∧ ω'[12] = UInt64.ofNat (req + 1) ∧ ω'[7] = UInt64.ofNat 196792 ∧
      μ'.readN (sp - 8) 8 = Num.encodeLE 8 ω[0].toNat ∧ μ'.readN (sp - 16) 8 = Num.encodeLE 8 ω[5].toNat ∧
      μ'.readN (sp - 24) 8 = Num.encodeLE 8 ω[6].toNat ∧ μ'.readN (sp - 40) 8 = Num.encodeLE 8 ω[10].toNat ∧
      rdN μ' (sp - 32) 8 = 204984 ∧
      (∀ a, a < 4294967296 → (a < sp - 152 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) := by
  have hb64 : s.base < 18446744073709551616 := by rw [← hb]; exact rdN_lt64 μ _
  obtain ⟨ω1, μ1, r1, a1, a11, a12, st0, st5, st6, st10, st32, sf1, ww1, g1⟩ :=
    al_pro (p := p) (P := P) (R := R) x ω μ sp 0 s.base h1 h7 (by rw [h8]) (by decide) hsp hsp1 hb hwr
  have hr1 : ∀ a, μ1.readable a = true := fun a => Memory.readable_of_writable (ww1 a)
  have tr : ∀ a n, a + n ≤ 2147483648 → rdN μ1 a n = rdN μ a n := fun a n h =>
    rdN_frame fun j hj => sf1 _ (by omega) (Or.inl (by omega))
  have r2 := al_br_used (p := p) (P := P) (R := R) x ω1 μ1 s.base a11 hb0 hb64
  obtain ⟨ω2, r3, b0, b2, b4, b12, g3⟩ := al_bins (p := p) (P := P) (R := R) x ω1 μ1 req
    (by rw [fget g1 9 (by decide) (by decide)]; exact h9) (by rw [fget g1 8 (by decide) (by decide)]; exact h8) a12 hm
  have hbU : binUp (req + 1) < 2432 := toBin_lt true (Nat.min_le_right _ _)
  have hbD : binDown (req + 1) < 2432 := toBin_lt false (Nat.min_le_right _ _)
  have hp1 : rdN μ1 206832 8 = s.primary := by rw [tr _ _ (by omega)]; exact hp
  have hs1 : ∀ q, q < 38 → rdN μ1 (q * 8 + 204984 + 1544) 8 = s.secondary q := fun q hq => by
    rw [tr _ _ (by omega)]; exact hs q hq
  have hf1 : rdN μ1 (sp - 152 + 120) 8 = 204984 := by rw [show sp - 152 + 120 = sp - 32 by omega]; exact st32
  have c7 : ω2[7] = UInt64.ofNat 196792 := by
    rw [fget g3 7 (by decide) (by decide), fget g1 7 (by decide) (by decide)]; exact h7
  have c1 : ω2[1] = UInt64.ofNat (sp - 152) := by rw [fget g3 1 (by decide) (by decide)]; exact a1
  have fu := find_up (p := p) (P := P) (R := R) x ω2 μ1 s (sp - 152) _ hbits c1 b2 c7 (by omega) hf1 hp1 hs1 hbU hr1
  -- the search ends at 41378 with the bin as word q, bit b
  obtain ⟨ω4, q, b, r45, hqb, hq, hb', d6, d2, d3, fr4⟩ : ∃ ω4 q b, FreeStepsH p R 41297 ω2 μ1 x 41378 ω4 μ1 x 60 ∧
      q * 64 + b = bin ∧ q < 38 ∧ b < 64 ∧ ω4[6] = UInt64.ofNat q ∧ ω4[2] = UInt64.ofNat b ∧
      ω4[3] = UInt64.ofNat 204984 ∧ ∀ j : Fin 13, j.val ∉ [2, 3, 5, 6, 10, 11] → ω4[j] = ω2[j] := by
    cases hu : findFirst s (binUp (req + 1)) with
    | some bin' =>
      have : bin' = bin := by rw [hu] at hbin; exact Option.some.inj hbin
      subst this
      obtain ⟨ω4, q, b, r, e1, e2, e3, e4, e5, e6, -, e8⟩ := fu.1 _ hu
      exact ⟨ω4, q, b, r.mono (by omega), e1, e2, e3, e4, e5, e6, e8⟩
    | none =>
      rw [hu, Option.none_or] at hbin
      obtain ⟨ω3, r, e5, e3, e8⟩ := fu.2 hu
      obtain ⟨ω4, q, b, r', f1, f2, f3, f4, f5, f6⟩ := (find_down (p := p) (P := P) (R := R) x ω3 μ1 s _ hbits
        (by rw [fget e8 0 (by decide) (by decide)]; exact b0) e5 e3 hs1 hbD hr1).1 _ hbin
      exact ⟨ω4, q, b, (r.trans r').mono (by omega), f1, f2, f3, f4, f5,
        by rw [fget f6 3 (by decide) (by decide)]; exact e3,
        frame_trans f6 e8 (fun j hj => by simp at hj ⊢; omega) (fun j hj => by simp at hj ⊢; omega)⟩
  have k7 : ω4[7] = UInt64.ofNat 196792 := by rw [fget fr4 7 (by decide) (by decide)]; exact c7
  have k12 : ω4[12] = UInt64.ofNat (req + 1) := by rw [fget fr4 12 (by decide) (by decide)]; exact b12
  have hC' : rdN μ1 (196792 + 4 * (q * 64 + b)) 4 = C := by rw [hqb, tr _ _ (by omega)]; exact hC
  have hw' : rdN μ1 (C + 4) 4 = w := by rw [tr _ _ (by omega)]; exact hw
  obtain ⟨ω5, r5, e10, e11, e5, g5⟩ := al_pick (p := p) (P := P) (R := R) x ω4 μ1 q b C w (w / 2 * 0 + (req + 1))
    d6 d2 k7 (by simpa using k12) hq hb' hC' hw' (by omega) (by omega) hr1
  have hw64 : w / 2 < 18446744073709551616 := by
    have := rdN_lt μ (C + 4) 4; rw [hw] at this; omega
  have r6 := al_size_ok (p := p) (P := P) (R := R) x ω5 μ1 (w / 2) (req + 1) e11
    (by rw [fget g5 12 (by decide) (by decide)]; exact k12) hS hw64
  have fr : ∀ j : Fin 13, j.val ∉ [0, 2, 3, 4, 5, 6, 10, 11, 12] → ω5[j] = ω1[j] :=
    frame_trans g5 (frame_trans (l := [0, 2, 3, 4, 5, 6, 10, 11, 12]) fr4 g3 (fun j hj => by simp at hj ⊢; omega) (fun j hj => by simp at hj ⊢; omega))
      (fun j hj => by simp at hj ⊢; omega) (fun j hj => by simp at hj ⊢; omega)
  refine ⟨ω5, μ1, ((((r1.trans r2).trans r3).trans r45).trans (r5.trans r6)).mono (by omega), q, b, hqb, hq, hb',
    by rw [fget fr 1 (by decide) (by decide)]; exact a1, e10, e11, by rw [e5, hqb],
    by rw [fget g5 2 (by decide) (by decide)]; exact d2, by rw [fget g5 6 (by decide) (by decide)]; exact d6,
    by rw [fget g5 3 (by decide) (by decide)]; exact d3,
    by rw [fget fr 8 (by decide) (by decide), fget g1 8 (by decide) (by decide)]; exact h8,
    by rw [fget fr 9 (by decide) (by decide), fget g1 9 (by decide) (by decide)]; exact h9,
    by rw [fget g5 4 (by decide) (by decide), fget fr4 4 (by decide) (by decide)]; exact b4,
    by rw [fget g5 12 (by decide) (by decide)]; exact k12,
    by rw [fget g5 7 (by decide) (by decide)]; exact k7,
    st0, st5, st6, st10, st32, sf1, ww1⟩

/-- **41589 … 41726**: the chosen chunk C, its bin's head, leaves the bin — the memory holds
    `unregister s C bin`; C's `prev` saved at sp + 48, ω₈ = 32·c. -/
theorem al_unreg {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (H F : Nat → Prop) (sp C c bin q b : Nat) (hrep : RepAt μ s H F)
    (hcb : s.heads bin = C) (hqb : q * 64 + b = bin) (hq : q < 38) (hb : b < 64)
    (hFC : F C) (hHC : H C) (hHF : ∀ a, H a ∨ F a → Al s.base a)
    (hnx : (s.hdr C).next ≠ 0 → F (s.hdr C).next) (hb0 : 206864 ≤ s.base)
    (hbT : s.base + 1073741824 < 2147483648) (hpv : (s.hdr C).prev < 2147483648) (hc : c < 33554432)
    (h1 : ω[1] = UInt64.ofNat sp) (h10 : ω[10] = UInt64.ofNat C) (h3 : ω[3] = UInt64.ofNat c)
    (h64 : rdN μ (sp + 64) 8 = 196792 + 4 * bin) (h40 : rdN μ (sp + 40) 8 = q) (h32 : rdN μ (sp + 32) 8 = b)
    (h88 : rdN μ (sp + 88) 8 = 204984) (h120 : rdN μ (sp + 120) 8 = 204984)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) (hw : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 41589 ω μ x 41726 ω' μ' x 30 ∧ RepAt μ' (unregister s C bin) H F ∧
      rdN μ' (sp + 48) 8 = (s.hdr C).prev ∧ ω'[8] = UInt64.ofNat (32 * c) ∧
      (∀ a, μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → 2147483648 ≤ a → (a < sp + 48 ∨ sp + 56 ≤ a) → μ'.read a = μ.read a) ∧
      ∀ j : Fin 13, j.val ∉ [2, 5, 6, 8, 10, 11, 12] → ω'[j] = ω[j] := by
  have hAC := hHF C (Or.inr hFC)
  unfold Al at hAC
  have hn : rdN μ (C + 8) 4 = (s.hdr C).next := hrep.next C hFC
  have hpC : rdN μ C 4 = (s.hdr C).prev := hrep.prev C hHC
  have hbB : bin < 2432 := by omega
  by_cases h0' : (s.hdr C).next = 0
  · obtain ⟨ω1, μ1, r1, s1, p48, e8, fr1, ww1, g1⟩ := au_last (p := p) (P := P) (R := R) x ω μ sp C c
      (196792 + 4 * bin) (s.hdr C).prev h1 h10 h3 h64 (by rw [hn, h0']) hpC hpv (by omega) (by omega) hc
      hsp0 hsp hw
    have hsec := hrep.sec q hq
    have hpri := hrep.pri
    unfold A0 at hsec hpri
    have tr : ∀ a n, 206520 ≤ a → a + n ≤ 2147483648 → rdN μ1 a n = rdN μ a n := fun a n h h' =>
      rdN_frame fun j hj => fr1 _ (by omega) (Or.inr (by omega)) (Or.inl (by omega))
    have trs : ∀ a, sp + 32 ≤ a → a + 8 ≤ sp + 48 → rdN μ1 a 8 = rdN μ a 8 := fun a h h' =>
      rdN_frame fun j hj => fr1 _ (by omega) (Or.inr (by omega)) (Or.inl (by omega))
    have trs' : ∀ a, sp + 56 ≤ a → a + 8 ≤ sp + 152 → rdN μ1 a 8 = rdN μ a 8 := fun a h h' =>
      rdN_frame fun j hj => fr1 _ (by omega) (Or.inr (by omega)) (Or.inr (by omega))
    obtain ⟨ω2, μ2, r2, c1, c2, cf, cw, cg⟩ := au_clear (p := p) (P := P) (R := R) x ω1 μ1 sp q b
      (s.secondary q) s.primary (by rw [fget g1 1 (by decide) (by decide)]; exact h1)
      (by rw [trs _ (by omega) (by omega)]; exact h40) (by rw [trs _ (by omega) (by omega)]; exact h32)
      (by rw [trs' _ (by omega) (by omega)]; exact h88) (by rw [trs' _ (by omega) (by omega)]; exact h120) hq hb
      (by rw [tr _ _ (by omega) (by omega), ← hsec, show 196792 + 9736 + 8 * q = q * 8 + 204984 + 1544 by omega])
      (by rw [tr _ _ (by omega) (by omega), ← hpri]) hsp0 hsp ww1
    refine ⟨ω2, μ2, (r1.trans r2).mono (by omega), ?_, ?_, by rw [fget cg 8 (by decide) (by decide)]; exact e8, cw,
      fun a h1 h2 h3 => ?_, ?_⟩
    · have hbq : bin / 64 = q := by omega
      have hbr : bin % 64 = b := by omega
      refine unregister_rep_last hrep hcb (by unfold binCount; omega) h0' ?_ ?_ ?_ ?_ (fun a ha => ?_)
      · rw [show 196792 + bin * 4 = 196792 + 4 * bin by omega, ← s1]
        exact rdN_frame fun j hj => cf _ (by omega) (by omega) (by omega)
      · rw [hbq, hbr, show 204984 + q * 8 + 1544 = q * 8 + 204984 + 1544 by omega, c1, ← hsec,
          show 196792 + 9736 + 8 * q = q * 8 + 204984 + 1544 by omega]
      · rw [hbq, hbr, show 204984 + q * 8 + 1544 = q * 8 + 204984 + 1544 by omega, c2, ← hsec, ← hpri,
          show 196792 + 9736 + 8 * q = q * 8 + 204984 + 1544 by omega, show 196792 + 10040 = 206832 from rfl]
      · intro a h1 h2 h3 h4
        rw [hbq] at h3
        rw [cf a (by omega) (by omega) h4, fr1 a (by omega) (by omega) (Or.inl (by omega))]
      · have := hHF a ha; unfold Al at this; omega
    · rw [← p48]; exact rdN_frame fun j hj => cf _ (by omega) (by omega) (by omega)
    · rw [cf a h1 (by omega) (by omega), fr1 a h1 (by omega) h3]
    · exact frame_trans cg g1 (fun j hj => by simp at hj ⊢; omega) (fun j hj => by simp at hj ⊢; omega)
  · have hFx := hnx h0'
    have hAx := hHF _ (Or.inr hFx)
    unfold Al at hAx
    obtain ⟨ω1, μ1, r1, s1, s2, p48, e8, fr1, ww1, g1⟩ := au_head (p := p) (P := P) (R := R) x ω μ sp C c
      (196792 + 4 * bin) (s.hdr C).next (s.hdr C).prev h1 h10 h3 h64 hn hpC hpv h0' (by omega) (by omega)
      (by omega) (by omega) hc hsp0 hsp hw
    refine ⟨ω1, μ1, r1.mono (by omega), ?_, p48, e8, ww1, fun a h1 h2 h3 => fr1 a h1 (by omega) (by omega) h3,
      fun j hj => g1 j (by simp at hj ⊢; omega)⟩
    refine unregister_rep_head hrep hcb (by unfold binCount; omega) h0'
      (by rw [show 196792 + bin * 4 = 196792 + 4 * bin by omega]; exact s1) s2
      (fun a h1 h2 h3 => fr1 a (by omega) (by omega) h3 (Or.inl (by omega))) (by omega) (fun a ha => ?_)
    have := hHF a ha; unfold Al at this; omega

end Services.Bootstrap.Alloc
