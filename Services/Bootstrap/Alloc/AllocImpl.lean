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

theorem rd_enc {μ : Memory} {a v : Nat} (h : μ.readN a 8 = Num.encodeLE 8 v) (hv : v < 18446744073709551616) :
    rdN μ a 8 = v := by
  unfold rdN; rw [h, Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt hv

/-- **41425 … 41726**, no growth: the chunk's offsets, then its unlink — the memory holds
    `unregister s C bin`; what the later stages read is left in registers and the frame. -/
theorem alloc_mid {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (H F : Nat → Prop) (sp req bin q b C sz : Nat) (hrep : RepAt μ s H F)
    (hcb : s.heads bin = C) (hqb : q * 64 + b = bin) (hq : q < 38) (hb : b < 64)
    (hFC : F C) (hHC : H C) (hHF : ∀ a, H a ∨ F a → Al s.base a)
    (hnx : (s.hdr C).next ≠ 0 → F (s.hdr C).next) (hb0 : 206864 ≤ s.base)
    (hbT : s.base + 1073741824 < 2147483648) (hpv : (s.hdr C).prev < 2147483648)
    (hrq : req + 1 ≤ sz) (hsz : sz ≤ 33554432) (hCend : C + 32 * sz ≤ s.base + 1073741824)
    (hal : s.allocated < 2147483648)
    (hend : (C - s.base) / 32 + 1 + req + (if sz - req - 1 = 0 then 0 else 1) ≤ s.allocated)
    (h1 : ω[1] = UInt64.ofNat sp) (h10 : ω[10] = UInt64.ofNat C) (h11 : ω[11] = UInt64.ofNat sz)
    (h5 : ω[5] = UInt64.ofNat (196792 + 4 * bin)) (h2 : ω[2] = UInt64.ofNat b) (h6 : ω[6] = UInt64.ofNat q)
    (h3 : ω[3] = UInt64.ofNat 204984) (h8 : ω[8] = UInt64.ofNat 1) (h9 : ω[9] = UInt64.ofNat req)
    (h120 : rdN μ (sp + 120) 8 = 204984)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) (hw : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 41425 ω μ x 41726 ω' μ' x 100 ∧ RepAt μ' (unregister s C bin) H F ∧
      ω'[1] = UInt64.ofNat sp ∧ ω'[8] = UInt64.ofNat (32 * ((C - s.base) / 32)) ∧ ω'[0] = UInt64.ofNat 0 ∧
      rdN μ' (sp + 96) 8 = s.base ∧ rdN μ' (sp + 48) 8 = (s.hdr C).prev ∧ rdN μ' (sp + 80) 8 = s.allocated ∧
      rdN μ' (sp + 72) 8 = (C - s.base) / 32 + 1 ∧ rdN μ' (sp + 104) 8 = sz - req - 1 ∧
      rdN μ' (sp + 88) 8 = 204984 ∧ rdN μ' (sp + 120) 8 = 204984 ∧
      (∀ a, μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → 2147483648 ≤ a → (a < sp + 32 ∨ sp + 112 ≤ a) → μ'.read a = μ.read a) ∧
      ∀ j : Fin 13, j.val ∉ [0, 2, 3, 5, 6, 8, 10, 11, 12] → ω'[j] = ω[j] := by
  have hAC := hHF C (Or.inr hFC)
  unfold Al at hAC
  have hbase : rdN μ 206520 8 = s.base := by have := hrep.base; unfold A0 at this; exact this
  have halloc : rdN μ 206840 4 = s.allocated := by have := hrep.alloc; unfold A0 at this; exact this
  have hHFl : ∀ a, H a ∨ F a → a + 16 < 2147483648 := fun a ha => by have := hHF a ha; unfold Al at this; omega
  -- the offsets
  obtain ⟨ω1, μ1, r1, a2, a5, a6, a12, s64, s32, s40, s88, fr1, ww1, g1⟩ := al_offs1 (p := p) (P := P) (R := R)
    x ω μ sp C s.base s.allocated h1 h10 h8 h120 hbase halloc hal (by omega) (by omega) hsp0 hsp hw
  obtain ⟨ω2, μ2, r2, b6, b8, b12, s96, fr2, ww2, g2⟩ := al_offs2 (p := p) (P := P) (R := R)
    x ω1 μ1 sp (C - s.base) s.base (by rw [fget g1 1 (by decide) (by decide)]; exact h1) a12 a6 a5
    (by omega) (by omega) hsp0 hsp ww1
  generalize hc : (C - s.base) / 32 = c at *
  obtain ⟨ω3, μ3, r3, c6, c3, c0, c11, c8, c5, s72, s104, s80, s56, fr3, ww3, g3⟩ := al_offs3 (p := p) (P := P)
    (R := R) x ω2 μ2 sp (s.base / 32) c req sz s.allocated C
    (by rw [fget g2 1 (by decide) (by decide), fget g1 1 (by decide) (by decide)]; exact h1) b6 b8 b12
    (by rw [fget g2 9 (by decide) (by decide), fget g1 9 (by decide) (by decide)]; exact h9)
    (by rw [fget g2 11 (by decide) (by decide), fget g1 11 (by decide) (by decide)]; exact h11)
    (by rw [fget g2 2 (by decide) (by decide)]; exact a2)
    (by rw [fget g2 10 (by decide) (by decide), fget g1 10 (by decide) (by decide)]; exact h10)
    (by omega) hrq (by omega) (by omega) (by omega) hal (by omega) hsp0 hsp ww2
  have r4 := al_nogrow (p := p) (P := P) (R := R) x ω3 μ3 s.allocated _
    (by rw [fget g3 2 (by decide) (by decide), fget g2 2 (by decide) (by decide)]; exact a2) c5 hend (by omega)
  -- the memory so far: only the frame changed
  have lo : ∀ a, a < 2147483648 → μ3.read a = μ.read a := fun a ha =>
    ((fr3 a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))).trans
      (fr2 a (by omega) (Or.inl (by omega)))).trans (fr1 a (by omega) (Or.inl (by omega)))
  have rep3 : RepAt μ3 s H F := hrep.congr_low lo hHFl
  have st : ∀ a, sp + 32 ≤ a → a + 8 ≤ sp + 152 → (a + 8 ≤ sp + 56 ∨ sp + 64 ≤ a) →
      (a + 8 ≤ sp + 72 ∨ sp + 88 ≤ a) → (a + 8 ≤ sp + 104 ∨ sp + 112 ≤ a) → (a + 8 ≤ sp + 96 ∨ sp + 104 ≤ a) →
      rdN μ3 a 8 = rdN μ1 a 8 := fun a h h' e1 e2 e3 e4 => rdN_frame fun j hj =>
    (fr3 _ (by omega) (by omega) (by omega) (by omega)).trans (fr2 _ (by omega) (by omega))
  have k64 : rdN μ3 (sp + 64) 8 = 196792 + 4 * bin := by
    rw [st _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    unfold rdN; rw [s64, Num.decodeLE_encodeLE, h5]; simp; omega
  have k40 : rdN μ3 (sp + 40) 8 = q := by
    rw [st _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    unfold rdN; rw [s40, Num.decodeLE_encodeLE, h6]; simp; omega
  have k32 : rdN μ3 (sp + 32) 8 = b := by
    rw [st _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    unfold rdN; rw [s32, Num.decodeLE_encodeLE, h2]; simp; omega
  have k88 : rdN μ3 (sp + 88) 8 = 204984 := by
    rw [st _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    unfold rdN; rw [s88, Num.decodeLE_encodeLE, h3]; rfl
  have k120 : rdN μ3 (sp + 120) 8 = 204984 := by
    rw [← h120]; exact rdN_frame fun j hj => ((fr3 _ (by omega) (by omega) (by omega) (by omega)).trans
      (fr2 _ (by omega) (by omega))).trans (fr1 _ (by omega) (by omega))
  obtain ⟨ω4, μ4, r5, rep4, p48, e8, ww4, fr4, g4⟩ := al_unreg (p := p) (P := P) (R := R) x ω3 μ3 s H F sp C c bin
    q b rep3 hcb hqb hq hb hFC hHC hHF hnx hb0 hbT hpv (by omega)
    (by rw [fget g3 1 (by decide) (by decide), fget g2 1 (by decide) (by decide), fget g1 1 (by decide) (by decide)]
        exact h1)
    (by rw [fget g3 10 (by decide) (by decide), fget g2 10 (by decide) (by decide),
          fget g1 10 (by decide) (by decide)]; exact h10)
    c3 k64 k40 k32 k88 k120 hsp0 hsp ww3
  have t4 : ∀ a, sp + 32 ≤ a → a + 8 ≤ sp + 152 → (a + 8 ≤ sp + 48 ∨ sp + 56 ≤ a) → rdN μ4 a 8 = rdN μ3 a 8 :=
    fun a h h' e => rdN_frame fun j hj => fr4 _ (by omega) (by omega) (by omega)
  refine ⟨ω4, μ4, ((((r1.trans r2).trans r3).trans r4).trans r5).mono (by omega), rep4,
    by rw [fget g4 1 (by decide) (by decide), fget g3 1 (by decide) (by decide), fget g2 1 (by decide) (by decide),
      fget g1 1 (by decide) (by decide)]; exact h1, e8,
    by rw [fget g4 0 (by decide) (by decide)]; exact c0, ?_, p48, ?_, ?_, ?_,
    by rw [t4 _ (by omega) (by omega) (by omega)]; exact k88, by rw [t4 _ (by omega) (by omega) (by omega)]; exact k120,
    ww4, fun a h1 h2 h3 => ?_, ?_⟩
  · rw [t4 _ (by omega) (by omega) (by omega)]
    rw [show rdN μ3 (sp + 96) 8 = rdN μ2 (sp + 96) 8 from rdN_frame fun j hj => fr3 _ (by omega) (by omega)
      (by omega) (by omega)]
    exact rd_enc s96 (by omega)
  · rw [t4 _ (by omega) (by omega) (by omega)]; exact rd_enc s80 (by omega)
  · rw [t4 _ (by omega) (by omega) (by omega)]; exact rd_enc s72 (by omega)
  · rw [t4 _ (by omega) (by omega) (by omega)]; exact rd_enc s104 (by omega)
  · rw [fr4 a h1 h2 (by omega), fr3 a h1 (by omega) (by omega) (by omega), fr2 a h1 (by omega),
      fr1 a h1 (by omega)]
  · exact frame_trans g4 (frame_trans (l := [0, 2, 3, 5, 6, 8, 10, 11, 12]) g3
      (frame_trans (l := [0, 2, 3, 5, 6, 8, 10, 11, 12]) g2 g1 (fun j hj => by simp at hj ⊢; omega)
        (fun j hj => by simp at hj ⊢; omega)) (fun j hj => hj) (fun j hj => by simp at hj ⊢; omega))
      (fun j hj => hj) (fun j hj => by simp at hj ⊢; omega)

/-- **`registerAlloc` against memory**: the chunk at `a` (one of H) records `pv` and `n` units used. -/
theorem registerAlloc_rep {μ μ' : Memory} {t : State} {H F : Nat → Prop} {a pv n : Nat}
    (h : RepAt μ t H F) (haH : H a) (w1 : rdN μ' a 4 = pv) (w2 : rdN μ' (a + 4) 4 = sizeWord n true)
    (wf : ∀ b, b < 2147483648 → (b < a ∨ a + 8 ≤ b) → μ'.read b = μ.read b)
    (ha : 206864 ≤ a)
    (hHa : ∀ b, H b ∨ F b → 206864 ≤ b ∧ b + 16 < 2147483648 ∧ (b = a ∨ b + 16 ≤ a ∨ a + 16 ≤ b)) :
    RepAt μ' (registerAlloc t a pv n) H F := by
  have pr : ∀ b, (registerAlloc t a pv n).hdr b =
      if b = a then { t.hdr a with prev := pv, size := sizeWord n true } else t.hdr b := by
    intro b; unfold registerAlloc; by_cases hb : b = a
    · subst hb; rw [setHdr_self, if_pos rfl]
    · rw [setHdr_other hb, if_neg hb]
  have hb2 := (hHa a (Or.inl haH)).2.1
  refine ⟨fun b hb => ?_, fun q hq => ?_, ?_, ?_, ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_,
    fun b hb => ?_⟩
  · rw [show (registerAlloc t a pv n).heads = t.heads from rfl, ← h.heads b hb]; unfold A0; unfold binCount at hb
    exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · rw [show (registerAlloc t a pv n).secondary = t.secondary from rfl, ← h.sec q hq]; unfold A0
    exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · rw [show (registerAlloc t a pv n).primary = t.primary from rfl, ← h.pri]; unfold A0
    exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · rw [show (registerAlloc t a pv n).base = t.base from rfl, ← h.base]; unfold A0
    exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · rw [show (registerAlloc t a pv n).allocated = t.allocated from rfl, ← h.alloc]; unfold A0
    exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · rw [pr]
    by_cases hba : b = a
    · subst hba; rw [if_pos rfl, w1]
    · rw [if_neg hba]
      obtain ⟨b1, b2, b3⟩ := hHa b (Or.inl hb)
      rw [← h.prev b hb]; exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · rw [pr]
    by_cases hba : b = a
    · subst hba; rw [if_pos rfl, w2]
    · rw [if_neg hba]
      obtain ⟨b1, b2, b3⟩ := hHa b (Or.inl hb)
      rw [← h.size b hb]; exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · obtain ⟨b1, b2, b3⟩ := hHa b (Or.inr hb)
    rw [pr]; split
    · rename_i hba; subst hba; rw [← h.next _ hb]; exact rdN_frame fun j hj => wf _ (by omega) (by omega)
    · rw [← h.next b hb]; exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · obtain ⟨b1, b2, b3⟩ := hHa b (Or.inr hb)
    rw [pr]; split
    · rename_i hba; subst hba; rw [← h.prevL _ hb]; exact rdN_frame fun j hj => wf _ (by omega) (by omega)
    · rw [← h.prevL b hb]; exact rdN_frame fun j hj => wf _ (by omega) (by omega)

/-- **41726 … 42054**: the allocated chunk C's header (`registerAlloc`), and the `rhs` units after it,
    at N, registered free (`register`), the memory holding the result; ω₃ what `register` returns. -/
theorem alloc_end1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (H F : Nat → Prop) (sp req C pv rhs : Nat) (hrep : RepAt μ s H F)
    (hHC : H C) (hHF : ∀ a, H a ∨ F a → Al s.base a) (hb0 : 206864 ≤ s.base)
    (hbT : s.base + 1073741824 < 2147483648) (hCa : (C - s.base) % 32 = 0) (hCb : s.base ≤ C)
    (hpv : pv < 2147483648) (hrq : req + 1 ≤ 33554432) (hrh : rhs ≤ 33554432)
    (hNe : C + 32 * (req + 1) + 32 * rhs ≤ s.base + 1073741824)
    (hNdis : rhs ≠ 0 → ∀ a, H a ∨ F a → a + 32 ≤ C + 32 * (req + 1) ∨ C + 32 * (req + 1) + 32 ≤ a)
    (hNold : rhs ≠ 0 → (registerAlloc s C pv (req + 1)).heads (binDown rhs) ≠ 0 →
      F ((registerAlloc s C pv (req + 1)).heads (binDown rhs)))
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat (32 * ((C - s.base) / 32)))
    (h0 : ω[0] = UInt64.ofNat 0) (h4 : ω[4] = UInt64.ofNat (req + 1)) (h9 : ω[9] = UInt64.ofNat req)
    (h7 : ω[7] = UInt64.ofNat 196792)
    (h96 : rdN μ (sp + 96) 8 = s.base) (h48 : rdN μ (sp + 48) 8 = pv) (A : Nat) (h80 : rdN μ (sp + 80) 8 = A)
    (h72 : rdN μ (sp + 72) 8 = (C - s.base) / 32 + 1) (h104 : rdN μ (sp + 104) 8 = rhs)
    (h88 : rdN μ (sp + 88) 8 = 204984) (h120 : rdN μ (sp + 120) 8 = 204984)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) (hw : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 41726 ω μ x 42054 ω' μ' x 80 ∧
      RepAt μ' (register (registerAlloc s C pv (req + 1)) (C + 32 * (req + 1)) (req + 1) rhs).1
        (fun a => H a ∨ (rhs ≠ 0 ∧ a = C + 32 * (req + 1))) (fun a => F a ∨ (rhs ≠ 0 ∧ a = C + 32 * (req + 1))) ∧
      ω'[3] = UInt64.ofNat (register (registerAlloc s C pv (req + 1)) (C + 32 * (req + 1)) (req + 1) rhs).2 ∧
      ω'[12] = UInt64.ofNat rhs ∧ ω'[8] = UInt64.ofNat (C + 32 * (req + 1)) ∧ ω'[2] = UInt64.ofNat (C + 32) ∧
      ω'[1] = UInt64.ofNat sp ∧ (∀ a, μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → 2147483648 ≤ a → μ'.read a = μ.read a) := by
  have hC : s.base + 32 * ((C - s.base) / 32) = C := by omega
  have hHFl : ∀ a, H a ∨ F a → 206864 ≤ a ∧ a + 16 < 2147483648 := fun a ha => by
    have := hHF a ha; unfold Al at this; omega
  have hAC := hHF C (Or.inl hHC)
  unfold Al at hAC
  obtain ⟨ω1, r1, a2, a0, g1⟩ := aw_left0 (p := p) (P := P) (R := R) x ω μ sp s.base ((C - s.base) / 32) pv h1 h8
    h0 h96 h48 (by omega) hsp (fun a => Memory.readable_of_writable (hw a))
  rw [hC] at a2
  obtain ⟨ω2, μ2, r2, m1, m2, b2, b8, b12, b3, fr2, ww2, g2⟩ := aw_hdr (p := p) (P := P) (R := R) x ω1 μ sp C pv req
    A ((C - s.base) / 32 + 1) rhs (by rw [fget g1 1 (by decide) (by decide)]; exact h1) a2 a0
    (by rw [fget g1 4 (by decide) (by decide)]; exact h4) (by rw [fget g1 9 (by decide) (by decide)]; exact h9)
    h80 h72 h104 (by omega) (by omega) (by omega) hsp0 hsp hw
  have rep2 : RepAt μ2 (registerAlloc s C pv (req + 1)) H F :=
    registerAlloc_rep hrep hHC m1 m2 (fun b h1 h2 => fr2 b (by omega) h2) (by omega) (fun b hb => by
      have := hHF b hb; unfold Al at this; omega)
  have k1 : ω2[1] = UInt64.ofNat sp := by
    rw [fget g2 1 (by decide) (by decide), fget g1 1 (by decide) (by decide)]; exact h1
  have tr2 : ∀ a, a < 4294967296 → 2147483648 ≤ a → μ2.read a = μ.read a := fun a h h' => fr2 a h (by omega)
  have st2 : ∀ a, sp + 32 ≤ a → a + 8 ≤ sp + 152 → rdN μ2 a 8 = rdN μ a 8 := fun a h h' =>
    rdN_frame fun j hj => tr2 _ (by omega) (by omega)
  by_cases hr0 : rhs = 0
  · subst hr0
    have r3 := ar_zero (p := p) (P := P) (R := R) x ω2 μ2 b12
    have e : register (registerAlloc s C pv (req + 1)) (C + 32 * (req + 1)) (req + 1) 0 =
        (registerAlloc s C pv (req + 1), req + 1) := by unfold register; simp
    have eH : (fun a => H a ∨ ((0 : Nat) ≠ 0 ∧ a = C + 32 * (req + 1))) = H := funext fun a => propext (by simp)
    have eF : (fun a => F a ∨ ((0 : Nat) ≠ 0 ∧ a = C + 32 * (req + 1))) = F := funext fun a => propext (by simp)
    rw [e, eH, eF]
    exact ⟨ω2, μ2, ((r1.trans r2).trans r3).mono (by omega), rep2, b3, b12, b8, b2, k1, ww2, tr2⟩
  · generalize hN : C + 32 * (req + 1) = N at *
    generalize hs3 : registerAlloc s C pv (req + 1) = s3 at *
    have hBin : binDown rhs < 2432 := toBin_lt false (Nat.min_le_right _ _)
    -- the bin of rhs, plus one, in ω₆
    obtain ⟨ω3, r3, c6, c12, g3⟩ : ∃ ω3, FreeStepsH p R 41910 ω2 μ2 x 41958 ω3 μ2 x 16 ∧
        ω3[6] = UInt64.ofNat (binDown rhs + 1) ∧ ω3[12] = UInt64.ofNat rhs ∧
        ∀ j : Fin 13, j.val ∉ [6, 9, 11, 12] → ω3[j] = ω2[j] := by
      by_cases hsm : rhs ≤ 127
      · obtain ⟨ω3, r, e6, g⟩ := ar_bin_small (p := p) (P := P) (R := R) x ω2 μ2 rhs b12 (by omega) hsm
        exact ⟨ω3, r.mono (by omega), e6, by rw [fget g 12 (by decide) (by decide)]; exact b12,
          fun j hj => g j (by simp at hj ⊢; omega)⟩
      · exact ar_bin_big (p := p) (P := P) (R := R) x ω2 μ2 sp rhs k1 b12 (by rw [st2 _ (by omega) (by omega)]; exact h104)
          (by omega) (by omega) hsp (fun a => Memory.readable_of_writable (ww2 a))
    have hold := rep2.heads (binDown rhs) (by unfold binCount; omega)
    unfold A0 at hold
    generalize hO : s3.heads (binDown rhs) = old at hold hNold
    have hOF := hNold hr0
    have hOA : old ≠ 0 → Al s.base old := fun h => hHF _ (Or.inr (hOF h))
    have hNd := hNdis hr0
    obtain ⟨ω4, μ4, r4, w1, w2, w3, w4, w5, w6, w7, w8, wf, ww4, d3, -, d12, g4⟩ := ar_write (p := p) (P := P) (R := R)
      x ω3 μ2 sp (binDown rhs) N (req + 1) rhs old
      (by rw [fget g3 1 (by decide) (by decide)]; exact k1) c6 (by rw [fget g3 8 (by decide) (by decide)]; exact b8)
      (by rw [fget g3 3 (by decide) (by decide)]; exact b3) c12
      (by rw [fget g3 7 (by decide) (by decide), fget g2 7 (by decide) (by decide), fget g1 7 (by decide) (by decide)]
          exact h7)
      (by rw [st2 _ (by omega) (by omega)]; exact h88) (by rw [st2 _ (by omega) (by omega)]; exact h120)
      (by rw [st2 _ (by omega) (by omega)]; exact h104) hBin (by omega) (by omega) (by omega) (by omega)
      (by rw [show 196792 + binDown rhs * 4 = 196792 + 4 * binDown rhs by omega]; exact hold)
      (by by_cases h0 : old = 0
          · omega
          · have := hOA h0; unfold Al at this; omega)
      (fun h0 => by
        have := hOA h0; have h2 := hNd old (Or.inr (hOF h0)); unfold Al at this; omega)
      hsp0 hsp ww2
    have hNa : 206864 ≤ N := by omega
    have rep4 := register_rep (M := N) (pv := req + 1) (size := rhs) rep2 hr0 (by unfold binCount; omega)
      (by rw [hO]; intro e; subst e; have := hNd _ (Or.inr (hOF (by omega))); omega)
      (by rw [show binDown rhs * 4 + 196792 = 196792 + binDown rhs * 4 by omega]; exact w1) w2 w3
      (by rw [hO]; exact w4) w5 (by rw [hO]; exact w6)
      (by rw [show 204984 + binDown rhs / 64 * 8 + 1544 = binDown rhs / 64 * 8 + 204984 + 1544 by omega]; exact w7) w8
      (fun a h1 h2 h3 h4 h5 h6 => wf a h1 (by omega) h3 (by rw [hO] at h4; exact h4) (by omega) h6)
      hNa (by omega) (by rw [hO]; intro h0; have := hOA h0; unfold Al at this; omega)
      (fun a ha => by
        rw [hO]
        have hAa := hHF a ha; have hda := hNd a ha
        unfold Al at hAa
        refine ⟨by omega, by omega, by omega, ?_⟩
        by_cases h0 : old = 0
        · exact Or.inl h0
        · have := hOA h0; unfold Al at this; omega)
    have eH : (fun a => H a ∨ (rhs ≠ 0 ∧ a = N)) = (fun a => H a ∨ a = N) :=
      funext fun a => propext (by simp [hr0])
    have eF : (fun a => F a ∨ (rhs ≠ 0 ∧ a = N)) = (fun a => F a ∨ a = N) :=
      funext fun a => propext (by simp [hr0])
    have e2 : (register s3 N (req + 1) rhs).2 = rhs := by unfold register; simp [hr0]
    rw [eH, eF, e2]
    refine ⟨ω4, μ4, (((r1.trans r2).trans r3).trans r4).mono (by omega), rep4, d3, d12,
      by rw [fget g4 8 (by decide) (by decide), fget g3 8 (by decide) (by decide)]; exact b8,
      by rw [fget g4 2 (by decide) (by decide), fget g3 2 (by decide) (by decide)]; exact b2,
      by rw [fget g4 1 (by decide) (by decide), fget g3 1 (by decide) (by decide)]; exact k1, ww4,
      fun a h h' => (wf a h (by omega) (by omega) (by
        by_cases h0 : old = 0
        · exact Or.inl h0
        · have := hOA h0; unfold Al at this; right; right; omega) (by omega) (by omega)).trans (tr2 a h h')⟩

/-- A 64-bit word's low half. -/
theorem rdN_lo (μ : Memory) (a : Nat) : rdN μ a 4 = rdN μ a 8 % 4294967296 := by
  simp only [rdN, Memory.readN, List.range, List.range.loop, List.map, Num.decodeLE, Nat.add_zero]
  have := (μ.read a).toNat_lt; have := (μ.read (a + 1)).toNat_lt; have := (μ.read (a + 2)).toNat_lt
  have := (μ.read (a + 3)).toNat_lt
  omega

/-- **42054 … 41423**, not zeroing: the final chunk F = N + 32·rhs records `pv` if below the heap's
    end — the memory holding the model's last step — and the data address D returned in ω₇. -/
theorem alloc_end2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (t : State) (H F : Nat → Prop) (sp N rhs pv D : Nat) (hrep : RepAt μ t H F)
    (hHF : ∀ a, H a ∨ F a → Al t.base a) (hb0 : 206864 ≤ t.base) (hbT : t.base + 1073741824 < 2147483648)
    (hFin : N + 32 * rhs < t.base + 1073741824 → H (N + 32 * rhs))
    (hNe : N + 32 * rhs ≤ t.base + 1073741824) (hNa : 206864 ≤ N)
    (h1 : ω[1] = UInt64.ofNat sp) (h12 : ω[12] = UInt64.ofNat rhs) (h8 : ω[8] = UInt64.ofNat N)
    (h3 : ω[3] = UInt64.ofNat pv) (h2 : ω[2] = UInt64.ofNat D)
    (h120 : rdN μ (sp + 120) 8 = 204984) (h112 : rdN μ (sp + 112) 8 = 0)
    (hpv : pv < 4294967296) (hD : D < 4294967296)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) (hw : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 42054 ω μ x 41423 ω' μ' x 30 ∧
      RepAt μ' (if N + 32 * rhs < t.base + 1073741824 then
        setHdr t (N + 32 * rhs) (fun h => { h with prev := pv }) else t) H F ∧
      ω'[7] = UInt64.ofNat D ∧ ω'[0] = UInt64.ofNat (rdN μ (sp + 144) 8) ∧
      ω'[5] = UInt64.ofNat (rdN μ (sp + 136) 8) ∧ ω'[6] = UInt64.ofNat (rdN μ (sp + 128) 8) ∧
      ω'[1] = UInt64.ofNat (sp + 152) ∧ (∀ a, μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → 2147483648 ≤ a → μ'.read a = μ.read a) ∧
      ∀ j : Fin 13, j.val ∉ [0, 1, 5, 6, 7, 8, 9, 10, 11] → ω'[j] = ω[j] := by
  have hb4 : rdN μ 206520 4 = t.base := by
    rw [rdN_lo]; have := hrep.base; unfold A0 at this; rw [this]; omega
  have hr : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hw a)
  by_cases hin : N + 32 * rhs < t.base + 1073741824
  · rw [if_pos hin]
    have hHF' := hFin hin
    have hAF := hHF _ (Or.inl hHF')
    unfold Al at hAF
    obtain ⟨ω1, μ1, r1, w1, e11, fr1, ww1, g1⟩ := an_tail_in (p := p) (P := P) (R := R) x ω μ sp N rhs pv t.base D
      h1 h12 h8 h3 h2 h120 h112 hb4 hbT hin hpv hD hsp0 hsp hw
    have rep1 : RepAt μ1 (setHdr t (N + 32 * rhs) (fun h => { h with prev := pv })) H F :=
      setPrev_rep hrep hHF' w1 fr1 (by omega) (fun b hb => by
        have := hHF b hb; unfold Al at this; omega)
    have tr : ∀ a, sp + 128 ≤ a → a + 8 ≤ sp + 152 → rdN μ1 a 8 = rdN μ a 8 := fun a h h' =>
      rdN_frame fun j hj => fr1 _ (by omega) (by omega)
    obtain ⟨ω2, r2, d7, d0, d5, d6, d1, g2⟩ := an_ret (p := p) (P := P) (R := R) x ω1 μ1 sp
      (by rw [fget g1 1 (by decide) (by decide)]; exact h1) hsp (fun a => Memory.readable_of_writable (ww1 a))
    refine ⟨ω2, μ1, (r1.trans r2).mono (by omega), rep1, by rw [d7, e11], by rw [d0, tr _ (by omega) (by omega)],
      by rw [d5, tr _ (by omega) (by omega)], by rw [d6, tr _ (by omega) (by omega)], d1, ww1,
      fun a h h' => fr1 a h (by omega),
      frame_trans g2 g1 (fun j hj => by simp at hj ⊢; omega) (fun j hj => by simp at hj ⊢; omega)⟩
  · rw [if_neg hin]
    obtain ⟨ω1, r1, e11, g1⟩ := an_tail_end (p := p) (P := P) (R := R) x ω μ sp N rhs t.base D
      h1 h12 h8 h2 h120 h112 hb4 hbT (by omega) (by omega) hD hsp hr
    obtain ⟨ω2, r2, d7, d0, d5, d6, d1, g2⟩ := an_ret (p := p) (P := P) (R := R) x ω1 μ sp
      (by rw [fget g1 1 (by decide) (by decide)]; exact h1) hsp hr
    exact ⟨ω2, μ, (r1.trans r2).mono (by omega), hrep, by rw [d7, e11], d0, d5, d6, d1, hw, fun _ _ _ => rfl,
      frame_trans g2 g1 (fun j hj => by simp at hj ⊢; omega) (fun j hj => by simp at hj ⊢; omega)⟩

/-- `allocPost`, for the bin's head C at a 32-aligned offset, as the binary computes it. -/
theorem allocPost_eq {s : State} {bin r S T C : Nat} (hcb : s.heads bin = C) (hCb : s.base ≤ C)
    (hCa : (C - s.base) % 32 = 0) :
    allocPost s bin r S T =
      if C + 32 * (r + 1) + 32 * (S - r - 1) < T then
        setHdr (register (registerAlloc (unregister s C bin) C (s.hdr C).prev (r + 1)) (C + 32 * (r + 1)) (r + 1)
          (S - r - 1)).1 (C + 32 * (r + 1) + 32 * (S - r - 1))
          (fun h => { h with prev := (register (registerAlloc (unregister s C bin) C (s.hdr C).prev (r + 1))
            (C + 32 * (r + 1)) (r + 1) (S - r - 1)).2 })
      else (register (registerAlloc (unregister s C bin) C (s.hdr C).prev (r + 1)) (C + 32 * (r + 1)) (r + 1)
          (S - r - 1)).1 := by
  have hA : s.base + 32 * ((C - s.base) / 32) = C := by omega
  have hu : unregister s C bin = unregisterFirst s C bin := by unfold unregister; rw [if_pos hcb]
  unfold allocPost
  simp only [hcb, hA, hu, show 1 + r = r + 1 from Nat.add_comm _ _]

/-- **The binary's `alloc_impl` refines the model's allocation step** (alignment one unit, the heap in
    use, no growth, not zeroing): from the entry (41177) to its return (41423), memory holding s at
    the header addresses H/F comes to hold `allocPost s bin req S top`, and C + 32 is returned —
    given the facts about the heap the stages need, which the invariant provides. -/
theorem alloc_impl {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (H F : Nat → Prop) (sp req bin C : Nat) (hrep : RepAt μ s H F)
    (hbits : BitsOk s.secondary s.primary s.heads)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat 1)
    (h9 : ω[9] = UInt64.ofNat req) (h10 : ω[10] = UInt64.ofNat 0)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648)
    (hm : req + 1 ≤ 33554432)
    (hbin : (findFirst s (binUp (req + 1))).or (findFirst s (binDown (req + 1))) = some bin) (hbn : bin < 2432)
    (hcb : s.heads bin = C) (hFC : F C) (hHC : H C) (hHF : ∀ a, H a ∨ F a → Al s.base a)
    (hnx : (s.hdr C).next ≠ 0 → F (s.hdr C).next) (hpv : (s.hdr C).prev < 2147483648)
    (hS : req + 1 ≤ wordSize (s.hdr C).size) (hCend : C + 32 * wordSize (s.hdr C).size ≤ s.base + 1073741824)
    (hal : s.allocated < 2147483648)
    (hend : (C - s.base) / 32 + 1 + req +
      (if wordSize (s.hdr C).size - req - 1 = 0 then 0 else 1) ≤ s.allocated)
    (hNdis : wordSize (s.hdr C).size - req - 1 ≠ 0 → ∀ a, H a ∨ F a →
      a + 32 ≤ C + 32 * (req + 1) ∨ C + 32 * (req + 1) + 32 ≤ a)
    (hNold : wordSize (s.hdr C).size - req - 1 ≠ 0 →
      (registerAlloc (unregister s C bin) C (s.hdr C).prev (req + 1)).heads (binDown (wordSize (s.hdr C).size - req - 1))
        ≠ 0 →
      F ((registerAlloc (unregister s C bin) C (s.hdr C).prev (req + 1)).heads
        (binDown (wordSize (s.hdr C).size - req - 1))))
    (hFin : C + 32 * wordSize (s.hdr C).size < s.base + 1073741824 → H (C + 32 * wordSize (s.hdr C).size))
    (hwr : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 41177 ω μ x 41423 ω' μ' x 400 ∧
      RepAt μ' (allocPost s bin req (wordSize (s.hdr C).size) (s.base + 1073741824))
        (fun a => H a ∨ (wordSize (s.hdr C).size - req - 1 ≠ 0 ∧ a = C + 32 * (req + 1)))
        (fun a => F a ∨ (wordSize (s.hdr C).size - req - 1 ≠ 0 ∧ a = C + 32 * (req + 1))) ∧
      ω'[7] = UInt64.ofNat (C + 32) ∧ ω'[0] = ω[0] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[1] = ω[1] ∧
      (∀ a, μ'.writable a = true) ∧ (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) := by
  have hAC := hHF C (Or.inr hFC)
  unfold Al at hAC
  have hHFl : ∀ a, H a ∨ F a → a + 16 < 2147483648 := fun a ha => by have := hHF a ha; unfold Al at this; omega
  generalize hSd : wordSize (s.hdr C).size = S at *
  have hsz := hrep.size C hHC
  have hwS : (s.hdr C).size / 2 = S := by rw [← hSd]; rfl
  have hsec : ∀ q, q < 38 → rdN μ (q * 8 + 204984 + 1544) 8 = s.secondary q := fun q hq => by
    have := hrep.sec q hq; unfold A0 at this; rw [show q * 8 + 204984 + 1544 = 196792 + 9736 + 8 * q by omega]
    exact this
  have hheads : rdN μ (196792 + 4 * bin) 4 = C := by
    have := hrep.heads bin hbn; unfold A0 at this; rw [this, hcb]
  have hbase : rdN μ 206520 8 = s.base := by have := hrep.base; unfold A0 at this; exact this
  have hpri : rdN μ 206832 8 = s.primary := by have := hrep.pri; unfold A0 at this; exact this
  obtain ⟨ω1, μ1, r1, q, b, hqb, hq, hb, a1, a10, a11, a5, a2, a6, a3, a8, a9, a4, a12, a7, st0, st5, st6, st10,
      st32, sf1, ww1⟩ := alloc_entry (p := p) (P := P) (R := R) x ω μ s sp req bin C (s.hdr C).size hbits h1 h7 h8 h9
    hsp hsp1 hbase (by omega) hpri hsec hm hbin hheads hsz (by omega) (by omega) hwr
  rw [hwS] at a11
  have rep1 : RepAt μ1 s H F := hrep.congr_low (fun a ha => sf1 a (by omega) (Or.inl (by omega))) hHFl
  obtain ⟨ω2, μ2, r2, rep2, b1, b8, b0, m96, m48, m80, m72, m104, m88, m120, ww2, fr2, g2⟩ := alloc_mid (p := p)
    (P := P) (R := R) x ω1 μ1 s H F (sp - 152) req bin q b C S rep1 hcb hqb hq hb hFC hHC hHF hnx hb0 hbT hpv hS
    (by omega) hCend hal hend a1 a10 a11 a5 a2 a6 a3 a8 a9 (by rw [show sp - 152 + 120 = sp - 32 by omega]; exact st32)
    (by omega) (by omega) ww1
  generalize hpvd : (s.hdr C).prev = pv at *
  generalize ht2 : unregister s C bin = t2 at *
  have e2b : t2.base = s.base := by rw [← ht2, unregister_base]
  have e2a : t2.allocated = s.allocated := by rw [← ht2, unregister_allocated]
  have hCa : (C - s.base) % 32 = 0 := hAC.2.1
  obtain ⟨ω3, μ3, r3, rep3, c3, c12, c8, c2, c1, ww3, fr3⟩ := alloc_end1 (p := p) (P := P) (R := R) x ω2 μ2 t2 H F
    (sp - 152) req C pv (S - req - 1) rep2 hHC (by rw [e2b]; exact hHF) (by rw [e2b]; exact hb0)
    (by rw [e2b]; exact hbT) (by rw [e2b]; exact hCa) (by rw [e2b]; omega) hpv (by omega) (by omega)
    (by rw [e2b]; omega) hNdis hNold b1 (by rw [e2b]; exact b8) b0
    (by rw [fget g2 4 (by decide) (by decide)]; exact a4) (by rw [fget g2 9 (by decide) (by decide)]; exact a9)
    (by rw [fget g2 7 (by decide) (by decide)]; exact a7) (by rw [e2b]; exact m96) m48 _ m80
    (by rw [e2b]; exact m72) m104 m88 m120 (by omega) (by omega) ww2
  generalize ht3 : register (registerAlloc t2 C pv (req + 1)) (C + 32 * (req + 1)) (req + 1) (S - req - 1) = rr at *
  have e3b : rr.1.base = s.base := by rw [← ht3, register_base, registerAlloc_base, e2b]
  have k112 : rdN μ3 (sp - 152 + 112) 8 = 0 := by
    rw [show rdN μ3 (sp - 152 + 112) 8 = rdN μ1 (sp - 152 + 112) 8 from rdN_frame fun j hj =>
      (fr3 _ (by omega) (by omega)).trans (fr2 _ (by omega) (by omega) (by omega)),
      show sp - 152 + 112 = sp - 40 by omega]
    unfold rdN; rw [st10, h10]; rfl
  have k120 : rdN μ3 (sp - 152 + 120) 8 = 204984 := by
    rw [← m120]; exact rdN_frame fun j hj => fr3 _ (by omega) (by omega)
  have hS32 : C + 32 * (req + 1) + 32 * (S - req - 1) = C + 32 * S := by omega
  obtain ⟨ω4, μ4, r4, rep4, d7, d0, d5, d6, d1, ww4, fr4, -⟩ := alloc_end2 (p := p) (P := P) (R := R) x ω3 μ3 rr.1
    (fun a => H a ∨ (S - req - 1 ≠ 0 ∧ a = C + 32 * (req + 1)))
    (fun a => F a ∨ (S - req - 1 ≠ 0 ∧ a = C + 32 * (req + 1))) (sp - 152) (C + 32 * (req + 1)) (S - req - 1) rr.2
    (C + 32) rep3
    (fun a ha => by
      rw [e3b]
      rcases ha with (h | ⟨h0, rfl⟩) | (h | ⟨h0, rfl⟩)
      · exact hHF a (Or.inl h)
      · unfold Al; omega
      · exact hHF a (Or.inr h)
      · unfold Al; omega)
    (by rw [e3b]; exact hb0) (by rw [e3b]; exact hbT)
    (fun h => Or.inl (by rw [hS32]; exact hFin (by rw [e3b, hS32] at h; exact h)))
    (by rw [e3b, hS32]; exact hCend) (by omega) c1 c12 c8 c3 c2 k120 k112
    (by rw [← ht3]; unfold register; split <;> simp <;> omega) (by omega) (by omega) (by omega) ww3
  have tr : ∀ a, sp - 152 + 128 ≤ a → a + 8 ≤ sp → rdN μ3 a 8 = rdN μ1 a 8 := fun a h h' =>
    rdN_frame fun j hj => (fr3 _ (by omega) (by omega)).trans (fr2 _ (by omega) (by omega) (by omega))
  refine ⟨ω4, μ4, (((r1.trans r2).trans r3).trans r4).mono (by omega), ?_, d7, ?_, ?_, ?_, ?_, ww4,
    fun a h h' => ((fr4 a h (by omega)).trans ((fr3 a h (by omega)).trans (fr2 a h (by omega) (by omega)))).trans
      (sf1 a h (Or.inr h'))⟩
  · rw [allocPost_eq hcb (by omega) hCa, hpvd, ht2, ht3]
    rw [e3b] at rep4
    exact rep4
  · rw [d0, tr _ (by omega) (by omega), show sp - 152 + 144 = sp - 8 by omega]
    unfold rdN; rw [st0, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]
  · rw [d5, tr _ (by omega) (by omega), show sp - 152 + 136 = sp - 16 by omega]
    unfold rdN; rw [st5, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]
  · rw [d6, tr _ (by omega) (by omega), show sp - 152 + 128 = sp - 24 by omega]
    unfold rdN; rw [st6, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]
  · rw [d1, h1]; congr 1; omega

end Services.Bootstrap.Alloc
