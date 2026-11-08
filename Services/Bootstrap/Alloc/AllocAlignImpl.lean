import Services.Bootstrap.Alloc.AllocAlignSteps
import Services.Picoalloc.AllocAlign

/-!
# The binary's `alloc_impl` with any alignment, composed

The stages of `alloc_impl` with an alignment of `2^k` units (the heap in use, no growth, not
zeroing): the entry and the bin search for `req + 2^k` units (41177 … 41425), the chunk's offsets
and its unlink (41425 … 41726), the left remainder registered free if any (41726 … 41870), the
allocated chunk's header and the right remainder (41870 … 42054), and the final chunk's `prev`
(42054 … 41423). `alloc_impl_align` ends with memory holding the model's `allocPostL`.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **41221 … 41297**, alignment `al` units: ω₀ and ω₂ the bins of `req + al` rounded down and up. -/
theorem al_binsA {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (req al : Nat) (h9 : ω[9] = UInt64.ofNat req) (h8 : ω[8] = UInt64.ofNat al)
    (h12 : ω[12] = UInt64.ofNat 1) (hal : 1 ≤ al) (hm : req + al ≤ 33554432) :
    ∃ ω', FreeStepsH p R 41221 ω μ x 41297 ω' μ x 30 ∧
      ω'[0] = UInt64.ofNat (binDown (req + al)) ∧ ω'[2] = UInt64.ofNat (binUp (req + al)) ∧
      ω'[4] = UInt64.ofNat (req + 1) ∧ ω'[12] = UInt64.ofNat (req + al) ∧
      ∀ j : Fin 13, j.val ∉ [0, 2, 3, 4, 5, 6, 11, 12] → ω'[j] = ω[j] := by
  by_cases hs : req + al < 128
  · obtain ⟨ω', r, a0, a2, a12, a4, g⟩ := al_bin_small (p := p) (P := P) (R := R) x ω μ req al h9 h8 h12 hal hs
    refine ⟨ω', r.mono (by omega), ?_, ?_, a4, a12, fun j hj => g j (by simp at hj ⊢; omega)⟩
    · rw [a0, binDown_small (by omega) (by omega)]
    · rw [a2, binUp_small (by omega) (by omega)]
  · exact al_bin_big (p := p) (P := P) (R := R) x ω μ req al h9 h8 h12 hal (by omega) (by omega) hm

/-- **41177 … 41425**, alignment `2^k` units, the heap in use: the frame, the bins of `req + 2^k`,
    the search to `bin`, and its first chunk C, large enough. -/
theorem alloc_entry_align {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (sp req k bin C w : Nat) (hbits : BitsOk s.secondary s.primary s.heads)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat (2 ^ k))
    (hk : k < 32)
    (h9 : ω[9] = UInt64.ofNat req) (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb : rdN μ 206520 8 = s.base) (hb0 : s.base ≠ 0)
    (hp : rdN μ 206832 8 = s.primary) (hs : ∀ q, q < 38 → rdN μ (q * 8 + 204984 + 1544) 8 = s.secondary q)
    (hm : req + 2 ^ k ≤ 33554432)
    (hbin : (findFirst s (binUp (req + 2 ^ k))).or (findFirst s (binDown (req + 2 ^ k))) = some bin)
    (hC : rdN μ (196792 + 4 * bin) 4 = C) (hw : rdN μ (C + 4) 4 = w) (hC1 : C + 8 < 2147483648)
    (hS : req + 2 ^ k ≤ w / 2) {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hSTk : S0 + 152 ≤ sp ∧ sp ≤ S1)
    (hCT : 196608 ≤ C ∧ C + 16 ≤ HT) (hwr : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 41177 ω μ x 41425 ω' μ' x 120 ∧ ∃ q b, q * 64 + b = bin ∧ q < 38 ∧ b < 64 ∧
      ω'[1] = UInt64.ofNat (sp - 152) ∧ ω'[10] = UInt64.ofNat C ∧ ω'[11] = UInt64.ofNat (w / 2) ∧
      ω'[5] = UInt64.ofNat (196792 + 4 * bin) ∧ ω'[2] = UInt64.ofNat b ∧ ω'[6] = UInt64.ofNat q ∧
      ω'[3] = UInt64.ofNat 204984 ∧ ω'[8] = UInt64.ofNat (2 ^ k) ∧ ω'[9] = UInt64.ofNat req ∧
      ω'[4] = UInt64.ofNat (req + 1) ∧ ω'[12] = UInt64.ofNat (req + 2 ^ k) ∧ ω'[7] = UInt64.ofNat 196792 ∧
      μ'.readN (sp - 8) 8 = Num.encodeLE 8 ω[0].toNat ∧ μ'.readN (sp - 16) 8 = Num.encodeLE 8 ω[5].toNat ∧
      μ'.readN (sp - 24) 8 = Num.encodeLE 8 ω[6].toNat ∧ μ'.readN (sp - 40) 8 = Num.encodeLE 8 ω[10].toNat ∧
      rdN μ' (sp - 32) 8 = 204984 ∧
      (∀ a, a < 4294967296 → (a < sp - 152 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) := by
  have hb64 : s.base < 18446744073709551616 := by rw [← hb]; exact rdN_lt64 μ _
  have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  obtain ⟨ω1, μ1, r1, a1, a11, a12, st0, st5, st6, st10, st32, sf1, ww1, g1⟩ :=
    al_pro (p := p) (P := P) (R := R) x ω μ sp k s.base h1 h7 h8 hk hsp hsp1 hb (by omega) hSTk hwr
  have hr1 := (hwr.of_eq ww1).rd
  have tr : ∀ a n, a + n ≤ 2147483648 → rdN μ1 a n = rdN μ a n := fun a n h =>
    rdN_frame fun j hj => sf1 _ (by omega) (Or.inl (by omega))
  have r2 := al_br_used (p := p) (P := P) (R := R) x ω1 μ1 s.base a11 hb0 hb64
  obtain ⟨ω2, r3, b0, b2, b4, b12, g3⟩ := al_binsA (p := p) (P := P) (R := R) x ω1 μ1 req (2 ^ k)
    (by rw [fget g1 9 (by decide) (by decide)]; exact h9) (by rw [fget g1 8 (by decide) (by decide)]; exact h8) a12
    hk1 hm
  have hbU : binUp (req + 2 ^ k) < 2432 := toBin_lt true (Nat.min_le_right _ _)
  have hbD : binDown (req + 2 ^ k) < 2432 := toBin_lt false (Nat.min_le_right _ _)
  have hp1 : rdN μ1 206832 8 = s.primary := by rw [tr _ _ (by omega)]; exact hp
  have hs1 : ∀ q, q < 38 → rdN μ1 (q * 8 + 204984 + 1544) 8 = s.secondary q := fun q hq => by
    rw [tr _ _ (by omega)]; exact hs q hq
  have hf1 : rdN μ1 (sp - 152 + 120) 8 = 204984 := by rw [show sp - 152 + 120 = sp - 32 by omega]; exact st32
  have c7 : ω2[7] = UInt64.ofNat 196792 := by
    rw [fget g3 7 (by decide) (by decide), fget g1 7 (by decide) (by decide)]; exact h7
  have c1 : ω2[1] = UInt64.ofNat (sp - 152) := by rw [fget g3 1 (by decide) (by decide)]; exact a1
  have fu := find_up (p := p) (P := P) (R := R) x ω2 μ1 s (sp - 152) _ hbits c1 b2 c7 (by omega) hf1 hp1 hs1 hbU hHTs ⟨by omega, by omega⟩ hr1
  obtain ⟨ω4, q, b, r45, hqb, hq, hb', d6, d2, d3, fr4⟩ : ∃ ω4 q b, FreeStepsH p R 41297 ω2 μ1 x 41378 ω4 μ1 x 60 ∧
      q * 64 + b = bin ∧ q < 38 ∧ b < 64 ∧ ω4[6] = UInt64.ofNat q ∧ ω4[2] = UInt64.ofNat b ∧
      ω4[3] = UInt64.ofNat 204984 ∧ ∀ j : Fin 13, j.val ∉ [2, 3, 5, 6, 10, 11] → ω4[j] = ω2[j] := by
    cases hu : findFirst s (binUp (req + 2 ^ k)) with
    | some bin' =>
      have : bin' = bin := by rw [hu] at hbin; exact Option.some.inj hbin
      subst this
      obtain ⟨ω4, q, b, r, e1, e2, e3, e4, e5, e6, -, e8⟩ := fu.1 _ hu
      exact ⟨ω4, q, b, r.mono (by omega), e1, e2, e3, e4, e5, e6, e8⟩
    | none =>
      rw [hu, Option.none_or] at hbin
      obtain ⟨ω3, r, e5, e3, e8⟩ := fu.2 hu
      obtain ⟨ω4, q, b, r', f1, f2, f3, f4, f5, f6⟩ := (find_down (p := p) (P := P) (R := R) x ω3 μ1 s _ hbits
        (by rw [fget e8 0 (by decide) (by decide)]; exact b0) e5 e3 hs1 hbD hHTs hr1).1 _ hbin
      exact ⟨ω4, q, b, (r.trans r').mono (by omega), f1, f2, f3, f4, f5,
        by rw [fget f6 3 (by decide) (by decide)]; exact e3,
        frame_trans f6 e8 (fun j hj => by simp at hj ⊢; omega) (fun j hj => by simp at hj ⊢; omega)⟩
  have k7 : ω4[7] = UInt64.ofNat 196792 := by rw [fget fr4 7 (by decide) (by decide)]; exact c7
  have k12 : ω4[12] = UInt64.ofNat (req + 2 ^ k) := by rw [fget fr4 12 (by decide) (by decide)]; exact b12
  have hC' : rdN μ1 (196792 + 4 * (q * 64 + b)) 4 = C := by rw [hqb, tr _ _ (by omega)]; exact hC
  have hw' : rdN μ1 (C + 4) 4 = w := by rw [tr _ _ (by omega)]; exact hw
  obtain ⟨ω5, r5, e10, e11, e5, g5⟩ := al_pick (p := p) (P := P) (R := R) x ω4 μ1 q b C w (req + 2 ^ k)
    d6 d2 k7 k12 hq hb' hC' hw' (by omega) (by omega) hHTs hCT hr1
  have hw64 : w / 2 < 18446744073709551616 := by
    have := rdN_lt μ (C + 4) 4; rw [hw] at this; omega
  have r6 := al_size_ok (p := p) (P := P) (R := R) x ω5 μ1 (w / 2) (req + 2 ^ k) e11
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

/-- **41425 … 41726**, alignment `2^k` units, no growth: the chunk's offsets, the left remainder
    `lhs` (the model's `leftOf`), then the chunk's unlink — the memory holds `unregister s C bin`;
    what the later stages read is left in registers and the frame. -/
theorem alloc_mid_align {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (H F : Nat → Prop) (sp req k bin q b C sz lhs : Nat) (hrep : RepAt μ s H F)
    (hcb : s.heads bin = C) (hqb : q * 64 + b = bin) (hq : q < 38) (hb : b < 64)
    (hFC : F C) (hHC : H C) (hHF : ∀ a, H a ∨ F a → Al s.base a)
    (hnx : (s.hdr C).next ≠ 0 → F (s.hdr C).next) (hb0 : 206864 ≤ s.base)
    (hbT : s.base + 1073741824 < 2147483648) (hpv : (s.hdr C).prev < 2147483648)
    (hk : 2 ^ k ≤ 33554432) (hl : leftOf s.base C (2 ^ k) = lhs)
    (hrq : lhs + req + 1 ≤ sz) (hsz : sz ≤ 33554432) (hCend : C + 32 * sz ≤ s.base + 1073741824)
    (hal : s.allocated < 2147483648)
    (hend : (C - s.base) / 32 + lhs + 1 + req + (if sz - lhs - req - 1 = 0 then 0 else 1) ≤ s.allocated)
    (h1 : ω[1] = UInt64.ofNat sp) (h10 : ω[10] = UInt64.ofNat C) (h11 : ω[11] = UInt64.ofNat sz)
    (h5 : ω[5] = UInt64.ofNat (196792 + 4 * bin)) (h2 : ω[2] = UInt64.ofNat b) (h6 : ω[6] = UInt64.ofNat q)
    (h3 : ω[3] = UInt64.ofNat 204984) (h8 : ω[8] = UInt64.ofNat (2 ^ k)) (h9 : ω[9] = UInt64.ofNat req)
    (h120 : rdN μ (sp + 120) 8 = 204984)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT)
    (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1) (hHFT : ∀ a, H a ∨ F a → a + 32 ≤ HT) (hw : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 41425 ω μ x 41726 ω' μ' x 100 ∧ RepAt μ' (unregister s C bin) H F ∧
      ω'[1] = UInt64.ofNat sp ∧ ω'[8] = UInt64.ofNat (32 * ((C - s.base) / 32 + lhs)) ∧
      ω'[0] = UInt64.ofNat lhs ∧
      rdN μ' (sp + 96) 8 = s.base ∧ rdN μ' (sp + 48) 8 = (s.hdr C).prev ∧ rdN μ' (sp + 80) 8 = s.allocated ∧
      rdN μ' (sp + 72) 8 = (C - s.base) / 32 + lhs + 1 ∧ rdN μ' (sp + 104) 8 = sz - lhs - req - 1 ∧
      rdN μ' (sp + 56) 8 = C ∧
      rdN μ' (sp + 88) 8 = 204984 ∧ rdN μ' (sp + 120) 8 = 204984 ∧
      (∀ a, μ'.writable a = μ.writable a) ∧
      (∀ a, a < 4294967296 → 2147483648 ≤ a → (a < sp + 32 ∨ sp + 112 ≤ a) → μ'.read a = μ.read a) ∧
      ∀ j : Fin 13, j.val ∉ [0, 2, 3, 5, 6, 8, 10, 11, 12] → ω'[j] = ω[j] := by
  have hAC := hHF C (Or.inr hFC)
  unfold Al at hAC
  have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hkk : k < 32 := by
    rcases Nat.lt_or_ge k 32 with h | h
    · exact h
    · have : 2 ^ 32 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) h
      simp only [Nat.reducePow] at this; omega
  obtain ⟨hl1, hl2, -⟩ := leftOf_spec (base := s.base) (C := C) (align := 2 ^ k) (by omega)
  rw [hl] at hl1 hl2
  have hbase : rdN μ 206520 8 = s.base := by have := hrep.base; unfold A0 at this; exact this
  have halloc : rdN μ 206840 4 = s.allocated := by have := hrep.alloc; unfold A0 at this; exact this
  have hHFl : ∀ a, H a ∨ F a → a + 16 < 2147483648 := fun a ha => by have := hHF a ha; unfold Al at this; omega
  -- the offsets
  obtain ⟨ω1, μ1, r1, a2, a5, a6, a12, s64, s32, s40, s88, fr1, ww1, g1⟩ := al_offs1A (p := p) (P := P) (R := R)
    x ω μ sp C s.base s.allocated (2 ^ k) h1 h10 h8 hk1 (by omega) h120 hbase halloc hal (by omega) (by omega)
    hsp0 hsp hHTs hSTk hw
  obtain ⟨ω2, μ2, r2, b6, b8, b12, s96, fr2, ww2, g2⟩ := al_offs2A (p := p) (P := P) (R := R)
    x ω1 μ1 sp (C - s.base) s.base k (by rw [fget g1 1 (by decide) (by decide)]; exact h1) a12 a6 a5 hkk
    (by omega) (by omega) hsp0 hsp hHTs hSTk (hw.of_eq ww1)
  rw [show s.base / 32 + (C - s.base) / 32 + 2 ^ k = s.base / 32 + (C - s.base) / 32 + 1 + (2 ^ k - 1) by omega,
    hl2] at b8
  generalize hc : (C - s.base) / 32 = c at *
  obtain ⟨ω3, μ3, r3, c6, c3, c0, c11, c8, c5, s72, s104, s80, s56, fr3, ww3, g3⟩ := al_offs3A (p := p) (P := P)
    (R := R) x ω2 μ2 sp (s.base / 32) c lhs req sz s.allocated C
    (by rw [fget g2 1 (by decide) (by decide), fget g1 1 (by decide) (by decide)]; exact h1) b6
    (by rw [b8]; congr 1) b12
    (by rw [fget g2 9 (by decide) (by decide), fget g1 9 (by decide) (by decide)]; exact h9)
    (by rw [fget g2 11 (by decide) (by decide), fget g1 11 (by decide) (by decide)]; exact h11)
    (by rw [fget g2 2 (by decide) (by decide)]; exact a2)
    (by rw [fget g2 10 (by decide) (by decide), fget g1 10 (by decide) (by decide)]; exact h10)
    (by omega) hrq (by omega) (by omega) (by omega) hal (by omega) hsp0 hsp hHTs hSTk ((hw.of_eq ww1).of_eq ww2)
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
  obtain ⟨ω4, μ4, r5, rep4, p48, e8, ww4, fr4, g4⟩ := al_unreg (p := p) (P := P) (R := R) x ω3 μ3 s H F sp C
    (c + lhs) bin q b rep3 hcb hqb hq hb hFC hHC hHF hnx hb0 hbT hpv (by omega)
    (by rw [fget g3 1 (by decide) (by decide), fget g2 1 (by decide) (by decide), fget g1 1 (by decide) (by decide)]
        exact h1)
    (by rw [fget g3 10 (by decide) (by decide), fget g2 10 (by decide) (by decide),
          fget g1 10 (by decide) (by decide)]; exact h10)
    c3 k64 k40 k32 k88 k120 hsp0 hsp hHTs hSTk hHFT (((hw.of_eq ww1).of_eq ww2).of_eq ww3)
  have t4 : ∀ a, sp + 32 ≤ a → a + 8 ≤ sp + 152 → (a + 8 ≤ sp + 48 ∨ sp + 56 ≤ a) → rdN μ4 a 8 = rdN μ3 a 8 :=
    fun a h h' e => rdN_frame fun j hj => fr4 _ (by omega) (by omega) (by omega)
  refine ⟨ω4, μ4, ((((r1.trans r2).trans r3).trans r4).trans r5).mono (by omega), rep4,
    by rw [fget g4 1 (by decide) (by decide), fget g3 1 (by decide) (by decide), fget g2 1 (by decide) (by decide),
      fget g1 1 (by decide) (by decide)]; exact h1, e8,
    by rw [fget g4 0 (by decide) (by decide)]; exact c0, ?_, p48, ?_, ?_, ?_, ?_,
    by rw [t4 _ (by omega) (by omega) (by omega)]; exact k88, by rw [t4 _ (by omega) (by omega) (by omega)]; exact k120,
    fun a => (ww4 a).trans ((ww3 a).trans ((ww2 a).trans (ww1 a))), fun a h1 h2 h3 => ?_, ?_⟩
  · rw [t4 _ (by omega) (by omega) (by omega)]
    rw [show rdN μ3 (sp + 96) 8 = rdN μ2 (sp + 96) 8 from rdN_frame fun j hj => fr3 _ (by omega) (by omega)
      (by omega) (by omega)]
    exact rd_enc s96 (by omega)
  · rw [t4 _ (by omega) (by omega) (by omega)]; exact rd_enc s80 (by omega)
  · rw [t4 _ (by omega) (by omega) (by omega)]; exact rd_enc s72 (by omega)
  · rw [t4 _ (by omega) (by omega) (by omega)]; exact rd_enc s104 (by omega)
  · rw [t4 _ (by omega) (by omega) (by omega)]; exact rd_enc s56 (by omega)
  · rw [fr4 a h1 h2 (by omega), fr3 a h1 (by omega) (by omega) (by omega), fr2 a h1 (by omega),
      fr1 a h1 (by omega)]
  · exact frame_trans g4 (frame_trans (l := [0, 2, 3, 5, 6, 8, 10, 11, 12]) g3
      (frame_trans (l := [0, 2, 3, 5, 6, 8, 10, 11, 12]) g2 g1 (fun j hj => by simp at hj ⊢; omega)
        (fun j hj => by simp at hj ⊢; omega)) (fun j hj => hj) (fun j hj => by simp at hj ⊢; omega))
      (fun j hj => hj) (fun j hj => by simp at hj ⊢; omega)

/-- **41726 … 41870**, a left remainder of `lhs ≠ 0` units: the left remainder at C (one of H and
    F) registered free — the memory holds `register t C pv lhs`; ω₂ the allocated chunk
    `base + 32·(c + lhs)`, ω₀ = lhs its `prev`. -/
theorem alloc_left {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (t : State) (H F : Nat → Prop) (sp C c lhs pv : Nat) (hrep : RepAt μ t H F)
    (hHC : H C) (hFC : F C) (hHF : ∀ a, H a ∨ F a → Al t.base a) (hb0 : 206864 ≤ t.base)
    (hbT : t.base + 1073741824 < 2147483648) (hl0 : lhs ≠ 0) (hl1 : lhs ≤ 33554432) (hpv : pv < 2147483648)
    (hold : t.heads (binDown lhs) ≠ 0 → F (t.heads (binDown lhs)) ∧ t.heads (binDown lhs) ≠ C)
    (hcA : t.base + 32 * (c + lhs) < 2147483648)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat (32 * (c + lhs))) (h0 : ω[0] = UInt64.ofNat lhs)
    (h7 : ω[7] = UInt64.ofNat 196792)
    (h96 : rdN μ (sp + 96) 8 = t.base) (h56 : rdN μ (sp + 56) 8 = C) (h48 : rdN μ (sp + 48) 8 = pv)
    (h88 : rdN μ (sp + 88) 8 = 204984) (h120 : rdN μ (sp + 120) 8 = 204984)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT)
    (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1) (hHFT : ∀ a, H a ∨ F a → a + 32 ≤ HT) (hw : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 41726 ω μ x 41870 ω' μ' x 60 ∧ RepAt μ' (register t C pv lhs).1 H F ∧
      ω'[2] = UInt64.ofNat (t.base + 32 * (c + lhs)) ∧ ω'[0] = UInt64.ofNat lhs ∧
      (∀ a, μ'.writable a = μ.writable a) ∧
      (∀ a, a < 4294967296 → 2147483648 ≤ a → μ'.read a = μ.read a) ∧
      ∀ j : Fin 13, j.val ∉ [2, 5, 6, 8, 10, 11, 12] → ω'[j] = ω[j] := by
  have hAC := hHF C (Or.inr hFC)
  have hCT := hHFT C (Or.inr hFC)
  unfold Al at hAC
  have hBin : binDown lhs < 2432 := toBin_lt false (Nat.min_le_right _ _)
  obtain ⟨ω1, r1, a2, g1⟩ := al_lbr (p := p) (P := P) (R := R) x ω μ sp t.base (c + lhs) lhs h1 h8 h0 hl0
    (by omega) h96 (by omega) hsp hHTs hSTk hw.rd
  have c0 : ω1[0] = UInt64.ofNat lhs := by rw [fget g1 0 (by decide) (by decide)]; exact h0
  obtain ⟨ω2, r2, b12, g2⟩ : ∃ ω2, FreeStepsH p R 41736 ω1 μ x 41777 ω2 μ x 14 ∧
      ω2[12] = UInt64.ofNat (binDown lhs + 1) ∧ ∀ j : Fin 13, j.val ∉ [6, 11, 12] → ω2[j] = ω1[j] := by
    by_cases hsm : lhs ≤ 127
    · obtain ⟨ω2, r, e, g⟩ := al_lbin_small (p := p) (P := P) (R := R) x ω1 μ lhs c0 (by omega) hsm
      exact ⟨ω2, r.mono (by omega), e, fun j hj => g j (by simp at hj ⊢; omega)⟩
    · exact al_lbin_big (p := p) (P := P) (R := R) x ω1 μ lhs c0 (by omega) (by omega)
  have hhd := hrep.heads (binDown lhs) (by unfold binCount; omega)
  unfold A0 at hhd
  generalize hO : t.heads (binDown lhs) = old at hhd hold
  have hOA : old ≠ 0 → Al t.base old := fun h => hHF _ (Or.inr (hold h).1)
  obtain ⟨ω3, μ3, r3, w1, w2, w3, w4, w5, w6, w7, w8, wf, ww3, g3⟩ := al_lwrite (p := p) (P := P) (R := R)
    x ω2 μ sp (binDown lhs) C pv lhs old
    (by rw [fget g2 1 (by decide) (by decide), fget g1 1 (by decide) (by decide)]; exact h1) b12
    (by rw [fget g2 0 (by decide) (by decide)]; exact c0)
    (by rw [fget g2 7 (by decide) (by decide), fget g1 7 (by decide) (by decide)]; exact h7)
    h56 h48 h88 h120 hBin (by omega) (by omega) (by omega) (by omega)
    (by rw [show binDown lhs * 4 + 196792 = 196792 + 4 * binDown lhs by omega]; exact hhd)
    (by by_cases h0 : old = 0
        · omega
        · have := hOA h0; unfold Al at this; omega)
    (fun h0 => by
      have := hOA h0; have h2 := (hold h0).2; unfold Al at this; omega)
    hsp0 hsp hHTs hSTk (by omega) (fun h0 => by have := hHFT _ (Or.inr (hold h0).1); omega) hw
  have rep3 := register_rep (M := C) (pv := pv) (size := lhs) hrep hl0 (by unfold binCount; omega)
    (by rw [hO]; intro e; exact (hold (by rw [e]; omega)).2 e)
    w1 w2 w3 (by rw [hO]; exact w4) w5 (by rw [hO]; exact w6)
    (by rw [show 204984 + binDown lhs / 64 * 8 + 1544 = binDown lhs / 64 * 8 + 204984 + 1544 by omega]; exact w7) w8
    (fun a h1 h2 h3 h4 h5 h6 => wf a h1 h2 h3 (by rw [hO] at h4; exact h4) (by omega) h6)
    (by omega) (by omega) (by rw [hO]; intro h0; have := hOA h0; unfold Al at this; omega)
    (fun a ha => by
      rw [hO]
      have hAa := hHF a ha
      unfold Al at hAa
      refine ⟨by omega, by omega, by omega, ?_⟩
      by_cases h0 : old = 0
      · exact Or.inl h0
      · have := hOA h0; unfold Al at this; omega)
  have eH : (fun a => H a ∨ a = C) = H := funext fun a => propext ⟨fun h => h.elim id (fun e => e ▸ hHC), Or.inl⟩
  have eF : (fun a => F a ∨ a = C) = F := funext fun a => propext ⟨fun h => h.elim id (fun e => e ▸ hFC), Or.inl⟩
  rw [eH, eF] at rep3
  refine ⟨ω3, μ3, ((r1.trans r2).trans r3).mono (by omega), rep3,
    by rw [fget g3 2 (by decide) (by decide), fget g2 2 (by decide) (by decide)]; exact a2,
    by rw [fget g3 0 (by decide) (by decide), fget g2 0 (by decide) (by decide)]; exact c0, ww3,
    fun a h h' => wf a h (by omega) (by omega) (by
        by_cases h0 : old = 0
        · exact Or.inl h0
        · have := hOA h0; unfold Al at this; right; right; omega) (by omega) (by omega), ?_⟩
  exact frame_trans g3 (frame_trans (l := [2, 5, 6, 8, 10, 11, 12]) g2 g1 (fun j hj => by simp at hj ⊢; omega)
    (fun j hj => by simp at hj ⊢; omega)) (fun j hj => by simp at hj ⊢; omega) (fun j hj => by simp at hj ⊢; omega)

/-- **`registerAlloc` against memory**, at a new header address: the chunk at `a` records `pv` and
    `n` units used, and joins H. -/
theorem registerAlloc_rep' {μ μ' : Memory} {t : State} {H F : Nat → Prop} {a pv n : Nat}
    (h : RepAt μ t H F) (w1 : rdN μ' a 4 = pv) (w2 : rdN μ' (a + 4) 4 = sizeWord n true)
    (wf : ∀ b, b < 2147483648 → (b < a ∨ a + 8 ≤ b) → μ'.read b = μ.read b)
    (ha : 206864 ≤ a) (ha2 : a + 16 < 2147483648)
    (hHa : ∀ b, H b ∨ F b → 206864 ≤ b ∧ b + 16 < 2147483648 ∧ (b = a ∨ b + 16 ≤ a ∨ a + 16 ≤ b)) :
    RepAt μ' (registerAlloc t a pv n) (fun b => H b ∨ b = a) F := by
  have pr : ∀ b, (registerAlloc t a pv n).hdr b =
      if b = a then { t.hdr a with prev := pv, size := sizeWord n true } else t.hdr b := by
    intro b; unfold registerAlloc; by_cases hb : b = a
    · subst hb; rw [setHdr_self, if_pos rfl]
    · rw [setHdr_other hb, if_neg hb]
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
      have hb' : H b := hb.resolve_right hba
      obtain ⟨b1, b2, b3⟩ := hHa b (Or.inl hb')
      rw [← h.prev b hb']; exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · rw [pr]
    by_cases hba : b = a
    · subst hba; rw [if_pos rfl, w2]
    · rw [if_neg hba]
      have hb' : H b := hb.resolve_right hba
      obtain ⟨b1, b2, b3⟩ := hHa b (Or.inl hb')
      rw [← h.size b hb']; exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · obtain ⟨b1, b2, b3⟩ := hHa b (Or.inr hb)
    rw [pr]; split
    · rename_i hba; subst hba; rw [← h.next _ hb]; exact rdN_frame fun j hj => wf _ (by omega) (by omega)
    · rw [← h.next b hb]; exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · obtain ⟨b1, b2, b3⟩ := hHa b (Or.inr hb)
    rw [pr]; split
    · rename_i hba; subst hba; rw [← h.prevL _ hb]; exact rdN_frame fun j hj => wf _ (by omega) (by omega)
    · rw [← h.prevL b hb]; exact rdN_frame fun j hj => wf _ (by omega) (by omega)

/-- **41870 … 42054**: the allocated chunk M's header (`registerAlloc`, M joining H), and the `rhs`
    units after it, at N, registered free (`register`), the memory holding the result; ω₃ what
    `register` returns. -/
theorem alloc_end1A {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (H F : Nat → Prop) (sp req M pv rhs : Nat) (hrep : RepAt μ s H F)
    (hHF : ∀ a, H a ∨ F a → Al s.base a) (hb0 : 206864 ≤ s.base)
    (hbT : s.base + 1073741824 < 2147483648) (hMa : (M - s.base) % 32 = 0) (hMb : s.base ≤ M)
    (hpv : pv < 2147483648) (hrq : req + 1 ≤ 33554432) (hrh : rhs ≤ 33554432)
    (hNe : M + 32 * (req + 1) + 32 * rhs ≤ s.base + 1073741824)
    (hNdis : rhs ≠ 0 → ∀ a, H a ∨ F a → a + 32 ≤ M + 32 * (req + 1) ∨ M + 32 * (req + 1) + 32 ≤ a)
    (hNold : rhs ≠ 0 → (registerAlloc s M pv (req + 1)).heads (binDown rhs) ≠ 0 →
      F ((registerAlloc s M pv (req + 1)).heads (binDown rhs)))
    (h1 : ω[1] = UInt64.ofNat sp) (h2 : ω[2] = UInt64.ofNat M) (h0 : ω[0] = UInt64.ofNat pv)
    (h4 : ω[4] = UInt64.ofNat (req + 1)) (h9 : ω[9] = UInt64.ofNat req)
    (h7 : ω[7] = UInt64.ofNat 196792)
    (A d : Nat) (h80 : rdN μ (sp + 80) 8 = A) (h72 : rdN μ (sp + 72) 8 = d) (h104 : rdN μ (sp + 104) 8 = rhs)
    (h88 : rdN μ (sp + 88) 8 = 204984) (h120 : rdN μ (sp + 120) 8 = 204984)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT)
    (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1) (hHFT : ∀ a, H a ∨ F a → a + 32 ≤ HT) (hMT : M + 32 * (req + 1) ≤ HT)
    (hNT : rhs ≠ 0 → M + 32 * (req + 1) + 32 ≤ HT) (hw : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 41870 ω μ x 42054 ω' μ' x 80 ∧
      RepAt μ' (register (registerAlloc s M pv (req + 1)) (M + 32 * (req + 1)) (req + 1) rhs).1
        (fun a => (H a ∨ a = M) ∨ (rhs ≠ 0 ∧ a = M + 32 * (req + 1)))
        (fun a => F a ∨ (rhs ≠ 0 ∧ a = M + 32 * (req + 1))) ∧
      ω'[3] = UInt64.ofNat (register (registerAlloc s M pv (req + 1)) (M + 32 * (req + 1)) (req + 1) rhs).2 ∧
      ω'[12] = UInt64.ofNat rhs ∧ ω'[8] = UInt64.ofNat (M + 32 * (req + 1)) ∧ ω'[2] = UInt64.ofNat (M + 32) ∧
      ω'[1] = UInt64.ofNat sp ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      (∀ a, a < 4294967296 → 2147483648 ≤ a → μ'.read a = μ.read a) := by
  have hHFl : ∀ a, H a ∨ F a → 206864 ≤ a ∧ a + 16 < 2147483648 := fun a ha => by
    have := hHF a ha; unfold Al at this; omega
  obtain ⟨ω2, μ2, r2, m1, m2, b2, b8, b12, b3, fr2, ww2, g2⟩ := aw_hdr (p := p) (P := P) (R := R) x ω μ sp M pv req
    A d rhs h1 h2 h0 h4 h9 h80 h72 h104 (by omega) (by omega) (by omega) hsp0 hsp hHTs hSTk ⟨by omega, by omega⟩ hw
  have rep2 : RepAt μ2 (registerAlloc s M pv (req + 1)) (fun a => H a ∨ a = M) F :=
    registerAlloc_rep' hrep m1 m2 (fun b h1 h2 => fr2 b (by omega) h2) (by omega) (by omega) (fun b hb => by
      have := hHF b hb; unfold Al at this; omega)
  have hHF' : ∀ a, (H a ∨ a = M) ∨ F a → Al s.base a := by
    rintro a ((h | rfl) | h)
    · exact hHF a (Or.inl h)
    · unfold Al; omega
    · exact hHF a (Or.inr h)
  have k1 : ω2[1] = UInt64.ofNat sp := by
    rw [fget g2 1 (by decide) (by decide)]; exact h1
  have tr2 : ∀ a, a < 4294967296 → 2147483648 ≤ a → μ2.read a = μ.read a := fun a h h' => fr2 a h (by omega)
  have st2 : ∀ a, sp + 32 ≤ a → a + 8 ≤ sp + 152 → rdN μ2 a 8 = rdN μ a 8 := fun a h h' =>
    rdN_frame fun j hj => tr2 _ (by omega) (by omega)
  by_cases hr0 : rhs = 0
  · subst hr0
    have r3 := ar_zero (p := p) (P := P) (R := R) x ω2 μ2 b12
    have e : register (registerAlloc s M pv (req + 1)) (M + 32 * (req + 1)) (req + 1) 0 =
        (registerAlloc s M pv (req + 1), req + 1) := by unfold register; simp
    have eH : (fun a => (H a ∨ a = M) ∨ ((0 : Nat) ≠ 0 ∧ a = M + 32 * (req + 1))) = (fun a => H a ∨ a = M) :=
      funext fun a => propext (by simp)
    have eF : (fun a => F a ∨ ((0 : Nat) ≠ 0 ∧ a = M + 32 * (req + 1))) = F := funext fun a => propext (by simp)
    rw [e, eH, eF]
    exact ⟨ω2, μ2, (r2.trans r3).mono (by omega), rep2, b3, b12, b8, b2, k1, ww2, tr2⟩
  · generalize hN : M + 32 * (req + 1) = N at *
    generalize hs3 : registerAlloc s M pv (req + 1) = s3 at *
    have hBin : binDown rhs < 2432 := toBin_lt false (Nat.min_le_right _ _)
    obtain ⟨ω3, r3, c6, c12, g3⟩ : ∃ ω3, FreeStepsH p R 41910 ω2 μ2 x 41958 ω3 μ2 x 16 ∧
        ω3[6] = UInt64.ofNat (binDown rhs + 1) ∧ ω3[12] = UInt64.ofNat rhs ∧
        ∀ j : Fin 13, j.val ∉ [6, 9, 11, 12] → ω3[j] = ω2[j] := by
      by_cases hsm : rhs ≤ 127
      · obtain ⟨ω3, r, e6, g⟩ := ar_bin_small (p := p) (P := P) (R := R) x ω2 μ2 rhs b12 (by omega) hsm
        exact ⟨ω3, r.mono (by omega), e6, by rw [fget g 12 (by decide) (by decide)]; exact b12,
          fun j hj => g j (by simp at hj ⊢; omega)⟩
      · exact ar_bin_big (p := p) (P := P) (R := R) x ω2 μ2 sp rhs k1 b12 (by rw [st2 _ (by omega) (by omega)]; exact h104)
          (by omega) (by omega) hsp hHTs hSTk (hw.of_eq ww2).rd
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
      (by rw [fget g3 7 (by decide) (by decide), fget g2 7 (by decide) (by decide)]; exact h7)
      (by rw [st2 _ (by omega) (by omega)]; exact h88) (by rw [st2 _ (by omega) (by omega)]; exact h120)
      (by rw [st2 _ (by omega) (by omega)]; exact h104) hBin (by omega) (by omega) (by omega) (by omega)
      (by rw [show 196792 + binDown rhs * 4 = 196792 + 4 * binDown rhs by omega]; exact hold)
      (by by_cases h0 : old = 0
          · omega
          · have := hOA h0; unfold Al at this; omega)
      (fun h0 => by
        have := hOA h0; have h2 := hNd old (Or.inr (hOF h0)); unfold Al at this; omega)
      hsp0 hsp hHTs hSTk (by have := hNT hr0; omega)
      (fun h0 => by have := hHFT _ (Or.inr (hOF h0)); omega) (hw.of_eq ww2)
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
        have hAa := hHF' a ha
        have hda : a + 32 ≤ N ∨ N + 32 ≤ a := by
          rcases ha with (h | rfl) | h
          · exact hNd a (Or.inl h)
          · omega
          · exact hNd a (Or.inr h)
        unfold Al at hAa
        refine ⟨by omega, by omega, by omega, ?_⟩
        by_cases h0 : old = 0
        · exact Or.inl h0
        · have := hOA h0; unfold Al at this; omega)
    have eH : (fun a => (H a ∨ a = M) ∨ (rhs ≠ 0 ∧ a = N)) = (fun a => (H a ∨ a = M) ∨ a = N) :=
      funext fun a => propext (by simp [hr0])
    have eF : (fun a => F a ∨ (rhs ≠ 0 ∧ a = N)) = (fun a => F a ∨ a = N) :=
      funext fun a => propext (by simp [hr0])
    have e2 : (register s3 N (req + 1) rhs).2 = rhs := by unfold register; simp [hr0]
    rw [eH, eF, e2]
    refine ⟨ω4, μ4, ((r2.trans r3).trans r4).mono (by omega), rep4, d3, d12,
      by rw [fget g4 8 (by decide) (by decide), fget g3 8 (by decide) (by decide)]; exact b8,
      by rw [fget g4 2 (by decide) (by decide), fget g3 2 (by decide) (by decide)]; exact b2,
      by rw [fget g4 1 (by decide) (by decide), fget g3 1 (by decide) (by decide)]; exact k1, fun a => (ww4 a).trans (ww2 a),
      fun a h h' => (wf a h (by omega) (by omega) (by
        by_cases h0 : old = 0
        · exact Or.inl h0
        · have := hOA h0; unfold Al at this; right; right; omega) (by omega) (by omega)).trans (tr2 a h h')⟩

/-- `allocPostL`, for the bin's head C at a 32-aligned offset, as the binary computes it. -/
theorem allocPostL_eq {s : State} {bin r S lhs T C : Nat} (hcb : s.heads bin = C) (hCb : s.base ≤ C)
    (hCa : (C - s.base) % 32 = 0) :
    allocPostL s bin r S lhs T =
      let ls := register (unregister s C bin) C (s.hdr C).prev lhs
      let rs := register (registerAlloc ls.1 (C + 32 * lhs) ls.2 (r + 1)) (C + 32 * lhs + 32 * (r + 1)) (r + 1)
        (S - lhs - r - 1)
      if C + 32 * lhs + 32 * (r + 1) + 32 * (S - lhs - r - 1) < T
      then setHdr rs.1 (C + 32 * lhs + 32 * (r + 1) + 32 * (S - lhs - r - 1)) (fun h => { h with prev := rs.2 })
      else rs.1 := by
  have hA : s.base + 32 * ((C - s.base) / 32) = C := by omega
  have hu : unregister s C bin = unregisterFirst s C bin := by unfold unregister; rw [if_pos hcb]
  rw [allocPostL_unfold hcb hA, hu, show 1 + r = r + 1 from Nat.add_comm _ _]

/-- **The binary's `alloc_impl` refines the model's allocation step, with an alignment of `2^k`
    units** (the heap in use, no growth, not zeroing): from the entry (41177) to its return
    (41423), memory holding s at the header addresses H/F comes to hold
    `allocPostL s bin req S lhs top` — the left remainder `lhs = leftOf base C 2^k` registered free
    at C, the allocated chunk at `C + 32·lhs`, the right remainder — and `C + 32·lhs + 32` is
    returned, given the facts about the heap the stages need. -/
theorem alloc_impl_align {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (H F : Nat → Prop) (sp req k bin C lhs : Nat) (hrep : RepAt μ s H F)
    (hbits : BitsOk s.secondary s.primary s.heads)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat (2 ^ k))
    (h9 : ω[9] = UInt64.ofNat req) (h10 : ω[10] = UInt64.ofNat 0)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648)
    (hm : req + 2 ^ k ≤ 33554432)
    (hbin : (findFirst s (binUp (req + 2 ^ k))).or (findFirst s (binDown (req + 2 ^ k))) = some bin)
    (hbn : bin < 2432)
    (hcb : s.heads bin = C) (hFC : F C) (hHC : H C) (hHF : ∀ a, H a ∨ F a → Al s.base a)
    (hnx : (s.hdr C).next ≠ 0 → F (s.hdr C).next) (hpv : (s.hdr C).prev < 2147483648)
    (hl : leftOf s.base C (2 ^ k) = lhs)
    (hS : req + 2 ^ k ≤ wordSize (s.hdr C).size)
    (hCend : C + 32 * wordSize (s.hdr C).size ≤ s.base + 1073741824)
    (hal : s.allocated < 2147483648)
    (hend : (C - s.base) / 32 + lhs + 1 + req +
      (if wordSize (s.hdr C).size - lhs - req - 1 = 0 then 0 else 1) ≤ s.allocated)
    (hLold : lhs ≠ 0 → (unregister s C bin).heads (binDown lhs) ≠ 0 →
      F ((unregister s C bin).heads (binDown lhs)) ∧ (unregister s C bin).heads (binDown lhs) ≠ C)
    (hNdis : wordSize (s.hdr C).size - lhs - req - 1 ≠ 0 → ∀ a, H a ∨ F a →
      a + 32 ≤ C + 32 * lhs + 32 * (req + 1) ∨ C + 32 * lhs + 32 * (req + 1) + 32 ≤ a)
    (hNold : wordSize (s.hdr C).size - lhs - req - 1 ≠ 0 →
      (registerAlloc (register (unregister s C bin) C (s.hdr C).prev lhs).1 (C + 32 * lhs)
        (register (unregister s C bin) C (s.hdr C).prev lhs).2 (req + 1)).heads
          (binDown (wordSize (s.hdr C).size - lhs - req - 1)) ≠ 0 →
      F ((registerAlloc (register (unregister s C bin) C (s.hdr C).prev lhs).1 (C + 32 * lhs)
        (register (unregister s C bin) C (s.hdr C).prev lhs).2 (req + 1)).heads
          (binDown (wordSize (s.hdr C).size - lhs - req - 1))))
    (hFin : C + 32 * wordSize (s.hdr C).size < s.base + 1073741824 → H (C + 32 * wordSize (s.hdr C).size))
    {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hSTk : S0 + 152 ≤ sp ∧ sp ≤ S1)
    (hHFT : ∀ a, H a ∨ F a → a + 32 ≤ HT) (hHT : s.base + 32 * s.allocated ≤ HT) (hwr : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 41177 ω μ x 41423 ω' μ' x 500 ∧
      RepAt μ' (allocPostL s bin req (wordSize (s.hdr C).size) lhs (s.base + 1073741824))
        (fun a => (H a ∨ a = C + 32 * lhs) ∨
          (wordSize (s.hdr C).size - lhs - req - 1 ≠ 0 ∧ a = C + 32 * lhs + 32 * (req + 1)))
        (fun a => F a ∨ (wordSize (s.hdr C).size - lhs - req - 1 ≠ 0 ∧ a = C + 32 * lhs + 32 * (req + 1))) ∧
      ω'[7] = UInt64.ofNat (C + 32 * lhs + 32) ∧ ω'[0] = ω[0] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[1] = ω[1] ∧
      (∀ a, μ'.writable a = μ.writable a) ∧ (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) := by
  have hAC := hHF C (Or.inr hFC)
  have hCT := hHFT C (Or.inr hFC)
  unfold Al at hAC
  have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hkk : k < 32 := by
    rcases Nat.lt_or_ge k 32 with h | h
    · exact h
    · have : 2 ^ 32 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) h
      simp only [Nat.reducePow] at this; omega
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
      st32, sf1, ww1⟩ := alloc_entry_align (p := p) (P := P) (R := R) x ω μ s sp req k bin C (s.hdr C).size hbits
    h1 h7 h8 hkk h9 hsp hsp1 hbase (by omega) hpri hsec hm hbin hheads hsz (by omega) (by omega) hHTs hSTk
    ⟨by omega, by omega⟩ hwr
  rw [hwS] at a11
  have rep1 : RepAt μ1 s H F := hrep.congr_low (fun a ha => sf1 a (by omega) (Or.inl (by omega))) hHFl
  obtain ⟨hl1, -, -⟩ := leftOf_spec (base := s.base) (C := C) (align := 2 ^ k) (by omega)
  rw [hl] at hl1
  obtain ⟨ω2, μ2, r2, rep2, b1, b8, b0, m96, m48, m80, m72, m104, m56, m88, m120, ww2, fr2, g2⟩ :=
    alloc_mid_align (p := p) (P := P) (R := R) x ω1 μ1 s H F (sp - 152) req k bin q b C S lhs rep1 hcb hqb hq hb
      hFC hHC hHF hnx hb0 hbT hpv (by omega) hl (by omega) (by omega) hCend hal hend a1 a10 a11 a5 a2 a6 a3 a8 a9
      (by rw [show sp - 152 + 120 = sp - 32 by omega]; exact st32)
      (by omega) (by omega) hHTs ⟨by omega, by omega⟩ hHFT (hwr.of_eq ww1)
  generalize hpvd : (s.hdr C).prev = pv at *
  generalize ht2 : unregister s C bin = t2 at *
  have e2b : t2.base = s.base := by rw [← ht2, unregister_base]
  have hCa : (C - s.base) % 32 = 0 := hAC.2.1
  have hA : s.base + 32 * ((C - s.base) / 32 + lhs) = C + 32 * lhs := by omega
  have hwr2 := (hwr.of_eq ww1).of_eq ww2
  -- the left remainder
  obtain ⟨ω3, μ3, r3, rep3, c2, c0, ww3, fr3, g3⟩ : ∃ ω3 μ3, FreeStepsH p R 41726 ω2 μ2 x 41870 ω3 μ3 x 60 ∧
      RepAt μ3 (register t2 C pv lhs).1 H F ∧ ω3[2] = UInt64.ofNat (C + 32 * lhs) ∧
      ω3[0] = UInt64.ofNat (register t2 C pv lhs).2 ∧ (∀ a, μ3.writable a = μ2.writable a) ∧
      (∀ a, a < 4294967296 → 2147483648 ≤ a → μ3.read a = μ2.read a) ∧
      ∀ j : Fin 13, j.val ∉ [0, 2, 5, 6, 8, 10, 11, 12] → ω3[j] = ω2[j] := by
    by_cases hl0 : lhs = 0
    · subst hl0
      obtain ⟨ω3, r, e2, e0, g⟩ := aw_left0 (p := p) (P := P) (R := R) x ω2 μ2 (sp - 152) s.base
        ((C - s.base) / 32) pv b1 (by rw [b8, Nat.add_zero]) b0 m96 m48 (by omega) (by omega) hHTs
        ⟨by omega, by omega⟩ hwr2.rd
      refine ⟨ω3, μ2, r.mono (by omega), by rw [register_zero]; exact rep2, by rw [e2]; congr 1 <;> omega,
        by rw [register_zero]; exact e0, fun _ => rfl, fun _ _ _ => rfl, fun j hj => g j (by simp at hj ⊢; omega)⟩
    · obtain ⟨ω3, μ3, r, rp, e2, e0, ww, fr, g⟩ := alloc_left (p := p) (P := P) (R := R) x ω2 μ2 t2 H F (sp - 152)
        C ((C - s.base) / 32) lhs pv rep2 hHC hFC (by rw [e2b]; exact hHF) (by rw [e2b]; exact hb0)
        (by rw [e2b]; exact hbT) hl0 (by omega) hpv (hLold hl0) (by rw [e2b]; omega) b1
        b8 b0
        (by rw [fget g2 7 (by decide) (by decide)]; exact a7) (by rw [e2b]; exact m96) m56 m48 m88 m120
        (by omega) (by omega) hHTs ⟨by omega, by omega⟩ hHFT hwr2
      have e2r : (register t2 C pv lhs).2 = lhs := by unfold register; simp [hl0]
      refine ⟨ω3, μ3, r.mono (by omega), rp, by rw [e2, e2b]; congr 1 <;> omega, by rw [e2r]; exact e0, ww, fr,
        fun j hj => g j (by simp at hj ⊢; omega)⟩
  generalize hls : register t2 C pv lhs = ls at *
  have e3b : ls.1.base = s.base := by rw [← hls, register_base, e2b]
  have hls2 : ls.2 < 2147483648 := by
    rw [← hls]; unfold register; split <;> simp <;> omega
  have tr3 : ∀ a, sp - 152 + 32 ≤ a → a + 8 ≤ sp → rdN μ3 a 8 = rdN μ2 a 8 := fun a h h' =>
    rdN_frame fun j hj => fr3 _ (by omega) (by omega)
  obtain ⟨ω4, μ4, r4, rep4, d3, d12, d8, d2, d1, ww4, fr4⟩ := alloc_end1A (p := p) (P := P) (R := R) x ω3 μ3 ls.1
    H F (sp - 152) req (C + 32 * lhs) ls.2 (S - lhs - req - 1) rep3 (by rw [e3b]; exact hHF) (by rw [e3b]; exact hb0)
    (by rw [e3b]; exact hbT) (by rw [e3b]; omega) (by rw [e3b]; omega) hls2 (by omega) (by omega)
    (by rw [e3b]; omega) hNdis hNold
    (by rw [fget g3 1 (by decide) (by decide)]; exact b1) c2 c0
    (by rw [fget g3 4 (by decide) (by decide), fget g2 4 (by decide) (by decide)]; exact a4)
    (by rw [fget g3 9 (by decide) (by decide), fget g2 9 (by decide) (by decide)]; exact a9)
    (by rw [fget g3 7 (by decide) (by decide), fget g2 7 (by decide) (by decide)]; exact a7)
    s.allocated ((C - s.base) / 32 + lhs + 1) (by rw [tr3 _ (by omega) (by omega)]; exact m80) (by rw [tr3 _ (by omega) (by omega)]; exact m72)
    (by rw [tr3 _ (by omega) (by omega)]; exact m104) (by rw [tr3 _ (by omega) (by omega)]; exact m88)
    (by rw [tr3 _ (by omega) (by omega)]; exact m120)
    (by omega) (by omega) hHTs ⟨by omega, by omega⟩ hHFT (by omega)
    (fun h0 => by have h' := hend; rw [if_neg h0] at h'; omega) (hwr2.of_eq ww3)
  generalize hrr : register (registerAlloc ls.1 (C + 32 * lhs) ls.2 (req + 1)) (C + 32 * lhs + 32 * (req + 1))
    (req + 1) (S - lhs - req - 1) = rr at *
  have e4b : rr.1.base = s.base := by rw [← hrr, register_base, registerAlloc_base, e3b]
  have k112 : rdN μ4 (sp - 152 + 112) 8 = 0 := by
    rw [show rdN μ4 (sp - 152 + 112) 8 = rdN μ1 (sp - 152 + 112) 8 from rdN_frame fun j hj =>
      ((fr4 _ (by omega) (by omega)).trans (fr3 _ (by omega) (by omega))).trans (fr2 _ (by omega) (by omega) (by omega)),
      show sp - 152 + 112 = sp - 40 by omega]
    unfold rdN; rw [st10, h10]; rfl
  have k120 : rdN μ4 (sp - 152 + 120) 8 = 204984 := by
    rw [← m120]; exact rdN_frame fun j hj => (fr4 _ (by omega) (by omega)).trans (fr3 _ (by omega) (by omega))
  have hS32 : C + 32 * lhs + 32 * (req + 1) + 32 * (S - lhs - req - 1) = C + 32 * S := by omega
  obtain ⟨ω5, μ5, r5, rep5, f7, f0, f5, f6, f1, ww5, fr5, -⟩ := alloc_end2 (p := p) (P := P) (R := R) x ω4 μ4 rr.1
    (fun a => (H a ∨ a = C + 32 * lhs) ∨ (S - lhs - req - 1 ≠ 0 ∧ a = C + 32 * lhs + 32 * (req + 1)))
    (fun a => F a ∨ (S - lhs - req - 1 ≠ 0 ∧ a = C + 32 * lhs + 32 * (req + 1))) (sp - 152)
    (C + 32 * lhs + 32 * (req + 1)) (S - lhs - req - 1) rr.2 (C + 32 * lhs + 32) rep4
    (fun a ha => by
      rw [e4b]
      rcases ha with ((h | rfl) | ⟨h0, rfl⟩) | (h | ⟨h0, rfl⟩)
      · exact hHF a (Or.inl h)
      · unfold Al; omega
      · unfold Al; omega
      · exact hHF a (Or.inr h)
      · unfold Al; omega)
    (by rw [e4b]; exact hb0) (by rw [e4b]; exact hbT)
    (fun h => Or.inl (Or.inl (by rw [hS32]; exact hFin (by rw [e4b, hS32] at h; exact h))))
    (by rw [e4b, hS32]; exact hCend) (by omega) d1 d12 d8 d3 d2 k120 k112
    (by rw [← hrr]; unfold register; split <;> simp <;> omega) (by omega) (by omega) (by omega) hHTs
    ⟨by omega, by omega⟩
    (fun a ha => by
      rcases ha with ((h | rfl) | ⟨h0, rfl⟩) | (h | ⟨h0, rfl⟩)
      · exact hHFT a (Or.inl h)
      · omega
      · have h' := hend; rw [if_neg h0] at h'; omega
      · exact hHFT a (Or.inr h)
      · have h' := hend; rw [if_neg h0] at h'; omega)
    ((hwr2.of_eq ww3).of_eq ww4)
  have tr : ∀ a, sp - 152 + 128 ≤ a → a + 8 ≤ sp → rdN μ4 a 8 = rdN μ1 a 8 := fun a h h' =>
    rdN_frame fun j hj => ((fr4 _ (by omega) (by omega)).trans (fr3 _ (by omega) (by omega))).trans
      (fr2 _ (by omega) (by omega) (by omega))
  refine ⟨ω5, μ5, ((((r1.trans r2).trans r3).trans r4).trans r5).mono (by omega), ?_, f7, ?_, ?_, ?_, ?_,
    fun a => (ww5 a).trans ((ww4 a).trans ((ww3 a).trans ((ww2 a).trans (ww1 a)))),
    fun a h h' => ((fr5 a h (by omega)).trans ((fr4 a h (by omega)).trans ((fr3 a h (by omega)).trans
      (fr2 a h (by omega) (by omega))))).trans (sf1 a h (Or.inr h'))⟩
  · rw [allocPostL_eq hcb (by omega) hCa, hpvd, ht2, hls]
    dsimp only
    rw [hrr]
    rw [e4b, hS32] at rep5
    rw [hS32]
    exact rep5
  · rw [f0, tr _ (by omega) (by omega), show sp - 152 + 144 = sp - 8 by omega]
    unfold rdN; rw [st0, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]
  · rw [f5, tr _ (by omega) (by omega), show sp - 152 + 136 = sp - 16 by omega]
    unfold rdN; rw [st5, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]
  · rw [f6, tr _ (by omega) (by omega), show sp - 152 + 128 = sp - 24 by omega]
    unfold rdN; rw [st6, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]
  · rw [f1, h1]; congr 1; omega

end Services.Bootstrap.Alloc
