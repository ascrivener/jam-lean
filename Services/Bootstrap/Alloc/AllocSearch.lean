import Services.Bootstrap.Alloc.AllocFind

/-!
# The binary's bin search against the model's `findFirst`
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem lowestAfter_spec {v i b : Nat} (h : lowestAfter v i = some b) :
    b < 64 ∧ (v / 2 ^ i * 2 ^ i).testBit b = true := by
  unfold lowestAfter at h
  simp only at h
  split at h
  · simp at h
  · have hm := List.mem_of_find?_eq_some h
    have hp := List.find?_some h
    exact ⟨List.mem_range.mp hm, by simpa using hp⟩

theorem lowestAfter_lt38 {v i b : Nat} (hv : v < 2 ^ 38) (h : lowestAfter v i = some b) : b < 38 := by
  obtain ⟨-, hb⟩ := lowestAfter_spec h
  have hle : v / 2 ^ i * 2 ^ i < 2 ^ 38 := Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) hv
  refine Nat.lt_of_not_le fun hc => ?_
  have := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hle (Nat.pow_le_pow_right (n := 2) (by decide) hc))
  rw [hb] at this; exact absurd this (by decide)

theorem lowestAfter_bit {v i b : Nat} (h : lowestAfter v i = some b) : v.testBit b = true := by
  obtain ⟨-, hb⟩ := lowestAfter_spec h
  have : (v / 2 ^ i * 2 ^ i) = v >>> i <<< i := by rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  rw [this, Nat.testBit_shiftLeft] at hb
  simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.testBit_shiftRight] at hb
  rw [show i + (b - i) = b by omega] at hb; exact hb.2

/-- The search's first case: a bin at or after `bin` in its own word. -/
theorem ff_A {s : State} {bin b : Nat} (hp : s.primary.testBit (bin / 64) = true)
    (hb : lowestAfter (s.secondary (bin / 64)) (bin % 64) = some b) : findFirst s bin = some (bin / 64 * 64 + b) := by
  unfold findFirst; simp [hp, hb]

/-- Its second: the next non-empty word. -/
theorem ff_B {s : State} {bin q b : Nat}
    (h1 : (if s.primary.testBit (bin / 64) then lowestAfter (s.secondary (bin / 64)) (bin % 64) else none) = none)
    (hq : lowestAfter s.primary (bin / 64 + 1) = some q) (hb : lowestAfter (s.secondary q) 0 = some b) :
    findFirst s bin = some (q * 64 + b) := by
  unfold findFirst; simp only [h1, hq, hb, Option.map_some]

theorem ff_C {s : State} {bin : Nat}
    (h1 : (if s.primary.testBit (bin / 64) then lowestAfter (s.secondary (bin / 64)) (bin % 64) else none) = none)
    (hq : lowestAfter s.primary (bin / 64 + 1) = none) : findFirst s bin = none := by
  unfold findFirst; simp only [h1, hq]

variable {X : Type} {R : HostRel X}

/-- Two register frames compose. -/
theorem frame_trans {ω'' ω' ω : Regs} {l1 l2 l : List Nat} (f2 : ∀ j : Fin 13, j.val ∉ l2 → ω''[j] = ω'[j])
    (f1 : ∀ j : Fin 13, j.val ∉ l1 → ω'[j] = ω[j]) (h1 : ∀ j, j ∉ l → j ∉ l1) (h2 : ∀ j, j ∉ l → j ∉ l2) :
    ∀ j : Fin 13, j.val ∉ l → ω''[j] = ω[j] := fun j hj => (f2 j (h2 _ hj)).trans (f1 j (h1 _ hj))

/-- **41297 …, the search from the rounded-up bin `bu`**: when the model's `findFirst` finds a bin
    q·64 + b, the code reaches 41378 with ω₆ = q, ω₂ = b; when it finds none, the code reaches the
    search from the rounded-down bin (41614). -/
theorem find_up {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (sp bu : Nat) (hbits : BitsOk s.secondary s.primary s.heads)
    (h1 : ω[1] = UInt64.ofNat sp) (h2 : ω[2] = UInt64.ofNat bu) (h7 : ω[7] = UInt64.ofNat 196792)
    (hsp : sp + 128 < 4294967296) (hf : rdN μ (sp + 120) 8 = 204984) (hp : rdN μ 206832 8 = s.primary)
    (hs : ∀ q, q < 38 → rdN μ (q * 8 + 204984 + 1544) 8 = s.secondary q) (hb : bu < 2432)
    (hr : ∀ a, μ.readable a = true) :
    (∀ bin, findFirst s bu = some bin → ∃ ω' q b, FreeStepsH p R 41297 ω μ x 41378 ω' μ x 30 ∧
      q * 64 + b = bin ∧ q < 38 ∧ b < 64 ∧ ω'[6] = UInt64.ofNat q ∧ ω'[2] = UInt64.ofNat b ∧
      ∀ j : Fin 13, j.val ∉ [2, 3, 5, 6, 10, 11] → ω'[j] = ω[j]) ∧
    (findFirst s bu = none → ∃ ω', FreeStepsH p R 41297 ω μ x 41614 ω' μ x 30 ∧
      ω'[5] = UInt64.ofNat s.primary ∧ ω'[3] = UInt64.ofNat 204984 ∧
      ∀ j : Fin 13, j.val ∉ [3, 5, 6, 10, 11] → ω'[j] = ω[j]) := by
  obtain ⟨-, hprim, hsec64, hpri38⟩ := hbits
  have hp64 : s.primary < 18446744073709551616 := Nat.lt_of_lt_of_le hpri38 (by decide)
  have hq0 : bu / 64 < 38 := by omega
  have hw : rdN μ (bu / 64 * 8 + 204984 + 1544) 8 = s.secondary (bu / 64) := hs _ hq0
  by_cases hA : s.primary.testBit (bu / 64) = true ∧
      s.secondary (bu / 64) / 2 ^ (bu % 64) * 2 ^ (bu % 64) ≠ 0
  · obtain ⟨hA1, hA2⟩ := hA
    obtain ⟨ω1, r1, a5, a3, a11, g1⟩ := ff_head_set (p := p) (P := P) (R := R) x ω μ sp bu s.primary h1 h2 h7 hsp hf hp hb hA1 hr
    obtain ⟨ω2, r2, l2, a6, g2⟩ := ff_sec_found (p := p) (P := P) (R := R) x ω1 μ bu (s.secondary (bu / 64))
      (by rw [fget g1 2 (by decide) (by decide)]; exact h2) a3 a11 hb hw hA2 hr
    have hff := ff_A hA1 l2
    refine ⟨fun bin hbin => ⟨ω2, bu / 64, ω2[2].toNat, (r1.trans r2).mono (by omega), ?_, hq0,
      (lowestAfter_spec l2).1, a6, UInt64.ofNat_toNat.symm, ?_⟩, fun hn => ?_⟩
    · rw [hff] at hbin; exact Option.some.inj hbin
    · exact frame_trans g2 g1 (fun j hj => by simp at hj ⊢; omega) (fun j hj => by simp at hj ⊢; omega)
    · rw [hff] at hn; exact absurd hn (by simp)
  · have h1none : (if s.primary.testBit (bu / 64) then lowestAfter (s.secondary (bu / 64)) (bu % 64) else none)
        = none := by
      split
      · rename_i ht; exact lowestAfter_none (by simp [ht] at hA; exact hA)
      · rfl
    obtain ⟨ω2, r12, a5, a3, a11, g12⟩ : ∃ ω2, FreeStepsH p R 41297 ω μ x 41346 ω2 μ x 16 ∧
        ω2[5] = UInt64.ofNat s.primary ∧ ω2[3] = UInt64.ofNat 204984 ∧ ω2[11] = UInt64.ofNat (bu / 64) ∧
        ∀ j : Fin 13, j.val ∉ [3, 5, 6, 10, 11] → ω2[j] = ω[j] := by
      cases ht : s.primary.testBit (bu / 64)
      · obtain ⟨ω1, r1, a5, a3, a11, g1⟩ := ff_head_clr (p := p) (P := P) (R := R) x ω μ sp bu s.primary h1 h2 h7 hsp hf hp hb ht hr
        exact ⟨ω1, r1.mono (by omega), a5, a3, a11, g1⟩
      · have he : s.secondary (bu / 64) / 2 ^ (bu % 64) * 2 ^ (bu % 64) = 0 := by simp [ht] at hA; exact hA
        obtain ⟨ω1, r1, a5, a3, a11, g1⟩ := ff_head_set (p := p) (P := P) (R := R) x ω μ sp bu s.primary h1 h2 h7 hsp hf hp hb ht hr
        obtain ⟨ω2, r2, g2⟩ := ff_sec_none (p := p) (P := P) (R := R) x ω1 μ bu (s.secondary (bu / 64))
          (by rw [fget g1 2 (by decide) (by decide)]; exact h2) a3 a11 hb hw he hr
        exact ⟨ω2, (r1.trans r2).mono (by omega), by rw [fget g2 5 (by decide) (by decide)]; exact a5,
          by rw [fget g2 3 (by decide) (by decide)]; exact a3, by rw [fget g2 11 (by decide) (by decide)]; exact a11,
          frame_trans g2 g1 (fun j hj => by simp at hj ⊢; omega) (fun j hj => by simp at hj ⊢; omega)⟩
    by_cases hB : s.primary / 2 ^ (bu / 64 + 1) * 2 ^ (bu / 64 + 1) ≠ 0
    · obtain ⟨ω3, q, r3, lq, a6, a2, g3⟩ := ff_next_found (p := p) (P := P) (R := R) x ω2 μ (bu / 64) s.primary a11 a5 a3 hq0 hp64 hB hr
      have hq : q < 38 := lowestAfter_lt38 hpri38 lq
      have hsq := hs q hq
      have hsne : s.secondary q ≠ 0 := by
        have := (hprim q hq).mp (lowestAfter_bit lq)
        intro h; rw [h] at this; exact this rfl
      have hl0 : lowestAfter (s.secondary q) 0 = some (Num.trailingZeros 64 (s.secondary q)) := by
        have := lowestAfter_tz (i := 0) (Nat.lt_of_lt_of_le (hsec64 q hq) (by decide)) (by simpa using hsne)
        simpa using this
      have hff := ff_B h1none lq hl0
      refine ⟨fun bin hbin => ⟨ω3, q, Num.trailingZeros 64 (s.secondary q), (r12.trans r3).mono (by omega), ?_, hq,
        (lowestAfter_spec hl0).1, a6, by rw [a2, hsq], ?_⟩, fun hn => ?_⟩
      · rw [hff] at hbin; exact Option.some.inj hbin
      · exact frame_trans g3 g12 (fun j hj => by simp at hj ⊢; omega) (fun j hj => by simp at hj ⊢; omega)
      · rw [hff] at hn; exact absurd hn (by simp)
    · have he : s.primary / 2 ^ (bu / 64 + 1) * 2 ^ (bu / 64 + 1) = 0 := by omega
      obtain ⟨ω3, r3, g3⟩ := ff_next_none (p := p) (P := P) (R := R) x ω2 μ (bu / 64) s.primary a11 a5 hq0 hp64 he
      have hff := ff_C h1none (lowestAfter_none he)
      refine ⟨fun bin hbin => by rw [hff] at hbin; exact absurd hbin (by simp), fun _ => ⟨ω3,
        (r12.trans r3).mono (by omega), by rw [fget g3 5 (by decide) (by decide)]; exact a5,
        by rw [fget g3 3 (by decide) (by decide)]; exact a3,
        frame_trans g3 g12 (fun j hj => by simp at hj ⊢; omega) (fun j hj => by simp at hj ⊢; omega)⟩⟩

/-- **41614 …, the search from the rounded-down bin `bd`**: to 41378 with ω₆ = q, ω₂ = b when the
    model's `findFirst` finds q·64 + b, to the failure at 41404 when it finds none. -/
theorem find_down {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (bd : Nat) (hbits : BitsOk s.secondary s.primary s.heads)
    (h0 : ω[0] = UInt64.ofNat bd) (h5 : ω[5] = UInt64.ofNat s.primary) (h3 : ω[3] = UInt64.ofNat 204984)
    (hs : ∀ q, q < 38 → rdN μ (q * 8 + 204984 + 1544) 8 = s.secondary q) (hb : bd < 2432)
    (hr : ∀ a, μ.readable a = true) :
    (∀ bin, findFirst s bd = some bin → ∃ ω' q b, FreeStepsH p R 41614 ω μ x 41378 ω' μ x 30 ∧
      q * 64 + b = bin ∧ q < 38 ∧ b < 64 ∧ ω'[6] = UInt64.ofNat q ∧ ω'[2] = UInt64.ofNat b ∧
      ∀ j : Fin 13, j.val ∉ [2, 6, 11] → ω'[j] = ω[j]) ∧
    (findFirst s bd = none → ∃ ω', FreeStepsH p R 41614 ω μ x 41404 ω' μ x 30 ∧
      ω'[11] = UInt64.ofNat 0 ∧ ∀ j : Fin 13, j.val ∉ [2, 6, 11] → ω'[j] = ω[j]) := by
  obtain ⟨-, hprim, hsec64, hpri38⟩ := hbits
  have hp64 : s.primary < 18446744073709551616 := Nat.lt_of_lt_of_le hpri38 (by decide)
  have hq0 : bd / 64 < 38 := by omega
  have hw : rdN μ (bd / 64 * 8 + 204984 + 1544) 8 = s.secondary (bd / 64) := hs _ hq0
  by_cases hA : s.primary.testBit (bd / 64) = true ∧
      s.secondary (bd / 64) / 2 ^ (bd % 64) * 2 ^ (bd % 64) ≠ 0
  · obtain ⟨hA1, hA2⟩ := hA
    obtain ⟨ω1, r1, a6, g1⟩ := fb_head_set (p := p) (P := P) (R := R) x ω μ bd s.primary h0 h5 hb hp64 hA1
    obtain ⟨ω2, r2, l2, b6, g2⟩ := fb_sec_found (p := p) (P := P) (R := R) x ω1 μ bd (s.secondary (bd / 64))
      (by rw [fget g1 0 (by decide) (by decide)]; exact h0) (by rw [fget g1 3 (by decide) (by decide)]; exact h3)
      a6 hb hw hA2 hr
    have hff := ff_A hA1 l2
    refine ⟨fun bin hbin => ⟨ω2, bd / 64, ω2[2].toNat, (r1.trans r2).mono (by omega), ?_, hq0,
      (lowestAfter_spec l2).1, b6, UInt64.ofNat_toNat.symm, ?_⟩, fun hn => ?_⟩
    · rw [hff] at hbin; exact Option.some.inj hbin
    · exact frame_trans g2 g1 (fun j hj => by simp at hj ⊢; omega) (fun j hj => by simp at hj ⊢; omega)
    · rw [hff] at hn; exact absurd hn (by simp)
  · have h1none : (if s.primary.testBit (bd / 64) then lowestAfter (s.secondary (bd / 64)) (bd % 64) else none)
        = none := by
      split
      · rename_i ht; exact lowestAfter_none (by simp [ht] at hA; exact hA)
      · rfl
    obtain ⟨ω2, r12, a6, g12⟩ : ∃ ω2, FreeStepsH p R 41614 ω μ x 41654 ω2 μ x 16 ∧
        ω2[6] = UInt64.ofNat (bd / 64) ∧ ∀ j : Fin 13, j.val ∉ [2, 6, 11] → ω2[j] = ω[j] := by
      cases ht : s.primary.testBit (bd / 64)
      · obtain ⟨ω1, r1, a6, g1⟩ := fb_head_clr (p := p) (P := P) (R := R) x ω μ bd s.primary h0 h5 hb hp64 ht
        exact ⟨ω1, r1.mono (by omega), a6, fun j hj => g1 j (by simp at hj ⊢; omega)⟩
      · have he : s.secondary (bd / 64) / 2 ^ (bd % 64) * 2 ^ (bd % 64) = 0 := by simp [ht] at hA; exact hA
        obtain ⟨ω1, r1, a6, g1⟩ := fb_head_set (p := p) (P := P) (R := R) x ω μ bd s.primary h0 h5 hb hp64 ht
        obtain ⟨ω2, r2, b6, g2⟩ := fb_sec_none (p := p) (P := P) (R := R) x ω1 μ bd (s.secondary (bd / 64))
          (by rw [fget g1 0 (by decide) (by decide)]; exact h0) (by rw [fget g1 3 (by decide) (by decide)]; exact h3)
          a6 hb hw he hr
        exact ⟨ω2, (r1.trans r2).mono (by omega), b6,
          frame_trans g2 g1 (fun j hj => by simp at hj ⊢; omega) (fun j hj => by simp at hj ⊢; omega)⟩
    have c5 : ω2[5] = UInt64.ofNat s.primary := by rw [fget g12 5 (by decide) (by decide)]; exact h5
    have c3 : ω2[3] = UInt64.ofNat 204984 := by rw [fget g12 3 (by decide) (by decide)]; exact h3
    by_cases hB : s.primary / 2 ^ (bd / 64 + 1) * 2 ^ (bd / 64 + 1) ≠ 0
    · obtain ⟨ω3, r3, a11, g3⟩ := fb_next_found (p := p) (P := P) (R := R) x ω2 μ (bd / 64) s.primary a6 c5 hq0 hp64 hB
      obtain ⟨ω4, r4, d6, d2, g4⟩ := ff_tail (p := p) (P := P) (R := R) x ω3 μ _ a11
        (by rw [fget g3 3 (by decide) (by decide)]; exact c3)
        (Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) hp64) hr
      have lq := lowestAfter_tz hp64 hB
      generalize Num.trailingZeros 64 (s.primary / 2 ^ (bd / 64 + 1) * 2 ^ (bd / 64 + 1)) = q at lq d6 d2
      have hq : q < 38 := lowestAfter_lt38 hpri38 lq
      have hsq := hs q hq
      have hsne : s.secondary q ≠ 0 := by
        have := (hprim q hq).mp (lowestAfter_bit lq)
        intro h; rw [h] at this; exact this rfl
      have hl0 : lowestAfter (s.secondary q) 0 = some (Num.trailingZeros 64 (s.secondary q)) := by
        have := lowestAfter_tz (i := 0) (Nat.lt_of_lt_of_le (hsec64 q hq) (by decide)) (by simpa using hsne)
        simpa using this
      have hff := ff_B h1none lq hl0
      refine ⟨fun bin hbin => ⟨ω4, q, Num.trailingZeros 64 (s.secondary q), ((r12.trans r3).trans r4).mono (by omega),
        ?_, hq, (lowestAfter_spec hl0).1, d6, by rw [d2, hsq], ?_⟩, fun hn => ?_⟩
      · rw [hff] at hbin; exact Option.some.inj hbin
      · exact frame_trans g4 (frame_trans g3 g12 (fun j hj => hj) (fun j hj => by simp at hj ⊢; omega))
          (fun j hj => hj) (fun j hj => by simp at hj ⊢; omega)
      · rw [hff] at hn; exact absurd hn (by simp)
    · have he : s.primary / 2 ^ (bd / 64 + 1) * 2 ^ (bd / 64 + 1) = 0 := by omega
      obtain ⟨ω3, r3, a11, g3⟩ := fb_next_none (p := p) (P := P) (R := R) x ω2 μ (bd / 64) s.primary a6 c5 hq0 hp64 he
      have hff := ff_C h1none (lowestAfter_none he)
      refine ⟨fun bin hbin => by rw [hff] at hbin; exact absurd hbin (by simp), fun _ => ⟨ω3,
        (r12.trans r3).mono (by omega), a11,
        frame_trans g3 g12 (fun j hj => hj) (fun j hj => by simp at hj ⊢; omega)⟩⟩

end Services.Bootstrap.Alloc
