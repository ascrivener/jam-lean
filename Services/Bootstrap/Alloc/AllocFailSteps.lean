import Services.Bootstrap.Alloc.AllocImpl

/-!
# The binary's `alloc_impl` failing, without growth

`alloc_impl` (41177 … 41423, alignment one unit, the heap in use) returns null (ω₇ = 0) when:

1. the request plus its header unit exceeds `MAX_ALLOCATION_SIZE` (2²⁵ units): 41221 … 41237,
   then the shared failure tail at 41404 with ω₁₁ = 0;
2. neither search, from the request's bin rounded up nor rounded down, finds a marked bin: the
   rounded-down search's none branch ends at 41404 with ω₁₁ = 0;
3. the found bin's first chunk is smaller than the request plus its header unit: 41398 → 41401.

On every path only the frame (sp − 152 … sp) is written.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- A register saved with `storeIndU64` comes back. -/
theorem rd_restore {μ : Memory} {a : Nat} {v : UInt64} (h : μ.readN a 8 = Num.encodeLE 8 v.toNat) :
    UInt64.ofNat (rdN μ a 8) = v := by
  unfold rdN; rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]

/-- **41221 … 41404, the request too large**: the minimum size `req + 1` (32-bit arithmetic, here
    exact) is above `MAX_ALLOCATION_SIZE` = 2²⁵ units; ω₁₁ = 0 for the failure tail. -/
theorem al_big_lo {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (req : Nat) (h9 : ω[9] = UInt64.ofNat req) (h8 : ω[8] = UInt64.ofNat 1)
    (hr : 33554432 < req + 1) (hr1 : req + 1 < 2147483648) :
    ∃ ω', FreeStepsH p R 41221 ω μ x 41404 ω' μ x 6 ∧ ω'[11] = UInt64.ofNat 0 ∧
      ∀ j : Fin 13, j.val ∉ [4, 11, 12] → ω'[j] = ω[j] := by
  have e : (req + 1) / 2147483648 = 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h9, h8, e, Nat.mod_eq_of_lt (show req + 1 < 18446744073709551616 by omega),
    show ¬ req + 1 ≤ 33554432 by omega]
  case post => exact ⟨by reg_val, by reg_frame⟩

/-- **41221 … 41404**, `req = 2³¹ − 1`: the 32-bit sum 2³¹ sign-extends to 2⁶⁴ − 2³¹, still above
    2²⁵. -/
theorem al_big_edge {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (h9 : ω[9] = UInt64.ofNat 2147483647) (h8 : ω[8] = UInt64.ofNat 1) :
    ∃ ω', FreeStepsH p R 41221 ω μ x 41404 ω' μ x 6 ∧ ω'[11] = UInt64.ofNat 0 ∧
      ∀ j : Fin 13, j.val ∉ [4, 11, 12] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h9, h8]
  case post => exact ⟨by reg_val, by reg_frame⟩

/-- **41221 … 41404, the request too large** (`req < 2³¹`). -/
theorem al_big {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (req : Nat) (h9 : ω[9] = UInt64.ofNat req) (h8 : ω[8] = UInt64.ofNat 1)
    (hr : 33554432 < req + 1) (hr1 : req < 2147483648) :
    ∃ ω', FreeStepsH p R 41221 ω μ x 41404 ω' μ x 6 ∧ ω'[11] = UInt64.ofNat 0 ∧
      ∀ j : Fin 13, j.val ∉ [4, 11, 12] → ω'[j] = ω[j] := by
  by_cases he : req = 2147483647
  · subst he; exact al_big_edge (p := p) (P := P) x ω μ h9 h8
  · exact al_big_lo (p := p) (P := P) x ω μ req h9 h8 hr (by omega)

/-- **41177 … 41423, the request too large**: null returned, only the frame written. -/
theorem alloc_fail_big {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp req base : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792)
    (h8 : ω[8] = UInt64.ofNat 1) (h9 : ω[9] = UInt64.ofNat req) (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb : rdN μ 206520 8 = base) (hb0 : base ≠ 0) (hr : 33554432 < req + 1) (hr1 : req < 2147483648)
    {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hSTk : S0 + 152 ≤ sp ∧ sp ≤ S1) (hwr : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 41177 ω μ x 41423 ω' μ' x 30 ∧ ω'[7] = UInt64.ofNat 0 ∧
      ω'[0] = ω[0] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[1] = ω[1] ∧
      (∀ a, μ'.writable a = μ.writable a) ∧
      (∀ a, a < 4294967296 → (a < sp - 152 ∨ sp ≤ a) → μ'.read a = μ.read a) := by
  have hb64 : base < 18446744073709551616 := by rw [← hb]; exact rdN_lt64 μ _
  obtain ⟨ω1, μ1, r1, a1, a11, -, st0, st5, st6, -, -, sf1, ww1, g1⟩ :=
    al_pro (p := p) (P := P) (R := R) x ω μ sp 0 base h1 h7 (by rw [h8]) (by decide) hsp hsp1 hb (by omega) hSTk hwr
  have r2 := al_br_used (p := p) (P := P) (R := R) x ω1 μ1 base a11 hb0 hb64
  obtain ⟨ω2, r3, b11, g3⟩ := al_big (p := p) (P := P) (R := R) x ω1 μ1 req
    (by rw [fget g1 9 (by decide) (by decide)]; exact h9) (by rw [fget g1 8 (by decide) (by decide)]; exact h8) hr hr1
  obtain ⟨ω3, r4, d7, d0, d5, d6, d1, -⟩ := an_ret (p := p) (P := P) (R := R) x ω2 μ1 (sp - 152)
    (by rw [fget g3 1 (by decide) (by decide)]; exact a1) (by omega) hHTs ⟨by omega, by omega⟩ (hwr.of_eq ww1).rd
  refine ⟨ω3, μ1, (((r1.trans r2).trans r3).trans r4).mono (by omega), by rw [d7, b11], ?_, ?_, ?_, ?_, ww1, sf1⟩
  · rw [d0, show sp - 152 + 144 = sp - 8 by omega]; exact rd_restore st0
  · rw [d5, show sp - 152 + 136 = sp - 16 by omega]; exact rd_restore st5
  · rw [d6, show sp - 152 + 128 = sp - 24 by omega]; exact rd_restore st6
  · rw [d1, h1]; congr 1; omega

/-- **41177 … 41423, no bin found**: neither the search from the request's bin rounded up nor the
    one from it rounded down finds a marked bin (the model's `findFirst` gives none twice); null
    returned, only the frame written. -/
theorem alloc_fail_nobin {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (sp req : Nat) (hbits : BitsOk s.secondary s.primary s.heads)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat 1)
    (h9 : ω[9] = UInt64.ofNat req) (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb : rdN μ 206520 8 = s.base) (hb0 : s.base ≠ 0)
    (hp : rdN μ 206832 8 = s.primary) (hs : ∀ q, q < 38 → rdN μ (q * 8 + 204984 + 1544) 8 = s.secondary q)
    (hm : req + 1 ≤ 33554432)
    (hbin : (findFirst s (binUp (req + 1))).or (findFirst s (binDown (req + 1))) = none)
    {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hSTk : S0 + 152 ≤ sp ∧ sp ≤ S1) (hwr : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 41177 ω μ x 41423 ω' μ' x 120 ∧ ω'[7] = UInt64.ofNat 0 ∧
      ω'[0] = ω[0] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[1] = ω[1] ∧
      (∀ a, μ'.writable a = μ.writable a) ∧
      (∀ a, a < 4294967296 → (a < sp - 152 ∨ sp ≤ a) → μ'.read a = μ.read a) := by
  have hb64 : s.base < 18446744073709551616 := by rw [← hb]; exact rdN_lt64 μ _
  have hu : findFirst s (binUp (req + 1)) = none := by
    revert hbin; cases findFirst s (binUp (req + 1)) <;> simp
  rw [hu, Option.none_or] at hbin
  obtain ⟨ω1, μ1, r1, a1, a11, a12, st0, st5, st6, -, st32, sf1, ww1, g1⟩ :=
    al_pro (p := p) (P := P) (R := R) x ω μ sp 0 s.base h1 h7 (by rw [h8]) (by decide) hsp hsp1 hb (by omega) hSTk hwr
  have hr1 := (hwr.of_eq ww1).rd
  have tr : ∀ a n, a + n ≤ 2147483648 → rdN μ1 a n = rdN μ a n := fun a n h =>
    rdN_frame fun j hj => sf1 _ (by omega) (Or.inl (by omega))
  have r2 := al_br_used (p := p) (P := P) (R := R) x ω1 μ1 s.base a11 hb0 hb64
  obtain ⟨ω2, r3, b0, b2, -, -, g3⟩ := al_bins (p := p) (P := P) (R := R) x ω1 μ1 req
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
  obtain ⟨ω3, r4, e5, e3, e8⟩ := (find_up (p := p) (P := P) (R := R) x ω2 μ1 s (sp - 152) _ hbits c1 b2 c7
    (by omega) hf1 hp1 hs1 hbU hHTs ⟨by omega, by omega⟩ hr1).2 hu
  obtain ⟨ω4, r5, f11, f6⟩ := (find_down (p := p) (P := P) (R := R) x ω3 μ1 s _ hbits
    (by rw [fget e8 0 (by decide) (by decide)]; exact b0) e5 e3 hs1 hbD hHTs hr1).2 hbin
  obtain ⟨ω5, r6, d7, d0, d5, d6, d1, -⟩ := an_ret (p := p) (P := P) (R := R) x ω4 μ1 (sp - 152)
    (by rw [fget f6 1 (by decide) (by decide), fget e8 1 (by decide) (by decide)]; exact c1) (by omega) hHTs
    ⟨by omega, by omega⟩ hr1
  refine ⟨ω5, μ1, (((((r1.trans r2).trans r3).trans r4).trans r5).trans r6).mono (by omega), by rw [d7, f11],
    ?_, ?_, ?_, ?_, ww1, sf1⟩
  · rw [d0, show sp - 152 + 144 = sp - 8 by omega]; exact rd_restore st0
  · rw [d5, show sp - 152 + 136 = sp - 16 by omega]; exact rd_restore st5
  · rw [d6, show sp - 152 + 128 = sp - 24 by omega]; exact rd_restore st6
  · rw [d1, h1]; congr 1; omega

/-- **41177 … 41398**, the heap in use: the frame, the bins of `req + 1`, the search to `bin`
    (the model's `findFirst`, rounded up, else rounded down), and its first chunk C with size word
    `w` picked: ω₁₁ = w / 2 against ω₁₂ = req + 1 (`alloc_entry` without the size check). -/
theorem alloc_pick {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (sp req bin C w : Nat) (hbits : BitsOk s.secondary s.primary s.heads)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat 1)
    (h9 : ω[9] = UInt64.ofNat req) (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb : rdN μ 206520 8 = s.base) (hb0 : s.base ≠ 0)
    (hp : rdN μ 206832 8 = s.primary) (hs : ∀ q, q < 38 → rdN μ (q * 8 + 204984 + 1544) 8 = s.secondary q)
    (hm : req + 1 ≤ 33554432)
    (hbin : (findFirst s (binUp (req + 1))).or (findFirst s (binDown (req + 1))) = some bin)
    (hC : rdN μ (196792 + 4 * bin) 4 = C) (hw : rdN μ (C + 4) 4 = w) (hC1 : C + 8 < 2147483648)
    {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hSTk : S0 + 152 ≤ sp ∧ sp ≤ S1)
    (hCT : 196608 ≤ C ∧ C + 16 ≤ HT) (hwr : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 41177 ω μ x 41398 ω' μ' x 120 ∧
      ω'[1] = UInt64.ofNat (sp - 152) ∧ ω'[11] = UInt64.ofNat (w / 2) ∧ ω'[12] = UInt64.ofNat (req + 1) ∧
      μ'.readN (sp - 8) 8 = Num.encodeLE 8 ω[0].toNat ∧ μ'.readN (sp - 16) 8 = Num.encodeLE 8 ω[5].toNat ∧
      μ'.readN (sp - 24) 8 = Num.encodeLE 8 ω[6].toNat ∧
      (∀ a, a < 4294967296 → (a < sp - 152 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) := by
  have hb64 : s.base < 18446744073709551616 := by rw [← hb]; exact rdN_lt64 μ _
  obtain ⟨ω1, μ1, r1, a1, a11, a12, st0, st5, st6, -, st32, sf1, ww1, g1⟩ :=
    al_pro (p := p) (P := P) (R := R) x ω μ sp 0 s.base h1 h7 (by rw [h8]) (by decide) hsp hsp1 hb (by omega) hSTk hwr
  have hr1 := (hwr.of_eq ww1).rd
  have tr : ∀ a n, a + n ≤ 2147483648 → rdN μ1 a n = rdN μ a n := fun a n h =>
    rdN_frame fun j hj => sf1 _ (by omega) (Or.inl (by omega))
  have r2 := al_br_used (p := p) (P := P) (R := R) x ω1 μ1 s.base a11 hb0 hb64
  obtain ⟨ω2, r3, b0, b2, -, b12, g3⟩ := al_bins (p := p) (P := P) (R := R) x ω1 μ1 req
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
  have fu := find_up (p := p) (P := P) (R := R) x ω2 μ1 s (sp - 152) _ hbits c1 b2 c7 (by omega) hf1 hp1 hs1 hbU hHTs ⟨by omega, by omega⟩ hr1
  obtain ⟨ω4, q, b, r45, hqb, hq, hb', d6, d2, fr4⟩ : ∃ ω4 q b, FreeStepsH p R 41297 ω2 μ1 x 41378 ω4 μ1 x 60 ∧
      q * 64 + b = bin ∧ q < 38 ∧ b < 64 ∧ ω4[6] = UInt64.ofNat q ∧ ω4[2] = UInt64.ofNat b ∧
      ∀ j : Fin 13, j.val ∉ [2, 3, 5, 6, 10, 11] → ω4[j] = ω2[j] := by
    cases hu : findFirst s (binUp (req + 1)) with
    | some bin' =>
      have : bin' = bin := by rw [hu] at hbin; exact Option.some.inj hbin
      subst this
      obtain ⟨ω4, q, b, r, e1, e2, e3, e4, e5, -, -, e8⟩ := fu.1 _ hu
      exact ⟨ω4, q, b, r.mono (by omega), e1, e2, e3, e4, e5, e8⟩
    | none =>
      rw [hu, Option.none_or] at hbin
      obtain ⟨ω3, r, e5, e3, e8⟩ := fu.2 hu
      obtain ⟨ω4, q, b, r', f1, f2, f3, f4, f5, f6⟩ := (find_down (p := p) (P := P) (R := R) x ω3 μ1 s _ hbits
        (by rw [fget e8 0 (by decide) (by decide)]; exact b0) e5 e3 hs1 hbD hHTs hr1).1 _ hbin
      exact ⟨ω4, q, b, (r.trans r').mono (by omega), f1, f2, f3, f4, f5,
        frame_trans f6 e8 (fun j hj => by simp at hj ⊢; omega) (fun j hj => by simp at hj ⊢; omega)⟩
  have k7 : ω4[7] = UInt64.ofNat 196792 := by rw [fget fr4 7 (by decide) (by decide)]; exact c7
  have k12 : ω4[12] = UInt64.ofNat (req + 1) := by rw [fget fr4 12 (by decide) (by decide)]; exact b12
  have hC' : rdN μ1 (196792 + 4 * (q * 64 + b)) 4 = C := by rw [hqb, tr _ _ (by omega)]; exact hC
  have hw' : rdN μ1 (C + 4) 4 = w := by rw [tr _ _ (by omega)]; exact hw
  obtain ⟨ω5, r5, -, e11, -, g5⟩ := al_pick (p := p) (P := P) (R := R) x ω4 μ1 q b C w (w / 2 * 0 + (req + 1))
    d6 d2 k7 (by simpa using k12) hq hb' hC' hw' (by omega) (by omega) hHTs hCT hr1
  refine ⟨ω5, μ1, ((((r1.trans r2).trans r3).trans r45).trans r5).mono (by omega),
    by rw [fget g5 1 (by decide) (by decide), fget fr4 1 (by decide) (by decide)]; exact c1, e11,
    by rw [fget g5 12 (by decide) (by decide)]; exact k12, st0, st5, st6, sf1, ww1⟩

/-- **41177 … 41423, the found chunk too small**: the first chunk of the bin the search finds has
    fewer units than `req + 1`; null returned, only the frame written. -/
theorem alloc_fail_small {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (sp req bin C w : Nat) (hbits : BitsOk s.secondary s.primary s.heads)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat 1)
    (h9 : ω[9] = UInt64.ofNat req) (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb : rdN μ 206520 8 = s.base) (hb0 : s.base ≠ 0)
    (hp : rdN μ 206832 8 = s.primary) (hs : ∀ q, q < 38 → rdN μ (q * 8 + 204984 + 1544) 8 = s.secondary q)
    (hm : req + 1 ≤ 33554432)
    (hbin : (findFirst s (binUp (req + 1))).or (findFirst s (binDown (req + 1))) = some bin)
    (hC : rdN μ (196792 + 4 * bin) 4 = C) (hw : rdN μ (C + 4) 4 = w) (hC1 : C + 8 < 2147483648)
    (hsmall : w / 2 < req + 1)
    {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hSTk : S0 + 152 ≤ sp ∧ sp ≤ S1)
    (hCT : 196608 ≤ C ∧ C + 16 ≤ HT) (hwr : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 41177 ω μ x 41423 ω' μ' x 130 ∧ ω'[7] = UInt64.ofNat 0 ∧
      ω'[0] = ω[0] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[1] = ω[1] ∧
      (∀ a, μ'.writable a = μ.writable a) ∧
      (∀ a, a < 4294967296 → (a < sp - 152 ∨ sp ≤ a) → μ'.read a = μ.read a) := by
  obtain ⟨ω1, μ1, r1, a1, a11, a12, st0, st5, st6, sf1, ww1⟩ := alloc_pick (p := p) (P := P) (R := R) x ω μ s
    sp req bin C w hbits h1 h7 h8 h9 hsp hsp1 hb hb0 hp hs hm hbin hC hw hC1 hHTs hSTk hCT hwr
  have r2 := al_size_small (p := p) (P := P) (R := R) x ω1 μ1 (w / 2) (req + 1) a11 a12 hsmall (by omega)
  obtain ⟨ω3, r3, d7, d0, d5, d6, d1, -⟩ := al_fail (p := p) (P := P) (R := R) x ω1 μ1 (sp - 152) a1 (by omega)
    hHTs ⟨by omega, by omega⟩ (hwr.of_eq ww1).rd
  refine ⟨ω3, μ1, ((r1.trans r2).trans r3).mono (by omega), d7, ?_, ?_, ?_, ?_, ww1, sf1⟩
  · rw [d0, show sp - 152 + 144 = sp - 8 by omega]; exact rd_restore st0
  · rw [d5, show sp - 152 + 136 = sp - 16 by omega]; exact rd_restore st5
  · rw [d6, show sp - 152 + 128 = sp - 24 by omega]; exact rd_restore st6
  · rw [d1, h1]; congr 1; omega

end Services.Bootstrap.Alloc
