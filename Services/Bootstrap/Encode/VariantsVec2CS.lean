import Services.Bootstrap.Encode.VariantsVecVec
import Services.Bootstrap.Encode.VariantsVec2CSSegs
import Services.Bootstrap.Encode.VariantsVec2CSSegs2
import Services.Bootstrap.Decode.CreateServiceElem

/-!
# `Instruction::encode_to`: `CreateService` (dispatch index 0)

`CreateService` (the enum's dataful variant; its slot as `Decode.CreateServiceElem` writes it) holds
its `Option<Vec<u8>>` ov in the words at 0, 8, 16 (the capacity word at 0 is the niche 2^64 − 1 for
`None`), the `Option<u32>` ou's tag word at 24 and value at 28, the hash h at 32, the `u64`s u₁ … u₄ at
64 … 88, the 128-octet array at 96 and the `u64` u₅ at 224 (`CSFields`). The arm (17905, after the
dispatch to index 0, `dispatch0`) appends the fields in that order (GP v0.8.0 Appendix C):

  0 :: (h ++ u₁ ++ u₂ ++ u₃ ++ u₄ ++ arr ++ ov ++ u₅ ++ ou)

with ov = [0] (`create_service_none`) or 1 :: ℰ(n) ++ bytes (`create_service_some`, the n < 2^32
octets at q; the code traps at 20397 for n ≥ 2^32), the encoding `Decode.CreateServiceElem` decodes.
`cs_head` is the shared run to the `Option<Vec<u8>>` (18058), `cs_tail` the shared run from u₅ (20239)
to the end 20329. The `Some` case reads the heap octets `VecSrc q n` and calls the length prefix
(`EncOkMD 192`); the `None` case reads none and calls no prefix (`EncOkMD 136`). Both are lifted to 232.
Bridges: `createServiceSomeRep_iff` (the decode side's `CreateServiceSomeRep`, its q existential) and
`create_service_empty_232` (`CreateServiceEmptyRep`, `Some([])`, as the `Some` case with q = 1, n = 0).
-/

namespace Services.Bootstrap.Encode.Enc

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeA
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Encode.EncMD Services.Bootstrap.Decode.CreateServiceElem

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- From 30145 to `CreateService`'s arm (17905), in `StD []`, for a first word W below 2^63 or the niche
    2^64 − 1: ω₅ = 2^64 − 1, ω₆ = W, the writer in ω₁₀ and the value in ω₁₁. -/
theorem start0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    {D F S v cap ptr len N ret t' : Nat} (L : LayD P D F S v cap ptr len N ret t' μ) (hD : 136 ≤ D)
    (W : Nat) (hW : W < 9223372036854775808 ∨ W = 18446744073709551615)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat F) (h7 : ω[7] = UInt64.ofNat S)
    (h8 : ω[8] = UInt64.ofNat v) (hW8 : μ.readN S 8 = Num.encodeLE 8 W)
    (tab : μ.readN 67376 100 = table) (hrt : ∀ a, 67376 ≤ a → a < 67476 → μ.readable a = true) :
    ∃ ω1 μ1, FreeStepsH p R 30145 ω μ x 17905 ω1 μ1 x 24 ∧
      StD D F v ptr len ret ω[5].toNat ω[6].toNat μ [] ω1 μ1 ∧
      ω1[5] = UInt64.ofNat 18446744073709551615 ∧ ω1[6] = UInt64.ofNat W ∧
      ω1[10] = UInt64.ofNat v ∧ ω1[11] = UInt64.ofNat S := by
  have hF := L.hF; have hF' := L.hF'; have hS := L.hS; have hS' := L.hS'; have hSF := L.hSF
  have hv := L.hv; have hvF := L.hvF
  have h5 : ω[5] = UInt64.ofNat ω[5].toNat := UInt64.ofNat_toNat.symm
  have h6 : ω[6] = UInt64.ofNat ω[6].toNat := UInt64.ofNat_toNat.symm
  have hret := L.hret
  obtain ⟨ω1, μ1, run1, a1, a5, a6, a10, a11, a0', a5', a6', av, afr, ard, awr⟩ := dispatch0 (p := p) (P := P)
    (R := R) x ω μ F S v ret ω[5].toNat ω[6].toNat W hW ⟨by omega, hF'⟩ h0 h1 h5 h6 h7 h8 (by omega)
    (UInt64.toNat_lt _) (UInt64.toNat_lt _) (by omega) (by omega) (by omega) hW8 tab hrt
    (fun a h1 h2 => L.hrS a h1 (by omega)) (fun a h1 h2 => L.hwF a (by omega) h2)
  refine ⟨ω1, μ1, run1, ⟨a1, a0', a5', a6', av, ?_, by simp [Memory.readN],
    fun a h0 h1 _ _ => afr a h0 (by omega), ard, awr⟩, a5, a6, a10, a11⟩
  rw [Memory.readN_congr (fun j hj => afr _ (by omega) (by omega))]; simpa using L.vl

/-- **A `u64` piece of `CreateService`** (`CSWord e r off`): from `StD pre` at e with S at sp, `StD (pre ++
    the 8 octets at S + off)` at the call's return e', S kept at sp, ω₅ and ω₆ kept. -/
theorem csWordD {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ μ0 : Memory)
    {D F S v cap ptr len N ret t r5 r6 : Nat} {pre : List UInt8} (L : LayD P D F S v cap ptr len N ret t μ0)
    (hD : 136 ≤ D) (st : StD D F v ptr len ret r5 r6 μ0 pre ω μ) (e r off e' : Nat) (hc : CSWord e r off)
    (hje : P.jumpTable.getD (r / 2 - 1) 0 = e') (hbe : P.isBlockStart e' = true)
    (hS0 : μ.readN (F - 56) 8 = Num.encodeLE 8 S) (hn : pre.length + 8 ≤ N) :
    ∃ ω' μ', FreeStepsH p R e ω μ x e' ω' μ' x 428 ∧
      StD D F v ptr len ret r5 r6 μ0 (pre ++ μ0.readN (S + off) 8) ω' μ' ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      μ'.readN (F - 56) 8 = Num.encodeLE 8 S := by
  have hF := L.hF; have hF' := L.hF'; have hv := L.hv; have hS := L.hS; have hS' := L.hS'
  have hr : 0 < r ∧ r ≤ 2806 ∧ r % 2 = 0 := by unfold CSWord at hc; omega
  have hoff : off + 8 ≤ 232 := by unfold CSWord at hc; omega
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bt, bfr, brd, bwr⟩ := seg_csWord (p := p) (P := P) (R := R)
    x ω μ e r off (F - 56) v S hc (by omega) (by omega) (by omega) st.h1 hS0
    (by rw [show F - 56 + 16 = F - 40 by omega]; exact st.sv)
    (fun a h1 h2 => by rw [st.rd]; exact L.hrS a (by omega) (by omega))
    (fun a h1 h2 => by rw [st.wr]; exact L.hwF a (by omega) (by omega))
  have st2 := st.scratch L hD (by omega) b1 (fun a h0 h1 => bfr a h0 (by omega)) brd bwr
  rw [st.slot L (by omega) off 8 hoff] at bt
  obtain ⟨ω3, μ3, run3, st3, c5, c6, cF⟩ := scratchD (p := p) (P := P) (R := R) x ω2 μ2 μ0 L hD st2
    (μ0.readN (S + off) 8) 8 r e' (by simp [Memory.readN]) (by decide) b0 b7 b8 b9 hr hje hbe (by omega) bt
  refine ⟨ω3, μ3, (run2.trans run3).mono (by omega), st3, c5.trans b5, c6.trans b6, ?_⟩
  rw [Memory.readN_congr (fun j hj => cF _ (by omega) (by omega)),
    Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))]; exact hS0

/-- **A direct piece of `CreateService`** (`CSDirect e r off n`: the hash or the array): from `StD pre` at e
    with S at sp, `StD (pre ++ the n octets at S + off)` at the call's return e', S kept at sp, ω₅ and ω₆
    kept. -/
theorem csDirectD {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ μ0 : Memory)
    {D F S v cap ptr len N ret t r5 r6 : Nat} {pre : List UInt8} (L : LayD P D F S v cap ptr len N ret t μ0)
    (hD : 136 ≤ D) (st : StD D F v ptr len ret r5 r6 μ0 pre ω μ) (e r off n e' : Nat) (hc : CSDirect e r off n)
    (hje : P.jumpTable.getD (r / 2 - 1) 0 = e') (hbe : P.isBlockStart e' = true)
    (hS0 : μ.readN (F - 56) 8 = Num.encodeLE 8 S) (hn : pre.length + n ≤ N) :
    ∃ ω' μ', FreeStepsH p R e ω μ x e' ω' μ' x (7 * n + 366) ∧
      StD D F v ptr len ret r5 r6 μ0 (pre ++ μ0.readN (S + off) n) ω' μ' ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      μ'.readN (F - 56) 8 = Num.encodeLE 8 S := by
  have hF := L.hF; have hF' := L.hF'; have hv := L.hv; have hS := L.hS; have hS' := L.hS'
  have hSF := L.hSF; have hdS := L.hdS; have hd := L.hd
  have hr : 0 < r ∧ r ≤ 2806 ∧ r % 2 = 0 := by unfold CSDirect at hc; omega
  have hoff : off + n ≤ 232 ∧ 32 ≤ off := by unfold CSDirect at hc; omega
  obtain ⟨ω2, run2, b0, b1, b5, b6, b7, b8, b9⟩ := seg_csDirect (p := p) (P := P) (R := R) x ω μ e r off n
    (F - 56) v S hc (by omega) (by omega) (by omega) st.h1 hS0
    (by rw [show F - 56 + 16 = F - 40 by omega]; exact st.sv)
    (fun a h1 h2 => by rw [st.rd]; exact Memory.readable_of_writable (L.hwF a (by omega) (by omega)))
  obtain ⟨ω3, μ3, run3, st3, c5, c6, cF⟩ := ext_stepD (p := p) (P := P) (R := R) x ω2 μ μ0 L hD
    ⟨b1.trans st.h1, st.s0, st.s5, st.s6, st.sv, st.vl, st.out, st.keep, st.rd, st.wr⟩ (S + off) n r e'
    b0 b7 b8 b9 hr hje hbe hn ⟨by omega, by omega⟩ (by omega) (by omega)
    (fun a h1 h2 => by rw [st.rd]; exact L.hrS a (by omega) (by omega))
  rw [st.slot L (by omega) off n hoff.1] at st3
  refine ⟨ω3, μ3, (run2.trans run3).mono (by omega), st3, c5.trans b5, c6.trans b6, ?_⟩
  rw [Memory.readN_congr (fun j hj => cF _ (by omega) (by omega))]; exact hS0

/-- **`CreateService`'s head** (30145 … 18051): from the dispatch with first word W (below 2^63 or the
    niche), the tag 0, the hash h (S + 32), the `u64`s u₁ … u₄ (S + 64 … S + 88) and the array (S + 96)
    appended, at 18058 with ω₅ = 2^64 − 1, ω₆ = W and S at sp. -/
theorem cs_head {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    {D F S v cap ptr len N ret t : Nat} (L : LayD P D F S v cap ptr len N ret t μ) (hD : 136 ≤ D)
    (W : Nat) (hW : W < 9223372036854775808 ∨ W = 18446744073709551615)
    (h u1 u2 u3 u4 arr : List UInt8) (hN : 193 ≤ N)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat F) (h7 : ω[7] = UInt64.ofNat S)
    (h8 : ω[8] = UInt64.ofNat v) (hW8 : μ.readN S 8 = Num.encodeLE 8 W)
    (c32 : μ.readN (S + 32) 32 = h) (c64 : μ.readN (S + 64) 8 = u1) (c72 : μ.readN (S + 72) 8 = u2)
    (c80 : μ.readN (S + 80) 8 = u3) (c88 : μ.readN (S + 88) 8 = u4) (c96 : μ.readN (S + 96) 128 = arr)
    (tab : μ.readN 67376 100 = table) (hrt : ∀ a, 67376 ≤ a → a < 67476 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 30145 ω μ x 18058 ω' μ' x 4000 ∧
      StD D F v ptr len ret ω[5].toNat ω[6].toNat μ (UInt8.ofNat 0 :: (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr)) ω' μ' ∧
      ω'[5] = UInt64.ofNat 18446744073709551615 ∧ ω'[6] = UInt64.ofNat W ∧
      μ'.readN (F - 56) 8 = Num.encodeLE 8 S := by
  have hF := L.hF; have hF' := L.hF'; have hS := L.hS; have hS' := L.hS'; have hv := L.hv
  have lh : h.length = 32 := by rw [← c32]; simp [Memory.readN]
  have l1 : u1.length = 8 := by rw [← c64]; simp [Memory.readN]
  have l2 : u2.length = 8 := by rw [← c72]; simp [Memory.readN]
  have l3 : u3.length = 8 := by rw [← c80]; simp [Memory.readN]
  have l4 : u4.length = 8 := by rw [← c88]; simp [Memory.readN]
  have la : arr.length = 128 := by rw [← c96]; simp [Memory.readN]
  obtain ⟨ω1, μ1, run1, st1, a5, a6, a10, a11⟩ := start0 (p := p) (P := P) (R := R) x ω μ L hD W hW h0 h1 h7 h8
    hW8 tab hrt
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bt, bS, bfr, brd, bwr⟩ := seg_17905 (p := p) (P := P)
    (R := R) x ω1 μ1 (F - 56) v S (by omega) (by omega) (by omega) st1.h1 a10 a11
    (fun a h1 h2 => by rw [st1.wr]; exact L.hwF a (by omega) (by omega))
  have st2 := st1.scratch L hD (by simp) b1 (fun a h0 h1 => bfr a h0 (by omega) (by omega)) brd bwr
  obtain ⟨ω3, μ3, run3, st3, c5, c6, cF⟩ := scratchD (p := p) (P := P) (R := R) x ω2 μ2 μ L hD st2
    [UInt8.ofNat 0] 1 704 17925 rfl (by decide) b0 b7 b8 b9 ⟨by decide, by decide, by decide⟩ jte_351 bs_17925
    (by simp <;> omega) bt
  have m3 : μ3.readN (F - 56) 8 = Num.encodeLE 8 S := by
    rw [Memory.readN_congr (fun j hj => cF _ (by omega) (by omega))]; exact bS
  obtain ⟨ω4, μ4, run4, st4, d5, d6, m4⟩ := csDirectD (p := p) (P := P) (R := R) x ω3 μ3 μ L hD st3 17925 706 32
    32 17943 (Or.inl ⟨rfl, rfl, rfl, rfl⟩) jte_352 bs_17943 m3 (by simp <;> omega)
  obtain ⟨ω5, μ5, run5, st5, e5, e6, m5⟩ := csWordD (p := p) (P := P) (R := R) x ω4 μ4 μ L hD st4 17943 708 64
    17967 (Or.inl ⟨rfl, rfl, rfl⟩) jte_353 bs_17967 m4 (by simp [c32, lh]; omega)
  obtain ⟨ω6, μ6, run6, st6, f5, f6, m6⟩ := csWordD (p := p) (P := P) (R := R) x ω5 μ5 μ L hD st5 17967 710 72
    17991 (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) jte_354 bs_17991 m5 (by simp [c32, c64, lh, l1]; omega)
  obtain ⟨ω7, μ7, run7, st7, g5, g6, m7⟩ := csWordD (p := p) (P := P) (R := R) x ω6 μ6 μ L hD st6 17991 712 80
    18015 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))) jte_355 bs_18015 m6
    (by simp [c32, c64, c72, lh, l1, l2]; omega)
  obtain ⟨ω8, μ8, run8, st8, i5, i6, m8⟩ := csWordD (p := p) (P := P) (R := R) x ω7 μ7 μ L hD st7 18015 714 88
    18039 (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))) jte_356 bs_18039 m7
    (by simp [c32, c64, c72, c80, lh, l1, l2, l3]; omega)
  obtain ⟨ω9, μ9, run9, st9, j5, j6, m9⟩ := csDirectD (p := p) (P := P) (R := R) x ω8 μ8 μ L hD st8 18039 716 96
    128 18058 (Or.inr ⟨rfl, rfl, rfl, rfl⟩) jte_357 bs_18058 m8
    (by simp [c32, c64, c72, c80, c88, lh, l1, l2, l3, l4]; omega)
  refine ⟨ω9, μ9, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans
    (run8.trans run9)))))))).mono (by omega), st9.cast ?_, by rw [j5, i5, g5, f5, e5, d5, c5, b5, a5],
    by rw [j6, i6, g6, f6, e6, d6, c6, b6, a6], m9⟩
  rw [c32, c64, c72, c80, c88, c96]; simp

/-- **`CreateService`'s tail** (20239 … 20322): from `StD pre` at 20239 with the writer in ω₅ and S at sp,
    u₅ (S + 224) and the `Option<u32>` ou (its tag word at S + 24, its value at S + 28) appended, at the
    end 20329. -/
theorem cs_tail {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ μ1 : Memory)
    {D F S v cap ptr len N ret t r5 r6 : Nat} {pre : List UInt8} (L : LayD P D F S v cap ptr len N ret t μ)
    (hD : 136 ≤ D) (st : StD D F v ptr len ret r5 r6 μ pre ω μ1) (u5 ou : List UInt8) (hou : OptU32Enc ou)
    (hN : pre.length + 8 + ou.length ≤ N) (h5 : ω[5] = UInt64.ofNat v)
    (hS0 : μ1.readN (F - 56) 8 = Num.encodeLE 8 S) (c224 : μ.readN (S + 224) 8 = u5)
    (c24 : μ.readN (S + 24) 4 = Num.encodeLE 4 (ou.headD 0).toNat)
    (c28 : ou.headD 0 = 1 → μ.readN (S + 28) 4 = ou.tail) :
    ∃ ω' μ', FreeStepsH p R 20239 ω μ1 x 20329 ω' μ' x 1500 ∧
      StD D F v ptr len ret r5 r6 μ (pre ++ u5 ++ ou) ω' μ' := by
  have hF := L.hF; have hF' := L.hF'; have hv := L.hv; have hS := L.hS; have hS' := L.hS'
  have l5 : u5.length = 8 := by rw [← c224]; simp [Memory.readN]
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bt, bfr, brd, bwr⟩ := seg_20239 (p := p) (P := P) (R := R)
    x ω μ1 (F - 56) v S (by omega) (by omega) (by omega) st.h1 h5 hS0
    (fun a h1 h2 => by rw [st.rd]; exact L.hrS a (by omega) (by omega))
    (fun a h1 h2 => by rw [st.wr]; exact L.hwF a (by omega) (by omega))
  have st2 := st.scratch L hD (by omega) b1 (fun a h0 h1 => bfr a h0 (by omega)) brd bwr
  rw [st.slot L (by omega) 224 8 (by decide), c224] at bt
  obtain ⟨ω3, μ3, run3, st3, c5, c6, _⟩ := scratchD (p := p) (P := P) (R := R) x ω2 μ2 μ L hD st2 u5 8 912 20263
    l5 (by decide) b0 b7 b8 b9 ⟨by decide, by decide, by decide⟩ jte_455 bs_20263 (by omega) bt
  have k24 : μ3.readN (S + 24) 4 = μ.readN (S + 24) 4 := st3.slot L (by simp <;> omega) 24 4 (by decide)
  have k28 : μ3.readN (S + 28) 4 = μ.readN (S + 28) 4 := st3.slot L (by simp <;> omega) 28 4 (by decide)
  have h5' : ω3[5] = UInt64.ofNat v := by rw [c5, b5, h5]
  rcases hou with rfl | ⟨u, hu, rfl⟩
  · have r24 : rdN μ3 (S + 24) 4 = 0 := by
      show Num.decodeLE _ = _; rw [k24, c24]; rfl
    obtain ⟨ω4, μ4, run4, d0, d1, d5, d6, d7, d8, d9, dt, dfr, drd, dwr⟩ := seg_20263_none (p := p) (P := P)
      (R := R) x ω3 μ3 (F - 56) v S (by omega) (by omega) (by omega) st3.h1 h5' (by rw [c6, b6]) r24
      (fun a h1 h2 => by rw [st3.rd]; exact L.hrS a (by omega) (by omega))
      (fun a h1 h2 => by rw [st3.wr]; exact L.hwF a (by omega) (by omega))
    have st4 := st3.scratch L hD (by simp <;> omega) d1 (fun a h0 h1 => dfr a h0 (by omega)) drd dwr
    obtain ⟨ω5, μ5, run5, st5, _, _, _⟩ := scratchD (p := p) (P := P) (R := R) x ω4 μ4 μ L hD st4
      [UInt8.ofNat 0] 1 916 20329 rfl (by decide) d0 d7 d8 d9 ⟨by decide, by decide, by decide⟩ jte_457 bs_20329
      (by simp at hN ⊢; omega) dt
    exact ⟨ω5, μ5, (run2.trans (run3.trans (run4.trans run5))).mono (by omega),
      st5.cast (by simp)⟩
  · have r24 : rdN μ3 (S + 24) 4 = 1 := by
      show Num.decodeLE _ = _
      rw [k24, c24, show ((1 :: u : List UInt8).headD 0).toNat = 1 from rfl]; rfl
    have c28' := c28 rfl
    simp only [List.tail_cons] at c28'
    obtain ⟨ω4, μ4, run4, d0, d1, d5, d6, d7, d8, d9, dt, dfr, drd, dwr⟩ := seg_20263_some (p := p) (P := P)
      (R := R) x ω3 μ3 (F - 56) v S (by omega) (by omega) (by omega) st3.h1 h5' (by rw [c6, b6]) r24
      (fun a h1 h2 => by rw [st3.rd]; exact L.hrS a (by omega) (by omega))
      (fun a h1 h2 => by rw [st3.wr]; exact L.hwF a (by omega) (by omega))
    have st4 := st3.scratch L hD (by simp <;> omega) d1 (fun a h0 h1 => dfr a h0 (by omega)) drd dwr
    obtain ⟨ω5, μ5, run5, st5, e5, e6, _⟩ := scratchD (p := p) (P := P) (R := R) x ω4 μ4 μ L hD st4
      [UInt8.ofNat 1] 1 914 20288 rfl (by decide) d0 d7 d8 d9 ⟨by decide, by decide, by decide⟩ jte_456 bs_20288
      (by simp at hN ⊢; omega) dt
    obtain ⟨ω6, μ6, run6, f0, f1, f5, f6, f7, f8, f9, ft, ffr, frd, fwr⟩ := seg_20288 (p := p) (P := P)
      (R := R) x ω5 μ5 (F - 56) v S (by omega) (by omega) (by omega) st5.h1 (by rw [e5, d5, h5'])
      (by rw [e6, d6, c6, b6])
      (fun a h1 h2 => by rw [st5.rd]; exact L.hrS a (by omega) (by omega))
      (fun a h1 h2 => by rw [st5.wr]; exact L.hwF a (by omega) (by omega))
    have st6 := st5.scratch L hD (by simp at hN ⊢; omega) f1 (fun a h0 h1 => ffr a h0 (by omega)) frd fwr
    rw [st5.slot L (by simp at hN ⊢; omega) 28 4 (by decide), c28'] at ft
    obtain ⟨ω7, μ7, run7, st7, _, _, _⟩ := scratchD (p := p) (P := P) (R := R) x ω6 μ6 μ L hD st6
      u 4 916 20329 hu (by decide) f0 f7 f8 f9 ⟨by decide, by decide, by decide⟩ jte_457 bs_20329
      (by simp [hu] at hN ⊢; omega) ft
    exact ⟨ω7, μ7, (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7))))).mono (by omega),
      st7.cast (by simp)⟩

/-- **`CreateService` with `Option<Vec<u8>>` = `None`** (dispatch index 0): a value whose first word is
    the niche 2^64 − 1 and whose other fields are as `CSFields` gives (`CreateServiceNoneRep`, as
    `Decode.CreateServiceElem` writes it) encodes to 0 :: (h ++ u₁ ++ u₂ ++ u₃ ++ u₄ ++ arr ++ [0] ++ u₅ ++ ou)
    (GP v0.8.0 Appendix C). It reads no heap octets. -/
theorem create_service_none {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P]
    (h u1 u2 u3 u4 arr u5 ou : List UInt8) (hh : h.length = 32) (h1 : u1.length = 8) (h2 : u2.length = 8)
    (h3 : u3.length = 8) (h4 : u4.length = 8) (harr : arr.length = 128) (h5 : u5.length = 8)
    (hou : OptU32Enc ou) :
    EncOkMD p P 136 (0 :: (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ [0] ++ u5 ++ ou))
      (fun bs _ => CreateServiceNoneRep h u1 u2 u3 u4 arr u5 ou bs) (fun _ => False) := by
  intro X R x ω μ F S v cap ptr len ret t g0 g1 g7 g8 rep L tab hrt _
  obtain ⟨r0, f24, f28, f32, f64, f72, f80, f88, f96, f224⟩ := rep
  have hW8 : μ.readN S 8 = Num.encodeLE 8 18446744073709551615 := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact r0
  have c24 : μ.readN (S + 24) 4 = Num.encodeLE 4 (ou.headD 0).toNat := by
    rw [← slot_take μ S 24 4 (by decide)]; exact f24
  have c28 : ou.headD 0 = 1 → μ.readN (S + 28) 4 = ou.tail := fun h1 => by
    rw [← slot_take μ S 28 4 (by decide)]; exact f28 h1
  have c32 : μ.readN (S + 32) 32 = h := by rw [← slot_take μ S 32 32 (by decide)]; exact f32
  have c64 : μ.readN (S + 64) 8 = u1 := by rw [← slot_take μ S 64 8 (by decide)]; exact f64
  have c72 : μ.readN (S + 72) 8 = u2 := by rw [← slot_take μ S 72 8 (by decide)]; exact f72
  have c80 : μ.readN (S + 80) 8 = u3 := by rw [← slot_take μ S 80 8 (by decide)]; exact f80
  have c88 : μ.readN (S + 88) 8 = u4 := by rw [← slot_take μ S 88 8 (by decide)]; exact f88
  have c96 : μ.readN (S + 96) 128 = arr := by rw [← slot_take μ S 96 128 (by decide)]; exact f96
  have c224 : μ.readN (S + 224) 8 = u5 := by rw [← slot_take μ S 224 8 (by decide)]; exact f224
  have hF := L.hF; have hF' := L.hF'; have hS := L.hS; have hS' := L.hS'; have hv := L.hv
  have hol := hou.length
  have hN : (0 :: (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ [0] ++ u5 ++ ou) : List UInt8).length =
      202 + ou.length := by simp [hh, h1, h2, h3, h4, harr, h5]; omega
  obtain ⟨ω1, μ1, run1, st1, a5, a6, m1⟩ := cs_head (p := p) (P := P) (R := R) x ω μ L (by decide)
    18446744073709551615 (Or.inr rfl) h u1 u2 u3 u4 arr (by omega) g0 g1 g7 g8 hW8 c32 c64 c72 c80 c88 c96 tab hrt
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b7, b8, b9, bt, bfr, brd, bwr⟩ := seg_18058_none (p := p) (P := P) (R := R)
    x ω1 μ1 (F - 56) v (by omega) (by omega) st1.h1 a5 a6
    (by rw [show F - 56 + 16 = F - 40 by omega]; exact st1.sv)
    (fun a h1 h2 => by rw [st1.wr]; exact L.hwF a (by omega) (by omega))
  have st2 := st1.scratch L (by decide) (by simp [hh, h1, h2, h3, h4, harr]; omega) b1
    (fun a h0 h1 => bfr a h0 (by omega)) brd bwr
  obtain ⟨ω3, μ3, run3, st3, c5, _, cF⟩ := scratchD (p := p) (P := P) (R := R) x ω2 μ2 μ L (by decide) st2
    [UInt8.ofNat 0] 1 910 20239 rfl (by decide) b0 b7 b8 b9 ⟨by decide, by decide, by decide⟩ jte_454 bs_20239
    (by simp [hh, h1, h2, h3, h4, harr]; omega) bt
  have m3 : μ3.readN (F - 56) 8 = Num.encodeLE 8 S := by
    rw [Memory.readN_congr (fun j hj => cF _ (by omega) (by omega)),
      Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))]; exact m1
  obtain ⟨ω4, μ4, run4, st4⟩ := cs_tail (p := p) (P := P) (R := R) x ω3 μ μ3 L (by decide) st3 u5 ou hou
    (by simp [hh, h1, h2, h3, h4, harr]; omega) (by rw [c5, b5]) m3 c224 c24 c28
  exact closeD L (by decide) 20329 _ (by decide) (by rw [hN]; omega)
    (run1.trans (run2.trans (run3.trans run4))) (st4.cast (by simp))

/-- `create_service_none` at the depth 232. -/
theorem create_service_none_232 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P]
    (h u1 u2 u3 u4 arr u5 ou : List UInt8) (hh : h.length = 32) (h1 : u1.length = 8) (h2 : u2.length = 8)
    (h3 : u3.length = 8) (h4 : u4.length = 8) (harr : arr.length = 128) (h5 : u5.length = 8)
    (hou : OptU32Enc ou) :
    EncOkMD p P 232 (0 :: (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ [0] ++ u5 ++ ou))
      (fun bs _ => CreateServiceNoneRep h u1 u2 u3 u4 arr u5 ou bs) (fun _ => False) :=
  (create_service_none h u1 u2 u3 u4 arr u5 ou hh h1 h2 h3 h4 harr h5 hou).mono (by decide)

/-- **`CreateService` with `Option<Vec<u8>>` = `Some(bytes)`'s slot, with the octets at q**:
    `CreateServiceSomeRep` with its q given. -/
def CSSomeRepAt (q n : Nat) (bytes h u1 u2 u3 u4 arr u5 ou : List UInt8) (bs : List UInt8) (μ : Memory) :
    Prop :=
  bs.take 8 = Num.encodeLE 8 n ∧ (bs.drop 8).take 8 = Num.encodeLE 8 q ∧
    (bs.drop 16).take 8 = Num.encodeLE 8 n ∧ μ.readN q n = bytes ∧ CSFields h u1 u2 u3 u4 arr u5 ou bs

/-- The decode side's `CreateServiceSomeRep` is `CSSomeRepAt` for some q. -/
theorem createServiceSomeRep_iff (n : Nat) (bytes h u1 u2 u3 u4 arr u5 ou bs : List UInt8) (μ : Memory) :
    CreateServiceSomeRep n bytes h u1 u2 u3 u4 arr u5 ou bs μ ↔
      ∃ q, CSSomeRepAt q n bytes h u1 u2 u3 u4 arr u5 ou bs μ := by
  constructor
  · rintro ⟨⟨q, h0, h1, h2, h3⟩, h4⟩; exact ⟨q, h0, h1, h2, h3, h4⟩
  · rintro ⟨q, h0, h1, h2, h3, h4⟩; exact ⟨⟨q, h0, h1, h2, h3⟩, h4⟩

/-- **`CreateService` with `Option<Vec<u8>>` = `Some(bytes)`** (dispatch index 0): a value holding the
    `Vec` `{cap n, ptr q, len n}` at 0 whose n < 2^32 octets at q are `bytes`, and the other fields as
    `CSFields` gives (`CSSomeRepAt`), encodes to
    0 :: (h ++ u₁ ++ u₂ ++ u₃ ++ u₄ ++ arr ++ (1 :: ℰ(n) ++ bytes) ++ u₅ ++ ou) (GP v0.8.0 Appendix C),
    reading the heap octets `VecSrc q n`. The code traps (20397) for n ≥ 2^32. -/
theorem create_service_some {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (q n : Nat) (bytes : List UInt8) (hbn : bytes.length = n) (hn : n < 4294967296)
    (hq64 : q < 18446744073709551616) (hq : 0 < n → 65536 ≤ q)
    (h u1 u2 u3 u4 arr u5 ou : List UInt8) (hh : h.length = 32) (h1 : u1.length = 8) (h2 : u2.length = 8)
    (h3 : u3.length = 8) (h4 : u4.length = 8) (harr : arr.length = 128) (h5 : u5.length = 8)
    (hou : OptU32Enc ou) :
    EncOkMD p P 192 (0 :: (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ (1 :: (Blob.encodeNat n ++ bytes)) ++ u5 ++ ou))
      (CSSomeRepAt q n bytes h u1 u2 u3 u4 arr u5 ou) (VecSrc q n) := by
  intro X R x ω μ F S v cap ptr len ret t g0 g1 g7 g8 rep L tab hrt hsrc
  obtain ⟨r0, r8, r16, rb, f24, f28, f32, f64, f72, f80, f88, f96, f224⟩ := rep
  have hW8 : μ.readN S 8 = Num.encodeLE 8 n := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact r0
  have c8 : μ.readN (S + 8) 8 = Num.encodeLE 8 q := by rw [← slot_take μ S 8 8 (by decide)]; exact r8
  have c16 : μ.readN (S + 16) 8 = Num.encodeLE 8 n := by rw [← slot_take μ S 16 8 (by decide)]; exact r16
  have c24 : μ.readN (S + 24) 4 = Num.encodeLE 4 (ou.headD 0).toNat := by
    rw [← slot_take μ S 24 4 (by decide)]; exact f24
  have c28 : ou.headD 0 = 1 → μ.readN (S + 28) 4 = ou.tail := fun h1 => by
    rw [← slot_take μ S 28 4 (by decide)]; exact f28 h1
  have c32 : μ.readN (S + 32) 32 = h := by rw [← slot_take μ S 32 32 (by decide)]; exact f32
  have c64 : μ.readN (S + 64) 8 = u1 := by rw [← slot_take μ S 64 8 (by decide)]; exact f64
  have c72 : μ.readN (S + 72) 8 = u2 := by rw [← slot_take μ S 72 8 (by decide)]; exact f72
  have c80 : μ.readN (S + 80) 8 = u3 := by rw [← slot_take μ S 80 8 (by decide)]; exact f80
  have c88 : μ.readN (S + 88) 8 = u4 := by rw [← slot_take μ S 88 8 (by decide)]; exact f88
  have c96 : μ.readN (S + 96) 128 = arr := by rw [← slot_take μ S 96 128 (by decide)]; exact f96
  have c224 : μ.readN (S + 224) 8 = u5 := by rw [← slot_take μ S 224 8 (by decide)]; exact f224
  have hF := L.hF; have hF' := L.hF'; have hS := L.hS; have hS' := L.hS'; have hv := L.hv
  have hol := hou.length
  have hE := encodeNat_pos n
  have hN : (0 :: (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ (1 :: (Blob.encodeNat n ++ bytes)) ++ u5 ++ ou) :
      List UInt8).length = 202 + (Blob.encodeNat n).length + n + ou.length := by
    simp [hh, h1, h2, h3, h4, harr, h5, hbn]; omega
  have hL0 : (UInt8.ofNat 0 :: (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr)).length = 193 := by
    simp [hh, h1, h2, h3, h4, harr]
  obtain ⟨ω1, μ1, run1, st1, a5, a6, m1⟩ := cs_head (p := p) (P := P) (R := R) x ω μ L (by decide) n
    (Or.inl (by omega)) h u1 u2 u3 u4 arr (by omega) g0 g1 g7 g8 hW8 c32 c64 c72 c80 c88 c96 tab hrt
  -- the option's tag
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b7, b8, b9, bt, bfr, brd, bwr⟩ := seg_18058_some (p := p) (P := P) (R := R)
    x ω1 μ1 (F - 56) v n (by omega) (by omega) (by omega) st1.h1 a5 a6
    (by rw [show F - 56 + 16 = F - 40 by omega]; exact st1.sv)
    (fun a h1 h2 => by rw [st1.wr]; exact L.hwF a (by omega) (by omega))
  have st2 := st1.scratch L (by decide) (by omega) b1 (fun a h0 h1 => bfr a h0 (by omega)) brd bwr
  obtain ⟨ω3, μ3, run3, st3, c5, _, cF⟩ := scratchD (p := p) (P := P) (R := R) x ω2 μ2 μ L (by decide) st2
    [UInt8.ofNat 1] 1 718 18084 rfl (by decide) b0 b7 b8 b9 ⟨by decide, by decide, by decide⟩ jte_358 bs_18084
    (by simp <;> omega) bt
  have m3 : μ3.readN (F - 56) 8 = Num.encodeLE 8 S := by
    rw [Memory.readN_congr (fun j hj => cF _ (by omega) (by omega)),
      Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))]; exact m1
  -- the length prefix
  obtain ⟨ω4, μ4, run4, d0, d1, d5, d6, d7, d8, dq, dn, dfr, drd, dwr⟩ := seg_18084 (p := p) (P := P) (R := R)
    x ω3 μ3 (F - 56) v S q n (by omega) (by omega) (by omega) hq64 hn st3.h1 (by rw [c5, b5]) m3
    (by rw [st3.slot L (by simp <;> omega) 8 8 (by decide)]; exact c8)
    (by rw [st3.slot L (by simp <;> omega) 16 8 (by decide)]; exact c16)
    (fun a h1 h2 => by rw [st3.rd]; exact L.hrS a (by omega) (by omega))
    (fun a h1 h2 => by rw [st3.wr]; exact L.hwF a (by omega) (by omega))
  have st4 := st3.scratch L (by decide) (by simp <;> omega) d1 (fun a h0 h1 => dfr a h0 (by omega) (by omega)) drd dwr
  obtain ⟨ω5, μ5, run5, st5, e5, e6, eF⟩ := prefixD (p := p) (P := P) (R := R) x ω4 μ4 μ L (by decide) st4 n 720
    18117 d0 (by rw [d7]; congr 1; omega) d8 (by rw [show F - 32 = F - 56 + 24 by omega]; exact dn)
    ⟨by decide, by decide, by decide⟩ jte_359 bs_18117 (by simp <;> omega)
  -- the octets
  obtain ⟨ω6, run6, g0', g1', g5', g6', g7', g8', g9'⟩ := seg_18117 (p := p) (P := P) (R := R) x ω5 μ5 (F - 56)
    v q n (by omega) hq64 (by omega) (by omega) st5.h1 (by rw [e5, d5, c5, b5]) (by rw [e6, d6])
    (by rw [Memory.readN_congr (fun j hj => eF _ (by omega) (by omega))]; exact dq)
    (fun a h1 h2 => by rw [st5.rd]; exact Memory.readable_of_writable (L.hwF a (by omega) (by omega)))
  have henc : (0 :: (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ (1 :: (Blob.encodeNat n ++ bytes)) ++ u5 ++ ou) :
      List UInt8) = ([] ++ [UInt8.ofNat 0] ++ (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr) ++ [UInt8.ofNat 1] ++
        Blob.encodeNat n) ++ bytes ++ (u5 ++ ou) := by
    simp only [List.nil_append, List.singleton_append, List.cons_append, List.append_assoc] <;> rfl
  have L' := L; rw [henc] at L'
  have st5' := st5.cast (show (UInt8.ofNat 0 :: (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr)) ++ [UInt8.ofNat 1] ++
      Blob.encodeNat n = [] ++ [UInt8.ofNat 0] ++ (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr) ++ [UInt8.ofNat 1] ++
      Blob.encodeNat n by simp)
  obtain ⟨ω7, μ7, run7, st7, k5, _, kF⟩ := heapD (p := p) (P := P) (R := R) x ω6 μ5 μ L' (by decide)
    ⟨g1'.trans st5'.h1, st5'.s0, st5'.s5, st5'.s6, st5'.sv, st5'.vl, st5'.out, st5'.keep, st5'.rd, st5'.wr⟩
    q n 910 20239 hbn rb g0' g7' g8' g9' ⟨by decide, by decide, by decide⟩ jte_454 bs_20239 hq
    (fun a ha => by rw [← henc]; exact hsrc a ha)
  have m7 : μ7.readN (F - 56) 8 = Num.encodeLE 8 S := by
    rw [Memory.readN_congr (fun j hj => kF _ (by omega) (by omega)),
      Memory.readN_congr (fun j hj => eF _ (by omega) (by omega)),
      Memory.readN_congr (fun j hj => dfr _ (by omega) (by omega) (by omega))]; exact m3
  -- u₅ and the `Option<u32>`
  obtain ⟨ω8, μ8, run8, st8⟩ := cs_tail (p := p) (P := P) (R := R) x ω7 μ μ7 L (by decide) st7 u5 ou hou
    (by simp [hh, h1, h2, h3, h4, harr, hbn]; omega) (by rw [k5, g5', e5, d5, c5, b5]) m7 c224 c24 c28
  exact closeD L (by decide) 20329 _ (by decide) (by rw [hN]; omega)
    (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans run8)))))))
    (st8.cast (by rw [henc]; simp))

/-- `create_service_some` at the depth 232. -/
theorem create_service_some_232 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (q n : Nat) (bytes : List UInt8) (hbn : bytes.length = n) (hn : n < 4294967296)
    (hq64 : q < 18446744073709551616) (hq : 0 < n → 65536 ≤ q)
    (h u1 u2 u3 u4 arr u5 ou : List UInt8) (hh : h.length = 32) (h1 : u1.length = 8) (h2 : u2.length = 8)
    (h3 : u3.length = 8) (h4 : u4.length = 8) (harr : arr.length = 128) (h5 : u5.length = 8)
    (hou : OptU32Enc ou) :
    EncOkMD p P 232 (0 :: (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ (1 :: (Blob.encodeNat n ++ bytes)) ++ u5 ++ ou))
      (CSSomeRepAt q n bytes h u1 u2 u3 u4 arr u5 ou) (VecSrc q n) :=
  (create_service_some q n bytes hbn hn hq64 hq h u1 u2 u3 u4 arr u5 ou hh h1 h2 h3 h4 harr h5 hou).mono
    (by decide)

/-- **`CreateService` with `Option<Vec<u8>>` = `Some([])`** (the decode side's `CreateServiceEmptyRep`:
    the empty `Vec` `{cap 0, ptr 1, len 0}`): `create_service_some` with q = 1 and n = 0, encoding to
    0 :: (h ++ u₁ ++ u₂ ++ u₃ ++ u₄ ++ arr ++ [1, 0] ++ u₅ ++ ou), reading no heap octets. -/
theorem create_service_empty_232 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (h u1 u2 u3 u4 arr u5 ou : List UInt8) (hh : h.length = 32) (h1 : u1.length = 8) (h2 : u2.length = 8)
    (h3 : u3.length = 8) (h4 : u4.length = 8) (harr : arr.length = 128) (h5 : u5.length = 8)
    (hou : OptU32Enc ou) :
    EncOkMD p P 232 (0 :: (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ [1, 0] ++ u5 ++ ou))
      (fun bs _ => CreateServiceEmptyRep h u1 u2 u3 u4 arr u5 ou bs) (fun _ => False) := by
  have H := create_service_some_232 (p := p) (P := P) 1 0 [] rfl (by decide) (by decide) (by decide)
    h u1 u2 u3 u4 arr u5 ou hh h1 h2 h3 h4 harr h5 hou
  have he : (0 :: (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ (1 :: (Blob.encodeNat 0 ++ [])) ++ u5 ++ ou) :
      List UInt8) = 0 :: (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ [1, 0] ++ u5 ++ ou) := rfl
  rw [he] at H
  intro X R x ω μ F S v cap ptr len ret t g0 g1 g7 g8 rep L tab hrt _
  obtain ⟨r0, r8, r16, rf⟩ := rep
  exact H X R x ω μ F S v cap ptr len ret t g0 g1 g7 g8 ⟨r0, r8, r16, by simp [Memory.readN], rf⟩ L tab hrt
    (fun a ha => absurd ha.1 (Nat.lt_irrefl 0))

end Services.Bootstrap.Encode.Enc
