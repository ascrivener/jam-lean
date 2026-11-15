import Services.Bootstrap.Encode.ArmsHVecCore
import Services.Bootstrap.Encode.VariantsVec3Designate

/-!
# `Designate` (13) with growth (`EncOkMH`)

`Enc.designate` re-proved over `GrowH.StDH`: `designate_loopH` (the key loop 19385 … 19467, each key's
four pieces appended straight from the kept stretch (q, 336 n), `heapDH`), `designateH` the arm. The
heap octets are the keys' stretch (q, 336 n) when n > 0 (`SrcAtP`).
-/

namespace Services.Bootstrap.Encode.GrowH

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX
  Services.Bootstrap.CodeA Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Encode.WriterGrow Services.Bootstrap.Encode.Enc
  Services.Bootstrap.Encode.EncMD Services.Bootstrap.Decode.VecKey336

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

section
variable {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
  {env : RefineHost.Env} {pb S0 S1 D F v len ptr0 ret r5 r6 : Nat} {s0 : State} {μ0 : Memory}

/-- **`Designate`'s key loop, with growth** (`Enc.designate_loop`): from the loop's head for key k
    (ω₆ = q + 336 k, ω₇ = 336 i, i = n − k > 0, the writer in ω₅) in `StDH (pre0 ++ ks.take (336 k))`,
    each key appended in the paper's order, at 20118 in `StDH (pre0 ++ ks)`; or a failed `realloc`. -/
theorem designate_loopH (K : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (x : RefineCtx)
    (Fr : FrH S0 S1 D F v) (hD : 136 ≤ D) (q n : Nat) (pre0 ks : List UInt8) (hks : ks.length = 336 * n)
    (hsrc : SafeR s0 ptr0 F S1 v q (336 * n)) (hkeys : μ0.readN q (336 * n) = keysRot n ks)
    (hlen : 2 * (len + pre0.length + 336 * n) ≤ capBound) :
    ∀ i k (ω : Regs) (μ1 : Memory), k + i = n → 0 < i →
      StDH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 (pre0 ++ ks.take (336 * k)) ω μ1 →
      ω[5] = UInt64.ofNat v → ω[6] = UInt64.ofNat (q + 336 * k) → ω[7] = UInt64.ofNat (336 * i) →
      (∃ ω' μ', FreeStepsH p (refineContractK K env) 19385 ω μ1 x 20118 ω' μ' x ((2000 + growGas) * (336 * i)) ∧
        StDH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 (pre0 ++ ks) ω' μ') ∨
      ExhaustsW env K pb p P 19385 ω μ1 x ((2000 + growGas) * (336 * i)) := by
  have := Fr.hF2; have := Fr.hFv; have := Fr.hvS1; have := Fr.hS1; have := Fr.hFS0
  intro i
  induction i with
  | zero => intro k ω μ1 _ h; omega
  | succ i ih =>
    intro k ω μ1 hki _ st h5 h6 h7
    have hk : k < n := by omega
    have hlenk : (ks.take (336 * k)).length = 336 * k := by simp [hks]; omega
    have hkey := keysRot_elem μ0 n q ks hks hkeys k hk
    have hkl : ((ks.drop (336 * k)).take 336).length = 336 := by simp [hks]; omega
    obtain ⟨cap1, ptr1, s1, W1⟩ := st.buf
    obtain ⟨bq1, bq2, bq3⟩ := SafeR.bounds W1.H Fr (W1.safe hsrc)
    -- the first piece
    obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bs0, bs8, bfr, brd, bwr⟩ := seg_19385 (p := p) (P := P)
      (R := refineContractK K env) x ω μ1 (F - 56) v (q + 336 * k) (336 * (i + 1)) (by omega) (by omega)
      (by omega) (by omega) st.h1 h5 h6 h7 (fun b h1 h2 => W1.H.st b (by omega) (by omega))
    have st2 := st.scratch Fr b1 (fun b h0 h1 => bfr b h0 (by omega)) brd bwr
    rcases heapDH (p := p) (P := P) env K hK1 hK x ω2 μ2 Fr hD st2 (q + 336 * k + 128) 32 840 19410
        (bytes := μ0.readN (q + 336 * k + 128) 32) (by simp [Memory.readN]) rfl b0 b7 b8 b9
        ⟨by decide, by decide, by decide⟩ jte_419 bs_19410 (by simp [hlenk]; omega)
        (Or.inr (hsrc.sub (by omega) (by omega))) with
      ⟨ω3, μ3, run3, st3, c5, c6, cF⟩ | hx
    rotate_left
    · exact Or.inr ((ExhaustsW.pre run2 hx).mono (by unfold stepGas growGas; omega))
    -- the second
    obtain ⟨ω4, run4, d0, d1, d5, d6, d7, d8, d9⟩ := seg_keyD (p := p) (P := P) (R := refineContractK K env)
      x ω3 μ3 19410 842 160 32 v (q + 336 * k) (Or.inl ⟨rfl, rfl, rfl, rfl⟩) (by omega) (by omega)
      (by rw [c5, b5, h5]) (by rw [c6, b6, h6])
    rcases heapDH (p := p) (P := P) env K hK1 hK x ω4 μ3 Fr hD
        ⟨⟨d1.trans st3.h1, st3.w0, st3.w5, st3.w6, st3.buf⟩, st3.sv⟩ (q + 336 * k + 160) 32 842 19426
        (bytes := μ0.readN (q + 336 * k + 160) 32) (by simp [Memory.readN]) rfl d0 d7 d8 d9
        ⟨by decide, by decide, by decide⟩ jte_420 bs_19426 (by simp [hlenk, Memory.readN]; omega)
        (Or.inr (hsrc.sub (by omega) (by omega))) with
      ⟨ω5, μ5, run5, st5, e5, e6, eF⟩ | hx
    rotate_left
    · exact Or.inr ((ExhaustsW.pre (run2.trans (run3.trans run4)) hx).mono (by unfold stepGas growGas; omega))
    -- the third
    obtain ⟨ω6, run6, f0, f1, f5, f6, f7, f8, f9⟩ := seg_keyD (p := p) (P := P) (R := refineContractK K env)
      x ω5 μ5 19426 844 192 144 v (q + 336 * k) (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)) (by omega) (by omega)
      (by rw [e5, d5, c5, b5, h5]) (by rw [e6, d6, c6, b6, h6])
    rcases heapDH (p := p) (P := P) env K hK1 hK x ω6 μ5 Fr hD
        ⟨⟨f1.trans st5.h1, st5.w0, st5.w5, st5.w6, st5.buf⟩, st5.sv⟩ (q + 336 * k + 192) 144 844 19443
        (bytes := μ0.readN (q + 336 * k + 192) 144) (by simp [Memory.readN]) rfl f0 f7 f8 f9
        ⟨by decide, by decide, by decide⟩ jte_421 bs_19443 (by simp [hlenk, Memory.readN]; omega)
        (Or.inr (hsrc.sub (by omega) (by omega))) with
      ⟨ω7, μ7, run7, st7, g5, g6, gF⟩ | hx
    rotate_left
    · exact Or.inr ((ExhaustsW.pre (run2.trans (run3.trans (run4.trans (run5.trans run6)))) hx).mono
        (by unfold stepGas growGas; omega))
    -- the fourth
    obtain ⟨ω8, run8, k0, k1, k5, k6, k7, k8, k9⟩ := seg_keyD (p := p) (P := P) (R := refineContractK K env)
      x ω7 μ7 19443 846 0 128 v (q + 336 * k) (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩)) (by omega) (by omega)
      (by rw [g5, f5, e5, d5, c5, b5, h5]) (by rw [g6, f6, e6, d6, c6, b6, h6])
    rw [Nat.add_zero] at k8
    rcases heapDH (p := p) (P := P) env K hK1 hK x ω8 μ7 Fr hD
        ⟨⟨k1.trans st7.h1, st7.w0, st7.w5, st7.w6, st7.buf⟩, st7.sv⟩ (q + 336 * k) 128 846 19458
        (bytes := μ0.readN (q + 336 * k) 128) (by simp [Memory.readN]) rfl k0 k7 k8 k9
        ⟨by decide, by decide, by decide⟩ jte_422 bs_19458 (by simp [hlenk, Memory.readN]; omega)
        (Or.inr (hsrc.sub (by omega) (by omega))) with
      ⟨ω9, μ9, run9, st9, m5, m6, mF⟩ | hx
    rotate_left
    · exact Or.inr ((ExhaustsW.pre (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans
        run8)))))) hx).mono (by unfold stepGas growGas; omega))
    have st9' := st9.cast (show pre0 ++ ks.take (336 * k) ++ μ0.readN (q + 336 * k + 128) 32 ++
        μ0.readN (q + 336 * k + 160) 32 ++ μ0.readN (q + 336 * k + 192) 144 ++ μ0.readN (q + 336 * k) 128 =
        pre0 ++ ks.take (336 * (k + 1)) by
      rw [take336_succ, ← keyRot_parts μ0 (q + 336 * k) _ hkl hkey]; simp [List.append_assoc])
    have fr : ∀ b, F - 56 ≤ b → b < F → μ9.read b = μ2.read b := fun b h1 h2 => by
      rw [mF b h1 h2, gF b h1 h2, eF b h1 h2, cF b h1 h2]
    have s0' : μ9.readN (F - 56) 8 = Num.encodeLE 8 (q + 336 * k + 336) := by
      rw [Memory.readN_congr (fun j hj => fr _ (by omega) (by omega))]; exact bs0
    have s8' : μ9.readN (F - 56 + 8) 8 = Num.encodeLE 8 (336 * (i + 1)) := by
      rw [Memory.readN_congr (fun j hj => fr _ (by omega) (by omega))]; exact bs8
    obtain ⟨cap9, ptr9, s9, W9⟩ := st9'.buf
    have hrd : ∀ c, F - 56 ≤ c → c < F - 56 + 16 → μ9.readable c = true := fun c h1 h2 =>
      Memory.readable_of_writable (W9.H.st c (by omega) (by omega))
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · obtain ⟨ω10, run10, n1⟩ := seg_19458_last (p := p) (P := P) (R := refineContractK K env) x ω9 μ9 (F - 56)
        (q + 336 * k + 336) (by omega) (by omega) st9'.h1 s0' s8' hrd
      have hkn : 336 * (k + 1) = ks.length := by omega
      exact Or.inl ⟨ω10, μ9, (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans (run8.trans
        (run9.trans run10)))))))).mono (by unfold stepGas growGas; omega),
        StDH.cast ⟨⟨n1.trans st9'.h1, st9'.w0, st9'.w5, st9'.w6, st9'.buf⟩, st9'.sv⟩
          (by rw [hkn, List.take_length])⟩
    · obtain ⟨ω10, run10, n1, n5, n6, n7⟩ := seg_19458_more (p := p) (P := P) (R := refineContractK K env) x ω9
        μ9 (F - 56) (336 * (i + 1)) (q + 336 * k + 336) (by omega) ⟨by omega, by omega⟩ (by omega) st9'.h1 s0'
        s8' hrd
      rcases ih (k + 1) ω10 μ9 (by omega) hi0 ⟨⟨n1.trans st9'.h1, st9'.w0, st9'.w5, st9'.w6, st9'.buf⟩, st9'.sv⟩
          (by rw [n5, m5, k5, g5, f5, e5, d5, c5, b5, h5]) (by rw [n6]; congr 1) (by rw [n7]; congr 1) with
        ⟨ω11, μ11, run11, st11⟩ | hx
      · exact Or.inl ⟨ω11, μ11, (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans
          (run8.trans (run9.trans (run10.trans run11))))))))).mono (by unfold stepGas growGas; omega), st11⟩
      · exact Or.inr ((ExhaustsW.pre (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans
          (run8.trans (run9.trans run10)))))))) hx).mono (by unfold stepGas growGas; omega))

end

/-- **`Designate` (index 13), with growth** (`Enc.designate` as `EncOkMH`): `DesignateRepAt q n ks`
    encodes to 13 :: ℰ(n) ++ ks, the heap octets the keys' stretch (q, 336 n) when n > 0. -/
theorem designateH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (q n : Nat) (ks : List UInt8) (hks : ks.length = 336 * n) (hn : n < 4294967296)
    (hq64 : q < 18446744073709551616) :
    EncOkMH env K pb p P 192 (13 :: (Blob.encodeNat n ++ ks)) (DesignateRepAt q n ks) (SrcAtP q (336 * n)) := by
  intro x ω μ s S0 S1 F S v cap ptr len ret t h0 h1 h7 h8 rep L hlen tab hrt hsrc
  obtain ⟨r0, r8, r16, r24, rkeys⟩ := rep
  have hD8 : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 13) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact r0
  have c16 : μ.readN (S + 16) 8 = Num.encodeLE 8 q := by rw [← slot_take μ S 16 8 (by decide)]; exact r16
  have c24 : μ.readN (S + 24) 8 = Num.encodeLE 8 n := by rw [← slot_take μ S 24 8 (by decide)]; exact r24
  have Fr := L.fr
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := L.nums
  have hS := L.hS; have hS' := L.hS'
  have hE := encodeNat_pos n
  have hN : (13 :: (Blob.encodeNat n ++ ks) : List UInt8).length = 1 + (Blob.encodeNat n).length + 336 * n := by
    simp [hks]; omega
  rw [hN] at hlen
  obtain ⟨ω1, μ1, run1, st1, a10, a11⟩ := startDH (p := p) (P := P) K x ω μ L (by decide) 13
    ⟨by decide, by decide⟩ h0 h1 h7 h8 hD8 tab hrt
  rw [show arm 13 = 19322 from rfl] at run1
  obtain ⟨cap1, ptr1, s1, W1⟩ := st1.buf
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b7, b8, b9, bt, bfr, brd, bwr⟩ := seg_19322 (p := p) (P := P)
    (R := refineContractK K env) x ω1 μ1 (F - 56) v S (by omega) (by omega) (by omega) st1.h1 a10 a11
    (fun a h1 h2 => W1.H.st a (by omega) (by omega))
  have st2 := st1.scratch Fr b1 (fun a h0 h1 => bfr a h0 (by omega)) brd bwr
  rcases scratchDH (p := p) (P := P) env K hK1 hK x ω2 μ2 Fr (by decide) st2 [UInt8.ofNat 13] 1 836 19343 rfl
      (by decide) b0 b7 b8 b9 ⟨by decide, by decide, by decide⟩ jte_417 bs_19343 (by simp; omega) bt with
    ⟨ω3, μ3, run3, st3, c5, -, -⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans run2) hx).mono (by unfold encGas stepGas growGas; rw [hN]; omega))
  -- the length prefix
  obtain ⟨cap3, ptr3, s3, W3⟩ := st3.buf
  obtain ⟨ω4, μ4, run4, d0, d1, d5, d6, d7, d8, dn, dfr, drd, dwr⟩ := seg_19343 (p := p) (P := P)
    (R := refineContractK K env) x ω3 μ3 (F - 56) v S q n (by omega) (by omega) (by omega) hq64 hn st3.h1
    (by rw [c5, b5])
    (by rw [st3.slot L.slot (by decide)]; exact c16)
    (by rw [st3.slot L.slot (by decide)]; exact c24)
    (by rw [show F - 56 + 16 = F - 40 by omega]; exact st3.sv)
    (fun a h1 h2 => W3.safe_readable (by omega) (W3.safe L.slot) a (by omega) (by omega))
    (fun a h1 h2 => W3.H.st a (by omega) (by omega))
  have st4 := st3.scratch Fr d1 (fun a h0 h1 => dfr a h0 (by omega)) drd dwr
  rcases prefixDH (p := p) (P := P) env K hK1 hK x ω4 μ4 Fr (by decide) st4 n 838 19373 d0
      (by rw [d7]; congr 1; omega) d8 (by rw [show F - 32 = F - 56 + 24 by omega]; exact dn)
      ⟨by decide, by decide, by decide⟩ jte_418 bs_19373 (by simp; omega) with
    ⟨ω5, μ5, run5, st5, e5, e6, -⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans run4))) hx).mono
      (by unfold encGas stepGas prefixGas growGas; rw [hN]; omega))
  have hpre : ([] ++ [UInt8.ofNat 13] ++ Blob.encodeNat n : List UInt8).length =
      1 + (Blob.encodeNat n).length := by simp; omega
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · -- no keys
    subst hn0
    have hk0 : ks = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hk0
    obtain ⟨ω6, run6, rfl⟩ := seg_19373_zero (p := p) (P := P) (R := refineContractK K env) x ω5 μ5
      (by rw [e5, d5])
    exact Or.inl (closeH L 20118 _ (by decide) (by unfold encGas stepGas prefixGas growGas; rw [hN]; omega)
      (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))) (st5.toStH.cast (by simp)))
  · have hsq := hsrc q (336 * n) ⟨by omega, rfl, rfl⟩
    obtain ⟨cap5, ptr5, s5, W5⟩ := st5.buf
    obtain ⟨ω6, run6, f1, f5, f6, f7⟩ := seg_19373_pos (p := p) (P := P) (R := refineContractK K env) x ω5 μ5
      (F - 56) v n (by omega) (by omega) ⟨hn0, by omega⟩ st5.h1 (by rw [e5, d5])
      (by rw [show F - 56 + 16 = F - 40 by omega]; exact st5.sv)
      (fun a h1 h2 => Memory.readable_of_writable (W5.H.st a (by omega) (by omega)))
    have henc : (13 :: (Blob.encodeNat n ++ ks) : List UInt8) = ([] ++ [UInt8.ofNat 13] ++ Blob.encodeNat n) ++ ks := by
      simp only [List.nil_append, List.cons_append] <;> rfl
    rcases designate_loopH (p := p) (P := P) K hK1 hK x Fr (by decide) q n
        ([] ++ [UInt8.ofNat 13] ++ Blob.encodeNat n) ks hks hsq rkeys (by rw [hpre]; omega) n 0 ω6 μ5 (by omega)
        hn0 (StDH.cast ⟨⟨f1.trans st5.h1, st5.w0, st5.w5, st5.w6, st5.buf⟩, st5.sv⟩ (by simp))
        f5 (by rw [f6, e6, d6]; congr 1) f7 with
      ⟨ω7, μ7, run7, st7⟩ | hx
    · exact Or.inl (closeH L 20118 _ (by decide) (by unfold encGas stepGas prefixGas growGas; rw [hN]; omega)
        (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7))))))
        (st7.toStH.cast henc.symm))
    · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))) hx).mono
        (by unfold encGas stepGas prefixGas growGas; rw [hN]; omega))

/-- `designateH` at the depth 232. -/
theorem designateH_232 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (q n : Nat) (ks : List UInt8) (hks : ks.length = 336 * n) (hn : n < 4294967296)
    (hq64 : q < 18446744073709551616) :
    EncOkMH env K pb p P 232 (13 :: (Blob.encodeNat n ++ ks)) (DesignateRepAt q n ks) (SrcAtP q (336 * n)) :=
  (designateH env K pb hK1 hK q n ks hks hn hq64).mono (by decide)

end Services.Bootstrap.Encode.GrowH
