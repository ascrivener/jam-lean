import Services.Bootstrap.Encode.GrowH

/-!
# The length prefix (30977) with growth

`Prefix.prefix_small`, `prefix_zero` and `PrefixBig.prefix_big` re-proved over `GrowH.BufH`: the
function's own pieces (`Prefix.pa`, `pb`, `pc`, `pz`, `pt`, `PrefixBig.pg`, `ph`) write only its frame
[F − 56, F), and each of its calls of `Vec<u8>::extend_from_slice` is `GrowH.extendH`, which may grow the
writer or reach a failed `realloc` (`ExhaustsW`). `prefix_anyH` joins them for any n < 2^32, appending
ℰ(n) (GP v0.8.0 Appendix C); `prefixH` / `prefixDH` are the call from an arm's frame (`StH` / `StDH`),
the count at the scratch word F − 32.
-/

namespace Services.Bootstrap.Encode.GrowH

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX
  Services.Bootstrap.CodeA Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Encode.WriterGrow

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- The gas of the length prefix of n: `prefix_any`'s, and one growth per octet of ℰ(n). -/
def prefixGas (n : Nat) : Nat := 900 + 1100 * min (n / 128) 1 + growGas * (Blob.encodeNat n).length

section
variable {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
  {env : RefineHost.Env} {pb S0 S1 B v len ptr0 : Nat} {s0 : State} {μ0 : Memory} {pre : List UInt8}
  {cap ptr : Nat} {s : State}

/-- **ℰ(n) for 0 < n < 2^7, with growth** (`Prefix.prefix_small` over `BufH`). -/
theorem prefix_smallH (K : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (x : RefineCtx) (ω : Regs) (μ : Memory) (W : BufH env pb S0 S1 B v len ptr0 s0 μ0 pre cap ptr s μ)
    (F c ret t r5 r6 n : Nat) (hF : S0 + 480 ≤ F ∧ 2147484128 ≤ F ∧ F % 8 = 0) (hB : F ≤ B) (hv : F ≤ v)
    (hS1 : S1 + 16 < 4294967296)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat F) (h5 : ω[5] = UInt64.ofNat r5)
    (h6 : ω[6] = UInt64.ofNat r6) (h7 : ω[7] = UInt64.ofNat c) (h8 : ω[8] = UInt64.ofNat v)
    (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hc : c + 4 ≤ 4294967296) (hcF : c + 4 ≤ F - 56 ∨ F ≤ c) (hn : rdN μ c 4 = n) (hn1 : 0 < n ∧ n < 128)
    (hrc : ∀ a, c ≤ a → a < c + 4 → μ.readable a = true)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) (hlen : 2 * (len + pre.length + 1) ≤ capBound) :
    (∃ cap' ptr' s' ω' μ', FreeStepsH p (refineContractK K env) 30977 ω μ x t ω' μ' x (900 + growGas) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat F ∧ ω'[5] = UInt64.ofNat r5 ∧ ω'[6] = UInt64.ofNat r6 ∧
      BufH env pb S0 S1 B v len ptr0 s0 μ0 (pre ++ [UInt8.ofNat n]) cap' ptr' s' μ' ∧
      (∀ a, a < 4294967296 → F ≤ a → (a < v ∨ v + 24 ≤ a) → μ'.read a = μ.read a)) ∨
    ExhaustsW env K pb p P 30977 ω μ x (900 + growGas) := by
  have vS := W.vS; have hst := W.H.st; have hS1' := W.H.hS1
  obtain ⟨hF0, hF2, hF8⟩ := hF
  have hret' : ret < 18446744073709551616 := by omega
  obtain ⟨ω1, μ1, run1, a1, a2, a6, a8, a0', a5', a6', afr, ard, awr⟩ := Prefix.pa (p := p) (P := P)
    (R := refineContractK K env) x ω μ F c v ret r5 r6 n ⟨by omega, by omega⟩ h0 h1 h5 h6 h7 h8 hret' hr5 hr6
    (by omega) hc hcF hn (by omega) hrc (fun a h1 h2 => hst a (by omega) (by omega))
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bo, bv, bz, bfr, brd, bwr⟩ := Prefix.pb (p := p) (P := P)
    (R := refineContractK K env) x ω1 μ1 (F - 56) v n (by omega) (by omega) hn1 a1 a2 a6 a8
    (fun a h1 h2 => by rw [awr]; exact hst a (by omega) (by omega))
  have k2 : ∀ a, a < 4294967296 → (a < F - 56 ∨ F ≤ a) → μ2.read a = μ.read a := fun a h0 h1 => by
    rw [bfr a h0 (by omega), afr a h0 h1]
  have W2 := W.frame (μ' := μ2) (F - 56) F (by omega) hB (Or.inl hv) k2 (fun a => by rw [brd, ard])
    (fun a => by rw [bwr, awr])
  rcases extendH env K hK1 hK x ω2 μ2 W2 (F - 56) (F - 56 + 24) 1 1466 31106 ⟨by omega, by omega, by omega⟩
      (by omega) (by omega) hS1 b0 b1 b7 b8 b9 ⟨by decide, by decide, by decide⟩ jte_732 bs_31106 hlen
      (Or.inr (Or.inl ⟨by omega, by omega, Or.inl (by omega)⟩)) with
    ⟨cap3, ptr3, s3, ω3, μ3, run3, c0, c1, c5, c6, W3, k3⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans run2) hx).mono (by unfold stepGas growGas; omega))
  rw [bo] at W3
  have k3f : ∀ a, F - 56 ≤ a → a < F → μ3.read a = μ2.read a := fun a h1 h2 =>
    k3 a (by omega) h1 (Or.inl (by omega))
  obtain ⟨ω4, μ4, run4, d0, d1, d7, d8, d9, dfr, drd, dwr⟩ := Prefix.pc (p := p) (P := P)
    (R := refineContractK K env) x ω3 μ3 (F - 56) v n (by omega) (by omega) (by omega) c1 (c5.trans b5)
    (c6.trans b6)
    (by rw [Memory.readN_congr (fun j hj => k3f _ (by omega) (by omega))]; exact bv)
    (by rw [Memory.readN_congr (fun j hj => k3f _ (by omega) (by omega))]; exact bz)
    (fun a h1 h2 => W3.H.st a (by omega) (by omega))
  have W4 := W3.frame (μ' := μ4) (F - 56 + 24) (F - 56 + 32) (by omega) (by omega) (Or.inl (by omega)) dfr drd dwr
  rcases extendH env K hK1 hK x ω4 μ4 W4 (F - 56) (F - 56 + 24) 0 1472 31348 ⟨by omega, by omega, by omega⟩
      (by omega) (by omega) hS1 d0 d1 d7 d8 d9 ⟨by decide, by decide, by decide⟩ jte_735 bs_31348
      (by simp; omega) (Or.inl rfl) with
    ⟨cap5, ptr5, s5, ω5, μ5, run5, e0, e1, e5, e6, W5, k5⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans run4))) hx).mono
      (by unfold stepGas growGas; omega))
  have kw : ∀ a, F - 24 ≤ a → a < F → μ5.read a = μ1.read a := fun a h1 h2 => by
    rw [k5 a (by omega) (by omega) (Or.inl (by omega)), dfr a (by omega) (by omega), k3f a (by omega) h2,
      bfr a (by omega) (by omega)]
  obtain ⟨ω6, run6, f0, f1, f5, f6⟩ := Prefix.pt (p := p) (P := P) (R := refineContractK K env) x ω5 μ5 31348
    (F - 56) ret t r5 r6 (Or.inr rfl) (by omega) e1
    (by rw [show F - 56 + 48 = F - 8 by omega, Memory.readN_congr (fun j hj => kw _ (by omega) (by omega))]
        exact a0')
    (by rw [show F - 56 + 40 = F - 16 by omega, Memory.readN_congr (fun j hj => kw _ (by omega) (by omega))]
        exact a5')
    (by rw [show F - 56 + 32 = F - 24 by omega, Memory.readN_congr (fun j hj => kw _ (by omega) (by omega))]
        exact a6')
    hr5 hr6 hret hjt hbt (fun a h1 h2 => Memory.readable_of_writable (W5.H.st a (by omega) (by omega)))
  refine Or.inl ⟨cap5, ptr5, s5, ω6, μ5,
    (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))).mono (by unfold stepGas growGas; omega),
    f0, by rw [f1]; congr 1; omega, f5, f6, W5.cast (by simp [Memory.readN]), fun a h0 h1 h2 => ?_⟩
  rw [k5 a h0 (by omega) h2, dfr a h0 (by omega), k3 a h0 (by omega) h2, k2 a h0 (Or.inr h1)]

/-- **ℰ(0) = [0], with growth** (`Prefix.prefix_zero` over `BufH`). -/
theorem prefix_zeroH (K : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (x : RefineCtx) (ω : Regs) (μ : Memory) (W : BufH env pb S0 S1 B v len ptr0 s0 μ0 pre cap ptr s μ)
    (F c ret t r5 r6 : Nat) (hF : S0 + 480 ≤ F ∧ 2147484128 ≤ F ∧ F % 8 = 0) (hB : F ≤ B) (hv : F ≤ v)
    (hS1 : S1 + 16 < 4294967296)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat F) (h5 : ω[5] = UInt64.ofNat r5)
    (h6 : ω[6] = UInt64.ofNat r6) (h7 : ω[7] = UInt64.ofNat c) (h8 : ω[8] = UInt64.ofNat v)
    (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hc : c + 4 ≤ 4294967296) (hcF : c + 4 ≤ F - 56 ∨ F ≤ c) (hn : rdN μ c 4 = 0)
    (hrc : ∀ a, c ≤ a → a < c + 4 → μ.readable a = true)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) (hlen : 2 * (len + pre.length + 1) ≤ capBound) :
    (∃ cap' ptr' s' ω' μ', FreeStepsH p (refineContractK K env) 30977 ω μ x t ω' μ' x (900 + growGas) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat F ∧ ω'[5] = UInt64.ofNat r5 ∧ ω'[6] = UInt64.ofNat r6 ∧
      BufH env pb S0 S1 B v len ptr0 s0 μ0 (pre ++ [UInt8.ofNat 0]) cap' ptr' s' μ' ∧
      (∀ a, a < 4294967296 → F ≤ a → (a < v ∨ v + 24 ≤ a) → μ'.read a = μ.read a)) ∨
    ExhaustsW env K pb p P 30977 ω μ x (900 + growGas) := by
  have vS := W.vS; have hst := W.H.st; have hS1' := W.H.hS1
  obtain ⟨hF0, hF2, hF8⟩ := hF
  have hret' : ret < 18446744073709551616 := by omega
  obtain ⟨ω1, μ1, run1, a0, a1, a7, a8, a9, ao, a0', a5', a6', afr, ard, awr⟩ := Prefix.pz (p := p) (P := P)
    (R := refineContractK K env) x ω μ F c v ret r5 r6 ⟨by omega, by omega⟩ h0 h1 h5 h6 h7 h8 hret' hr5 hr6
    (by omega) hc hcF hn hrc (fun a h1 h2 => hst a (by omega) (by omega))
  have W1 := W.frame (μ' := μ1) (F - 56) F (by omega) hB (Or.inl hv) afr ard awr
  rcases extendH env K hK1 hK x ω1 μ1 W1 (F - 56) (F - 32) 1 1468 31129 ⟨by omega, by omega, by omega⟩
      (by omega) (by omega) hS1 a0 a1 a7 a8 a9 ⟨by decide, by decide, by decide⟩ jte_733 bs_31129 hlen
      (Or.inr (Or.inl ⟨by omega, by omega, Or.inl (by omega)⟩)) with
    ⟨cap2, ptr2, s2, ω2, μ2, run2, b0, b1, b5, b6, W2, k2⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre run1 hx).mono (by unfold stepGas growGas; omega))
  rw [ao] at W2
  have kw : ∀ a, F - 24 ≤ a → a < F → μ2.read a = μ1.read a := fun a h1 h2 =>
    k2 a (by omega) (by omega) (Or.inl (by omega))
  obtain ⟨ω3, run3, c0, c1, c5, c6⟩ := Prefix.pt (p := p) (P := P) (R := refineContractK K env) x ω2 μ2 31129
    (F - 56) ret t r5 r6 (Or.inl rfl) (by omega) b1
    (by rw [show F - 56 + 48 = F - 8 by omega, Memory.readN_congr (fun j hj => kw _ (by omega) (by omega))]
        exact a0')
    (by rw [show F - 56 + 40 = F - 16 by omega, Memory.readN_congr (fun j hj => kw _ (by omega) (by omega))]
        exact a5')
    (by rw [show F - 56 + 32 = F - 24 by omega, Memory.readN_congr (fun j hj => kw _ (by omega) (by omega))]
        exact a6')
    hr5 hr6 hret hjt hbt (fun a h1 h2 => Memory.readable_of_writable (W2.H.st a (by omega) (by omega)))
  refine Or.inl ⟨cap2, ptr2, s2, ω3, μ2, (run1.trans (run2.trans run3)).mono (by unfold stepGas growGas; omega),
    c0, by rw [c1]; congr 1; omega, c5, c6, W2, fun a h0 h1 h2 => ?_⟩
  rw [k2 a h0 (by omega) h2, afr a h0 (Or.inr h1)]

/-- **ℰ(n) for 2^7 ≤ n < 2^32, with growth** (`PrefixBig.prefix_big` over `BufH`). -/
theorem prefix_bigH (K : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (x : RefineCtx) (ω : Regs) (μ : Memory) (W : BufH env pb S0 S1 B v len ptr0 s0 μ0 pre cap ptr s μ)
    (F c ret t r5 r6 n : Nat) (hF : S0 + 480 ≤ F ∧ 2147484128 ≤ F ∧ F % 8 = 0) (hB : F ≤ B) (hv : F ≤ v)
    (hS1 : S1 + 16 < 4294967296)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat F) (h5 : ω[5] = UInt64.ofNat r5)
    (h6 : ω[6] = UInt64.ofNat r6) (h7 : ω[7] = UInt64.ofNat c) (h8 : ω[8] = UInt64.ofNat v)
    (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hc : c + 4 ≤ 4294967296) (hcF : c + 4 ≤ F - 56 ∨ F ≤ c) (hn : rdN μ c 4 = n) (hn1 : 128 ≤ n)
    (hrc : ∀ a, c ≤ a → a < c + 4 → μ.readable a = true)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) (hlen : 2 * (len + pre.length + (Blob.encodeNat n).length) ≤ capBound) :
    (∃ cap' ptr' s' ω' μ', FreeStepsH p (refineContractK K env) 30977 ω μ x t ω' μ' x
        (2000 + growGas * (Blob.encodeNat n).length) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat F ∧ ω'[5] = UInt64.ofNat r5 ∧ ω'[6] = UInt64.ofNat r6 ∧
      BufH env pb S0 S1 B v len ptr0 s0 μ0 (pre ++ Blob.encodeNat n) cap' ptr' s' μ' ∧
      (∀ a, a < 4294967296 → F ≤ a → (a < v ∨ v + 24 ≤ a) → μ'.read a = μ.read a)) ∨
    ExhaustsW env K pb p P 30977 ω μ x (2000 + growGas * (Blob.encodeNat n).length) := by
  have vS := W.vS; have hst := W.H.st; have hS1' := W.H.hS1
  obtain ⟨hF0, hF2, hF8⟩ := hF
  have hret' : ret < 18446744073709551616 := by omega
  have hn4 : n < 4294967296 := by rw [← hn]; exact rdN_lt μ c 4
  obtain ⟨l, hl, hnl⟩ : ∃ l, (l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4) ∧ 2 ^ (7 * l) ≤ n ∧ n < 2 ^ (7 * (l + 1)) := by
    by_cases h2 : n < 16384
    · exact ⟨1, by omega, by simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]; omega⟩
    by_cases h3 : n < 2097152
    · exact ⟨2, by omega, by simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]; omega⟩
    by_cases h4 : n < 268435456
    · exact ⟨3, by omega, by simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]; omega⟩
    · exact ⟨4, by omega, by simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]; omega⟩
  have henc := PrefixBig.encodeNat_big n l hl hnl
  have hw : (Blob.encodeNat n).length = 1 + l := by rw [henc]; simp; omega
  rw [hw] at hlen ⊢
  have hl4 : 1 ≤ l ∧ l ≤ 4 := by omega
  obtain ⟨ω1, μ1, run1, a1, a2, a6, a8, a0', a5', a6', afr, ard, awr⟩ := Prefix.pa (p := p) (P := P)
    (R := refineContractK K env) x ω μ F c v ret r5 r6 n ⟨by omega, by omega⟩ h0 h1 h5 h6 h7 h8 hret' hr5 hr6
    (by omega) hc hcF hn (by omega) hrc (fun a h1 h2 => hst a (by omega) (by omega))
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b7, b8, b9, bo, bn, bl, bv, bfr, brd, bwr⟩ := PrefixBig.pg (p := p) (P := P)
    (R := refineContractK K env) x ω1 μ1 (F - 56) v n l hl hnl (by omega) (by omega) a1 a2 a6 a8
    (fun a h1 h2 => by rw [awr]; exact hst a (by omega) (by omega))
  have k2 : ∀ a, a < 4294967296 → (a < F - 56 ∨ F ≤ a) → μ2.read a = μ.read a := fun a h0 h1 => by
    rw [bfr a h0 (by omega), afr a h0 h1]
  have W2 := W.frame (μ' := μ2) (F - 56) F (by omega) hB (Or.inl hv) k2 (fun a => by rw [brd, ard])
    (fun a => by rw [bwr, awr])
  rcases extendH env K hK1 hK x ω2 μ2 W2 (F - 56) (F - 56 + 24) 1 1470 31291 ⟨by omega, by omega, by omega⟩
      (by omega) (by omega) hS1 b0 b1 b7 b8 b9 ⟨by decide, by decide, by decide⟩ jte_734 bs_31291 (by omega)
      (Or.inr (Or.inl ⟨by omega, by omega, Or.inl (by omega)⟩)) with
    ⟨cap3, ptr3, s3, ω3, μ3, run3, c0, c1, c5, c6, W3, k3⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans run2) hx).mono (by unfold stepGas growGas; omega))
  rw [bo] at W3
  have k3f : ∀ a, F - 56 ≤ a → a < F → μ3.read a = μ2.read a := fun a h1 h2 =>
    k3 a (by omega) h1 (Or.inl (by omega))
  obtain ⟨ω4, μ4, run4, d0, d1, d7, d8, d9, dw, dfr, drd, dwr⟩ := PrefixBig.ph (p := p) (P := P)
    (R := refineContractK K env) x ω3 μ3 (F - 56) v n l hl (by omega) (by omega) (by omega) c1 (c5.trans b5)
    (by rw [Memory.readN_congr (fun j hj => k3f _ (by omega) (by omega))]; exact bn)
    (by rw [Memory.readN_congr (fun j hj => k3f _ (by omega) (by omega))]; exact bl)
    (by rw [Memory.readN_congr (fun j hj => k3f _ (by omega) (by omega))]; exact bv)
    (fun a h1 h2 => W3.H.st a (by omega) (by omega))
  have W4 := W3.frame (μ' := μ4) (F - 56 + 24) (F - 56 + 32) (by omega) (by omega) (Or.inl (by omega)) dfr drd dwr
  rcases extendH env K hK1 hK x ω4 μ4 W4 (F - 56) (F - 56 + 24) l 1472 31348 ⟨by omega, by omega, by omega⟩
      (by omega) (by omega) hS1 d0 d1 d7 d8 d9 ⟨by decide, by decide, by decide⟩ jte_735 bs_31348
      (by simp; omega) (Or.inr (Or.inl ⟨by omega, by omega, Or.inl (by omega)⟩)) with
    ⟨cap5, ptr5, s5, ω5, μ5, run5, e0, e1, e5, e6, W5, k5⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans run4))) hx).mono
      (by unfold stepGas growGas; rw [Nat.min_eq_right (by omega : 1 ≤ l)]; omega))
  have kw : ∀ a, F - 24 ≤ a → a < F → μ5.read a = μ1.read a := fun a h1 h2 => by
    rw [k5 a (by omega) (by omega) (Or.inl (by omega)), dfr a (by omega) (by omega), k3f a (by omega) h2,
      bfr a (by omega) (by omega)]
  obtain ⟨ω6, run6, f0, f1, f5, f6⟩ := Prefix.pt (p := p) (P := P) (R := refineContractK K env) x ω5 μ5 31348
    (F - 56) ret t r5 r6 (Or.inr rfl) (by omega) e1
    (by rw [show F - 56 + 48 = F - 8 by omega, Memory.readN_congr (fun j hj => kw _ (by omega) (by omega))]
        exact a0')
    (by rw [show F - 56 + 40 = F - 16 by omega, Memory.readN_congr (fun j hj => kw _ (by omega) (by omega))]
        exact a5')
    (by rw [show F - 56 + 32 = F - 24 by omega, Memory.readN_congr (fun j hj => kw _ (by omega) (by omega))]
        exact a6')
    hr5 hr6 hret hjt hbt (fun a h1 h2 => Memory.readable_of_writable (W5.H.st a (by omega) (by omega)))
  have hl8 : μ4.readN (F - 56 + 24) l = Num.encodeLE l (n % 2 ^ (8 * l)) := by
    rw [← readN_take _ _ 8 l (by omega), dw, PrefixBig.enc_take l _ (by omega)]
  rw [hl8] at W5
  refine Or.inl ⟨cap5, ptr5, s5, ω6, μ5,
    (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))).mono
      (by unfold stepGas growGas; rw [Nat.min_eq_right (by omega : 1 ≤ l)]; omega),
    f0, by rw [f1]; congr 1; omega, f5, f6, W5.cast (by rw [henc]; simp), fun a h0 h1 h2 => ?_⟩
  rw [k5 a h0 (by omega) h2, dfr a h0 (by omega), k3 a h0 (by omega) h2, k2 a h0 (Or.inr h1)]

/-- **The length prefix of any n < 2^32, with growth** (`VecCore.prefix_any` over `BufH`): ℰ(n) appended
    (GP v0.8.0 Appendix C), or a failed `realloc` (`ExhaustsW`). Gas `prefixGas n`. -/
theorem prefix_anyH (K : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (x : RefineCtx) (ω : Regs) (μ : Memory) (W : BufH env pb S0 S1 B v len ptr0 s0 μ0 pre cap ptr s μ)
    (F c ret t r5 r6 n : Nat) (hF : S0 + 480 ≤ F ∧ 2147484128 ≤ F ∧ F % 8 = 0) (hB : F ≤ B) (hv : F ≤ v)
    (hS1 : S1 + 16 < 4294967296)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat F) (h5 : ω[5] = UInt64.ofNat r5)
    (h6 : ω[6] = UInt64.ofNat r6) (h7 : ω[7] = UInt64.ofNat c) (h8 : ω[8] = UInt64.ofNat v)
    (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hc : c + 4 ≤ 4294967296) (hcF : c + 4 ≤ F - 56 ∨ F ≤ c) (hn : rdN μ c 4 = n)
    (hrc : ∀ a, c ≤ a → a < c + 4 → μ.readable a = true)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) (hlen : 2 * (len + pre.length + (Blob.encodeNat n).length) ≤ capBound) :
    (∃ cap' ptr' s' ω' μ', FreeStepsH p (refineContractK K env) 30977 ω μ x t ω' μ' x (prefixGas n) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat F ∧ ω'[5] = UInt64.ofNat r5 ∧ ω'[6] = UInt64.ofNat r6 ∧
      BufH env pb S0 S1 B v len ptr0 s0 μ0 (pre ++ Blob.encodeNat n) cap' ptr' s' μ' ∧
      (∀ a, a < 4294967296 → F ≤ a → (a < v ∨ v + 24 ≤ a) → μ'.read a = μ.read a)) ∨
    ExhaustsW env K pb p P 30977 ω μ x (prefixGas n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · have he : Blob.encodeNat 0 = [UInt8.ofNat 0] := rfl
    rw [he] at hlen
    rcases prefix_zeroH K hK1 hK x ω μ W F c ret t r5 r6 hF hB hv hS1 h0 h1 h5 h6 h7 h8 hr5 hr6 hc hcF hn hrc
        hret hjt hbt (by simpa using hlen) with ⟨a, b, c', d, e, run, rest⟩ | hx
    · exact Or.inl ⟨a, b, c', d, e, run.mono (by unfold prefixGas; rw [he]; simp), rest.1, rest.2.1, rest.2.2.1,
        rest.2.2.2.1, by rw [he]; exact rest.2.2.2.2.1, rest.2.2.2.2.2⟩
    · exact Or.inr (hx.mono (by unfold prefixGas; rw [he]; simp))
  rcases Nat.lt_or_ge n 128 with hs | hs
  · have he := PrefixBig.encodeNat_small n ⟨hn1, hs⟩
    rw [he] at hlen
    have hg : 900 + growGas ≤ prefixGas n := by
      unfold prefixGas; rw [he, Nat.div_eq_of_lt hs]; simp
    rcases prefix_smallH K hK1 hK x ω μ W F c ret t r5 r6 n hF hB hv hS1 h0 h1 h5 h6 h7 h8 hr5 hr6 hc hcF hn
        ⟨hn1, hs⟩ hrc hret hjt hbt (by simpa using hlen) with ⟨a, b, c', d, e, run, rest⟩ | hx
    · exact Or.inl ⟨a, b, c', d, e, run.mono hg, rest.1, rest.2.1, rest.2.2.1, rest.2.2.2.1,
        by rw [he]; exact rest.2.2.2.2.1, rest.2.2.2.2.2⟩
    · exact Or.inr (hx.mono hg)
  · have hg : 2000 + growGas * (Blob.encodeNat n).length ≤ prefixGas n := by
      unfold prefixGas; rw [Nat.min_eq_right (by omega : 1 ≤ n / 128)]; omega
    rcases prefix_bigH K hK1 hK x ω μ W F c ret t r5 r6 n hF hB hv hS1 h0 h1 h5 h6 h7 h8 hr5 hr6 hc hcF hn hs
        hrc hret hjt hbt hlen with ⟨a, b, c', d, e, run, rest⟩ | hx
    · exact Or.inl ⟨a, b, c', d, e, run.mono hg, rest⟩
    · exact Or.inr (hx.mono hg)

end

/-- **The length prefix from an arm's frame** (30977, returning to e) for the count n < 2^32 in the scratch
    word F − 32: `StH pre` becomes `StH (pre ++ ℰ(n))`, the frame [F − 56, F) and ω₅, ω₆ kept; or a failed
    `realloc`. The callee frames reach F − 192. -/
theorem prefixH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (x : RefineCtx) (ω : Regs) (μ : Memory)
    {pb S0 S1 D F v len ptr0 ret r5 r6 : Nat} {s0 : State} {μ0 : Memory} {pre : List UInt8}
    (Fr : FrH S0 S1 D F v) (hD : 192 ≤ D) (st : StH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 pre ω μ)
    (n r e : Nat)
    (h0 : ω[0] = UInt64.ofNat r) (h7 : ω[7] = UInt64.ofNat (F - 32)) (h8 : ω[8] = UInt64.ofNat v)
    (hn : rdN μ (F - 32) 4 = n) (hr : 0 < r ∧ r ≤ 2806 ∧ r % 2 = 0)
    (hje : P.jumpTable.getD (r / 2 - 1) 0 = e) (hbe : P.isBlockStart e = true)
    (hlen : 2 * (len + pre.length + (Blob.encodeNat n).length) ≤ capBound) :
    (∃ ω' μ', FreeStepsH p (refineContractK K env) 30977 ω μ x e ω' μ' x (prefixGas n) ∧
      StH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 (pre ++ Blob.encodeNat n) ω' μ' ∧ ω'[5] = ω[5] ∧
      ω'[6] = ω[6] ∧ (∀ a, F - 56 ≤ a → a < F → μ'.read a = μ.read a)) ∨
    ExhaustsW env K pb p P 30977 ω μ x (prefixGas n) := by
  have := Fr.hF8; have := Fr.hFS0; have := Fr.hF2; have := Fr.hFv; have := Fr.hvS1
  obtain ⟨cap, ptr, s, W⟩ := st.buf
  have h5 : ω[5] = UInt64.ofNat ω[5].toNat := UInt64.ofNat_toNat.symm
  have h6 : ω[6] = UInt64.ofNat ω[6].toNat := UInt64.ofNat_toNat.symm
  rcases prefix_anyH K hK1 hK x ω μ W (F - 56) (F - 32) r e ω[5].toNat ω[6].toNat n
      ⟨by omega, by omega, by omega⟩ (by omega) (by omega) Fr.hS1 h0 st.h1 h5 h6 h7 h8 (UInt64.toNat_lt _)
      (UInt64.toNat_lt _) (by omega) (Or.inr (by omega)) hn
      (fun a h1 h2 => Memory.readable_of_writable (W.H.st a (by omega) (by omega))) hr hje hbe hlen with
    ⟨cap', ptr', s', ω', μ', run, e0, e1, e5, e6, W', kF⟩ | hx
  · have kF' : ∀ a, F - 56 ≤ a → a < F → μ'.read a = μ.read a := fun a h1 h2 =>
      kF a (by omega) h1 (Or.inl (by omega))
    refine Or.inl ⟨ω', μ', run, ⟨by rw [e1], ?_, ?_, ?_, ⟨cap', ptr', s', W'⟩⟩, by rw [e5, ← h5],
      by rw [e6, ← h6], kF'⟩
    · rw [Memory.readN_congr (fun j hj => kF' _ (by omega) (by omega))]; exact st.w0
    · rw [Memory.readN_congr (fun j hj => kF' _ (by omega) (by omega))]; exact st.w5
    · rw [Memory.readN_congr (fun j hj => kF' _ (by omega) (by omega))]; exact st.w6
  · exact Or.inr hx

/-- `prefixH` for `StDH`. -/
theorem prefixDH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (x : RefineCtx) (ω : Regs) (μ : Memory)
    {pb S0 S1 D F v len ptr0 ret r5 r6 : Nat} {s0 : State} {μ0 : Memory} {pre : List UInt8}
    (Fr : FrH S0 S1 D F v) (hD : 192 ≤ D) (st : StDH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 pre ω μ)
    (n r e : Nat)
    (h0 : ω[0] = UInt64.ofNat r) (h7 : ω[7] = UInt64.ofNat (F - 32)) (h8 : ω[8] = UInt64.ofNat v)
    (hn : rdN μ (F - 32) 4 = n) (hr : 0 < r ∧ r ≤ 2806 ∧ r % 2 = 0)
    (hje : P.jumpTable.getD (r / 2 - 1) 0 = e) (hbe : P.isBlockStart e = true)
    (hlen : 2 * (len + pre.length + (Blob.encodeNat n).length) ≤ capBound) :
    (∃ ω' μ', FreeStepsH p (refineContractK K env) 30977 ω μ x e ω' μ' x (prefixGas n) ∧
      StDH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 (pre ++ Blob.encodeNat n) ω' μ' ∧ ω'[5] = ω[5] ∧
      ω'[6] = ω[6] ∧ (∀ a, F - 56 ≤ a → a < F → μ'.read a = μ.read a)) ∨
    ExhaustsW env K pb p P 30977 ω μ x (prefixGas n) := by
  have := Fr.hF2
  rcases prefixH env K hK1 hK x ω μ Fr hD st.toStH n r e h0 h7 h8 hn hr hje hbe hlen with
    ⟨ω', μ', run, st', e5, e6, kF⟩ | hx
  · exact Or.inl ⟨ω', μ', run, ⟨st', by rw [Memory.readN_congr (fun j hj => kF _ (by omega) (by omega))]; exact st.sv⟩,
      e5, e6, kF⟩
  · exact Or.inr hx

end Services.Bootstrap.Encode.GrowH
