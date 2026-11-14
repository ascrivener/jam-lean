import Services.Bootstrap.Encode.VariantsVec

/-!
# The arms `Bless` (11), `Assign` (12) and `Designate` (13): shared pieces

* `startD`: the dispatch (`Encode.Dispatch.dispatch`) into `StD []` for any variant 1 ≤ t ≤ 24, with
  the writer in ω₁₀ and the value in ω₁₁ (as `Fixed.start`, with the stack [F − D, F)).
* `ext_srcD`: one call of `Vec<u8>::extend_from_slice` (58508) for n > 0 octets at `src` inside the
  heap stretch [lo, hi), its conditions on `src` derived from the padded stretch [lo − 24, hi + 24)
  being below 2^32, readable and apart from the frame [F − D, F), the element's encoding and the writer
  (as `EncOkMD` asks of its heap octets, `VecSrc`); the octets are as at entry.
-/

namespace Services.Bootstrap.Encode.Enc

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeA
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Encode.EncMD

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- From 30145 to the arm of the variant with discriminant word 2^63 + t − 1, in `StD []`, with the
    writer in ω₁₀ and the value in ω₁₁. -/
theorem startD {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    {D F S v cap ptr len N ret t' : Nat} (L : LayD P D F S v cap ptr len N ret t' μ) (hD : 136 ≤ D)
    (t : Nat) (ht : 1 ≤ t ∧ t < 25)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat F) (h7 : ω[7] = UInt64.ofNat S)
    (h8 : ω[8] = UInt64.ofNat v) (hD8 : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + t))
    (tab : μ.readN 67376 100 = table) (hrt : ∀ a, 67376 ≤ a → a < 67476 → μ.readable a = true) :
    ∃ ω1 μ1, FreeStepsH p R 30145 ω μ x (arm t) ω1 μ1 x 24 ∧
      StD D F v ptr len ret ω[5].toNat ω[6].toNat μ [] ω1 μ1 ∧
      ω1[10] = UInt64.ofNat v ∧ ω1[11] = UInt64.ofNat S := by
  have hF := L.hF; have hF' := L.hF'; have hS := L.hS; have hS' := L.hS'; have hSF := L.hSF
  have hv := L.hv; have hvF := L.hvF
  have h5 : ω[5] = UInt64.ofNat ω[5].toNat := UInt64.ofNat_toNat.symm
  have h6 : ω[6] = UInt64.ofNat ω[6].toNat := UInt64.ofNat_toNat.symm
  have hret := L.hret
  obtain ⟨ω1, μ1, run1, a1, a10, a11, a0', a5', a6', av, afr, ard, awr⟩ := dispatch (p := p) (P := P)
    (R := R) x ω μ F S v ret ω[5].toNat ω[6].toNat t ht ⟨by omega, hF'⟩ h0 h1 h5 h6 h7 h8 (by omega)
    (UInt64.toNat_lt _) (UInt64.toNat_lt _) (by omega) (by omega) (by omega) hD8 tab hrt
    (fun a h1 h2 => L.hrS a h1 (by omega)) (fun a h1 h2 => L.hwF a (by omega) h2)
  refine ⟨ω1, μ1, run1, ⟨a1, a0', a5', a6', av, ?_, by simp [Memory.readN],
    fun a h0 h1 _ _ => afr a h0 (by omega), ard, awr⟩, a10, a11⟩
  rw [Memory.readN_congr (fun j hj => afr _ (by omega) (by omega))]; simpa using L.vl

/-- **One call of `Vec<u8>::extend_from_slice` for n > 0 heap octets** (58508, returning to e) at `src`
    inside [lo, hi), the padded stretch [lo − 24, hi + 24) below 2^32, readable and apart from the frame
    [F − D, F), the element's encoding (N octets at ptr + len) and the writer, with 65536 ≤ lo:
    `StD pre` becomes `StD (pre ++ μ0.readN src n)`, the octets as at entry. -/
theorem ext_srcD {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ μ0 : Memory)
    {D F S v cap ptr len N ret t r5 r6 : Nat} {pre : List UInt8} (L : LayD P D F S v cap ptr len N ret t μ0)
    (hD : 136 ≤ D) (st : StD D F v ptr len ret r5 r6 μ0 pre ω μ) (src n r e lo hi : Nat)
    (h0 : ω[0] = UInt64.ofNat r) (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat src)
    (h9 : ω[9] = UInt64.ofNat n) (hr : 0 < r ∧ r ≤ 2806 ∧ r % 2 = 0) (hje : P.jumpTable.getD (r / 2 - 1) 0 = e)
    (hbe : P.isBlockStart e = true) (hn : pre.length + n ≤ N) (hn0 : 0 < n)
    (hin : lo ≤ src ∧ src + n ≤ hi) (hlo : 65536 ≤ lo)
    (hsrc : ∀ a, lo ≤ a + 24 → a < hi + 24 → a < 4294967296 ∧ μ0.readable a = true ∧
      (a < F - D ∨ F ≤ a) ∧ (a < ptr + len ∨ ptr + len + N ≤ a) ∧ (a < v ∨ v + 24 ≤ a)) :
    ∃ ω' μ', FreeStepsH p R 58508 ω μ x e ω' μ' x (7 * n + 360) ∧
      StD D F v ptr len ret r5 r6 μ0 (pre ++ μ0.readN src n) ω' μ' ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      (∀ a, F - 56 ≤ a → a < F → μ'.read a = μ.read a) := by
  have hF := L.hF; have hF' := L.hF'
  have hlo' : lo - 24 < hi + 24 := by omega
  have s1 := side (X := F - D) (Y := F) (by omega) hlo' (fun a h1 h2 => (hsrc a (by omega) h2).2.2.1)
  have s2 := side (X := ptr + len) (Y := ptr + len + N) (by have := L.hd; omega) hlo'
    (fun a h1 h2 => (hsrc a (by omega) h2).2.2.2.1)
  have s3 := (hsrc (hi + 23) (by omega) (by omega)).1
  have kq : ∀ a, src ≤ a → a < src + n → μ.read a = μ0.read a := fun a h1 h2 => by
    obtain ⟨a0, -, a2, a3, a4⟩ := hsrc a (by omega) (by omega)
    exact st.keep a a0 a2 (by omega) (by omega)
  obtain ⟨ω', μ', run, st', c5, c6, kF⟩ := ext_stepD (p := p) (P := P) (R := R) x ω μ μ0 L hD st src n r e
    h0 h7 h8 h9 hr hje hbe hn ⟨by omega, by omega⟩ (by omega) (by omega)
    (fun a h1 h2 => by rw [st.rd]; exact (hsrc a (by omega) (by omega)).2.1)
  rw [Memory.readN_congr (fun j hj => kq _ (by omega) (by omega))] at st'
  exact ⟨ω', μ', run, st', c5, c6, kF⟩

end Services.Bootstrap.Encode.Enc
