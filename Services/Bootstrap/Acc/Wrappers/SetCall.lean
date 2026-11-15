import Services.Bootstrap.Acc.Wrappers.Set
import Services.Bootstrap.Acc.Wrappers.GetCall

/-!
# The SDK's `set` (48104) as a run of `accContractS`

From the call with out at ω₇, the key at ω₈ (ω₉ octets) and the value at ω₁₀ (ω₁₁ octets): one Ω_W
(GP v0.8.0 Appendix B) on this service's storage (`write_stepS`), then `SetOut` at out. x's account
becomes `writeSelf`, y and the answer stream are kept (`set_call`). Two entries of the error table in
read-only data (69056, 69072) are hypotheses until read-only memory is carried through runs.
-/

namespace Services.Bootstrap.Acc
open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- What `set` leaves at out for Ω_W's reply r: `Err` (−1, then the code 3) for FULL, `Ok(None)` (0)
    for NONE, `Ok(Some(r))` (1, r) otherwise. -/
def SetOut (μ : Memory) (out r : Nat) : Prop :=
  if r = Result.FULL then μ.readN out 8 = Num.encodeLE 8 18446744073709551615 ∧ μ.readN (out + 8) 1 = [3]
  else if r = Result.NONE then μ.readN out 8 = Num.encodeLE 8 0
  else μ.readN out 8 = Num.encodeLE 8 1 ∧ μ.readN (out + 8) 8 = Num.encodeLE 8 r

/-- **The SDK's `set`, 48104 → its return**: one Ω_W of (key, value) on this service's storage, then
    `SetOut` at out, ω₀, ω₅, ω₆ restored and the frame popped, at one of the three returns' `jumpInd`
    (48158, 48250, 48235). x's account is `writeSelf`; y and the stream are kept. The error table's
    entries for NONE and FULL (read-only data at 69072 and 69056) are taken as hypotheses. -/
theorem set_call {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : AccEnv)
    (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory) (sp out kO kZ vO vZ : Nat) (key value : List UInt8)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat out) (h8 : ω[8] = UInt64.ofNat kO)
    (h9 : ω[9] = UInt64.ofNat kZ) (h10 : ω[10] = UInt64.ofNat vO) (h11 : ω[11] = UInt64.ofNat vZ)
    (hkZ : kZ < 2 ^ 32) (hvZ : vZ < 2 ^ 32) (hkr : kO + kZ ≤ 4294967296) (hvr : vO + vZ ≤ 4294967296)
    (hsp : 65536 + 24 ≤ sp ∧ sp < 4294967296) (hout : 65536 ≤ out ∧ out + 16 < 4294967296)
    (hwf : ∀ a, sp - 24 ≤ a → a < sp → μ.writable a = true)
    (hwo : ∀ a, out ≤ a → a < out + 16 → μ.writable a = true) (dos : out + 16 ≤ sp - 24 ∨ sp ≤ out)
    (hk : μ.rangeReadable kO kZ = true) (hkey : μ.readN kO kZ = key)
    (hv : μ.rangeReadable vO vZ = true) (hval : μ.readN vO vZ = value) (hvl : value.length = vZ)
    (dk : kO + kZ ≤ sp - 24 ∨ sp ≤ kO) (dv : vO + vZ ≤ sp - 24 ∨ sp ≤ vO)
    (ht8 : rdN μ 69072 4 = 4294900408) (ht4 : rdN μ 69056 4 = 4294900402)
    (htr : ∀ a, 69056 ≤ a → a < 69076 → μ.readable a = true) (dt : 69076 ≤ sp - 24)
    (hold : ∀ v, c.1.self.storage.get? key = some v → v.length < 2 ^ 63) :
    ∃ e ω' μ', (e = 48158 ∨ e = 48250 ∨ e = 48235) ∧
      FreeStepsH p (YIn (accContractS env) c.2 c.2) 48104 ω μ (c, f) e ω' μ'
        ((c.1.setSelf (writeSelf c.1.self key value), c.2), f) 50 ∧
      ω'[0] = ω[0] ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      SetOut μ' out (writeR7 c.1.self key value) ∧
      (∀ a, a < 4294967296 → (a < sp - 24 ∨ sp ≤ a) → (a < out ∨ out + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨ω1, μ1, run1, b1, b5, b6, b7, b8, b9, b10, b0, m16, m8, m0, fr1, rd1, wr1, bo1⟩ :=
    sw_pre (p := p) (P := P) (R := YIn (accContractS env) c.2 c.2) (c, f) ω μ sp h1 hsp hwf
  have keep1 : ∀ o n, o + n ≤ 4294967296 → (o + n ≤ sp - 24 ∨ sp ≤ o) → μ1.readN o n = μ.readN o n :=
    fun o n h0 h => PVM.Memory.readN_congr fun j hj => fr1 _ (by omega) (by omega)
  have rr : ∀ o n, μ1.rangeReadable o n = μ.rangeReadable o n := fun o n => by
    unfold Memory.rangeReadable; simp only [rd1]
  have hst : YIn (accContractS env) c.2 c.2 5 ω1 μ1 (c, f) .cont (setR7 ω1 (writeR7 c.1.self key value)) μ1
      ((c.1.setSelf (writeSelf c.1.self key value), c.2), f) :=
    ⟨write_stepS env ω1 μ1 (c, f) kO kZ vO vZ key value (reg_of (b7.trans h8) (by omega))
      (reg_of (b8.trans h9) (by omega)) (reg_of (b9.trans h10) (by omega)) (reg_of (b10.trans h11) (by omega))
      hkZ hvZ (by rw [rr]; exact hk) (by rw [keep1 _ _ hkr dk]; exact hkey) (by rw [rr]; exact hv)
      (by rw [keep1 _ _ hvr dv]; exact hval) hvl, .inl rfl⟩
  generalize hr : writeR7 c.1.self key value = r at hst ⊢
  have e7 : (setR7 ω1 r)[7] = UInt64.ofNat r := by unfold setR7; rw [Vector.getElem_set]; simp
  have sr : ∀ j : Nat, (hj : j < 13) → j ≠ 7 → (setR7 ω1 r)[j] = ω1[j] := by
    intro j hj h; unfold setR7; rw [Vector.getElem_set]; simp [Ne.symm h]
  have e1 : (setR7 ω1 r)[1] = UInt64.ofNat (sp - 24) := (sr 1 (by decide) (by decide)).trans b1
  have e5 : (setR7 ω1 r)[5] = UInt64.ofNat out := (sr 5 (by decide) (by decide)).trans (b5.trans h7)
  have e6 : (setR7 ω1 r)[6] = UInt64.ofNat 18446744073709551606 := (sr 6 (by decide) (by decide)).trans b6
  have n0 : μ1.readN (sp - 24) 8 = Num.encodeLE 8 ω[6].toNat := readN_of_rdN m0
  have n8 : μ1.readN (sp - 24 + 8) 8 = Num.encodeLE 8 ω[5].toNat := readN_of_rdN m8
  have n16 : μ1.readN (sp - 24 + 16) 8 = Num.encodeLE 8 ω[0].toNat := readN_of_rdN m16
  have hrf : ∀ a, sp - 24 ≤ a → a < sp - 24 + 24 → μ1.readable a = true := fun a h1 h2 => by
    rw [rd1]; exact Memory.readable_of_writable (hwf a h1 (by omega))
  have hwo1 : ∀ a, out ≤ a → a < out + 16 → μ1.writable a = true := fun a h1 h2 => by rw [wr1]; exact hwo a h1 h2
  have tk : ∀ a, 69056 ≤ a → a < 69076 → μ1.read a = μ.read a := fun a h1 h2 => fr1 a (by omega) (Or.inl (by omega))
  have ht8' : rdN μ1 69072 4 = 4294900408 := by
    rw [← ht8]; unfold rdN; congr 1; exact PVM.Memory.readN_congr fun j hj => tk _ (by omega) (by omega)
  have ht4' : rdN μ1 69056 4 = 4294900402 := by
    rw [← ht4]; unfold rdN; congr 1; exact PVM.Memory.readN_congr fun j hj => tk _ (by omega) (by omega)
  have htr' : ∀ a, 69056 ≤ a → a < 69076 → μ1.readable a = true := fun a h1 h2 => by rw [rd1]; exact htr a h1 h2
  have hrv : r = Result.FULL ∨ r = Result.NONE ∨ r < 2 ^ 63 := by
    rw [← hr]; unfold writeR7
    split
    · exact .inl rfl
    · cases hg : c.1.self.storage.get? key with
      | none => exact .inr (.inl rfl)
      | some v => exact .inr (.inr (by simpa using hold v hg))
  have dos' : out + 16 ≤ sp - 24 ∨ sp - 24 + 24 ≤ out := by omega
  rcases hrv with rfl | rfl | hlt
  · obtain ⟨ω2, μ2, run2, g0, g1, g5, g6, o0, o8, fr2, rd2, wr2⟩ :=
      sw_full (p := p) (P := P) (R := YIn (accContractS env) c.2 c.2) _ (setR7 ω1 Result.FULL) μ1 (sp - 24) out
        ω[0].toNat ω[5].toNat ω[6].toNat e1 e5 e6 e7 ht4' (fun a h1 h2 => htr' a h1 (by omega))
        ⟨by omega, by omega⟩ hout n0 n8 n16 hrf hwo1 dos' (UInt64.toNat_lt _) (UInt64.toNat_lt _) (UInt64.toNat_lt _)
    refine ⟨48235, ω2, μ2, .inr (.inr rfl), (run1.trans (FreeStepsH.host_decode (d_48132 (p := p) (P := P)) hst run2)).mono
      (by omega), by rw [g0, UInt64.ofNat_toNat], by rw [g1, show sp - 24 + 24 = sp by omega],
      by rw [g5, UInt64.ofNat_toNat], by rw [g6, UInt64.ofNat_toNat], ?_, fun a h0 hs ho => ?_,
      fun a => (rd2 a).trans (rd1 a), fun a => (wr2 a).trans (wr1 a)⟩
    · unfold SetOut; rw [if_pos rfl]; exact ⟨o0, o8⟩
    · rw [fr2 a h0 (by omega), fr1 a h0 hs]
  · obtain ⟨ω2, μ2, run2, g0, g1, g5, g6, o0, fr2, rd2, wr2⟩ :=
      sw_none (p := p) (P := P) (R := YIn (accContractS env) c.2 c.2) _ (setR7 ω1 Result.NONE) μ1 (sp - 24) out
        ω[0].toNat ω[5].toNat ω[6].toNat e1 e5 e6 e7 ht8' (fun a h1 h2 => htr' a (by omega) h2)
        ⟨by omega, by omega⟩ hout n0 n8 n16 hrf hwo1 dos' (UInt64.toNat_lt _) (UInt64.toNat_lt _) (UInt64.toNat_lt _)
    refine ⟨48250, ω2, μ2, .inr (.inl rfl), (run1.trans (FreeStepsH.host_decode (d_48132 (p := p) (P := P)) hst run2)).mono
      (by omega), by rw [g0, UInt64.ofNat_toNat], by rw [g1, show sp - 24 + 24 = sp by omega],
      by rw [g5, UInt64.ofNat_toNat], by rw [g6, UInt64.ofNat_toNat], ?_, fun a h0 hs ho => ?_,
      fun a => (rd2 a).trans (rd1 a), fun a => (wr2 a).trans (wr1 a)⟩
    · unfold SetOut; rw [if_neg (by decide), if_pos rfl]; exact o0
    · rw [fr2 a h0 (by omega), fr1 a h0 hs]
  · obtain ⟨ω2, μ2, run2, g0, g1, g5, g6, o0, o8, fr2, rd2, wr2⟩ :=
      sw_some (p := p) (P := P) (R := YIn (accContractS env) c.2 c.2) _ (setR7 ω1 r) μ1 (sp - 24) out
        ω[0].toNat ω[5].toNat ω[6].toNat e1 e5 e6 r e7 (by omega)
        ⟨by omega, by omega⟩ hout n0 n8 n16 hrf hwo1 dos' (UInt64.toNat_lt _) (UInt64.toNat_lt _) (UInt64.toNat_lt _)
    refine ⟨48158, ω2, μ2, .inl rfl, (run1.trans (FreeStepsH.host_decode (d_48132 (p := p) (P := P)) hst run2)).mono
      (by omega), by rw [g0, UInt64.ofNat_toNat], by rw [g1, show sp - 24 + 24 = sp by omega],
      by rw [g5, UInt64.ofNat_toNat], by rw [g6, UInt64.ofNat_toNat], ?_, fun a h0 hs ho => ?_,
      fun a => (rd2 a).trans (rd1 a), fun a => (wr2 a).trans (wr1 a)⟩
    · unfold SetOut
      rw [if_neg (by unfold Result.FULL; omega), if_neg (by unfold Result.NONE; omega)]; exact ⟨o0, o8⟩
    · rw [fr2 a h0 ho, fr1 a h0 hs]

end Services.Bootstrap.Acc
