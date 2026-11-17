import Services.Bootstrap.Acc.Wrappers.Remove
import Services.Bootstrap.Acc.Wrappers.SetCall

/-!
# The SDK's `remove` (48481) as a run of `accContractS`

From the call with the key at ω₇ (ω₈ octets): one Ω_W (GP v0.8.0 Appendix B) of an empty value on
this service's storage (`write_stepS`). Ω_W's reply r = `writeR7 self key []` then decides:
- FULL: the run reaches the trap at 48533 (`rm_full`). This is quirk Q18; the spec panics there too.
- otherwise r is the old value's length (< 2⁶³ by `ValuesFit`) or NONE, and `remove` returns 1 or 0
  (`rm_ret`), with x's account := `writeSelf self key []`.
-/

namespace Services.Bootstrap.Acc
open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
variable {X : Type} {R : HostRel X}

/-- **48495 … 48533**, Ω_W's reply FULL (2⁶⁴ − 5): not below 2⁶⁴ − 9 and not NONE, so the run
    reaches the trap at 48533 (quirk Q18). -/
theorem rm_full {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (h7 : ω[7] = UInt64.ofNat Result.FULL) :
    ∃ ω', FreeStepsH p R 48495 ω μ x 48533 ω' μ x 4 := by
  unfold Result.FULL at h7
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run⟩
  case run => pvm_go [h7]

/-- **The SDK's `remove`, 48481 → its return or the trap**, for the key at ω₇ (ω₈ octets) in memory
    off the 16-octet frame. One Ω_W of (key, []) on this service's storage: x's account becomes
    `writeSelf self key []`, y and the stream are kept. If its reply `writeR7 self key []` is FULL
    the run reaches the trap at 48533 (quirk Q18); otherwise it returns, at one of the two returns'
    `jumpInd` (48514, 48531), with ω₇ = 1 if the key held a value and 0 if not, ω₀ and ω₅ as at the
    call, the frame popped, and memory kept off the frame. -/
theorem remove_call {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : AccEnv)
    (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory) (sp kO kZ : Nat) (key : List UInt8)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat kO) (h8 : ω[8] = UInt64.ofNat kZ)
    (hkZ : kZ < 2 ^ 32) (hkr : kO + kZ ≤ 4294967296)
    (hsp : 65536 + 16 ≤ sp ∧ sp < 4294967296)
    (hwf : ∀ a, sp - 16 ≤ a → a < sp → μ.writable a = true)
    (hk : μ.rangeReadable kO kZ = true) (hkey : μ.readN kO kZ = key) (dk : kO + kZ ≤ sp - 16 ∨ sp ≤ kO)
    (hold : ∀ v, c.1.self.storage.get? key = some v → v.length < 2 ^ 63) :
    let c' := ((c.1.setSelf (writeSelf c.1.self key []), c.2), f)
    (writeR7 c.1.self key [] = Result.FULL ∧
      ∃ ω' μ', FreeStepsH p (YIn (accContractS env) c.2 c.2) 48481 ω μ (c, f) 48533 ω' μ' c' 11) ∨
    (writeR7 c.1.self key [] ≠ Result.FULL ∧
      ∃ e ω' μ', (e = 48514 ∨ e = 48531) ∧
        FreeStepsH p (YIn (accContractS env) c.2 c.2) 48481 ω μ (c, f) e ω' μ' c' 19 ∧
        ω'[7] = UInt64.ofNat (if c.1.self.storage.get? key = none then 0 else 1) ∧
        ω'[0] = ω[0] ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
        (∀ a, a < 4294967296 → (a < sp - 16 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
        (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a)) := by
  intro c'
  obtain ⟨ω1, μ1, run1, b1, b9, b10, m8, m0, fr1, rd1, wr1, bo1⟩ :=
    rm_pre (p := p) (P := P) (R := YIn (accContractS env) c.2 c.2) (c, f) ω μ sp h1 hsp hwf
  have rr : ∀ o n, μ1.rangeReadable o n = μ.rangeReadable o n := fun o n => by
    unfold Memory.rangeReadable; simp only [rd1]
  have keyk : μ1.readN kO kZ = key := by
    rw [← hkey]; exact PVM.Memory.readN_congr fun j hj => fr1 _ (by omega) (by omega)
  have b7 : ω1[7] = ω[7] := bo1 7 (by decide)
  have b8 : ω1[8] = ω[8] := bo1 8 (by decide)
  have hst : YIn (accContractS env) c.2 c.2 5 ω1 μ1 (c, f) .cont (setR7 ω1 (writeR7 c.1.self key []))
      μ1 c' :=
    ⟨write_stepS env ω1 μ1 (c, f) kO kZ 0 0 key [] (reg_of (b7.trans h7) (by omega))
      (reg_of (b8.trans h8) (by omega)) (reg_of b9 (by decide)) (reg_of b10 (by decide))
      hkZ (by decide) (by rw [rr]; exact hk) keyk (by simp [Memory.rangeReadable]) rfl rfl, .inl rfl⟩
  generalize hr : writeR7 c.1.self key [] = r at hst ⊢
  have e7 : (setR7 ω1 r)[7] = UInt64.ofNat r := by unfold setR7; rw [Vector.getElem_set]; simp
  have sr : ∀ j : Nat, (hj : j < 13) → j ≠ 7 → (setR7 ω1 r)[j] = ω1[j] := by
    intro j hj h; unfold setR7; rw [Vector.getElem_set]; simp [Ne.symm h]
  by_cases hF : r = Result.FULL
  · subst hF
    obtain ⟨ω2, run2⟩ := rm_full (p := p) (P := P) (R := YIn (accContractS env) c.2 c.2) c'
      (setR7 ω1 Result.FULL) μ1 e7
    exact .inl ⟨rfl, ω2, μ1, (run1.trans (FreeStepsH.host_decode (d_48493 (p := p) (P := P)) hst run2))⟩
  · right
    refine ⟨hF, ?_⟩
    have hrv : (c.1.self.storage.get? key = none ∧ r = Result.NONE) ∨
        (c.1.self.storage.get? key ≠ none ∧ r < 2 ^ 63) := by
      rw [← hr] at hF ⊢; unfold writeR7 at hF ⊢
      split at hF
      · exact absurd rfl hF
      · rename_i hb
        rw [if_neg hb]
        cases hg : c.1.self.storage.get? key with
          | none => exact .inl ⟨rfl, by simp⟩
          | some v => exact .inr ⟨by simp, by simpa using hold v hg⟩
    have e1 : (setR7 ω1 r)[1] = UInt64.ofNat (sp - 16) := (sr 1 (by decide) (by decide)).trans b1
    have n0 : μ1.readN (sp - 16) 8 = Num.encodeLE 8 ω[5].toNat := readN_of_rdN m0
    have n8 : μ1.readN (sp - 16 + 8) 8 = Num.encodeLE 8 ω[0].toNat := readN_of_rdN m8
    have hrf : ∀ a, sp - 16 ≤ a → a < sp - 16 + 16 → μ1.readable a = true := fun a h1 h2 => by
      rw [rd1]; exact Memory.readable_of_writable (hwf a h1 (by omega))
    obtain ⟨e, ω2, run2, hlt, hnone, g0, g1, g5, g6⟩ :=
      rm_ret (p := p) (P := P) (R := YIn (accContractS env) c.2 c.2) c' (setR7 ω1 r) μ1 (sp - 16) r
        ω[0].toNat ω[5].toNat e1 e7
        (by rcases hrv with ⟨-, h⟩ | ⟨-, h⟩
            · exact .inr (by rw [h]; rfl)
            · exact .inl (by omega))
        ⟨by omega, by omega⟩ n0 n8 hrf (UInt64.toNat_lt _) (UInt64.toNat_lt _)
    have he : (e = 48514 ∨ e = 48531) ∧
        ω2[7] = UInt64.ofNat (if c.1.self.storage.get? key = none then 0 else 1) := by
      rcases hrv with ⟨hg, rfl⟩ | ⟨hg, h⟩
      · obtain ⟨ee, ew⟩ := hnone (by rfl); rw [if_pos hg]; exact ⟨.inr ee, ew⟩
      · obtain ⟨ee, ew⟩ := hlt (by omega); rw [if_neg hg]; exact ⟨.inl ee, ew⟩
    exact ⟨e, ω2, μ1, he.1, (run1.trans (FreeStepsH.host_decode (d_48493 (p := p) (P := P)) hst run2)).mono
      (by omega), he.2, by rw [g0, UInt64.ofNat_toNat], by rw [g1, show sp - 16 + 16 = sp by omega],
      by rw [g5, UInt64.ofNat_toNat],
      by rw [g6, sr 6 (by decide) (by decide)]; exact bo1 ⟨6, by decide⟩ (by decide),
      fun a h0 hs => fr1 a h0 hs, rd1, wr1⟩

end Services.Bootstrap.Acc
