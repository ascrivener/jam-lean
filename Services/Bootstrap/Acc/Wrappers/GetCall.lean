import Services.Bootstrap.Acc.Wrappers.Get
import Services.Bootstrap.Acc.Wrappers.GrowS

/-!
# The SDK's `get` (47857) as runs of `accContractS`

From the call with the key at ω₈ (ω₉ octets) and out at ω₇: Ω_R (GP v0.8.0 Appendix B) on this
service's storage, then `Option<Vec<u8>>` at out, with the context and the answer stream kept.
- `get_none`: an absent key, `None` (the capacity word −1) at out (47927);
- `get_empty`: an empty value, `Some(Vec { 0, 1, 0 })` (47957).
-/

namespace Services.Bootstrap.Acc
open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem reg_of {ω : Regs} {k : Fin 13} {n : Nat} (h : ω[k] = UInt64.ofNat n) (hn : n < 2 ^ 64) : reg ω k = n := by
  unfold reg; rw [show ω.get k = ω[k] from rfl, h, UInt64.toNat_ofNat_of_lt' hn]

theorem readRegs_7 (ω : Regs) (v : Option (List UInt8)) :
    (readRegs ω v)[7] = UInt64.ofNat (match v with | none => Result.NONE | some v => v.length) := by
  cases v <;> (unfold readRegs setR7; rw [Vector.getElem_set]; simp only [↓reduceIte])

theorem readRegs_ne (ω : Regs) (v : Option (List UInt8)) (j : Nat) (hj : j < 13) (h : j ≠ 7) :
    (readRegs ω v)[j] = ω[j] := by
  unfold readRegs setR7; rw [Vector.getElem_set]; simp [Ne.symm h]

theorem readN_of_rdN {μ : Memory} {a n v : Nat} (h : rdN μ a n = v) : μ.readN a n = Num.encodeLE n v := by
  have e := encodeLE_decodeLE (μ.readN a n)
  rw [Memory.length_readN] at e
  rw [← e]; unfold rdN at h; rw [h]

/-- **The SDK's `get`, 47857 → 47927, for an absent key**: `None` at out, ω₀, ω₅, ω₆ restored and
    the frame popped, at the return's `jumpInd`; the context and the stream kept. -/
theorem get_none {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : AccEnv)
    (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory) (sp out kO kZ : Nat) (key : List UInt8)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat out) (h8 : ω[8] = UInt64.ofNat kO)
    (h9 : ω[9] = UInt64.ofNat kZ) (hkZ : kZ < 2 ^ 32)
    (hsp : 65536 + 48 ≤ sp ∧ sp < 4294967296) (hout : sp ≤ out ∧ out + 8 < 4294967296)
    (hwf : ∀ a, sp - 48 ≤ a → a < sp → μ.writable a = true)
    (hwo : ∀ a, out ≤ a → a < out + 8 → μ.writable a = true)
    (hk : μ.rangeReadable kO kZ = true) (hkey : μ.readN kO kZ = key)
    (dk : kO + kZ ≤ sp - 48 ∨ sp ≤ kO) (hkr : kO + kZ ≤ 4294967296)
    (hv : c.1.self.storage.get? key = none) :
    ∃ ω' μ', FreeStepsH p (KeepCtx (accContractS env)) 47857 ω μ (c, f) 47927 ω' μ' (c, f) 40 ∧
      ω'[0] = ω[0] ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      μ'.readN out 8 = Num.encodeLE 8 18446744073709551615 ∧
      (∀ a, a < 4294967296 → (a < sp - 48 ∨ sp ≤ a) → (a < out ∨ out + 8 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨ω1, μ1, run1, b1, b5, b7, b10, b11, b12, m40, m32, m24, m16, m8, fr1, rd1, wr1, bo⟩ :=
    gr_pre (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω μ sp h1 hsp hwf
  have hk1 : μ1.rangeReadable kO kZ = true := by
    rw [← hk]; unfold Memory.rangeReadable; simp only [rd1]
  have hkey1 : μ1.readN kO kZ = key := by
    rw [← hkey]; apply PVM.Memory.readN_congr; intro j hj
    exact fr1 _ (by omega) (by omega)
  have hst : KeepCtx (accContractS env) 4 ω1 μ1 (c, f) .cont (readRegs ω1 none) (readMem μ1 0 0 none) (c, f) := by
    have := read_stepS env ω1 μ1 (c, f) kO kZ 0 0 key (reg_of b7 (by decide))
      (reg_of ((bo 8 (by decide)).trans h8) (by omega)) (reg_of ((bo 9 (by decide)).trans h9) (by omega))
      (reg_of b10 (by decide)) (reg_of b11 (by decide)) (reg_of b12 (by decide)) hkZ (by decide) hk1 hkey1
      (by simp [Memory.rangeWritable])
    rw [hv] at this
    exact ⟨this, rfl⟩
  simp only [readMem] at hst
  have e7 : (readRegs ω1 none)[7] = UInt64.ofNat 18446744073709551615 := readRegs_7 ω1 none
  have e1 : (readRegs ω1 none)[1] = UInt64.ofNat (sp - 48) := (readRegs_ne ω1 none 1 (by decide) (by decide)).trans b1
  have hrf : ∀ a, sp - 48 ≤ a → a < sp - 48 + 48 → μ1.readable a = true := fun a h1 h2 => by
    rw [rd1]; exact Memory.readable_of_writable (hwf a h1 (by omega))
  have hwo1 : ∀ a, out ≤ a → a < out + 8 → μ1.writable a = true := fun a h1 h2 => by rw [wr1]; exact hwo a h1 h2
  obtain ⟨ω2, μ2, run2, g0, g1, g5, g6, o0, fr2, rd2, wr2⟩ :=
    gr_none (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) (readRegs ω1 none) μ1 (sp - 48) out
      ω[0].toNat ω[5].toNat ω[6].toNat e1 e7 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (readN_of_rdN (m16.trans (by rw [h7, UInt64.toNat_ofNat_of_lt' (show out < 2 ^ 64 by omega)]))) (readN_of_rdN m24) (readN_of_rdN m32) (readN_of_rdN m40) hrf hwo1 (by omega)
      (UInt64.toNat_lt _) (UInt64.toNat_lt _) (UInt64.toNat_lt _)
  refine ⟨ω2, μ2, ((run1.trans (FreeStepsH.host_decode (d_47886 (p := p) (P := P)) hst run2))).mono (by omega),
    by rw [g0, UInt64.ofNat_toNat], by rw [g1, show sp - 48 + 48 = sp by omega], by rw [g5, UInt64.ofNat_toNat],
    by rw [g6, UInt64.ofNat_toNat], o0, fun a h0 hs ho => ?_, fun a => (rd2 a).trans (rd1 a),
    fun a => (wr2 a).trans (wr1 a)⟩
  rw [fr2 a h0 ho, fr1 a h0 (by omega)]

/-- **The SDK's `get`, 47857 → 47957, for an empty value**: `Some(Vec { 0, 1, 0 })` at out, ω₀, ω₅, ω₆ restored and
    the frame popped, at the return's `jumpInd`; the context and the stream kept. -/
theorem get_empty {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : AccEnv)
    (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory) (sp out kO kZ : Nat) (key : List UInt8)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat out) (h8 : ω[8] = UInt64.ofNat kO)
    (h9 : ω[9] = UInt64.ofNat kZ) (hkZ : kZ < 2 ^ 32)
    (hsp : 65536 + 48 ≤ sp ∧ sp < 4294967296) (hout : sp ≤ out ∧ out + 24 < 4294967296)
    (hwf : ∀ a, sp - 48 ≤ a → a < sp → μ.writable a = true)
    (hwo : ∀ a, out ≤ a → a < out + 24 → μ.writable a = true)
    (hk : μ.rangeReadable kO kZ = true) (hkey : μ.readN kO kZ = key)
    (dk : kO + kZ ≤ sp - 48 ∨ sp ≤ kO) (hkr : kO + kZ ≤ 4294967296)
    (hv : c.1.self.storage.get? key = some []) :
    ∃ ω' μ', FreeStepsH p (KeepCtx (accContractS env)) 47857 ω μ (c, f) 47957 ω' μ' (c, f) 40 ∧
      ω'[0] = ω[0] ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      μ'.readN out 8 = Num.encodeLE 8 0 ∧ μ'.readN (out + 8) 8 = Num.encodeLE 8 1 ∧
      μ'.readN (out + 16) 8 = Num.encodeLE 8 0 ∧
      (∀ a, a < 4294967296 → (a < sp - 48 ∨ sp ≤ a) → (a < out ∨ out + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨ω1, μ1, run1, b1, b5, b7, b10, b11, b12, m40, m32, m24, m16, m8, fr1, rd1, wr1, bo⟩ :=
    gr_pre (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω μ sp h1 hsp hwf
  have hk1 : μ1.rangeReadable kO kZ = true := by
    rw [← hk]; unfold Memory.rangeReadable; simp only [rd1]
  have hkey1 : μ1.readN kO kZ = key := by
    rw [← hkey]; apply PVM.Memory.readN_congr; intro j hj
    exact fr1 _ (by omega) (by omega)
  have hst : KeepCtx (accContractS env) 4 ω1 μ1 (c, f) .cont (readRegs ω1 (some [])) (readMem μ1 0 0 (some [])) (c, f) := by
    have := read_stepS env ω1 μ1 (c, f) kO kZ 0 0 key (reg_of b7 (by decide))
      (reg_of ((bo 8 (by decide)).trans h8) (by omega)) (reg_of ((bo 9 (by decide)).trans h9) (by omega))
      (reg_of b10 (by decide)) (reg_of b11 (by decide)) (reg_of b12 (by decide)) hkZ (by decide) hk1 hkey1
      (by simp [Memory.rangeWritable])
    rw [hv] at this
    exact ⟨this, rfl⟩
  simp only [readMem, List.take_nil, PVM.Memory.writeN_nil] at hst
  have e7 : (readRegs ω1 (some []))[7] = UInt64.ofNat 0 := readRegs_7 ω1 (some [])
  have e1 : (readRegs ω1 (some []))[1] = UInt64.ofNat (sp - 48) := (readRegs_ne ω1 (some []) 1 (by decide) (by decide)).trans b1
  have hrf : ∀ a, sp - 48 ≤ a → a < sp - 48 + 48 → μ1.readable a = true := fun a h1 h2 => by
    rw [rd1]; exact Memory.readable_of_writable (hwf a h1 (by omega))
  have hwo1 : ∀ a, out ≤ a → a < out + 24 → μ1.writable a = true := fun a h1 h2 => by rw [wr1]; exact hwo a h1 h2
  obtain ⟨ω2, μ2, run2, g0, g1, g5, g6, o0, o8, o16, fr2, rd2, wr2⟩ :=
    gr_empty (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) (readRegs ω1 (some [])) μ1 (sp - 48) out
      ω[0].toNat ω[5].toNat ω[6].toNat e1 e7 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (readN_of_rdN (m16.trans (by rw [h7, UInt64.toNat_ofNat_of_lt' (show out < 2 ^ 64 by omega)]))) (readN_of_rdN m24) (readN_of_rdN m32) (readN_of_rdN m40) hrf hwo1 (by omega)
      (UInt64.toNat_lt _) (UInt64.toNat_lt _) (UInt64.toNat_lt _)
  refine ⟨ω2, μ2, ((run1.trans (FreeStepsH.host_decode (d_47886 (p := p) (P := P)) hst run2))).mono (by omega),
    by rw [g0, UInt64.ofNat_toNat], by rw [g1, show sp - 48 + 48 = sp by omega], by rw [g5, UInt64.ofNat_toNat],
    by rw [g6, UInt64.ofNat_toNat], o0, o8, o16, fun a h0 hs ho => ?_, fun a => (rd2 a).trans (rd1 a),
    fun a => (wr2 a).trans (wr1 a)⟩
  rw [fr2 a h0 ho, fr1 a h0 (by omega)]

end Services.Bootstrap.Acc
