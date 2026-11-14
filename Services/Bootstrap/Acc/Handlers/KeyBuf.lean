import Services.Bootstrap.Acc.Handlers.KeyEnc

/-!
# The fixed-buffer storage-key encoder (51243)

`add_recent_work_item` (8158) encodes a storage key into a 35-octet buffer at ω₈ with the function
at 51243, from the same key value as the encoder at 33843 (a `u16` tag at kp = ω₇, an `i16` at
kp + 2, a payload from kp + 4): the tag octet, then for tag 1 the four octets at kp + 4, for tag 2
the 32 octets at kp + 4 and the two at kp + 2. It returns the buffer in ω₇ and the length in ω₈.
The octets are `KeyEnc.keyEnc μ kp t`, as the encoder at 33843 writes.
-/

namespace Services.Bootstrap.Acc.Handlers.KeyBuf

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.Acc.Handlers.KeyEnc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **51243 … the return, t ∈ {0, 3}**: the tag octet at buf, length 1. -/
theorem kf_t03 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (kp buf t ret tr : Nat) (ht : t = 0 ∨ t = 3) (h0 : ω[0] = UInt64.ofNat ret) (h7 : ω[7] = UInt64.ofNat kp)
    (h8 : ω[8] = UInt64.ofNat buf) (hkp : kp + 36 < 4294967296) (hbuf : buf + 35 < 4294967296)
    (mt : rdN μ kp 2 = t) (hrk : ∀ a, kp ≤ a → a < kp + 2 → μ.readable a = true)
    (hwb : ∀ a, buf ≤ a → a < buf + 1 → μ.writable a = true)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = tr)
    (hbt : P.isBlockStart tr = true) :
    ∃ ω', FreeStepsH p R 51243 ω μ x tr ω' (μ.writeN buf [UInt8.ofNat t]) x 20 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat buf ∧ ω'[8] = UInt64.ofNat 1 := by
  rw [show ω = regsNF ω [] from rfl]
  rcases ht with rfl | rfl
  all_goals
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h0, h7, h8, hkp, hbuf, mt, hrk, hwb, hret, hjt, hbt]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h0, h8]

/-- **51243 … the return, t = 2**: the tag octet, the 32 octets at kp + 4 (four words) and the `i16`
    at kp + 2 at buf, length 35. -/
theorem kf_t2 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (kp buf ret tr w0 w1 w2 w3 v : Nat) (h0 : ω[0] = UInt64.ofNat ret) (h7 : ω[7] = UInt64.ofNat kp)
    (h8 : ω[8] = UInt64.ofNat buf) (hkp : kp + 36 < 4294967296) (hbuf : buf + 35 < 4294967296)
    (hd : buf + 35 ≤ kp ∨ kp + 36 ≤ buf) (mt : rdN μ kp 2 = 2) (m0 : rdN μ (kp + 4) 8 = w0)
    (m1 : rdN μ (kp + 12) 8 = w1) (m2 : rdN μ (kp + 20) 8 = w2) (m3 : rdN μ (kp + 28) 8 = w3)
    (mv : rdN μ (kp + 2) 2 = v) (hv : v < 65536)
    (hrk : ∀ a, kp ≤ a → a < kp + 36 → μ.readable a = true)
    (hwb : ∀ a, buf ≤ a → a < buf + 35 → μ.writable a = true)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = tr)
    (hbt : P.isBlockStart tr = true) :
    ∃ ω' μ', FreeStepsH p R 51243 ω μ x tr ω' μ' x 30 ∧
      μ' = (((((μ.writeN buf [UInt8.ofNat 2]).writeN (buf + 1) (Num.encodeLE 8 w0)).writeN (buf + 9)
        (Num.encodeLE 8 w1)).writeN (buf + 17) (Num.encodeLE 8 w2)).writeN (buf + 25) (Num.encodeLE 8 w3)).writeN
        (buf + 33) (Num.encodeLE 2 v) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat buf ∧ ω'[8] = UInt64.ofNat 35 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h7, h8, hkp, hbuf, hd, mt, m0, m1, m2, m3, mv, hrk, hwb, hret, hjt, hbt,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · congr 2 <;> sorry
    all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h0, h8]

end Services.Bootstrap.Acc.Handlers.KeyBuf
