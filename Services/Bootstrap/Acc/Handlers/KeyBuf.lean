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
    ∃ ω', FreeStepsH p R 51243 ω μ x tr ω' (μ.writeN buf [UInt8.ofNat t]) x 30 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat buf ∧ ω'[8] = UInt64.ofNat 1 := by
  rw [show ω = regsNF ω [] from rfl]
  rcases ht with rfl | rfl
  all_goals
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h0, h7, h8, hkp, hbuf, mt, hrk, hwb, hret, hjt, hbt, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h0, h8]

/-- **51243 … the return, t = 2**: the tag octet, the 32 octets at kp + 4 (four words) and the `i16`
    at kp + 2 at buf, length 35. -/
theorem kf_t2 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (kp buf ret tr w0 w1 w2 w3 v : Nat) (h0 : ω[0] = UInt64.ofNat ret) (h7 : ω[7] = UInt64.ofNat kp)
    (h8 : ω[8] = UInt64.ofNat buf) (hkp : kp + 36 < 4294967296) (hbuf : buf + 35 < 4294967296)
    (hd : buf + 35 ≤ kp ∨ kp + 36 ≤ buf) (mt : rdN μ kp 2 = 2) (m0 : rdN μ (kp + 4) 8 = w0)
    (m1 : rdN μ (kp + 12) 8 = w1) (m2 : rdN μ (kp + 20) 8 = w2) (m3 : rdN μ (kp + 28) 8 = w3)
    (mv : rdN μ (kp + 2) 2 = v) (hv : v < 65536) (hw0 : w0 < 18446744073709551616)
    (hw1 : w1 < 18446744073709551616) (hw2 : w2 < 18446744073709551616) (hw3 : w3 < 18446744073709551616)
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
    · congr 1
      all_goals (try congr 1)
      all_goals (try (split <;> omega))
      all_goals (try simp only [Nat.mod_eq_of_lt hw0, Nat.mod_eq_of_lt hw1, Nat.mod_eq_of_lt hw2, Nat.mod_eq_of_lt hw3])
    all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h0, h8]

/-- **51243 … the return, t = 1**: the tag octet and the `i32` at kp + 4 at buf, length 5. -/
theorem kf_t1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (kp buf ret tr v : Nat) (h0 : ω[0] = UInt64.ofNat ret) (h7 : ω[7] = UInt64.ofNat kp)
    (h8 : ω[8] = UInt64.ofNat buf) (hkp : kp + 36 < 4294967296) (hbuf : buf + 35 < 4294967296)
    (hd : buf + 35 ≤ kp ∨ kp + 36 ≤ buf) (mt : rdN μ kp 2 = 1) (mv : rdN μ (kp + 4) 4 = v)
    (hv : v < 4294967296)
    (hrk : ∀ a, kp ≤ a → a < kp + 36 → μ.readable a = true)
    (hwb : ∀ a, buf ≤ a → a < buf + 35 → μ.writable a = true)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = tr)
    (hbt : P.isBlockStart tr = true) :
    ∃ ω' μ', FreeStepsH p R 51243 ω μ x tr ω' μ' x 30 ∧
      μ' = (μ.writeN buf [UInt8.ofNat 1]).writeN (buf + 1) (Num.encodeLE 4 v) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat buf ∧ ω'[8] = UInt64.ofNat 5 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h7, h8, hkp, hbuf, hd, mt, mv, hrk, hwb, hret, hjt, hbt, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · congr 1
      all_goals (try congr 1)
      all_goals (try (split <;> omega))
    all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h0, h8]

/-- Reading back a write that ends a prefix: n octets at a, then l written at a + n. -/
theorem rd_snoc (μ : Memory) (a n : Nat) (l : List UInt8) (h : a + n + l.length ≤ 4294967296) :
    (μ.writeN (a + n) l).readN a (n + l.length) = μ.readN a n ++ l := by
  rw [Services.Bootstrap.Decode.VecU8.readN_split, rdN_wr _ _ _ _ _ l.length rfl (.inr (by omega)) (by omega) (by omega),
    Memory.readN_writeN_same _ _ _ _ rfl (by unfold two32; omega)]

theorem rd_snoc' (μ : Memory) (a n : Nat) (l : List UInt8) (m : Nat) (hm : m = n + l.length)
    (h : a + n + l.length ≤ 4294967296) : (μ.writeN (a + n) l).readN a m = μ.readN a n ++ l := by
  subst hm; exact rd_snoc μ a n l h

/-- **The encoder at 51243, one call**: with the key value at kp (tag t < 4, readable for 36 octets)
    and a writable 35-octet buffer at buf apart from it, the run returns to t's entry tr with
    `keyEnc μ kp t` at buf, ω₇ = buf and ω₈ its length, memory kept off the buffer, and ω₀, ω₁, ω₅, ω₆
    as at the call. -/
theorem kf_call {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (kp buf t ret tr : Nat) (h0 : ω[0] = UInt64.ofNat ret) (h7 : ω[7] = UInt64.ofNat kp)
    (h8 : ω[8] = UInt64.ofNat buf) (hkp : kp + 36 < 4294967296) (hbuf : buf + 35 < 4294967296)
    (hd : buf + 35 ≤ kp ∨ kp + 36 ≤ buf) (ht : t < 4) (mt : μ.readN kp 2 = Num.encodeLE 2 t)
    (hrk : ∀ a, kp ≤ a → a < kp + 36 → μ.readable a = true)
    (hwb : ∀ a, buf ≤ a → a < buf + 35 → μ.writable a = true)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = tr)
    (hbt : P.isBlockStart tr = true) :
    ∃ ω' μ', FreeStepsH p R 51243 ω μ x tr ω' μ' x 30 ∧
      μ'.readN buf (keyEnc μ kp t).length = keyEnc μ kp t ∧
      (∀ a, a < 4294967296 → (a < buf ∨ buf + 35 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat buf ∧ ω'[8] = UInt64.ofNat (keyEnc μ kp t).length := by
  have rt : rdN μ kp 2 = t := by
    show Num.decodeLE _ = _
    rw [mt, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (by omega)]
  have l8 : ∀ v, (Num.encodeLE 8 v).length = 8 := fun v => Num.length_encodeLE ..
  have e8 : ∀ b, Num.encodeLE 8 (rdN μ b 8) = μ.readN b 8 := fun b => (readN_enc μ b 8).symm
  have hw1 : ∀ a, a < 4294967296 → (a < buf ∨ buf + 35 ≤ a) → ∀ (m : Memory) (b : Nat) (l : List UInt8),
      buf ≤ b → b + l.length ≤ buf + 35 → (m.writeN b l).read a = m.read a := fun a h1 h2 m b l hb hl =>
    rd_wr _ _ _ _ l.length rfl (by omega) (by omega) h1
  have hb8 : ∀ b, rdN μ b 8 < 18446744073709551616 := fun b => by
    have := decodeLE_readN_lt μ b 8; simp only [Nat.reducePow] at this; exact this
  by_cases t1 : t = 1
  · subst t1
    rw [show (keyEnc μ kp 1).length = 5 by simp [keyEnc]]
    have hv := decodeLE_readN_lt μ (kp + 4) 4
    simp only [Nat.reducePow] at hv
    obtain ⟨ω', μ', run, eμ, r0, r1, r5, r6, r7, r8⟩ := kf_t1 (R := R) (P := P) x ω μ kp buf ret tr _ h0 h7 h8 hkp
      hbuf hd rt rfl hv hrk hwb hret hjt hbt
    subst eμ
    refine ⟨ω', _, run, ?_, fun a h1 h2 => ?_, fun a => by simp, fun a => by simp, r0, r1, r5, r6, r7, r8⟩
    · rw [show (5 : Nat) = 1 + (Num.encodeLE 4 (rdN μ (kp + 4) 4)).length by simp [Num.length_encodeLE],
        rd_snoc _ _ _ _ (by simp only [Num.length_encodeLE]; omega),
        Memory.readN_writeN_same _ _ 1 _ rfl (by unfold two32; omega),
        show Num.encodeLE 4 (rdN μ (kp + 4) 4) = μ.readN (kp + 4) 4 from (readN_enc μ _ 4).symm]
      simp [keyEnc]
    · rw [hw1 a h1 h2 _ _ _ (by omega) (by simp only [Num.length_encodeLE]; omega),
        hw1 a h1 h2 _ _ _ (Nat.le_refl _) (by simp only [List.length_cons, List.length_nil]; omega)]
  by_cases t2 : t = 2
  · subst t2
    rw [show (keyEnc μ kp 2).length = 35 by simp [keyEnc]]
    have hv := decodeLE_readN_lt μ (kp + 2) 2
    simp only [Nat.reducePow] at hv
    obtain ⟨ω', μ', run, eμ, r0, r1, r5, r6, r7, r8⟩ := kf_t2 (R := R) (P := P) x ω μ kp buf ret tr _ _ _ _ _ h0 h7 h8
      hkp hbuf hd rt rfl rfl rfl rfl rfl hv (hb8 _) (hb8 _) (hb8 _)
      (hb8 _) hrk hwb hret hjt hbt
    subst eμ
    refine ⟨ω', _, run, ?_, fun a h1 h2 => ?_, fun a => by simp, fun a => by simp, r0, r1, r5, r6, r7, r8⟩
    · have s32 : μ.readN (kp + 4) 32 =
          μ.readN (kp + 4) 8 ++ (μ.readN (kp + 12) 8 ++ (μ.readN (kp + 20) 8 ++ μ.readN (kp + 28) 8)) := by
        rw [show (32 : Nat) = 8 + 24 from rfl, Services.Bootstrap.Decode.VecU8.readN_split,
          show kp + 4 + 8 = kp + 12 by omega, show (24 : Nat) = 8 + 16 from rfl,
          Services.Bootstrap.Decode.VecU8.readN_split, show kp + 12 + 8 = kp + 20 by omega,
          show (16 : Nat) = 8 + 8 from rfl, Services.Bootstrap.Decode.VecU8.readN_split,
          show kp + 20 + 8 = kp + 28 by omega]
      rw [rd_snoc' _ buf 33 _ 35 (by simp only [Num.length_encodeLE]) (by simp only [Num.length_encodeLE]; omega),
        rd_snoc' _ buf 25 _ 33 (by simp only [Num.length_encodeLE]) (by simp only [Num.length_encodeLE]; omega),
        rd_snoc' _ buf 17 _ 25 (by simp only [Num.length_encodeLE]) (by simp only [Num.length_encodeLE]; omega),
        rd_snoc' _ buf 9 _ 17 (by simp only [Num.length_encodeLE]) (by simp only [Num.length_encodeLE]; omega),
        rd_snoc' _ buf 1 _ 9 (by simp only [Num.length_encodeLE]) (by simp only [Num.length_encodeLE]; omega),
        Memory.readN_writeN_same _ _ 1 _ rfl (by unfold two32; omega), e8, e8, e8, e8,
        show Num.encodeLE 2 (rdN μ (kp + 2) 2) = μ.readN (kp + 2) 2 from (readN_enc μ _ 2).symm]
      simp [keyEnc, s32]
    · repeat rw [hw1 a h1 h2 _ _ _ (by omega) (by simp only [Num.length_encodeLE, List.length_cons, List.length_nil]; omega)]
  have h03 : t = 0 ∨ t = 3 := by omega
  rw [show (keyEnc μ kp t).length = 1 by simp [keyEnc, t1, t2]]
  obtain ⟨ω', run, r0, r1, r5, r6, r7, r8⟩ := kf_t03 (R := R) (P := P) x ω μ kp buf t ret tr h03 h0 h7 h8 hkp hbuf
    rt (fun a h1 h2 => hrk a h1 (by omega)) (fun a h1 h2 => hwb a h1 (by omega)) hret hjt hbt
  refine ⟨ω', _, run, ?_, fun a h1 h2 => ?_, fun a => by simp, fun a => by simp, r0, r1, r5, r6, r7, r8⟩
  · rw [Memory.readN_writeN_same _ _ 1 _ rfl (by unfold two32; omega)]
    simp [keyEnc, t1, t2]
  · exact hw1 a h1 h2 _ _ _ (Nat.le_refl _) (by simp only [List.length_cons, List.length_nil]; omega)

end Services.Bootstrap.Acc.Handlers.KeyBuf
