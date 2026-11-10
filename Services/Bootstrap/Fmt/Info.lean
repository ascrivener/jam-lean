import Services.Bootstrap.Fmt.InfoSteps
import Services.Bootstrap.Memzero

/-!
# `info` of the accumulating service (49454), frame-only

`info_self`: the call at 6501 (→ 49454, `info` (6) on the service itself, then the decode of its
96-octet record into the destination D) returns to its caller with only its stack frames and the
96 octets at D changed, and the context unchanged. The record's contents are not stated.

It holds under `accContractK cap env` (cap ≥ 𝖬_I), proved from the model's `info` (Ω_I), given two
facts of the accumulate context x: the service's own account a is among its accounts, and its
`info` record is shorter than 2⁶⁴ − 9 octets (it is 96 octets when the code hash has 32).
-/

namespace Services.Bootstrap.Fmt

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Acc
  Services.Bootstrap.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- The inner function's state while it reads the record: the result's address O at T + 56, the
    saved 2192, D, ω₆ at T + 256, T + 248, T + 240, and the reader at T + 160 having consumed c of
    the 96 octets at T + 64. -/
structure ISt (μ : Memory) (T O D v6 c : Nat) : Prop where
  res : rdN μ (T + 56) 8 = O
  s0 : rdN μ (T + 256) 8 = 2192
  s5 : rdN μ (T + 248) 8 = D
  s6 : rdN μ (T + 240) 8 = v6
  rp : rdN μ (T + 160) 8 = T + 64 + c
  rl : rdN μ (T + 160 + 8) 8 = 96 - c

/-- The read state is kept by a change that keeps T + 56 … T + 64 and T + 240 … T + 264, given the
    reader's new words. -/
theorem ISt.congr {μ μ' : Memory} {T O D v6 c c' : Nat} (h : ISt μ T O D v6 c)
    (k : ∀ a, (T + 56 ≤ a ∧ a < T + 64) ∨ (T + 240 ≤ a ∧ a < T + 264) → μ'.read a = μ.read a)
    (hp : rdN μ' (T + 160) 8 = T + 64 + c') (hl : rdN μ' (T + 160 + 8) 8 = 96 - c') : ISt μ' T O D v6 c' :=
  ⟨by rw [rdN_frame (fun j hj => k _ (by omega))]; exact h.res,
   by rw [rdN_frame (fun j hj => k _ (by omega))]; exact h.s0,
   by rw [rdN_frame (fun j hj => k _ (by omega))]; exact h.s5,
   by rw [rdN_frame (fun j hj => k _ (by omega))]; exact h.s6, hp, hl⟩

/-- **One read of the record by `read_exact`**: a segment from i to the call (`ib` … `ie`, `io_a2`'s
    shape: ω₇ = T + 160, ω₈ = T + 208, ω₉ = k, return address ret), then `read_exact`, back at j with
    `Ok`, the reader k octets further on. Memory changes only in T − 104 … T + 56 and
    T + 160 … T + 240. -/
theorem rd_step_re {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (T O D v6 c i j ret k s : Nat) (hT : 65536 + 104 ≤ T ∧ T + 264 < 4294967296 ∧ T % 8 = 0)
    (hc : c + k ≤ 96) (hk : k ≤ 32) (hst : ISt μ T O D v6 c)
    (hseg : ∃ ω1 μ1, FreeStepsH p R i ω μ x 58434 ω1 μ1 x s ∧ ω1[0] = UInt64.ofNat ret ∧
      ω1[1] = UInt64.ofNat T ∧ ω1[7] = UInt64.ofNat (T + 160) ∧ ω1[8] = UInt64.ofNat (T + 208) ∧
      ω1[9] = UInt64.ofNat k ∧
      (∀ a, a < 4294967296 → (a < T ∨ (T + 56 ≤ a ∧ a < T + 176) ∨ T + 240 ≤ a) → μ1.read a = μ.read a) ∧
      (∀ a, μ1.readable a = μ.readable a) ∧ (∀ a, μ1.writable a = μ.writable a))
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = j)
    (hbt : P.isBlockStart j = true)
    (hw : ∀ a, T - 104 ≤ a → a < T + 264 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R i ω μ x j ω' μ' x (s + 7 * k + 350) ∧ ω'[1] = UInt64.ofNat T ∧
      ω'[7] = UInt64.ofNat 0 ∧ ISt μ' T O D v6 (c + k) ∧
      (∀ a, a < 4294967296 → (a < T - 104 ∨ (T + 56 ≤ a ∧ a < T + 160) ∨ T + 240 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨ω1, μ1, run1, a0, a1, a7, a8, a9, fr1, rd1, wr1⟩ := hseg
  have k1 : ∀ a, T + 56 ≤ a → a < T + 176 → μ1.read a = μ.read a := fun a h1 h2 => fr1 a (by omega) (by omega)
  have k1' : ∀ a, T + 240 ≤ a → a < T + 264 → μ1.read a = μ.read a := fun a h1 h2 => fr1 a (by omega) (by omega)
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, bp, bl, fr2, rd2, wr2⟩ := read_exact (p := p) (P := P) (R := R) x ω1 μ1
    T (T + 160) (T + 208) k (T + 64 + c) (96 - c) ret j ⟨by omega, by omega, hT.2.2⟩ a0 a1 a7 a8 a9 hret hjt hbt
    (by rw [rdN_frame (fun j hj => k1 _ (by omega) (by omega))]; exact hst.rp)
    (by rw [rdN_frame (fun j hj => k1 _ (by omega) (by omega))]; exact hst.rl) (by omega) (Or.inr (by omega))
    (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
    (Or.inl (by omega))
    (fun a h1 h2 => by rw [rd1]; exact Memory.readable_of_writable (hw a (by omega) (by omega)))
    (fun a h1 h2 => by rw [wr1]; exact hw a (by omega) (by omega))
    (fun a h1 h2 => by rw [wr1]; exact hw a (by omega) (by omega))
    (fun a h1 h2 => by rw [wr1]; exact hw a (by omega) (by omega))
  refine ⟨ω2, μ2, (run1.trans run2).mono (by omega), b1.trans a1, b7, ?_, fun a ha h => ?_,
    fun a => by rw [rd2, rd1], fun a => by rw [wr2, wr1]⟩
  · refine hst.congr (fun a ha => ?_) (bp.trans (by omega)) (bl.trans (by omega))
    rw [fr2 a (by omega) (by omega) (by omega) (by omega)]
    rcases ha with ha | ha
    · exact k1 a ha.1 (by omega)
    · exact k1' a ha.1 ha.2
  · rw [fr2 a ha (by omega) (by omega) (by omega), fr1 a ha (by omega)]

/-- **One read of the record by `rd_u64` or `rd_u32`**: a segment from i to the call at e (`if_` …
    `ik`'s shape: ω₇ = T + 160, return address ret), then the read of k = 8 or 4 octets, back at j
    with `Ok`. Memory changes only in T − 104 … T + 56 and T + 160 … T + 240. -/
theorem rd_step_uN {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (T O D v6 c i j ret e k s : Nat) (he : (e = 46040 ∧ k = 8) ∨ (e = 46008 ∧ k = 4))
    (hT : 65536 + 104 ≤ T ∧ T + 264 < 4294967296 ∧ T % 8 = 0)
    (hc : c + k ≤ 96) (hst : ISt μ T O D v6 c)
    (hseg : ∃ ω1 μ1, FreeStepsH p R i ω μ x e ω1 μ1 x s ∧ ω1[0] = UInt64.ofNat ret ∧
      ω1[1] = UInt64.ofNat T ∧ ω1[7] = UInt64.ofNat (T + 160) ∧
      (∀ a, a < 4294967296 → (a < T ∨ (T + 56 ≤ a ∧ a < T + 176) ∨ T + 240 ≤ a) → μ1.read a = μ.read a) ∧
      (∀ a, μ1.readable a = μ.readable a) ∧ (∀ a, μ1.writable a = μ.writable a))
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = j)
    (hbt : P.isBlockStart j = true)
    (hw : ∀ a, T - 104 ≤ a → a < T + 264 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R i ω μ x j ω' μ' x (s + 420) ∧ ω'[1] = UInt64.ofNat T ∧
      ω'[7] = UInt64.ofNat 0 ∧ ISt μ' T O D v6 (c + k) ∧
      (∀ a, a < 4294967296 → (a < T - 104 ∨ (T + 56 ≤ a ∧ a < T + 160) ∨ T + 240 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨ω1, μ1, run1, a0, a1, a7, fr1, rd1, wr1⟩ := hseg
  have k1 : ∀ a, T + 56 ≤ a → a < T + 176 → μ1.read a = μ.read a := fun a h1 h2 => fr1 a (by omega) (by omega)
  have k1' : ∀ a, T + 240 ≤ a → a < T + 264 → μ1.read a = μ.read a := fun a h1 h2 => fr1 a (by omega) (by omega)
  have hk : k ≤ 8 := by omega
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, bp, bl, fr2, rd2, wr2⟩ := rd_uN (p := p) (P := P) (R := R) x ω1 μ1
    e k T (T + 160) (T + 64 + c) (96 - c) ret j he ⟨by omega, by omega, hT.2.2⟩ a0 a1 a7 hret hjt hbt
    (by rw [rdN_frame (fun j hj => k1 _ (by omega) (by omega))]; exact hst.rp)
    (by rw [rdN_frame (fun j hj => k1 _ (by omega) (by omega))]; exact hst.rl) (by omega) (by omega) (by omega)
    ⟨by omega, by omega⟩ (Or.inr (by omega))
    (fun a h1 h2 => by rw [rd1]; exact Memory.readable_of_writable (hw a (by omega) (by omega)))
    (fun a h1 h2 => by rw [wr1]; exact hw a (by omega) (by omega))
    (fun a h1 h2 => by rw [wr1]; exact hw a (by omega) (by omega))
  refine ⟨ω2, μ2, (run1.trans run2).mono (by omega), b1.trans a1, b7, ?_, fun a ha h => ?_,
    fun a => by rw [rd2, rd1], fun a => by rw [wr2, wr1]⟩
  · refine hst.congr (fun a ha => ?_) (bp.trans (by omega)) (bl.trans (by omega))
    rw [fr2 a (by omega) (by omega) (by omega)]
    rcases ha with ha | ha
    · exact k1 a ha.1 (by omega)
    · exact k1' a ha.1 ha.2
  · rw [fr2 a ha (by omega) (by omega), fr1 a ha (by omega)]

/-- **The record's eleven reads** (58434, the code hash's `read_exact`, … 48871): from the reader
    over the 96 octets at T + 64 (`ISt` at 0), every read succeeds and the run reaches 48871 with
    `Ok`, the reader at the end (`ISt` at 96). Memory changes only in T − 104 … T + 56 and
    T + 160 … T + 240. -/
theorem info_reads {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (T O D v6 : Nat) (hT : 65536 + 104 ≤ T ∧ T + 264 < 4294967296 ∧ T % 8 = 0) (hst : ISt μ T O D v6 0)
    (h0 : ω[0] = UInt64.ofNat 2160) (h1 : ω[1] = UInt64.ofNat T) (h7 : ω[7] = UInt64.ofNat (T + 160))
    (h8 : ω[8] = UInt64.ofNat (T + 208)) (h9 : ω[9] = UInt64.ofNat 32)
    (hw : ∀ a, T - 104 ≤ a → a < T + 264 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 58434 ω μ x 48871 ω' μ' x 5000 ∧ ω'[1] = UInt64.ofNat T ∧
      ω'[7] = UInt64.ofNat 0 ∧ ISt μ' T O D v6 96 ∧
      (∀ a, a < 4294967296 → (a < T - 104 ∨ (T + 56 ≤ a ∧ a < T + 160) ∨ T + 240 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr0 : ∀ a, T ≤ a → a < T + 264 → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (hw a (by omega) h2)
  obtain ⟨ω0, μ0, run0, c1_0, c7_0, st0, fr0, rd0, wr0⟩ := rd_step_re (p := p) (P := P) (R := R) x ω μ T O D v6
    0 58434 48601 2160 32 0 hT (by omega) (by omega) hst
    ⟨ω, μ, FreeStepsH.refl, h0, h1, h7, h8, h9, fun _ _ _ => rfl, fun _ => rfl, fun _ => rfl⟩ (by decide)
    jte_1079 bs_48601 hw
  have hw0' : ∀ a, T - 104 ≤ a → a < T + 264 → μ0.writable a = true := fun a h1 h2 => by
    rw [wr0]; exact hw a h1 h2
  obtain ⟨ω1, μ1, run1, c1_1, c7_1, st1, fr1, rd1, wr1⟩ := rd_step_re (p := p) (P := P) (R := R) x ω0 μ0
    T O D v6 32 48601 48659 2162 8 16 hT (by omega) (by omega) st0
    (ib (p := p) (P := P) (R := R) x ω0 μ0 T ⟨by omega, by omega⟩ c1_0 c7_0 (fun a h1 h2 => Memory.readable_of_writable (hw0' a (by omega) h2)) (fun a h1 h2 => hw0' a (by omega) h2))
    (by decide) jte_1080 bs_48659 hw0'
  have hw1' : ∀ a, T - 104 ≤ a → a < T + 264 → μ1.writable a = true := fun a h1 h2 => by
    rw [wr1]; exact hw0' a h1 h2
  obtain ⟨ω2, μ2, run2, c1_2, c7_2, st2, fr2, rd2, wr2⟩ := rd_step_re (p := p) (P := P) (R := R) x ω1 μ1
    T O D v6 40 48659 48688 2164 8 8 hT (by omega) (by omega) st1
    (ic (p := p) (P := P) (R := R) x ω1 μ1 T ⟨by omega, by omega⟩ c1_1 c7_1 (fun a h1 h2 => Memory.readable_of_writable (hw1' a (by omega) h2)) (fun a h1 h2 => hw1' a (by omega) h2))
    (by decide) jte_1081 bs_48688 hw1'
  have hw2' : ∀ a, T - 104 ≤ a → a < T + 264 → μ2.writable a = true := fun a h1 h2 => by
    rw [wr2]; exact hw1' a h1 h2
  obtain ⟨ω3, μ3, run3, c1_3, c7_3, st3, fr3, rd3, wr3⟩ := rd_step_re (p := p) (P := P) (R := R) x ω2 μ2
    T O D v6 48 48688 48717 2166 8 8 hT (by omega) (by omega) st2
    (id (p := p) (P := P) (R := R) x ω2 μ2 T ⟨by omega, by omega⟩ c1_2 c7_2 (fun a h1 h2 => Memory.readable_of_writable (hw2' a (by omega) h2)) (fun a h1 h2 => hw2' a (by omega) h2))
    (by decide) jte_1082 bs_48717 hw2'
  have hw3' : ∀ a, T - 104 ≤ a → a < T + 264 → μ3.writable a = true := fun a h1 h2 => by
    rw [wr3]; exact hw2' a h1 h2
  obtain ⟨ω4, μ4, run4, c1_4, c7_4, st4, fr4, rd4, wr4⟩ := rd_step_re (p := p) (P := P) (R := R) x ω3 μ3
    T O D v6 56 48717 48750 2168 8 10 hT (by omega) (by omega) st3
    (ie (p := p) (P := P) (R := R) x ω3 μ3 T ⟨by omega, by omega⟩ c1_3 c7_3 (fun a h1 h2 => Memory.readable_of_writable (hw3' a (by omega) h2)) (fun a h1 h2 => hw3' a (by omega) h2))
    (by decide) jte_1083 bs_48750 hw3'
  have hw4' : ∀ a, T - 104 ≤ a → a < T + 264 → μ4.writable a = true := fun a h1 h2 => by
    rw [wr4]; exact hw3' a h1 h2
  obtain ⟨ω5, μ5, run5, c1_5, c7_5, st5, fr5, rd5, wr5⟩ := rd_step_uN (p := p) (P := P) (R := R) x ω4 μ4
    T O D v6 64 48750 48772 2170 46040 8 7 (by decide) hT (by omega) st4
    (if_ (p := p) (P := P) (R := R) x ω4 μ4 T ⟨by omega, by omega⟩ c1_4 c7_4 (fun a h1 h2 => Memory.readable_of_writable (hw4' a (by omega) h2)) (fun a h1 h2 => hw4' a (by omega) h2))
    (by decide) jte_1084 bs_48772 hw4'
  have hw5' : ∀ a, T - 104 ≤ a → a < T + 264 → μ5.writable a = true := fun a h1 h2 => by
    rw [wr5]; exact hw4' a h1 h2
  obtain ⟨ω6, μ6, run6, c1_6, c7_6, st6, fr6, rd6, wr6⟩ := rd_step_uN (p := p) (P := P) (R := R) x ω5 μ5
    T O D v6 72 48772 48792 2172 46008 4 6 (by decide) hT (by omega) st5
    (ig (p := p) (P := P) (R := R) x ω5 μ5 T ⟨by omega, by omega⟩ c1_5 c7_5 (fun a h1 h2 => Memory.readable_of_writable (hw5' a (by omega) h2)) (fun a h1 h2 => hw5' a (by omega) h2))
    (by decide) jte_1085 bs_48792 hw5'
  have hw6' : ∀ a, T - 104 ≤ a → a < T + 264 → μ6.writable a = true := fun a h1 h2 => by
    rw [wr6]; exact hw5' a h1 h2
  obtain ⟨ω7, μ7, run7, c1_7, c7_7, st7, fr7, rd7, wr7⟩ := rd_step_uN (p := p) (P := P) (R := R) x ω6 μ6
    T O D v6 76 48792 48812 2174 46040 8 6 (by decide) hT (by omega) st6
    (ih (p := p) (P := P) (R := R) x ω6 μ6 T ⟨by omega, by omega⟩ c1_6 c7_6 (fun a h1 h2 => Memory.readable_of_writable (hw6' a (by omega) h2)) (fun a h1 h2 => hw6' a (by omega) h2))
    (by decide) jte_1086 bs_48812 hw6'
  have hw7' : ∀ a, T - 104 ≤ a → a < T + 264 → μ7.writable a = true := fun a h1 h2 => by
    rw [wr7]; exact hw6' a h1 h2
  obtain ⟨ω8, μ8, run8, c1_8, c7_8, st8, fr8, rd8, wr8⟩ := rd_step_uN (p := p) (P := P) (R := R) x ω7 μ7
    T O D v6 84 48812 48832 2176 46008 4 6 (by decide) hT (by omega) st7
    (ii (p := p) (P := P) (R := R) x ω7 μ7 T ⟨by omega, by omega⟩ c1_7 c7_7 (fun a h1 h2 => Memory.readable_of_writable (hw7' a (by omega) h2)) (fun a h1 h2 => hw7' a (by omega) h2))
    (by decide) jte_1087 bs_48832 hw7'
  have hw8' : ∀ a, T - 104 ≤ a → a < T + 264 → μ8.writable a = true := fun a h1 h2 => by
    rw [wr8]; exact hw7' a h1 h2
  obtain ⟨ω9, μ9, run9, c1_9, c7_9, st9, fr9, rd9, wr9⟩ := rd_step_uN (p := p) (P := P) (R := R) x ω8 μ8
    T O D v6 88 48832 48852 2178 46008 4 6 (by decide) hT (by omega) st8
    (ij (p := p) (P := P) (R := R) x ω8 μ8 T ⟨by omega, by omega⟩ c1_8 c7_8 (fun a h1 h2 => Memory.readable_of_writable (hw8' a (by omega) h2)) (fun a h1 h2 => hw8' a (by omega) h2))
    (by decide) jte_1088 bs_48852 hw8'
  have hw9' : ∀ a, T - 104 ≤ a → a < T + 264 → μ9.writable a = true := fun a h1 h2 => by
    rw [wr9]; exact hw8' a h1 h2
  obtain ⟨ω10, μ10, run10, c1_10, c7_10, st10, fr10, rd10, wr10⟩ := rd_step_uN (p := p) (P := P) (R := R) x ω9 μ9
    T O D v6 92 48852 48871 2180 46008 4 6 (by decide) hT (by omega) st9
    (ik (p := p) (P := P) (R := R) x ω9 μ9 T ⟨by omega, by omega⟩ c1_9 c7_9 (fun a h1 h2 => Memory.readable_of_writable (hw9' a (by omega) h2)) (fun a h1 h2 => hw9' a (by omega) h2))
    (by decide) jte_1089 bs_48871 hw9'
  refine ⟨ω10, μ10, ((((((((((run0.trans run1).trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8).trans run9).trans run10).mono (by omega), c1_10, c7_10, st10, fun a ha h => ?_,
    fun a => by simp only [rd10, rd9, rd8, rd7, rd6, rd5, rd4, rd3, rd2, rd1, rd0],
    fun a => by simp only [wr10, wr9, wr8, wr7, wr6, wr5, wr4, wr3, wr2, wr1, wr0]⟩
  rw [fr10 a ha h, fr9 a ha h, fr8 a ha h, fr7 a ha h, fr6 a ha h, fr5 a ha h, fr4 a ha h, fr3 a ha h, fr2 a ha h,
    fr1 a ha h, fr0 a ha h]

end Services.Bootstrap.Fmt
