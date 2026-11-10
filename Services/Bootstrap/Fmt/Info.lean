import Services.Bootstrap.Fmt.InfoSteps
import Services.Bootstrap.Memzero
import Services.Bootstrap.Fmt.Memcpy

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

theorem setR7_getElem (ω : Regs) (v k : Nat) (hk : k < 13) (h7 : k ≠ 7) : (setR7 ω v)[k] = ω[k] := by
  simp only [setR7, Vector.getElem_set]
  split <;> simp_all

theorem setR7_getElem7 (ω : Regs) (v : Nat) : (setR7 ω v)[7] = UInt64.ofNat v := by
  simp [setR7, Vector.getElem_set]

/-- **`info` of the accumulating service, frame-only** (49454, called at 6501 with the destination
    D in ω₇): under `accContractK cap env` (𝖬_I ≤ cap), when the service's own account a is in the
    context's accounts and its `info` record is shorter than 2⁶⁴ − 9 octets, the call returns to t
    (the address ω₀ resolves to) with ω₀, ω₁, ω₅, ω₆ as they were and the context unchanged. Memory
    changes only in S − 488 … S (its frames) and the 96 octets at D (the decoded record, not
    stated). -/
theorem info_self {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (cap : Nat)
    (hcap : 703 ≤ cap ∧ cap < 2 ^ 64) (env : AccEnv) (x : AccCtx) (a : ServiceAccount)
    (ha : x.1.state.accounts.get? x.1.id = some a) (hlen : (infoValue a).length < 18446744073709551607)
    (ω : Regs) (μ : Memory) (S D ret t : Nat)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat D)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hS : 65536 + 600 ≤ S ∧ S % 8 = 0) (hD : S + 8 ≤ D ∧ D + 96 + 16 < 4294967296)
    (hwS : ∀ a, S - 488 ≤ a → a < S → μ.writable a = true)
    (hwD : ∀ a, D ≤ a → a < D + 96 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (accContractK cap env) 49454 ω μ x t ω' μ' x 8000 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      (∀ b, b < 4294967296 → (b < S - 488 ∨ S ≤ b) → (b < D ∨ D + 96 ≤ b) → μ'.read b = μ.read b) ∧
      (∀ b, μ'.readable b = μ.readable b) ∧ (∀ b, μ'.writable b = μ.writable b) := by
  have hv5 := UInt64.toNat_lt ω[5]
  have hv6 := UInt64.toNat_lt ω[6]
  have hw : ∀ b, S - 488 ≤ b → b < S → μ.writable b = true := hwS
  -- the frames
  obtain ⟨ω1, μ1, run1, a0, a1, a6, a7, a8, a9, m112, m104, m256, m248, m240, m56, fr1, rd1, wr1⟩ :=
    io_entry (p := p) (P := P) (R := accContractK cap env) x ω μ S D ret ω[5].toNat ω[6].toNat ⟨by omega, by omega⟩ h0 h1
      UInt64.ofNat_toNat.symm UInt64.ofNat_toNat.symm h7 ⟨by omega, hv5, hv6, by omega⟩
      (fun b h1 h2 => hw b (by omega) h2)
  -- memset of the buffer
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, -, fr2, rd2, wr2⟩ := Memzero.memzero (p := p) (P := P) (R := accContractK cap env) x ω1 μ1
    (S - 384 + 64) 96 2158 48534 (by omega) ⟨by omega, by omega⟩ (by omega) a0 a7 a8 a9 (by decide) jte_1078
    bs_48534 (fun b h1 h2 => by rw [wr1]; exact hw b (by omega) (by omega))
  obtain ⟨ω3, run3, c1, c7, c8, c9, c10⟩ := io_a1 (p := p) (P := P) (R := accContractK cap env) x ω2 μ2 (S - 384) ⟨by omega, by omega⟩
    (b1.trans a1) (b6.trans a6)
  -- after the host call
  obtain ⟨L, hL⟩ : ∃ L, (infoValue a).length = L := ⟨_, rfl⟩
  rw [hL] at hlen
  obtain ⟨μ4, hμ4⟩ : ∃ m, m = μ2.writeN (S - 384 + 64) ((infoValue a).take (min 96 L)) := ⟨_, rfl⟩
  have fr4 : ∀ b, b < 4294967296 → (b < S - 384 + 64 ∨ S - 384 + 160 ≤ b) → μ4.read b = μ2.read b := fun b hb h => by
    rw [hμ4, Memory.read_writeN_disjoint _ _ _ _ (by simp only [List.length_take]; omega)
      (by simp only [List.length_take, two32]; omega) (by simp only [two32]; omega)]
  have wr4 : ∀ b, μ4.writable b = μ2.writable b := fun b => by rw [hμ4, Memory.writable_writeN]
  have rd4 : ∀ b, μ4.readable b = μ2.readable b := fun b => by rw [hμ4, Memory.readable_writeN]
  have k14 : ∀ b, b < 4294967296 → (b < S - 384 + 64 ∨ S - 384 + 160 ≤ b) → μ4.read b = μ1.read b := fun b hb h => by
    rw [fr4 b hb h, fr2 b hb h]
  have wr14 : ∀ b, μ4.writable b = μ1.writable b := fun b => by rw [wr4, wr2]
  have hw4 : ∀ b, S - 488 ≤ b → b < S → μ4.writable b = true := fun b h1 h2 => by
    rw [wr14, wr1]; exact hw b h1 h2
  obtain ⟨ω4, hω4⟩ : ∃ w, w = setR7 ω3 L := ⟨_, rfl⟩
  have d1 : ω4[1] = UInt64.ofNat (S - 384) := by rw [hω4, setR7_getElem _ _ _ (by decide) (by decide), c1]
  have d7 : ω4[7] = UInt64.ofNat L := by rw [hω4, setR7_getElem7]
  obtain ⟨ω5, μ5, run5, e0, e1, e7, e8, e9, rp5, rl5, fr5, rd5, wr5⟩ := io_a2 (p := p) (P := P) (R := accContractK cap env) x ω4 μ4
    (S - 384) L ⟨by omega, by omega⟩ hlen d1 d7 (fun b h1 h2 => hw4 b (by omega) (by omega))
  have k15 : ∀ b, b < 4294967296 → (b < S - 384 + 64 ∨ (S - 384 + 240 ≤ b)) → μ5.read b = μ1.read b :=
    fun b hb h => by rw [fr5 b hb (by omega), k14 b hb (by omega)]
  have st5 : ISt μ5 (S - 384) (S - 120) D ω[6].toNat 0 :=
    ⟨by rw [rdN_frame (fun j hj => k15 _ (by omega) (by omega))]; exact m56,
     by rw [rdN_frame (fun j hj => k15 _ (by omega) (by omega))]; exact m256,
     by rw [rdN_frame (fun j hj => k15 _ (by omega) (by omega))]; exact m248,
     by rw [rdN_frame (fun j hj => k15 _ (by omega) (by omega))]; exact m240,
     by rw [rp5], by rw [rl5]⟩
  have hw5 : ∀ b, S - 384 - 104 ≤ b → b < S - 384 + 264 → μ5.writable b = true := fun b h1 h2 => by
    rw [wr5]; exact hw4 b (by omega) (by omega)
  obtain ⟨ω6, μ6, run6, f1, f7, st6, fr6, rd6, wr6⟩ := info_reads (p := p) (P := P) (R := accContractK cap env) x ω5 μ5 (S - 384)
    (S - 120) D ω[6].toNat ⟨by omega, by omega, by omega⟩ st5 e0 e1 e7 e8 e9 hw5
  -- the record's write-back, the copy to D and the return
  have hw6 : ∀ b, S - 488 ≤ b → b < S → μ6.writable b = true := fun b h1 h2 => by
    rw [wr6, wr5]; exact hw4 b h1 h2
  obtain ⟨ω7, μ7, run7, g1, g5, g6, gt, fr7, rd7, wr7⟩ := io_l (p := p) (P := P) (R := accContractK cap env) x ω6 μ6 (S - 384) D
    ω[6].toNat ⟨by omega, by omega⟩ f1 f7 (by rw [st6.res]; omega) st6.s0 st6.s5 st6.s6
    (fun b h1 h2 => Memory.readable_of_writable (hw6 b (by omega) (by omega)))
    (fun b h1 h2 => hw6 b (by omega) (by omega))
  obtain ⟨ω8, run8, h80, h81, h85, h86, h87, h88, h89⟩ := io_b (p := p) (P := P) (R := accContractK cap env) x ω7 μ7 (S - 120) D
    ⟨by omega, by omega⟩ (by omega) (by rw [g1]; congr 1; omega) g5 (by rw [show S - 120 = S - 384 + 264 by omega]; exact gt)
    (fun b h1 h2 => by rw [rd7]; exact Memory.readable_of_writable (hw6 b (by omega) (by omega)))
  obtain ⟨ω9, μ9, run9, i0, i1, i5, i6, fr9, rd9, wr9⟩ := memcpy_frame (p := p) (P := P) (R := accContractK cap env) x ω8 μ7 2194 49529
    (S - 120) D (S - 120 + 8) 96 h80 h81 h87 h88 h89 (by decide) jte_1096 bs_49529 ⟨by omega, by omega, by omega⟩
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
    (fun b h1 h2 => by rw [rd7]; exact Memory.readable_of_writable (hw6 b (by omega) (by omega)))
    (fun b h1 h2 => by rw [wr7, wr6, wr5, wr14, wr1]; exact hwD b h1 h2)
    (fun b h1 h2 => by rw [wr7]; exact hw6 b (by omega) (by omega))
  -- the outer frame's words, kept since io_entry
  have kO : ∀ b, S - 120 + 104 ≤ b → b < S → μ9.read b = μ1.read b := fun b h1 h2 => by
    rw [fr9 b (by omega) (Or.inl (by omega)) (Or.inr (by omega)), fr7 b (by omega) (Or.inr (by omega)),
      fr6 b (by omega) (Or.inr (Or.inr (by omega))), k15 b (by omega) (Or.inr (by omega))]
  obtain ⟨ω10, run10, j0, j1, j5, j6⟩ := io_c (p := p) (P := P) (R := accContractK cap env) x ω9 μ9 (S - 120) ret t ω[5].toNat
    ⟨by omega, by omega⟩ (i1.trans h81)
    (by rw [rdN_frame (fun j hj => kO _ (by omega) (by omega))]; exact m112)
    (by rw [rdN_frame (fun j hj => kO _ (by omega) (by omega))]; exact m104) hret hjt hbt
    (fun b h1 h2 => by rw [rd9, rd7, rd6, rd5, rd4, rd2, rd1]; exact Memory.readable_of_writable (hw b (by omega) (by omega)))
  -- the run: the host step after io_a1
  have rest : FreeStepsH p (accContractK cap env) 48549 ω4 μ4 x t ω10 μ9 x
      (15 + 5000 + 40 + 6 + (7 * 96 + 320) + 5) :=
    (((((run5.trans run6).trans run7).trans run8).trans run9).trans run10)
  have run4 := FreeStepsH.infoSelf cap hcap env (P := P) (i := 48547) (n := 48549) d_48547 ha c7 c8 c9 c10
    (by omega) (fun b h1 h2 => by rw [wr2, wr1]; exact hw b (by omega) (by omega))
    (by rw [hL, ← hω4, ← hμ4]; exact rest)
  refine ⟨ω10, μ9, (((run1.trans run2).trans run3).trans run4).mono (by omega), j0.trans h0.symm,
    by rw [j1, h1, show S - 120 + 120 = S by omega], ?_, ?_, fun b hb h h' => ?_, fun b => ?_, fun b => ?_⟩
  · rw [j5, UInt64.ofNat_toNat]
  · rw [j6, i6, h86, g6, UInt64.ofNat_toNat]
  · rw [fr9 b hb h' (by omega), fr7 b hb (by omega), fr6 b hb (by omega), fr5 b hb (by omega), fr4 b hb (by omega),
      fr2 b hb (by omega), fr1 b hb (by omega)]
  · rw [rd9, rd7, rd6, rd5, rd4, rd2, rd1]
  · rw [wr9, wr7, wr6, wr5, wr4, wr2, wr1]

end Services.Bootstrap.Fmt
