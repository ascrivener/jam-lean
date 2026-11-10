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

end Services.Bootstrap.Fmt
