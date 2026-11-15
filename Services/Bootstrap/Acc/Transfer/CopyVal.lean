import Services.Bootstrap.Fmt.ReadExact
import Services.Bootstrap.MemcpyBig

/-!
# `memcpy` and `read_exact` with the copied octets stated

`Fmt.memcpy_frame` and `Fmt.read_exact` are frame-only. `on_transfer` needs the octets they copy: the
memo's copy to sp + 1144 (7159 → 68729, 128 octets) and the counter's 4 octets read by `read_exact`
(7237 → 58434). `memcpy_val` and `read_exact_val` are the same runs with `μ'.readN dst n = μ.readN src n`
added: `memcpy_small` and `memcpy_big` state it.
-/

namespace Services.Bootstrap.Acc
open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc Services.Bootstrap.Fmt

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **`memcpy`, any length, with the copy stated**: `Fmt.memcpy_frame` and the n octets at dst
    equal to the n octets at src before the call. -/
theorem memcpy_val {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (ret t sp dst src n : Nat) (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp)
    (h7 : ω[7] = UInt64.ofNat dst) (h8 : ω[8] = UInt64.ofNat src) (h9 : ω[9] = UInt64.ofNat n)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) (hsp : 65536 + 48 ≤ sp ∧ sp < 4294967296 ∧ sp % 8 = 0)
    (hs : 65536 ≤ src ∧ src + n + 16 < 4294967296) (hd : 65536 ≤ dst ∧ dst + n + 16 < 4294967296)
    (hdj : dst + n + 24 ≤ src ∨ src + n + 24 ≤ dst) (hfd : sp ≤ dst ∨ dst + n ≤ sp - 48)
    (hfs : sp + 8 ≤ src ∨ src + n + 16 ≤ sp - 48)
    (hr : ∀ a, src ≤ a → a < src + n → μ.readable a = true)
    (hw : ∀ a, dst ≤ a → a < dst + n → μ.writable a = true)
    (hwf : ∀ a, sp - 48 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 68729 ω μ x t ω' μ' x (7 * n + 320) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      μ'.readN dst n = μ.readN src n ∧
      (∀ a, a < 4294967296 → (a < dst ∨ dst + n ≤ a) → (a < sp - 48 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have mF : ∀ a, a < 4294967296 → (a < sp - 48 ∨ sp ≤ a) → (memcpyFrame μ ω sp).read a = μ.read a := by
    intro a ha0 ha1
    unfold memcpyFrame
    rw [Memory.read_writeN_disjoint _ _ _ _ (by simp only [Num.length_encodeLE]; omega)
        (by simp only [Num.length_encodeLE, two32]; omega) (by simp only [two32]; omega),
      Memory.read_writeN_disjoint _ _ _ _ (by simp only [Num.length_encodeLE]; omega)
        (by simp only [Num.length_encodeLE, two32]; omega) (by simp only [two32]; omega),
      Memory.read_writeN_disjoint _ _ _ _ (by simp only [Num.length_encodeLE]; omega)
        (by simp only [Num.length_encodeLE, two32]; omega) (by simp only [two32]; omega)]
  by_cases hn : n < 16
  · obtain ⟨ω', run, e0, e1, e5, e6, -⟩ := memcpy_small (p := p) (P := P) (R := R) x ω μ ret t sp dst src n
      h0 h1 h7 h8 h9 hn hret hjt hbt ⟨hsp.1, hsp.2.1⟩ ⟨hd.1, by omega⟩ ⟨hs.1, by omega⟩ (by omega)
      (by omega) (by omega) hwf hr hw
    refine ⟨ω', _, run.mono (by omega), e0, e1, e5, e6, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    · have hl : ((memcpyFrame μ ω sp).readN src n).length = n := Memory.length_readN
      have := Memory.readN_writeN (memcpyFrame μ ω sp) dst ((memcpyFrame μ ω sp).readN src n)
        (by rw [hl]; unfold two32; omega)
      rw [hl] at this
      rw [this]
      exact readN_frame fun j hj => mF _ (by omega) (by omega)
    · rw [Memory.read_writeN_disjoint _ _ _ _ (by simp only [Memory.length_readN]; omega)
        (by simp only [Memory.length_readN, two32]; omega) (by simp only [two32]; omega)]
      exact mF a ha0 ha2
    · simp only [memcpyFrame, Memory.readable_writeN]
    · simp only [memcpyFrame, Memory.writable_writeN]
  · obtain ⟨ω', μ', run, e0, e1, e5, e6, cp, fr, rd, wr⟩ := memcpy_big (p := p) (P := P) (R := R) x ω μ ret t sp
      dst src n h0 h1 h7 h8 h9 hret hjt hbt hsp (by omega) (by omega) (by omega) hdj hfd hfs hr hw hwf
    exact ⟨ω', μ', run.mono (by omega), by rw [e0, h0], by rw [e1, h1], e5, e6, cp, fr, rd, wr⟩

/-- **`read_exact` on a slice reader, with the copy stated**: `Fmt.read_exact` and the n octets at
    dst equal to the n octets at ptr before the call. -/
theorem read_exact_val {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp Rd dst n ptr len r0 t : Nat) (hsp : 65536 + 88 ≤ sp ∧ sp < 4294967296 ∧ sp % 8 = 0)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat Rd)
    (h8 : ω[8] = UInt64.ofNat dst) (h9 : ω[9] = UInt64.ofNat n)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (rp : rdN μ Rd 8 = ptr) (rl : rdN μ (Rd + 8) 8 = len) (hn : n ≤ len)
    (hRd : Rd + 16 ≤ sp - 88 ∨ sp ≤ Rd) (hRd1 : Rd + 16 < 4294967296)
    (hs : 65536 ≤ ptr ∧ ptr + n + 16 < 4294967296) (hd : 65536 ≤ dst ∧ dst + n + 16 < 4294967296)
    (hdj : dst + n + 24 ≤ ptr ∨ ptr + n + 24 ≤ dst) (hfd : sp ≤ dst ∨ dst + n ≤ sp - 88)
    (hfs : sp ≤ ptr ∨ ptr + n + 16 ≤ sp - 88)
    (hRdd : Rd + 16 ≤ dst ∨ dst + n ≤ Rd)
    (hr : ∀ a, ptr ≤ a → a < ptr + n → μ.readable a = true)
    (hw : ∀ a, dst ≤ a → a < dst + n → μ.writable a = true)
    (hwR : ∀ a, Rd ≤ a → a < Rd + 16 → μ.writable a = true)
    (hwf : ∀ a, sp - 88 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 58434 ω μ x t ω' μ' x (7 * n + 350) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat 0 ∧
      μ'.readN dst n = μ.readN ptr n ∧
      rdN μ' Rd 8 = ptr + n ∧ rdN μ' (Rd + 8) 8 = len - n ∧
      (∀ a, a < 4294967296 → (a < dst ∨ dst + n ≤ a) → (a < sp - 88 ∨ sp ≤ a) → (a < Rd ∨ Rd + 16 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hl64 : len < 18446744073709551616 := rl ▸ rdN_lt64 μ (Rd + 8)
  have hrR : ∀ a, Rd ≤ a → a < Rd + 16 → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (hwR a h1 h2)
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, m0, m8, m16, m24, m32, fr1, rd1, wr1⟩ :=
    re_a (p := p) (P := P) (R := R) x ω μ sp Rd dst n ptr len r0 ω[5].toNat ω[6].toNat ⟨by omega, hsp.2.1⟩
      h0 h1 UInt64.ofNat_toNat.symm UInt64.ofNat_toNat.symm h7 h8 h9
      ⟨by omega, UInt64.toNat_lt _, UInt64.toNat_lt _, by omega, by omega⟩ (by omega) hRd1 rp rl hn hrR
      (fun a h1 h2 => hwf a (by omega) h2)
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, cp2, fr2, rd2, wr2⟩ := memcpy_val (p := p) (P := P) (R := R) x ω1 μ1
    2550 58474 (sp - 40) dst ptr n a0 a1 a7 a8 a9 (by decide) jte_1274 bs_58474
    ⟨by omega, by omega, by omega⟩ hs hd hdj (by omega) (by omega)
    (fun a h1 h2 => by rw [rd1]; exact hr a h1 h2) (fun a h1 h2 => by rw [wr1]; exact hw a h1 h2)
    (fun a h1 h2 => by rw [wr1]; exact hwf a (by omega) (by omega))
  have k2 : ∀ a, sp - 40 ≤ a → a < sp → μ2.read a = μ1.read a := fun a h1 h2 =>
    fr2 a (by omega) (by omega) (Or.inr h1)
  obtain ⟨ω3, μ3, run3, c0, c1, c5, c6, c7, cp, cl, fr3, rd3, wr3⟩ := re_b (p := p) (P := P) (R := R) x ω2 μ2
    (sp - 40) Rd n ptr len r0 t ω[5].toNat ω[6].toNat ⟨by omega, by omega⟩ (b1.trans a1) (b5.trans a5)
    (b6.trans a6) hn hl64
    (by rw [rdN_frame (fun j hj => k2 _ (by omega) (by omega))]; exact m0)
    (by rw [rdN_frame (fun j hj => k2 _ (by omega) (by omega))]; exact m8)
    (by rw [rdN_frame (fun j hj => k2 _ (by omega) (by omega))]; exact m16)
    (by rw [rdN_frame (fun j hj => k2 _ (by omega) (by omega))]; exact m24)
    (by rw [rdN_frame (fun j hj => k2 _ (by omega) (by omega))]; exact m32)
    hret hjt hbt (by omega) hRd1 (by omega)
    (fun a h1 h2 => by rw [rd2, rd1]; exact Memory.readable_of_writable (hwf a (by omega) (by omega)))
    (fun a h1 h2 => by rw [wr2, wr1]; exact hwR a h1 h2)
  refine ⟨ω3, μ3, ((run1.trans run2).trans run3).mono (by omega), c0.trans h0.symm,
    by rw [c1, h1, show sp - 40 + 40 = sp by omega], c5.trans UInt64.ofNat_toNat,
    c6.trans UInt64.ofNat_toNat, c7, ?_, cp, cl, fun a ha hd' hf hR => ?_, fun a => ?_, fun a => ?_⟩
  · rw [readN_frame (fun j hj => fr3 _ (by omega) (by omega)), cp2]
    exact readN_frame fun j hj => fr1 _ (by omega) (by omega)
  · rw [fr3 a ha hR, fr2 a ha hd' (by omega), fr1 a ha (by omega)]
  · rw [rd3, rd2, rd1]
  · rw [wr3, wr2, wr1]

end Services.Bootstrap.Acc
