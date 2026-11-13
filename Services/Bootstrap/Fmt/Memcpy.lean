import Services.Bootstrap.MemcpyBig

/-!
# `memcpy` of any length, as a frame

`memcpy_frame` puts `memcpy_small` (n < 16) and `memcpy_big` (n ≥ 16) together. The compiler's
`memcpy` (68729) writes only its 48-octet frame below sp and the n octets at dst, keeps every
page's access, and returns within 7n + 320 steps.
-/

namespace Services.Bootstrap.Fmt

open PVM Services.Bootstrap Services.Bootstrap.Code

variable {X : Type} {R : HostRel X}

/-- **`memcpy`, any length**: from ω₇ = dst, ω₈ = src, ω₉ = n, ω₁ = sp (8-aligned) and a return
    address ω₀ that `djump` resolves to `t`, `memcpy` returns to `t` with ω₀, ω₁, ω₅, ω₆ as they
    were. Memory changes only in sp − 48 … sp and dst … dst + n, and every page keeps its access.
    The two ranges and src … src + n are apart, with 24 octets to spare. -/
theorem memcpy_frame {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
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
      (∀ a, a < 4294967296 → (a < dst ∨ dst + n ≤ a) → (a < sp - 48 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  by_cases hn : n < 16
  · obtain ⟨ω', run, e0, e1, e5, e6, -⟩ := memcpy_small (p := p) (P := P) (R := R) x ω μ ret t sp dst src n
      h0 h1 h7 h8 h9 hn hret hjt hbt ⟨hsp.1, hsp.2.1⟩ ⟨hd.1, by omega⟩ ⟨hs.1, by omega⟩ (by omega)
      (by omega) (by omega) hwf hr hw
    refine ⟨ω', _, run.mono (by omega), e0, e1, e5, e6, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    · rw [Memory.read_writeN_disjoint _ _ _ _ (by simp only [Memory.length_readN]; omega)
        (by simp only [Memory.length_readN, two32]; omega) (by simp only [two32]; omega)]
      unfold memcpyFrame
      rw [Memory.read_writeN_disjoint _ _ _ _ (by simp only [Num.length_encodeLE]; omega)
          (by simp only [Num.length_encodeLE, two32]; omega) (by simp only [two32]; omega),
        Memory.read_writeN_disjoint _ _ _ _ (by simp only [Num.length_encodeLE]; omega)
          (by simp only [Num.length_encodeLE, two32]; omega) (by simp only [two32]; omega),
        Memory.read_writeN_disjoint _ _ _ _ (by simp only [Num.length_encodeLE]; omega)
          (by simp only [Num.length_encodeLE, two32]; omega) (by simp only [two32]; omega)]
    · simp only [memcpyFrame, Memory.readable_writeN]
    · simp only [memcpyFrame, Memory.writable_writeN]
  · obtain ⟨ω', μ', run, e0, e1, e5, e6, -, fr, rd, wr⟩ := memcpy_big (p := p) (P := P) (R := R) x ω μ ret t sp
      dst src n h0 h1 h7 h8 h9 hret hjt hbt hsp (by omega) (by omega) (by omega) hdj hfd hfs hr hw hwf
    exact ⟨ω', μ', run.mono (by omega), by rw [e0, h0], by rw [e1, h1], e5, e6, fr, rd, wr⟩

end Services.Bootstrap.Fmt
