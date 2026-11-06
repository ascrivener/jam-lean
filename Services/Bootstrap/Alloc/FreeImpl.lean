import Services.Bootstrap.Alloc.StageA

/-!
# The binary's `free`, whole

`free_impl`: the compiled free path, from its entry (42327, called by `dealloc` with ω₀ = 1986)
to the return into `dealloc` (40681), leaves memory that holds the model's `free s ptr` — given the
facts about the heap the stages need, which the invariant provides.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **The binary's free path refines the model's `free`.** -/
theorem free_impl {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s s1 s2 : State) (H F : Nat → Prop) (sp ptr M sz1 pv' total : Nat) (hrep : RepAt μ s H F)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr) (h7 : ω[7] = UInt64.ofNat 196792)
    (h0 : ω[0] = UInt64.ofNat 1986) (hsp : 2147483700 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648)
    (hX : Al s.base (ptr - 32)) (hptr : 32 ≤ ptr) (hXH : H (ptr - 32)) (hHF : ∀ a, H a ∨ F a → Al s.base a)
    (hpv : (s.hdr (ptr - 32)).prev < 2147483648)
    (hm : mergePrev s (ptr - 32) (wordSize (s.hdr (ptr - 32)).size) (s.hdr (ptr - 32)).prev = (s1, M, sz1, pv'))
    (hn : mergeNext s1 M sz1 (s.base + 1073741824) = (s2, total))
    -- stage A
    (hpH : ptr - 32 ≠ s.base → 32 * (s.hdr (ptr - 32)).prev ≤ ptr - 32 - s.base ∧
      H (ptr - 32 - 32 * (s.hdr (ptr - 32)).prev))
    (hpf : ptr - 32 ≠ s.base → (s.hdr (ptr - 32 - 32 * (s.hdr (ptr - 32)).prev)).size % 2 = 0 →
      PvFree s F s.base (ptr - 32 - 32 * (s.hdr (ptr - 32)).prev) (wordSize (s.hdr (ptr - 32)).size)
        (s.hdr (ptr - 32)).prev)
    -- stage B
    (hs1 : s1.base = s.base) (hAM : Al s.base M) (hM : M + 32 * sz1 ≤ s.base + 1073741824)
    (hnc : M + 32 * sz1 < s.base + 1073741824 → H (M + 32 * sz1))
    (hnf : M + 32 * sz1 < s.base + 1073741824 → (s1.hdr (M + 32 * sz1)).size % 2 = 0 →
      NxFree s1 F s.base (M + 32 * sz1) sz1)
    -- stage C
    (ht1 : 1 ≤ total) (ht2 : total ≤ 33554432) (hMt : M + 32 * total ≤ s.base + 1073741824)
    (hpv' : pv' < 4294967296) (hold : s2.heads (binDown total) ≠ M)
    (hold1 : s2.heads (binDown total) ≠ 0 → Al s.base (s2.heads (binDown total)))
    (hnext : M + 32 * total < s.base + 1073741824 → H (M + 32 * total))
    (hw : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 42327 ω μ x 40681 ω' μ' x 220 ∧
      RepAt μ' (free s ptr) (fun a => H a ∨ a = M) (fun a => F a ∨ a = M) ∧
      (∀ a, μ'.writable a = true) ∧ (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧ ω'[0] = UInt64.ofNat 1986 ∧ ω'[1] = UInt64.ofNat sp ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have hHFl : ∀ b, H b ∨ F b → b + 16 < 2147483648 := fun b hb => by
    have := hHF b hb; unfold Al at this; omega
  obtain ⟨hX1, hX2, hX3⟩ := hX
  have hbase : rdN μ 206520 8 = s.base := by have := hrep.base; unfold A0 at this; exact this
  have hwX : rdN μ (ptr - 32 + 4) 4 = (s.hdr (ptr - 32)).size := hrep.size _ hXH
  have hpX : rdN μ (ptr - 32) 4 = (s.hdr (ptr - 32)).prev := hrep.prev _ hXH
  obtain ⟨ω1, μ1, r1, a1, a8, a4, a5, a10, a3, a9, a11, a2, st0, st5, st6, sf1, ww1, g1⟩ :=
    free_pro (p := p) (P := P) (R := R) x ω μ sp ptr s.base (s.hdr (ptr - 32)).size (s.hdr (ptr - 32)).prev
      h1 h8 h7 (by omega) hsp1 hbase hwX hpX hpv (by omega) (by omega) hw
  have rep1 := hrep.congr_low (fun b hb => sf1 b (by omega) (Or.inl (by omega))) hHFl
  obtain ⟨ω2, μ2, r2, rep2, b8, b2, b3, b5, ww2, sf2, g2⟩ := free_prev (p := p) (P := P) (R := R) x ω1 μ1 s H F
    (ptr - 32) (wordSize (s.hdr (ptr - 32)).size) (s.hdr (ptr - 32)).prev rep1 a9 a11 a8 a3 a2 a5
    (by rw [fget g1 7 (by decide) (by decide)]; exact h7) a4 hb0 hbT ⟨hX1, hX2, hX3⟩ hHF hpH hpf ww1
  rw [hm] at rep2 b8 b2 b3
  simp only at rep2 b8 b2 b3
  obtain ⟨ω3, μ3, r3, rep3, c2, c12, ww3, sf3, g3⟩ := free_next (p := p) (P := P) (R := R) x ω2 μ2 s1 H F s.base M
    sz1 rep2 b5 b2 b8 (by rw [fget g2 7 (by decide) (by decide), fget g1 7 (by decide) (by decide)]; exact h7)
    (by rw [fget g2 4 (by decide) (by decide)]; exact a4) hb0 hbT hAM hM hHF hnc hnf ww2
  rw [hn] at rep3 c2
  simp only at rep3 c2
  have stk : ∀ a, a < 4294967296 → 2147483648 ≤ a → μ3.read a = μ1.read a := fun a h1 h2 =>
    (sf3 a h1 h2).trans (sf2 a h1 h2)
  obtain ⟨ω4, μ4, r4, rep4, ww4, sf4, e0, e1, e5, e6⟩ := free_tail (p := p) (P := P) (R := R) x ω3 μ3 s2 H F
    s.base M pv' total sp ω[5].toNat ω[6].toNat rep3 c2
    (by rw [fget g3 8 (by decide) (by decide)]; exact b8)
    (by rw [fget g3 3 (by decide) (by decide)]; exact b3)
    (by rw [fget g3 7 (by decide) (by decide), fget g2 7 (by decide) (by decide),
      fget g1 7 (by decide) (by decide)]; exact h7)
    (by rw [fget g3 4 (by decide) (by decide), fget g2 4 (by decide) (by decide)]; exact a4) c12
    (by rw [fget g3 1 (by decide) (by decide), fget g2 1 (by decide) (by decide)]; exact a1)
    hb0 hbT ht1 ht2 hAM hMt hpv' hold hold1 hHF hnext
    (by
      have e : ω[0].toNat = 1986 := by rw [h0]; rfl
      rw [← e, ← st0]; exact readN_frame fun j hj => stk _ (by omega) (by omega))
    (by rw [← st5]; exact readN_frame fun j hj => stk _ (by omega) (by omega))
    (by rw [← st6]; exact readN_frame fun j hj => stk _ (by omega) (by omega))
    (UInt64.toNat_lt _) (UInt64.toNat_lt _) hsp hsp1 ww3
  refine ⟨ω4, μ4, ((((r1.trans r2).trans r3).trans r4)).mono (by omega), ?_, ww4,
    fun a h1 h2 => ((sf4 a h1 (by omega)).trans (stk a h1 (by omega))).trans (sf1 a h1 (Or.inr h2)), e0, e1,
    by rw [e5, UInt64.ofNat_toNat], by rw [e6, UInt64.ofNat_toNat]⟩
  unfold free
  simp only [hm, hn, maxSize_val, Nat.reduceMul]
  exact rep4

end Services.Bootstrap.Alloc
