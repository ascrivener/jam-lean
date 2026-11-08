import Services.Bootstrap.Alloc.ReallocGrowStages

/-!
# The binary's `grow_inplace` after the checks

43504 … 40805, in one lemma: the old next chunk leaves its bin (`grow_unreg`), and the chunk takes
its new size with the free tail and the return (`grow_tail`). It needs only the frame's slots, so
callers elaborate it in a small context.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **43504 … 40805**: the chunk X (sp + 88, sp + 120) of `cur` units grows to n units over its
    free next chunk nc = X + 32·cur of `sz` units — the memory holds the model's
    `freeFinal (growHdr (unregister s nc (binDown sz)) X n) …`, and the code returns into
    `realloc` (40805) with ω₇ = ptr and ω₀, ω₁, ω₅, ω₆ from the frame. -/
theorem grow_post {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (H F : Nat → Prop) (sp base Xc cur sz n ptr v5 v6 : Nat) (hrep : RepAt μ s H F)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h3 : ω[3] = UInt64.ofNat 204984)
    (h8 : ω[8] = UInt64.ofNat ptr) (hp : ptr < 18446744073709551616)
    (s40 : rdN μ (sp + 40) 8 = sz) (s48 : rdN μ (sp + 48) 8 = 2 * sz) (s112 : rdN μ (sp + 112) 8 = n)
    (s64 : rdN μ (sp + 64) 8 = Xc + 32 * n) (s72 : rdN μ (sp + 72) 8 = cur + sz)
    (s56 : rdN μ (sp + 56) 8 = Xc + 32 * cur) (s80 : rdN μ (sp + 80) 8 = Xc + 32 * cur)
    (s88 : rdN μ (sp + 88) 8 = Xc) (s120 : rdN μ (sp + 120) 8 = Xc)
    (s96 : rdN μ (sp + 96) 8 = base + 1073741824)
    (s0 : rdN μ (sp + 144) 8 = 1988) (s5 : rdN μ (sp + 136) 8 = v5) (s6 : rdN μ (sp + 128) 8 = v6)
    (hn : n ≤ cur + sz) (hcn : cur < n) (hn1 : 1 ≤ n) (hnb : n < 33554432) (hcs : cur + sz < 2147483648)
    (hb0 : 206864 ≤ base) (hbT : base + 1073741824 < 2147483648) (hHF : ∀ a, H a ∨ F a → Al base a)
    (hAX : Al base Xc) (hXH : H Xc)
    (hsz : (s.hdr (Xc + 32 * cur)).size = 2 * sz) (hfree : NxFree s F base (Xc + 32 * cur) 0)
    (hMt : Xc + 32 * (cur + sz) ≤ base + 1073741824)
    (hold : cur + sz - n ≠ 0 →
      (growHdr (unregister s (Xc + 32 * cur) (binDown sz)) Xc n).heads (binDown (cur + sz - n)) ≠ Xc + 32 * n)
    (hold1 : cur + sz - n ≠ 0 →
      (growHdr (unregister s (Xc + 32 * cur) (binDown sz)) Xc n).heads (binDown (cur + sz - n)) ≠ 0 →
      Al base ((growHdr (unregister s (Xc + 32 * cur) (binDown sz)) Xc n).heads (binDown (cur + sz - n))))
    (hnext : Xc + 32 * (cur + sz) < base + 1073741824 → H (Xc + 32 * (cur + sz)))
    (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296) {HT S0 S1 : Nat}
    (hHFT : ∀ a, H a ∨ F a → a + 32 ≤ HT) (hS : S0 ≤ sp ∧ sp + 152 ≤ S1) (hw : WrAt μ HT S0 S1)
    (hNT : cur + sz - n ≠ 0 → Xc + 32 * n + 32 ≤ HT)
    (hold1T : cur + sz - n ≠ 0 →
      (growHdr (unregister s (Xc + 32 * cur) (binDown sz)) Xc n).heads (binDown (cur + sz - n)) ≠ 0 →
      (growHdr (unregister s (Xc + 32 * cur) (binDown sz)) Xc n).heads (binDown (cur + sz - n)) + 32 ≤ HT) :
    ∃ ω' μ', FreeStepsH p R 43504 ω μ x 40805 ω' μ' x 150 ∧
      RepAt μ' (freeFinal (growHdr (unregister s (Xc + 32 * cur) (binDown sz)) Xc n) (Xc + 32 * n) n (cur + sz - n)
          (base + 1073741824))
        (fun a => H a ∨ (cur + sz - n ≠ 0 ∧ a = Xc + 32 * n)) (fun a => F a ∨ (cur + sz - n ≠ 0 ∧ a = Xc + 32 * n)) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧
      (∀ a, a < 4294967296 → 2147483648 ≤ a → (a < sp + 104 ∨ sp + 112 ≤ a) → μ'.read a = μ.read a) ∧
      ω'[7] = UInt64.ofNat ptr ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat (sp + 152) ∧
      ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 := by
  have hT : PLift ((_ : Prop) ∧ (_ : Prop)) := ⟨⟨hNT, hold1T⟩⟩
  have hszN : sz ≤ 33554432 := by have := hfree.2.2.1; rw [hsz] at this; omega
  clear hNT hold1T
  obtain ⟨ω1, μ1, r1, rep1, ww1, sf1, u2, u5, u6, g1⟩ := grow_unreg (p := p) (P := P) (R := R) x ω μ s H F
    sp base (Xc + 32 * cur) sz n (Xc + 32 * n) (cur + sz) hrep h1 h7 h3 s40 s48 s112 s64 s72 s56 s80 hn
    (by omega) hb0 hbT hHF hsz hfree hsp hsp1 hHFT hS hw
  have rd : ∀ a v, rdN μ a 8 = v → sp ≤ a → a + 8 ≤ sp + 152 → rdN μ1 a 8 = v := fun a v h h1 h2 => by
    rw [← h]; exact rdN_frame fun j hj => sf1 _ (by omega) (by omega)
  obtain ⟨ω2, μ2, r2, rep2, ww2, sf2, e7, e0, e1, e5, e6⟩ := grow_tail (p := p) (P := P) (R := R) x ω1 μ1
    (unregister s (Xc + 32 * cur) (binDown sz)) H F sp base Xc n (cur + sz - n) ptr v5 v6 rep1
    (by rw [fget g1 1 (by decide) (by decide)]; exact h1) u5 u6 u2
    (by rw [fget g1 7 (by decide) (by decide)]; exact h7) (by rw [fget g1 3 (by decide) (by decide)]; exact h3)
    (by rw [fget g1 8 (by decide) (by decide)]; exact h8) hp
    (rd _ _ s88 (by omega) (by omega)) (rd _ _ s120 (by omega) (by omega)) (rd _ _ s112 (by omega) (by omega))
    (by rw [show n + (cur + sz - n) = cur + sz by omega]; exact rd _ _ s72 (by omega) (by omega))
    (rd _ _ s96 (by omega) (by omega)) hb0 hbT hAX hXH (by omega) hn1 hnb
    (by rw [show n + (cur + sz - n) = cur + sz by omega]; exact hMt) hold hold1 hHF
    (by rw [show n + (cur + sz - n) = cur + sz by omega]; exact hnext)
    (rd _ _ s0 (by omega) (by omega)) (rd _ _ s5 (by omega) (by omega)) (rd _ _ s6 (by omega) (by omega))
    hsp hsp1 hHFT hS (hw.of_eq ww1) hT.down.1 hT.down.2
  exact ⟨ω2, μ2, (r1.trans r2).mono (by omega), rep2, fun a => (ww2 a).trans (ww1 a),
    fun a h1 h2 h3 => (sf2 a h1 h2 h3).trans (sf1 a h1 h2), e7, e0, e1, e5, e6⟩

end Services.Bootstrap.Alloc
