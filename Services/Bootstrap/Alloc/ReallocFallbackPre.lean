import Services.Bootstrap.Alloc.ReallocGrow

/-!
# The binary's `realloc_impl`: to the fallback

42980 … 43259, when the chunk cannot grow in place without the heap: its next chunk lies past the
heap's end, is used, or with it the chunk is still too small. The memory changes only in the frame.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 43224: the next chunk at or past the heap's end: to the fallback. -/
theorem rg_br_out {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (a b : Nat) (h0 : ω[0] = UInt64.ofNat a) (h4 : ω[4] = UInt64.ofNat b) (hab : b ≤ a)
    (ha : a < 2147483648) (hb : b < 2147483648) :
    FreeStepsH p R 43224 ω μ x 43259 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0, h4, hab]

/-- **42980 … 43259**: a request of req units above the chunk X's `cur − 1` usable units, its next
    chunk past the heap's end, used, or too small: at the fallback with the frame at sp − 152,
    ω₆ = cur − 1, ω₇ the allocator, ω₈ = ptr, ω₁₀ = req, ω₉ kept; the caller's ω₀, ω₅, ω₆ saved;
    the memory changed only in the frame. -/
theorem fallback_pre {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (H F : Nat → Prop) (sp ptr req cur : Nat) (hrep : RepAt μ s H F)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr) (h7 : ω[7] = UInt64.ofNat 196792)
    (h10 : ω[10] = UInt64.ofNat req)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648)
    (hX : Al s.base (ptr - 32)) (hptr : 32 ≤ ptr) (hXH : H (ptr - 32)) (hHF : ∀ a, H a ∨ F a → Al s.base a)
    (hsz : (s.hdr (ptr - 32)).size = 2 * cur + 1) (hlt : cur < req + 1) (hr : req < 33554431) (hc1 : 1 ≤ cur)
    (hXend : ptr - 32 + 32 * cur ≤ s.base + 1073741824)
    (hcase : s.base + 1073741824 ≤ ptr - 32 + 32 * cur ∨
      (ptr - 32 + 32 * cur < s.base + 1073741824 ∧ H (ptr - 32 + 32 * cur) ∧
        (s.hdr (ptr - 32 + 32 * cur)).size % 2 = 1) ∨
      (ptr - 32 + 32 * cur < s.base + 1073741824 ∧ H (ptr - 32 + 32 * cur) ∧
        (s.hdr (ptr - 32 + 32 * cur)).size % 2 = 0 ∧ cur + (s.hdr (ptr - 32 + 32 * cur)).size / 2 < req + 1))
    {HT S0 S1 : Nat} (hHFT : ∀ a, H a ∨ F a → a + 32 ≤ HT)
    (hS : S0 + 152 ≤ sp ∧ sp ≤ S1) (hwr : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 42980 ω μ x 43259 ω' μ' x 70 ∧ RepAt μ' s H F ∧
      (∀ a, μ'.writable a = μ.writable a) ∧
      (∀ a, a < 4294967296 → (a < sp - 152 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      μ'.readN (sp - 8) 8 = Num.encodeLE 8 ω[0].toNat ∧ μ'.readN (sp - 16) 8 = Num.encodeLE 8 ω[5].toNat ∧
      μ'.readN (sp - 24) 8 = Num.encodeLE 8 ω[6].toNat ∧
      ω'[1] = UInt64.ofNat (sp - 152) ∧ ω'[6] = UInt64.ofNat (cur - 1) ∧ ω'[7] = UInt64.ofNat 196792 ∧
      ω'[8] = UInt64.ofNat ptr ∧ ω'[9] = ω[9] ∧ ω'[10] = UInt64.ofNat req := by
  have hXT := hHFT _ (Or.inl hXH)
  obtain ⟨hX1, hX2, hX3⟩ := hX
  have hHFl : ∀ b, H b ∨ F b → b + 16 < 2147483648 := fun b hb => by
    have := hHF b hb; unfold Al at this; omega
  have hwX : rdN μ (ptr - 28) 4 = 2 * cur + 1 := by
    rw [show ptr - 28 = ptr - 32 + 4 by omega, hrep.size _ hXH, hsz]
  obtain ⟨ω1, μ1, r1, a1, -, a6, st0, st5, st6, sf1, ww1, g1⟩ := rl_pro (p := p) (P := P) (R := R) x ω μ sp
    ptr (2 * cur + 1) h1 h8 (by omega) (by omega) hwX (by omega) hsp hsp1 ⟨by omega, by omega⟩ hS hwr
  have W1 := hwr.of_eq ww1
  have rep1 : RepAt μ1 s H F := hrep.congr_low (fun a ha => sf1 a (by omega) (Or.inl (by omega))) hHFl
  have lo1 : ∀ a n, a + n ≤ 2147483648 → rdN μ1 a n = rdN μ a n := fun a n h =>
    rdN_frame fun j hj => sf1 _ (by omega) (Or.inl (by omega))
  obtain ⟨ω2, r2, b3, b5, g2⟩ := rl_go_grow (p := p) (P := P) (R := R) x ω1 μ1 req ((2 * cur + 1) / 2 - 1)
    (by rw [fget g1 10 (by decide) (by decide)]; exact h10) a6
    (by rw [fget g1 7 (by decide) (by decide)]; exact h7) (by omega) (by omega)
  have hb1 : rdN μ1 206520 8 = s.base := by have := rep1.base; unfold A0 at this; exact this
  obtain ⟨ω3, μ3, r3, c0, c4, c2, c12, c5, -, -, c112, -, sf3, ww3, g3⟩ := rg_pre (p := p) (P := P)
    (R := R) x ω2 μ1 (sp - 152) ptr req cur s.base
    (by rw [fget g2 1 (by decide) (by decide)]; exact a1)
    (by rw [fget g2 8 (by decide) (by decide), fget g1 8 (by decide) (by decide)]; exact h8)
    (by rw [fget g2 10 (by decide) (by decide), fget g1 10 (by decide) (by decide)]; exact h10) b5 b3
    (by omega) (by rw [lo1 _ _ (by omega), hrep.size _ hXH, hsz]) hlt (by omega) hb1 hbT (by omega)
    (by omega) (by omega) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ W1
  have W3 := W1.of_eq ww3
  have rep3 : RepAt μ3 s H F := rep1.congr_low (fun a ha => sf3 a (by omega) (Or.inl (by omega))) hHFl
  -- registers kept through the prefix
  have K : ∀ j : Nat, (hj : j < 13) → j ∉ [0, 1, 2, 3, 4, 5, 6, 11, 12] → ω3[j]'hj = ω[j]'hj := fun j hj h => by
    rw [fget g3 j hj (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega),
      fget g2 j hj (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega),
      fget g1 j hj (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega)]
  have K1 : ω3[1] = UInt64.ofNat (sp - 152) := by
    rw [fget g3 1 (by decide) (by decide), fget g2 1 (by decide) (by decide)]; exact a1
  have K6 : ω3[6] = UInt64.ofNat (cur - 1) := by
    rw [fget g3 6 (by decide) (by decide), fget g2 6 (by decide) (by decide), a6]; congr 1; omega
  have fin : ∀ ω' μ' n, FreeStepsH p R 43224 ω3 μ3 x 43259 ω' μ' x n →
      (∀ a, μ'.writable a = μ3.writable a) →
      (∀ a, a < 4294967296 → (a < sp - 152 + 80 ∨ sp - 152 + 88 ≤ a) → μ'.read a = μ3.read a) →
      (∀ j : Fin 13, j.val ∉ [0, 4, 5, 11, 12] → ω'[j] = ω3[j]) → n ≤ 30 →
      ∃ ω' μ', FreeStepsH p R 42980 ω μ x 43259 ω' μ' x 70 ∧ RepAt μ' s H F ∧
        (∀ a, μ'.writable a = μ.writable a) ∧
        (∀ a, a < 4294967296 → (a < sp - 152 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
        μ'.readN (sp - 8) 8 = Num.encodeLE 8 ω[0].toNat ∧ μ'.readN (sp - 16) 8 = Num.encodeLE 8 ω[5].toNat ∧
        μ'.readN (sp - 24) 8 = Num.encodeLE 8 ω[6].toNat ∧
        ω'[1] = UInt64.ofNat (sp - 152) ∧ ω'[6] = UInt64.ofNat (cur - 1) ∧ ω'[7] = UInt64.ofNat 196792 ∧
        ω'[8] = UInt64.ofNat ptr ∧ ω'[9] = ω[9] ∧ ω'[10] = UInt64.ofNat req := by
    intro ω' μ' n run ww fr g hn
    have sv : ∀ a, sp - 24 ≤ a → a + 8 ≤ sp → μ'.readN a 8 = μ1.readN a 8 := fun a h1 h2 =>
      Memory.readN_congr fun j hj => (fr _ (by omega) (Or.inr (by omega))).trans (sf3 _ (by omega) (Or.inr (by omega)))
    refine ⟨ω', μ', (((r1.trans r2).trans r3).trans run).mono (by omega),
      rep3.congr_low (fun a ha => fr a (by omega) (Or.inl (by omega))) hHFl,
      fun a => (ww a).trans ((ww3 a).trans (ww1 a)),
      fun a h1 h2 => (fr a h1 (by omega)).trans ((sf3 a h1 (by omega)).trans (sf1 a h1 (by omega))),
      by rw [sv _ (by omega) (by omega)]; exact st0, by rw [sv _ (by omega) (by omega)]; exact st5,
      by rw [sv _ (by omega) (by omega)]; exact st6,
      by rw [fget g 1 (by decide) (by decide)]; exact K1, by rw [fget g 6 (by decide) (by decide)]; exact K6,
      by rw [fget g 7 (by decide) (by decide), K 7 (by decide) (by decide)]; exact h7,
      by rw [fget g 8 (by decide) (by decide), K 8 (by decide) (by decide)]; exact h8,
      by rw [fget g 9 (by decide) (by decide), K 9 (by decide) (by decide)],
      by rw [fget g 10 (by decide) (by decide), K 10 (by decide) (by decide)]; exact h10⟩
  rcases hcase with hout | ⟨hin, hnc, hodd⟩ | ⟨hin, hnc, hev, hsm⟩
  · -- past the heap's end
    have b := rg_br_out (p := p) (P := P) (R := R) x ω3 μ3 _ _ c0 c4 hout (by omega) hbT
    exact fin ω3 μ3 1 b (fun a => rfl) (fun a _ _ => rfl) (fun j _ => rfl) (by omega)
  all_goals
    have hnT := hHFT _ (Or.inl hnc)
    have b4 := rg_br_in (p := p) (P := P) (R := R) x ω3 μ3 (ptr - 32 + 32 * cur) (s.base + 1073741824) c0 c4 hin
      (by omega) hbT
    have hwn : rdN μ3 (ptr - 32 + 32 * cur + 4) 4 = (s.hdr (ptr - 32 + 32 * cur)).size := rep3.size _ hnc
    have hw32 : (s.hdr (ptr - 32 + 32 * cur)).size < 4294967296 := by
      rw [← hwn]; exact rdN_lt _ _ 4
    obtain ⟨ω5, μ5, r5, d5, d11, -, sf5, ww5, g5⟩ := rg_nhdr (p := p) (P := P) (R := R) x ω3 μ3 (sp - 152)
      (ptr - 32 + 32 * cur) _ K1 c0 (by omega) hwn (by omega) (by omega)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ W3
  · -- the next chunk used
    have b6 := rg_br_used (p := p) (P := P) (R := R) x ω5 μ5 1 (by rw [d11, hodd]) (by decide) (by decide)
    exact fin ω5 μ5 _ ((b4.trans r5).trans b6) ww5 (fun a h1 h2 => sf5 a h1 h2)
      (fun j hj => g5 j (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega)) (by omega)
  · -- too small with it
    have b6 := rg_br_free (p := p) (P := P) (R := R) x ω5 μ5 (by rw [d11, hev])
    have k112 : rdN μ5 (sp - 152 + 112) 8 = req + 1 := by
      rw [← c112]; exact rdN_frame fun j hj => sf5 _ (by omega) (Or.inr (by omega))
    obtain ⟨ω6, r6, g6⟩ := rg_avail_lt (p := p) (P := P) (R := R) x ω5 μ5 (sp - 152) cur
      ((s.hdr (ptr - 32 + 32 * cur)).size / 2) (req + 1)
      (by rw [fget g5 1 (by decide) (by decide)]; exact K1)
      (by rw [d5]; congr 1; omega) (by rw [fget g5 12 (by decide) (by decide)]; exact c12) k112 hsm (by omega)
      (by omega) (by omega) ⟨by omega, by omega⟩ (W3.of_eq ww5).rd
    exact fin ω6 μ5 _ (((b4.trans r5).trans b6).trans r6) ww5 (fun a h1 h2 => sf5 a h1 h2)
      (fun j hj => by
        rw [g6 j (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega),
          g5 j (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega)]) (by omega)

end Services.Bootstrap.Alloc
