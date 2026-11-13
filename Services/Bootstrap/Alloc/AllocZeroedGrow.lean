import Services.Bootstrap.Alloc.AllocZeroedImpl
import Services.Bootstrap.Alloc.AllocGrowImpl

/-!
# The binary's `alloc_impl` with the zero flag, the heap grown

`AllocGrowImpl.lean`'s composition with the zero flag generic, ending at the caller's return target.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code JAM

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **`alloc_impl_growKG` with the zero flag z**, to the caller's return target tg; the memory kept off
    the headers and the block's data. -/
theorem alloc_impl_growKGZ {X : Type} {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X)
    (cap : Nat) (hcap : cap < 18446744073709551616) (x : X) (ω : Regs)
    (μ : Memory)
    (s : State) (H F : Nat → Prop) (sp req bin C : Nat) (hrep : RepAt μ s H F)
    (hbits : BitsOk s.secondary s.primary s.heads)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat 1)
    (h9 : ω[9] = UInt64.ofNat req) (z : Nat) (hz : z < 18446744073709551616) (h10 : ω[10] = UInt64.ofNat z)
    (ret tg : Nat) (h0 : ω[0] = UInt64.ofNat ret) (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = tg) (hbt : P.isBlockStart tg = true)
    (hreq : 1 ≤ req) (hb8 : s.base % 8 = 0)
    (hCdis : ∀ a, H a ∨ F a → a ≠ C → a + 16 ≤ C ∨ C + 32 * wordSize (s.hdr C).size ≤ a)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648)
    (hm : req + 1 ≤ 33554432)
    (hbin : (findFirst s (binUp (req + 1))).or (findFirst s (binDown (req + 1))) = some bin) (hbn : bin < 2432)
    (hcb : s.heads bin = C) (hFC : F C) (hHC : H C) (hHF : ∀ a, H a ∨ F a → Al s.base a)
    (hnx : (s.hdr C).next ≠ 0 → F (s.hdr C).next) (hpv : (s.hdr C).prev < 2147483648)
    (hS : req + 1 ≤ wordSize (s.hdr C).size) (hCend : C + 32 * wordSize (s.hdr C).size ≤ s.base + 1073741824)
    (hal : s.allocated < 2147483648)
    (E : Nat) (hE : (C - s.base) / 32 + 1 + req + (if wordSize (s.hdr C).size - req - 1 = 0 then 0 else 1) = E)
    (hgr : s.allocated < E) (pb h : Nat) (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ h) (hhb : h ≤ pb)
    (hbs : pb < 4294967296) (hR : pagesOf (s.base + 32 * E) ≤ pb)
    (hcost : 275 + 121 * (growTop (pagesOf (s.base + 32 * E)) h pb - h) ≤ cap)
    (hNdis : wordSize (s.hdr C).size - req - 1 ≠ 0 → ∀ a, H a ∨ F a →
      a + 32 ≤ C + 32 * (req + 1) ∨ C + 32 * (req + 1) + 32 ≤ a)
    (hNold : wordSize (s.hdr C).size - req - 1 ≠ 0 →
      (registerAlloc (unregister { s with allocated := E } C bin) C (s.hdr C).prev (req + 1)).heads (binDown (wordSize (s.hdr C).size - req - 1))
        ≠ 0 →
      F ((registerAlloc (unregister { s with allocated := E } C bin) C (s.hdr C).prev (req + 1)).heads
        (binDown (wordSize (s.hdr C).size - req - 1))))
    (hFin : C + 32 * wordSize (s.hdr C).size < s.base + 1073741824 → H (C + 32 * wordSize (s.hdr C).size))
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * h) (hSTk : S0 + 152 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0)
    (hp : HeapPages μ 48 pb h) (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true)
    (hHFT : ∀ a, H a ∨ F a → a + 32 ≤ 4096 * h) :
    ∃ ω' μ', FreeStepsH p (env.rel cap) 41177 ω μ x tg ω' μ' x (96 * req + 560) ∧
      RepAt μ' (allocPost { s with allocated := E } bin req (wordSize (s.hdr C).size) (s.base + 1073741824))
        (fun a => H a ∨ (wordSize (s.hdr C).size - req - 1 ≠ 0 ∧ a = C + 32 * (req + 1)))
        (fun a => F a ∨ (wordSize (s.hdr C).size - req - 1 ≠ 0 ∧ a = C + 32 * (req + 1))) ∧
      ω'[7] = UInt64.ofNat (C + 32) ∧ ω'[0] = ω[0] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[1] = ω[1] ∧
      HeapPages μ' 48 pb (growTop (pagesOf (s.base + 32 * E)) h pb) ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧ (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      HKeepGD μ μ' (fun a => (H a ∨ F a) ∨ (wordSize (s.hdr C).size - req - 1 ≠ 0 ∧ a = C + 32 * (req + 1)))
        (C + 32) (C + 32 + 32 * req) := by
  have hwr := HeapPages.wrAt hp hhb hst
  obtain ⟨hRt, ht1, ht2⟩ := growTop_ge (h := h) hR
  have hpE := pagesOf_ge (s.base + 32 * E)
  generalize hT : growTop (pagesOf (s.base + 32 * E)) h pb = t at *
  have hAC := hHF C (Or.inr hFC)
  unfold Al at hAC
  have hHFl : ∀ a, H a ∨ F a → a + 16 < 2147483648 := fun a ha => by have := hHF a ha; unfold Al at this; omega
  generalize hSd : wordSize (s.hdr C).size = S at *
  have hsz := hrep.size C hHC
  have hwS : (s.hdr C).size / 2 = S := by rw [← hSd]; rfl
  have hsec : ∀ q, q < 38 → rdN μ (q * 8 + 204984 + 1544) 8 = s.secondary q := fun q hq => by
    have := hrep.sec q hq; unfold A0 at this; rw [show q * 8 + 204984 + 1544 = 196792 + 9736 + 8 * q by omega]
    exact this
  have hheads : rdN μ (196792 + 4 * bin) 4 = C := by
    have := hrep.heads bin hbn; unfold A0 at this; rw [this, hcb]
  have hbase : rdN μ 206520 8 = s.base := by have := hrep.base; unfold A0 at this; exact this
  have hpri : rdN μ 206832 8 = s.primary := by have := hrep.pri; unfold A0 at this; exact this
  obtain ⟨ω1, μ1, r1, q, b, hqb, hq, hb, a1, a10, a11, a5, a2, a6, a3, a8, a9, a4, a12, a7, st0, st5, st6, st10,
      st32, sf1, ww1⟩ := alloc_entry (p := p) (P := P) (R := env.rel cap) x ω μ s sp req bin C (s.hdr C).size hbits h1 h7 h8 h9
    hsp hsp1 hbase (by omega) hpri hsec hm hbin hheads hsz (by omega) (by omega) hHTs hSTk ⟨by omega, by have := hHFT C (Or.inr hFC); omega⟩ hwr
  rw [hwS] at a11
  have rep1 : RepAt μ1 s H F := hrep.congr_low (fun a ha => sf1 a (by omega) (Or.inl (by omega))) hHFl
  obtain ⟨ω2, μ2, r2, rep2, b1, b8, b0, m96, m48, m80, m72, m104, m88, m120, hp2, hst2, fr2, hk2, g2⟩ := alloc_mid_growKG (p := p)
    (P := P) (S0 := S0) (S1 := S1) env cap hcap x ω1 μ1 s H F (sp - 152) req bin q b C S rep1 hcb hqb hq hb hFC hHC hHF hnx hb0 hbT hpv hS
    (by omega) hCend hal E hE hgr pb h hbd h48 hhb hbs hR (by rw [hT]; exact hcost) a1 a10 a11 a5 a2 a6 a3 a8 a9 (by rw [show sp - 152 + 120 = sp - 32 by omega]; exact st32)
    (by omega) (by omega) hHTs ⟨by omega, by omega⟩ hSb (HeapPages.of_eq hp ww1)
    (fun a h1 h2 => by rw [ww1]; exact hst a h1 h2) hHFT
  rw [hT] at hp2
  have hw2 := HeapPages.wrAt hp2 (by omega) hst2
  have hHFT2 : ∀ a, H a ∨ F a → a + 32 ≤ 4096 * t := fun a ha => by have := hHFT a ha; omega
  generalize hpvd : (s.hdr C).prev = pv at *
  generalize ht2 : unregister { s with allocated := E } C bin = t2 at *
  have e2b : t2.base = s.base := by rw [← ht2, unregister_base]

  have hCa : (C - s.base) % 32 = 0 := hAC.2.1
  obtain ⟨ω3, μ3, r3, rep3, c3, c12, c8, c2, c1, c4, ww3, fr3, hk3⟩ := alloc_end1Z (p := p) (P := P) (R := env.rel cap) x ω2 μ2 t2 H F
    (sp - 152) req C pv (S - req - 1) rep2 hHC (by rw [e2b]; exact hHF) (by rw [e2b]; exact hb0)
    (by rw [e2b]; exact hbT) (by rw [e2b]; exact hCa) (by rw [e2b]; omega) hpv (by omega) (by omega)
    (by rw [e2b]; omega) hNdis hNold b1 (by rw [e2b]; exact b8) b0
    (by rw [fget g2 4 (by decide) (by decide)]; exact a4) (by rw [fget g2 9 (by decide) (by decide)]; exact a9)
    (by rw [fget g2 7 (by decide) (by decide)]; exact a7) (by rw [e2b]; exact m96) m48 _ m80
    (by rw [e2b]; exact m72) m104 m88 m120 (by omega) (by omega) (by omega) ⟨by omega, by omega⟩ hHFT2
    (fun h0 => by have h' := hE; rw [if_neg h0] at h'; omega) hw2
  generalize ht3 : register (registerAlloc t2 C pv (req + 1)) (C + 32 * (req + 1)) (req + 1) (S - req - 1) = rr at *
  have e3b : rr.1.base = s.base := by rw [← ht3, register_base, registerAlloc_base, e2b]
  have k112 : rdN μ3 (sp - 152 + 112) 8 = z := by
    rw [show rdN μ3 (sp - 152 + 112) 8 = rdN μ1 (sp - 152 + 112) 8 from rdN_frame fun j hj =>
      (fr3 _ (by omega) (by omega)).trans (fr2 _ (by omega) (by omega) (by omega)),
      show sp - 152 + 112 = sp - 40 by omega]
    unfold rdN; rw [st10, h10, Num.decodeLE_encodeLE, UInt64.toNat_ofNat_of_lt' hz, Nat.mod_eq_of_lt hz]
  have k144 : rdN μ3 (sp - 152 + 144) 8 = ret := by
    rw [show rdN μ3 (sp - 152 + 144) 8 = rdN μ1 (sp - 152 + 144) 8 from rdN_frame fun j hj =>
      (fr3 _ (by omega) (by omega)).trans (fr2 _ (by omega) (by omega) (by omega)),
      show sp - 152 + 144 = sp - 8 by omega]
    unfold rdN; rw [st0, h0, Num.decodeLE_encodeLE]
    have : ret < 18446744073709551616 := by omega
    rw [UInt64.toNat_ofNat_of_lt' this, Nat.mod_eq_of_lt this]
  have hC8 : (C + 32) % 8 = 0 := by omega
  have k120 : rdN μ3 (sp - 152 + 120) 8 = 204984 := by
    rw [← m120]; exact rdN_frame fun j hj => fr3 _ (by omega) (by omega)
  have hS32 : C + 32 * (req + 1) + 32 * (S - req - 1) = C + 32 * S := by omega
  obtain ⟨ω4, μ4, r4, rep4, d7, d0, d5, d6, d1, ww4, fr4, hk4⟩ := alloc_end2Z (p := p) (P := P) (R := env.rel cap) x ω3 μ3 rr.1
    (fun a => H a ∨ (S - req - 1 ≠ 0 ∧ a = C + 32 * (req + 1)))
    (fun a => F a ∨ (S - req - 1 ≠ 0 ∧ a = C + 32 * (req + 1))) (sp - 152) (C + 32 * (req + 1)) (S - req - 1) rr.2
    (C + 32) req z ret tg rep3
    (fun a ha => by
      rw [e3b]
      rcases ha with (h | ⟨h0, rfl⟩) | (h | ⟨h0, rfl⟩)
      · exact hHF a (Or.inl h)
      · unfold Al; omega
      · exact hHF a (Or.inr h)
      · unfold Al; omega)
    (by rw [e3b]; exact hb0) (by rw [e3b]; exact hbT)
    (fun h => Or.inl (by rw [hS32]; exact hFin (by rw [e3b, hS32] at h; exact h)))
    (by rw [e3b, hS32]; exact hCend) (by omega) c1 c12 c8 c3 c2 c4 k120 hz k112 k144 hret hjt hbt
    (by rw [← ht3]; unfold register; split <;> simp <;> omega) hC8 (by omega) hreq (by omega)
    (fun a ha => by
      rcases ha with (h | ⟨h0, rfl⟩) | (h | ⟨h0, rfl⟩)
      · by_cases e : a = C
        · subst e; omega
        · have := hCdis a (Or.inl h) e; omega
      · omega
      · by_cases e : a = C
        · subst e; omega
        · have := hCdis a (Or.inr h) e; omega
      · omega)
    (by omega) (by omega) (by omega) ⟨by omega, by omega⟩
    (fun a ha => by
      rcases ha with (h' | ⟨h0, rfl⟩) | (h' | ⟨h0, rfl⟩)
      · exact hHFT2 a (Or.inl h')
      · have h'' := hE; rw [if_neg h0] at h''; omega
      · exact hHFT2 a (Or.inr h')
      · have h'' := hE; rw [if_neg h0] at h''; omega)
    (by have h'' := hE; split at h'' <;> omega)
    (hw2.of_eq ww3)
  have tr : ∀ a, sp - 152 + 128 ≤ a → a + 8 ≤ sp → rdN μ3 a 8 = rdN μ1 a 8 := fun a h h' =>
    rdN_frame fun j hj => (fr3 _ (by omega) (by omega)).trans (fr2 _ (by omega) (by omega) (by omega))
  refine ⟨ω4, μ4, (((r1.trans r2).trans r3).trans r4).mono (by omega), ?_, d7, ?_, ?_, ?_, ?_,
    HeapPages.of_eq hp2 (fun a => (ww4 a).trans (ww3 a)), fun a h1 h2 => by rw [ww4, ww3]; exact hst2 a h1 h2,
    fun a h h' => ((fr4 a h (by omega)).trans ((fr3 a h (by omega)).trans (fr2 a h (by omega) (by omega)))).trans
      (sf1 a h (Or.inr h')),
    fun a ha hd => (hk4 a ⟨ha.1, ha.2.1, fun b hb => ha.2.2 b (by
      rcases hb with (h | h) | (h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h)⟩ hd).trans ((((HKeepG.of_low fun a h1 h2 _ => sf1 a (by omega) (Or.inl (by omega))).trans
      (hk2.mono fun b hb => Or.inl (Or.inl hb))).trans hk3) a ha)⟩
  · rw [allocPost_eq (s := { s with allocated := E }) hcb (show s.base ≤ C by omega) hCa]
    dsimp only
    rw [hpvd, ht2, ht3]
    rw [e3b] at rep4
    exact rep4
  · rw [d0, h0]
  · rw [d5, tr _ (by omega) (by omega), show sp - 152 + 136 = sp - 16 by omega]
    unfold rdN; rw [st5, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]
  · rw [d6, tr _ (by omega) (by omega), show sp - 152 + 128 = sp - 24 by omega]
    unfold rdN; rw [st6, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]
  · rw [d1, h1]; congr 1; omega

end Services.Bootstrap.Alloc
