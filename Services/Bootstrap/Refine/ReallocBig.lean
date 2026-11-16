import Services.Bootstrap.Decode.ReallocCall

/-!
# `realloc` with a request beyond the heap

The binary's `realloc` (40701) for a request of 2^25 ≤ units < 2^31 − 1 (sizes below 2^36 octets): the heap holds 2^30
octets, so `realloc_impl` (42980) cannot grow the chunk in place (its next chunk lies past the heap's end, is used,
or with it the chunk holds fewer than req + 1 units) and falls back to `alloc_impl` (41177), which fails, and
`realloc` returns null with the allocator's context unchanged; the model's `realloc` is `none`. This extends
`Decode.ReallocCall.realloc_call`, whose bound `hr1` (units < 2^25 − 1) the Alloc chain needs for its success paths.
The proofs are `Alloc.fallback_pre`, `fallback_entryG` and `fallback_refines_failG` with req < 2^31 − 1 (all their
32-bit arithmetic needs) and the grow-heap branch impossible. GP v0.8.0 Appendix B.4 (Ψ_R running the service's code).
-/

namespace Services.Bootstrap.Refine.ReallocBig

open PVM Picoalloc Services.Bootstrap.Code JAM Services.Bootstrap.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **The model's `growInplace` fails for a request of at least 2^25 units**, and the request is above the usable
    size: the chunk and its next chunk lie inside the heap's 2^25 units. -/
theorem growInplace_none_big {grow : Grow} {s : State} {ptr req : Nat} (hwf : WF s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hbig : 33554432 ≤ req) :
    growInplace grow s ptr req = none ∧ usable s ptr < req := by
  obtain ⟨c, hcm, hca, hcu⟩ := hc
  obtain ⟨pre, post, hcs⟩ := List.append_of_mem hcm
  have hceq : c = ⟨ptr - 32, c.size, true⟩ := by
    cases c; simp only at hca hcu ⊢; subst hcu; simp only [Chunk.mk.injEq, and_true]; omega
  rw [hceq] at hcs
  generalize hn0 : c.size = cur at hcs
  have hXmem : (⟨ptr - 32, cur, true⟩ : Chunk) ∈ chunks s := by
    rw [hcs]; exact List.mem_append_right _ List.mem_cons_self
  have hXs : (s.hdr (ptr - 32)).size = sizeWord cur true := by
    have := chunks_hdr _ hXmem; simp only at this; exact this
  have hcur : wordSize (s.hdr (ptr - 32)).size = cur := by rw [hXs, wordSize_sizeWord]
  have husable : usable s ptr = cur - 1 := by unfold usable; rw [hcur]
  obtain ⟨-, -, -, htiles, -, -, -, -⟩ := hwf
  unfold TilesOk at htiles
  have henc := @chunks_hdr s
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  rw [hcs] at htiles henc
  rw [htop] at htiles
  have hXm : (⟨ptr - 32, cur, true⟩ : Chunk) ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: post :=
    List.mem_append_right _ List.mem_cons_self
  have hXl := htiles.mem_lt _ hXm
  simp only at hXl
  obtain ⟨-, hph, -, -⟩ := Tiles.around htiles
  have hnx : ptr - 32 + 32 * cur < s.base + 1073741824 →
      ∃ e ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: post, e.addr = ptr - 32 + 32 * cur := by
    intro hlt'
    cases hpo : post with
    | nil =>
      rw [hpo] at htiles
      obtain ⟨m, -, hm1, -, hm3⟩ := Tiles.append.mp htiles
      simp only [Tiles] at hm1 hm3; omega
    | cons e es =>
      exact ⟨e, List.mem_append_right _ (List.mem_cons_of_mem _ (by simp)), hph e (by rw [hpo]; rfl)⟩
  refine ⟨growInplace_none_of hcur (by omega) ?_, by omega⟩
  by_cases hin : s.base + 1073741824 ≤ ptr - 32 + 32 * cur
  · exact Or.inl hin
  · refine Or.inr (Or.inr ?_)
    obtain ⟨e, hem, hea⟩ := hnx (by omega)
    have hes := henc e hem
    rw [hea] at hes
    have hel := htiles.mem_lt e hem
    have hws : wordSize (s.hdr (ptr - 32 + 32 * cur)).size = e.size := by rw [hes, wordSize_sizeWord]
    rw [hws]
    omega

/-- **The model's `alloc` fails for a request of at least 2^25 units**: its minimum size exceeds `maxSize`. -/
theorem alloc_none_big {grow : Grow} {hb req : Nat} {s : State} (hbig : 33554432 ≤ req) :
    alloc grow hb 1 req s = none := by
  unfold alloc
  have h1 : ¬ (req + 1 + (1 - 1) ≤ maxSize) := by rw [maxSize_val]; omega
  cases h : init grow hb s with
  | none => simp
  | some s' => simp; omega

/-- **42980 … 43259**: a request of req units above the chunk X's `cur − 1` usable units, its next
    chunk past the heap's end, used, or too small: at the fallback with the frame at sp − 152,
    ω₆ = cur − 1, ω₇ the allocator, ω₈ = ptr, ω₁₀ = req, ω₉ kept; the caller's ω₀, ω₅, ω₆ saved;
    the memory changed only in the frame. -/
theorem fallback_preB {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (H F : Nat → Prop) (sp ptr req cur : Nat) (hrep : RepAt μ s H F)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr) (h7 : ω[7] = UInt64.ofNat 196792)
    (h10 : ω[10] = UInt64.ofNat req)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648)
    (hX : Al s.base (ptr - 32)) (hptr : 32 ≤ ptr) (hXH : H (ptr - 32)) (hHF : ∀ a, H a ∨ F a → Al s.base a)
    (hsz : (s.hdr (ptr - 32)).size = 2 * cur + 1) (hlt : cur < req + 1) (hr : req < 2147483647) (hc1 : 1 ≤ cur)
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

theorem fallback_entryB {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X) (x : X)
    (ω : Regs) (μ : Memory) (s : State) (sp ptr req pb ph : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr : usable s ptr < req) (hr1 : req < 2147483647) (hbig : 33554432 ≤ req)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (hnone : growInplace (growTo pb) s ptr req = none)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr) (h7 : ω[7] = UInt64.ofNat 196792)
    (h10 : ω[10] = UInt64.ofNat req)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    {S0 S1 : Nat} (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 152 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (env.rel hostCostMax) 42980 ω μ x 43259 ω' μ' x 120 ∧ Rep μ' s ∧
      HeapPages μ' 48 pb ph ∧ (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → (a < sp - 152 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      μ'.readN (sp - 8) 8 = Num.encodeLE 8 ω[0].toNat ∧ μ'.readN (sp - 16) 8 = Num.encodeLE 8 ω[5].toNat ∧
      μ'.readN (sp - 24) 8 = Num.encodeLE 8 ω[6].toNat ∧
      ω'[1] = UInt64.ofNat (sp - 152) ∧ ω'[6] = UInt64.ofNat (usable s ptr) ∧ ω'[7] = UInt64.ofNat 196792 ∧
      ω'[8] = UInt64.ofNat ptr ∧ ω'[9] = ω[9] ∧ ω'[10] = UInt64.ofNat req := by
  have hw := HeapPages.wrAt hp hhb hst
  have hc' := hc
  obtain ⟨c, hcm, hca, hcu⟩ := hc'
  obtain ⟨pre, post, hcs⟩ := List.append_of_mem hcm
  have hceq : c = ⟨ptr - 32, c.size, true⟩ := by
    cases c; simp only at hca hcu ⊢; subst hcu; simp only [Chunk.mk.injEq, and_true]; omega
  rw [hceq] at hcs
  generalize hn0 : c.size = cur at hcs
  have hXmem : (⟨ptr - 32, cur, true⟩ : Chunk) ∈ chunks s := by
    rw [hcs]; exact List.mem_append_right _ List.mem_cons_self
  have hXs : (s.hdr (ptr - 32)).size = sizeWord cur true := by
    have := chunks_hdr _ hXmem; simp only at this; exact this
  have hcur : wordSize (s.hdr (ptr - 32)).size = cur := by rw [hXs, wordSize_sizeWord]
  have husable : usable s ptr = cur - 1 := by unfold usable; rw [hcur]
  have hwf' := hwf
  obtain ⟨-, -, -, htiles, -, -, -, hspace⟩ := hwf'
  unfold TilesOk at htiles
  have henc := @chunks_hdr s
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  rw [hcs] at htiles henc
  rw [htop] at htiles
  -- the header addresses
  generalize hH : HA (pre ++ ⟨ptr - 32, cur, true⟩ :: post) = H
  generalize hF : FA (pre ++ ⟨ptr - 32, cur, true⟩ :: post) = F
  have mkH : ∀ c ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: post, H c.addr := fun c hc => hH ▸ ⟨c, hc, rfl⟩
  have unH : ∀ a, H a → ∃ c ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: post, c.addr = a := fun a h => by
    rw [← hH] at h; exact h
  have unF : ∀ a, F a → ∃ c ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: post, c.addr = a ∧ c.used = false := fun a h => by
    rw [← hF] at h; exact h
  have unHF : ∀ a, H a ∨ F a → ∃ c ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: post, c.addr = a := by
    rintro a (h | h)
    · exact unH a h
    · obtain ⟨c, hc, h1, -⟩ := unF a h; exact ⟨c, hc, h1⟩
  have hHF : ∀ a, H a ∨ F a → Al s.base a := by
    intro a h
    obtain ⟨c, hc, rfl⟩ := unHF a h
    have := htiles.aligned c hc; have := htiles.mem_lt c hc; unfold Al; omega
  have hcs' : chunks s = pre ++ ⟨ptr - 32, cur, true⟩ :: post := hcs
  have hHFT : ∀ a, H a ∨ F a → a + 32 ≤ 4096 * ph := by
    intro a ha
    obtain ⟨c, hc, rfl⟩ := unHF a ha
    unfold SpaceOk at hspace; have := (hspace c (hcs' ▸ hc)).2; omega
  have hrep' : RepAt μ s H F :=
    ⟨hrep.heads, hrep.sec, hrep.pri, hrep.base, hrep.alloc,
      fun a h => by obtain ⟨c, hc, rfl⟩ := unH a h; exact hrep.prev c (hcs' ▸ hc),
      fun a h => by obtain ⟨c, hc, rfl⟩ := unH a h; exact hrep.size c (hcs' ▸ hc),
      fun a h => by obtain ⟨c, hc, rfl, hu⟩ := unF a h; exact hrep.next c (hcs' ▸ hc) hu,
      fun a h => by obtain ⟨c, hc, rfl, hu⟩ := unF a h; exact hrep.prevL c (hcs' ▸ hc) hu⟩
  have hXm : (⟨ptr - 32, cur, true⟩ : Chunk) ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: post :=
    List.mem_append_right _ List.mem_cons_self
  have hXl := htiles.mem_lt _ hXm
  simp only at hXl
  have hc1 : 1 ≤ cur := by omega
  have hlt : cur < req + 1 := by omega
  obtain ⟨-, hph, -, -⟩ := Tiles.around htiles
  -- the next chunk, when below the heap's end, is a chunk
  have hnx : ptr - 32 + 32 * cur < s.base + 1073741824 →
      ∃ e ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: post, e.addr = ptr - 32 + 32 * cur := by
    intro hlt'
    cases hpo : post with
    | nil =>
      rw [hpo] at htiles
      obtain ⟨m, -, hm1, -, hm3⟩ := Tiles.append.mp htiles
      simp only [Tiles] at hm1 hm3; omega
    | cons e es =>
      exact ⟨e, List.mem_append_right _ (List.mem_cons_of_mem _ (by simp)), hph e (by rw [hpo]; rfl)⟩
  have hnc : ptr - 32 + 32 * cur < s.base + 1073741824 → H (ptr - 32 + 32 * cur) := fun hlt' => by
    obtain ⟨e, hem, hea⟩ := hnx hlt'; rw [← hea]; exact mkH e hem
  rcases growInplace_none_cases hcur hlt hnone with hcase | ⟨hin, hfree, hav, hgr, hno⟩
  · -- the next chunk past the end, used, or too small
    have hcase' : s.base + 1073741824 ≤ ptr - 32 + 32 * cur ∨
        (ptr - 32 + 32 * cur < s.base + 1073741824 ∧ H (ptr - 32 + 32 * cur) ∧
          (s.hdr (ptr - 32 + 32 * cur)).size % 2 = 1) ∨
        (ptr - 32 + 32 * cur < s.base + 1073741824 ∧ H (ptr - 32 + 32 * cur) ∧
          (s.hdr (ptr - 32 + 32 * cur)).size % 2 = 0 ∧ cur + (s.hdr (ptr - 32 + 32 * cur)).size / 2 < req + 1) := by
      by_cases hin : s.base + 1073741824 ≤ ptr - 32 + 32 * cur
      · exact Or.inl hin
      · have hH' := hnc (by omega)
        by_cases hodd : (s.hdr (ptr - 32 + 32 * cur)).size % 2 = 1
        · exact Or.inr (Or.inl ⟨by omega, hH', hodd⟩)
        · refine Or.inr (Or.inr ⟨by omega, hH', by omega, ?_⟩)
          rcases hcase with h | h | h
          · omega
          · exfalso; unfold wordUsed at h; simp at h; omega
          · unfold wordSize at h; exact h
    obtain ⟨ω1, μ1, r1, -, ww1, fr1, st0, st5, st6, a1, a6, a7, a8, a9, a10⟩ := fallback_preB (p := p) (P := P)
      (R := env.rel hostCostMax) x ω μ s H F sp ptr req cur hrep' h1 h8 h7 h10 hsp hsp1 hb0 hbT
      (hHF _ (Or.inl (mkH _ hXm))) (by omega) (mkH _ hXm) hHF (by rw [hXs]; unfold sizeWord; simp) hlt hr1 hc1
      (by omega) hcase' hHFT hS hw
    exact ⟨ω1, μ1, r1.mono (by omega),
      hrep.congr_lock hwf hb0 hbT (fun a ha1 ha2 ha3 => fr1 a (by omega) (Or.inl (by omega))),
      HeapPages.of_eq hp ww1, fun a h1 h2 => by rw [ww1]; exact hst a h1 h2, fr1, st0, st5, st6, a1,
      by rw [a6, husable], a7, a8, a9, a10⟩
  · -- the next chunk free and large enough: impossible, the two chunks would hold more than the heap
    exfalso
    obtain ⟨e, hem, hea⟩ := hnx hin
    have hes := henc e hem
    rw [hea] at hes
    have hel := htiles.mem_lt e hem
    have hw0 : (s.hdr (ptr - 32 + 32 * cur)).size % 2 = 0 := by
      unfold wordUsed at hfree; simp only [beq_eq_false_iff_ne, ne_eq] at hfree; omega
    have hw2 : (s.hdr (ptr - 32 + 32 * cur)).size = 2 * e.size := by
      rw [hes] at hw0 ⊢; unfold sizeWord at hw0 ⊢
      cases hu : e.used
      · simp
      · simp [hu] at hw0
    have hws : wordSize (s.hdr (ptr - 32 + 32 * cur)).size = e.size := by rw [hw2]; unfold wordSize; omega
    rw [hws] at hav
    have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
    omega

theorem fallback_refines_failB {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X)
    (x : X) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (sp ptr req pb ph : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr : usable s ptr < req) (hr1 : req < 2147483647) (hbig : 33554432 ≤ req)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (hnone : growInplace (growTo pb) s ptr req = none) (ha : alloc (growTo pb) hb 1 req s = none)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr) (h7 : ω[7] = UInt64.ofNat 196792)
    (h9 : ω[9] = UInt64.ofNat 1) (h10 : ω[10] = UInt64.ofNat req) (h0 : ω[0] = UInt64.ofNat 1988)
    (hsp : 2147483952 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 304 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    realloc (growTo pb) hb s ptr 1 req = none ∧
      ∃ ω' μ', FreeStepsH p (env.rel hostCostMax) 42980 ω μ x 40805 ω' μ' x 640 ∧ Rep μ' s ∧
        HeapPages μ' 48 pb ph ∧ (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
        (∀ a, a < 4294967296 → (a < sp - 304 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
        ω'[7] = UInt64.ofNat 0 ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat sp ∧
        ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  refine ⟨realloc_fallback_none hr hnone ha, ?_⟩
  have hp32 : ptr < 4294967296 := by
    obtain ⟨c, hcm, hca, -⟩ := hc
    have ht := hwf.2.2.2.1
    unfold TilesOk at ht
    have := ht.mem_lt c hcm
    have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
    omega
  obtain ⟨ω1, μ1, r1, rep1, hp1, hst1, fr1, st0, st5, st6, a1, -, a7, a8, a9, a10⟩ := fallback_entryB
    (p := p) (P := P) env x ω μ s sp ptr req pb ph hwf hrep hc hr hr1 hbig hbd h48 hhb hbs hnone h1 h8 h7 h10
    (by omega) hsp1 hb0 hbT hA hHT ⟨by omega, by omega⟩ hSb hp hst
  have rd : ∀ a v, μ1.readN a 8 = Num.encodeLE 8 v → v < 18446744073709551616 → rdN μ1 a 8 = v :=
    fun a v h hv => rd_enc h hv
  obtain ⟨ω2, μ2, r2, rep2, hp2, hst2, fr2, e7, e0, e1, e5, e6⟩ := fallback_tail_failG (p := p) (P := P) env x
    ω1 μ1 (hb := hb) s (sp - 152) ptr req ω[5].toNat ω[6].toNat pb ph hwf rep1 hbd h48 hhb hbs ha (by omega)
    a1 a7 a8 (by rw [a9]; exact h9) a10 hp32
    (by rw [show sp - 152 + 144 = sp - 8 by omega]; exact (rd _ _ st0 (UInt64.toNat_lt _)).trans (by rw [h0]; rfl))
    (by rw [show sp - 152 + 136 = sp - 16 by omega]; exact rd _ _ st5 (UInt64.toNat_lt _))
    (by rw [show sp - 152 + 128 = sp - 24 by omega]; exact rd _ _ st6 (UInt64.toNat_lt _))
    (by omega) (by omega) hb0 hbT hA hHTs hHT ⟨by omega, by omega⟩ hSb hp1 hst1
  exact ⟨ω2, μ2, (r1.trans r2).mono (by omega), rep2, hp2, hst2,
    fun a h1 h2 => (fr2 a h1 (by omega) (by omega)).trans (fr1 a h1 (by omega)), e7, e0,
    by rw [e1]; congr 1; omega, by rw [e5, UInt64.ofNat_toNat], by rw [e6, UInt64.ofNat_toNat]⟩

open Services.Bootstrap.Decode.HeapCtx in
/-- **`realloc` with a request of 2^25 ≤ units < 2^31 − 1** (sizes below 2^36 − 32 octets), the outcome
    `Decode.ReallocCall.realloc_callG` leaves out: the model's `realloc` is `none`, and the binary's `realloc` (40701)
    returns null at 40821 with the allocator's context for the same state, the stack from sp up and the globals
    kept, and ω₀, ω₁, ω₅, ω₆ restored. -/
theorem realloc_call_bigG {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : X) (ω : Regs) (μ : Memory)
    {hb : Nat} (s : State) (sp ptr al size pb S0 S1 : Nat) (H : HeapCtxC env.code pb S0 S1 μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hbig : 33554432 ≤ (size + 31) / 32) (hs : size + 31 < 68719476704) (hba : s.base % 8 = 0)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hal1 : 1 ≤ al) (hal2 : al ≤ 32)
    (hsp : 2147483968 ≤ sp ∧ sp % 8 = 0) (hS : S0 + 320 ≤ sp ∧ sp ≤ S1) :
    realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = none ∧ ∃ ω' μ',
      FreeStepsH p (env.rel cap) 40701 ω μ x 40821 ω' μ' x 685 ∧
      ω'[7] = UInt64.ofNat 0 ∧ HeapCtxC env.code pb S0 S1 μ' s ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      (∀ a, Glob a → μ'.read a = μ.read a) := by
  obtain ⟨ph, h48, hhb, hp, hHTs, hHT⟩ := H.pages
  have hS1 := H.hS1
  have hSb := H.hSb
  have hb0 := H.hb0
  have hbT := H.hbT
  have hal : (al + 31) / 32 = 1 := by omega
  rw [hal]
  obtain ⟨hnone, hr⟩ := growInplace_none_big (grow := growTo pb) H.wf hc hbig
  have ha : alloc (growTo pb) hb 1 ((size + 31) / 32) s = none := alloc_none_big hbig
  have hc' := hc
  obtain ⟨c, hcm, hca, -⟩ := hc'
  have ht := H.wf.2.2.2.1
  unfold TilesOk at ht
  have hcl := ht.mem_lt c hcm
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hwr := HeapPages.wrAt hp hhb H.st
  obtain ⟨ω1, μ1, r1, a1, a8, a7, a9, a10, a0, a5, -, st8, st16, fr1, ww1, g1⟩ :=
    rw_lock (p := p) (P := P) (R := env.rel cap) x ω μ sp ptr al size h1 h7 h9 h10 (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) H.lock (by omega) ⟨by omega, by omega⟩ hwr
  have rep1 : Rep μ1 s := H.rep.congr_lock H.wf hb0 hbT fun a ha1 ha2 ha3 =>
    fr1 a (by omega) (Or.inl (by omega)) (Or.inr (by unfold A0 at ha1; omega)) ha3
  have hp1 := HeapPages.of_eq hp ww1
  have hst1 : ∀ a, S0 ≤ a → a < S1 → μ1.writable a = true := fun a h1 h2 => by rw [ww1]; exact H.st a h1 h2
  obtain ⟨-, ω2, μ2, r2, rep2, hp2, hst2, fr2, e7, e0, e1, e5, e6⟩ := fallback_refines_failB (p := p) (P := P)
    env x ω1 μ1 (hb := hb) s (sp - 16) ptr ((size + 31) / 32) pb ph H.wf rep1 hc hr (by omega) hbig H.bd h48 hhb
    (by omega) hnone ha a1 a8 a7 (by rw [a9, hal]) a10 a0 (by omega) (by omega) hb0 hbT H.hA hHTs hHT
    ⟨by omega, by omega⟩ hSb hp1 hst1
  obtain ⟨ω3, μ3, r3, c0, c5, c1, cl, fr3, ww3, g3⟩ :=
    rw_unlock (p := p) (P := P) (R := env.rel cap) x ω2 μ2 (sp - 16) e1 (by rw [e5, a5]) (by omega)
      (by omega) (by omega) ⟨by omega, by omega⟩ (HeapPages.wrAt hp2 hhb hst2)
  have run := (r1.trans ((Decode.ReallocCall.liftG (p := p) (env := env) (cap := cap) (by omega) hcap r2).trans
    r3)).mono (show 40 + 640 + 5 ≤ 685 by omega)
  obtain ⟨kp', kr⟩ := HeapHost.keepRO H.bd run
  have ro' : ∀ a, a < 196608 → μ3.writable a = false := fun a ha => by
    have := H.ro a ha
    unfold Memory.writable at this ⊢
    rw [kp' _ (Or.inl (by unfold pageSize; omega))]; exact this
  refine ⟨realloc_fallback_none hr hnone ha, ω3, μ3, run, by rw [fget g3 7 (by decide) (by decide)]; exact e7,
    ⟨H.wf, rep2.congr_lock H.wf hb0 hbT (fun a ha1 ha2 ha3 => fr3 a (by omega) (by omega)), H.fo, cl, hb0, hbT,
      H.hA, H.bd, ⟨ph, h48, hhb, HeapPages.of_eq hp2 ww3, hHTs, hHT⟩, hSb, hS1,
      fun a h1 h2 => by rw [ww3]; exact hst2 a h1 h2, ro'⟩,
    fun a ha1 ha2 => ((fr3 a ha1 (by omega)).trans (fr2 a ha1 (by omega))).trans
      (fr1 a ha1 (Or.inr ha2) (Or.inr (by omega)) (Or.inr (by omega))), ?_, ?_, ?_, ?_, ?_⟩
  · rw [c0, rdN_frame (μ := μ1) fun j hj => fr2 _ (by omega) (by omega), show sp - 16 + 8 = sp - 8 by omega]
    exact rd_restore st8
  · rw [c1, h1]; congr 1; omega
  · rw [c5, rdN_frame (μ := μ1) fun j hj => fr2 _ (by omega) (by omega)]
    exact rd_restore st16
  · rw [fget g3 6 (by decide) (by decide), e6, fget g1 6 (by decide) (by decide)]
  · intro a ha
    have hg := ha; unfold Glob at hg
    rw [fr3 a (by omega) (by omega), fr2 a (by omega) (by omega)]
    exact fr1 a (by omega) (Or.inl (by omega)) (Or.inr (by omega)) (Or.inl (by omega))

open Services.Bootstrap.Decode.HeapCtx in
/-- `realloc_call_bigG` for the refine host (`refineHeap env`, refine's contract with cap `cap`). -/
theorem realloc_call_big {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs) (μ : Memory)
    {hb : Nat} (s : State) (sp ptr al size pb S0 S1 : Nat) (H : HeapCtx env pb S0 S1 μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hbig : 33554432 ≤ (size + 31) / 32) (hs : size + 31 < 68719476704) (hba : s.base % 8 = 0)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hal1 : 1 ≤ al) (hal2 : al ≤ 32)
    (hsp : 2147483968 ≤ sp ∧ sp % 8 = 0) (hS : S0 + 320 ≤ sp ∧ sp ≤ S1) :
    realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = none ∧ ∃ ω' μ',
      FreeStepsH p (refineContractK cap env) 40701 ω μ x 40821 ω' μ' x 685 ∧
      ω'[7] = UInt64.ofNat 0 ∧ HeapCtx env pb S0 S1 μ' s ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      (∀ a, Glob a → μ'.read a = μ.read a) :=
  realloc_call_bigG (p := p) (P := P) (refineHeap env) cap hcap1 hcap x ω μ (hb := hb) s sp ptr al size pb S0 S1 H
    hc hbig hs hba h1 h7 h9 h10 hal1 hal2 hsp hS

end Services.Bootstrap.Refine.ReallocBig
