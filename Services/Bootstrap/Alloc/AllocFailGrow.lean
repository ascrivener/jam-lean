import Services.Bootstrap.Alloc.AllocFailSteps
import Services.Bootstrap.Alloc.AllocGrow

/-!
# The binary's `alloc_impl` failing to grow the heap

The fourth failure: the found chunk is large enough, but the allocation ends past the allocated
space and the host cannot grow the heap to cover it (`grow_heap`, Ω_♊, GP Appendix B, returns the
heap's top unchanged when the requested page lies past the heap's bound). The offsets
(41425 … 41514), the growth's attempt (41517 … 41401, `ag_grow_fail`), and the failure tail.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code JAM

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **41425 … 41401, the heap cannot grow**: the chosen chunk's offsets, the allocation's end E past
    the allocated space A, and the host refusing to grow the heap to cover E (its bound `pb` pages
    below the pages E needs): to the failure, the heap's pages as they were, only the frame
    (sp … sp + 112) written.
    Under `refineContractK cap`, for any cap covering the call's 275. -/
theorem alloc_mid_failK {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (cap : Nat) (hcap : cap < 18446744073709551616) (h275 : 275 ≤ cap) (x : RefineCtx)
    (ω : Regs) (μ : Memory) (sp req C sz base A pb h : Nat)
    (h1 : ω[1] = UInt64.ofNat sp) (h10 : ω[10] = UInt64.ofNat C) (h11 : ω[11] = UInt64.ofNat sz)
    (h8 : ω[8] = UInt64.ofNat 1) (h9 : ω[9] = UInt64.ofNat req)
    (h120 : rdN μ (sp + 120) 8 = 204984) (hbase : rdN μ 206520 8 = base) (halloc : rdN μ 206840 4 = A)
    (hA : A < 2147483648) (hbC : base ≤ C) (hbT : base + 1073741824 < 2147483648)
    (hrq : req + 1 ≤ sz) (hCend : C + 32 * sz ≤ base + 1073741824)
    (hgr : A < (C - base) / 32 + 1 + req + (if sz - req - 1 = 0 then 0 else 1))
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ h) (hhb : h ≤ pb) (hbs : pb < 4294967296)
    (hR : pb < pagesOf (base + 32 * ((C - base) / 32 + 1 + req + (if sz - req - 1 = 0 then 0 else 1))))
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * h)
    (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb h)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (refineContractK cap env) 41425 ω μ x 41401 ω' μ' x 70 ∧ ω'[1] = UInt64.ofNat sp ∧
      HeapPages μ' 48 pb h ∧ (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → (a < sp ∨ sp + 112 ≤ a) → μ'.read a = μ.read a) := by
  have hw := HeapPages.wrAt hp hhb hst
  obtain ⟨ω1, μ1, r1, a2, a5, a6, a12, -, -, -, -, fr1, ww1, g1⟩ := al_offs1 (p := p) (P := P)
    (R := refineContractK cap env) x ω μ sp C base A h1 h10 h8 h120 hbase halloc hA hbC (by omega) hsp0 hsp hHTs hSTk hw
  obtain ⟨ω2, μ2, r2, b6, b8, b12, s96, fr2, ww2, g2⟩ := al_offs2 (p := p) (P := P) (R := refineContractK cap env)
    x ω1 μ1 sp (C - base) base (by rw [fget g1 1 (by decide) (by decide)]; exact h1) a12 a6 a5
    (by omega) (by omega) hsp0 hsp hHTs hSTk (hw.of_eq ww1)
  generalize hc : (C - base) / 32 = c at *
  obtain ⟨ω3, μ3, r3, -, -, -, -, -, c5, -, -, -, -, fr3, ww3, g3⟩ := al_offs3 (p := p) (P := P)
    (R := refineContractK cap env) x ω2 μ2 sp (base / 32) c req sz A C
    (by rw [fget g2 1 (by decide) (by decide), fget g1 1 (by decide) (by decide)]; exact h1) b6 b8 b12
    (by rw [fget g2 9 (by decide) (by decide), fget g1 9 (by decide) (by decide)]; exact h9)
    (by rw [fget g2 11 (by decide) (by decide), fget g1 11 (by decide) (by decide)]; exact h11)
    (by rw [fget g2 2 (by decide) (by decide)]; exact a2)
    (by rw [fget g2 10 (by decide) (by decide), fget g1 10 (by decide) (by decide)]; exact h10)
    (by omega) hrq (by omega) (by omega) (by omega) hA (by omega) hsp0 hsp hHTs hSTk ((hw.of_eq ww1).of_eq ww2)
  generalize hEd : c + 1 + req + (if sz - req - 1 = 0 then 0 else 1) = E at *
  have hE2 : E ≤ 33554432 := by rw [← hEd]; split <;> omega
  have r4 := al_grow (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 A E
    (by rw [fget g3 2 (by decide) (by decide), fget g2 2 (by decide) (by decide)]; exact a2) c5 hgr (by omega)
  have h96 : rdN μ3 (sp + 96) 8 = base := by
    rw [show rdN μ3 (sp + 96) 8 = rdN μ2 (sp + 96) 8 from rdN_frame fun j hj => fr3 _ (by omega) (by omega)
      (by omega) (by omega)]
    exact rd_enc s96 (by omega)
  have c1 : ω3[1] = UInt64.ofNat sp := by
    rw [fget g3 1 (by decide) (by decide), fget g2 1 (by decide) (by decide), fget g1 1 (by decide) (by decide)]
    exact h1
  obtain ⟨ω4, μ4, r5, e1, fr4, hp4, hst4⟩ := ag_grow_failK (p := p) (P := P) env cap hcap h275 x ω3 μ3 sp E base pb h hbd h48
    hhb hbs hR c1 c5 h96 hE2 (by omega) hsp0 hsp hSTk hSb
    (HeapPages.of_eq hp fun a => (ww3 a).trans ((ww2 a).trans (ww1 a)))
    (fun a h1 h2 => by rw [ww3, ww2, ww1]; exact hst a h1 h2)
  refine ⟨ω4, μ4, ((((r1.trans r2).trans r3).trans r4).trans r5).mono (by omega), by rw [e1]; exact c1, hp4, hst4,
    fun a ha h' => ?_⟩
  rw [fr4 a ha (by omega) (by omega), fr3 a ha (by omega) (by omega) (by omega), fr2 a ha (by omega),
    fr1 a ha (by omega)]

/-- `alloc_mid_failK` at `hostCostMax`, the cap of `refineContract`. -/
theorem alloc_mid_fail {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (x : RefineCtx)
    (ω : Regs) (μ : Memory) (sp req C sz base A pb h : Nat)
    (h1 : ω[1] = UInt64.ofNat sp) (h10 : ω[10] = UInt64.ofNat C) (h11 : ω[11] = UInt64.ofNat sz)
    (h8 : ω[8] = UInt64.ofNat 1) (h9 : ω[9] = UInt64.ofNat req)
    (h120 : rdN μ (sp + 120) 8 = 204984) (hbase : rdN μ 206520 8 = base) (halloc : rdN μ 206840 4 = A)
    (hA : A < 2147483648) (hbC : base ≤ C) (hbT : base + 1073741824 < 2147483648)
    (hrq : req + 1 ≤ sz) (hCend : C + 32 * sz ≤ base + 1073741824)
    (hgr : A < (C - base) / 32 + 1 + req + (if sz - req - 1 = 0 then 0 else 1))
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ h) (hhb : h ≤ pb) (hbs : pb < 4294967296)
    (hR : pb < pagesOf (base + 32 * ((C - base) / 32 + 1 + req + (if sz - req - 1 = 0 then 0 else 1))))
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * h)
    (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb h)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (refineContract env) 41425 ω μ x 41401 ω' μ' x 70 ∧ ω'[1] = UInt64.ofNat sp ∧
      HeapPages μ' 48 pb h ∧ (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → (a < sp ∨ sp + 112 ≤ a) → μ'.read a = μ.read a) :=
  alloc_mid_failK (p := p) (P := P) (S0 := S0) (S1 := S1) env hostCostMax (by decide) (by decide) x
    ω μ sp req C sz base A pb h h1 h10 h11 h8 h9 h120 hbase halloc hA hbC hbT hrq hCend hgr hbd h48
    hhb hbs hR hsp0 hsp hHTs hSTk hSb hp hst

/-- **41177 … 41423, the heap cannot grow**: the found bin's first chunk C (size word `w`) is large
    enough, but the allocation's end E lies past the allocated space and the heap's bound `pb`
    (in pages) is below the pages E needs; the host leaves the heap as it was and null is
    returned, only the frame written.
    Under `refineContractK cap`, for any cap covering the call's 275. -/
theorem alloc_fail_growK {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (cap : Nat) (hcap : cap < 18446744073709551616) (h275 : 275 ≤ cap) (x : RefineCtx)
    (ω : Regs) (μ : Memory) (s : State) (sp req bin C w pb h : Nat) (hbits : BitsOk s.secondary s.primary s.heads)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat 1)
    (h9 : ω[9] = UInt64.ofNat req) (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb : rdN μ 206520 8 = s.base) (hb0 : s.base ≠ 0)
    (hp : rdN μ 206832 8 = s.primary) (hs : ∀ q, q < 38 → rdN μ (q * 8 + 204984 + 1544) 8 = s.secondary q)
    (ha : rdN μ 206840 4 = s.allocated) (hal : s.allocated < 2147483648)
    (hm : req + 1 ≤ 33554432)
    (hbin : (findFirst s (binUp (req + 1))).or (findFirst s (binDown (req + 1))) = some bin)
    (hC : rdN μ (196792 + 4 * bin) 4 = C) (hw : rdN μ (C + 4) 4 = w) (hbT : s.base + 1073741824 < 2147483648)
    (hbC : s.base ≤ C) (hS : req + 1 ≤ w / 2) (hCend : C + 32 * (w / 2) ≤ s.base + 1073741824)
    (hgr : s.allocated < (C - s.base) / 32 + 1 + req + (if w / 2 - req - 1 = 0 then 0 else 1))
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ h) (hhb : h ≤ pb) (hbs : pb < 4294967296)
    (hR : pb < pagesOf (s.base + 32 * ((C - s.base) / 32 + 1 + req + (if w / 2 - req - 1 = 0 then 0 else 1))))
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * h) (hSTk : S0 + 152 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0)
    (hCT : 196608 ≤ C ∧ C + 16 ≤ 4096 * h) (hpg : HeapPages μ 48 pb h)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (refineContractK cap env) 41177 ω μ x 41423 ω' μ' x 200 ∧ ω'[7] = UInt64.ofNat 0 ∧
      ω'[0] = ω[0] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[1] = ω[1] ∧
      HeapPages μ' 48 pb h ∧ (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → (a < sp - 152 ∨ sp ≤ a) → μ'.read a = μ.read a) := by
  have hwr := HeapPages.wrAt hpg hhb hst
  obtain ⟨ω1, μ1, r1, -, -, -, -, -, a1, a10, a11, -, -, -, -, a8, a9, -, -, -, st0, st5, st6, -, st32, sf1, ww1⟩ :=
    alloc_entry (p := p) (P := P) (R := refineContractK cap env) x ω μ s sp req bin C w hbits h1 h7 h8 h9 hsp hsp1 hb hb0
      hp hs hm hbin hC hw (by omega) hS hHTs hSTk hCT hwr
  have tr : ∀ a n, a + n ≤ 2147483648 → rdN μ1 a n = rdN μ a n := fun a n h =>
    rdN_frame fun j hj => sf1 _ (by omega) (Or.inl (by omega))
  obtain ⟨ω2, μ2, r2, b1, hp2, hst2, fr2⟩ := alloc_mid_failK (p := p) (P := P) (S0 := S0) (S1 := S1) env cap hcap h275 x ω1 μ1
    (sp - 152) req C (w / 2) s.base s.allocated pb h a1 a10 a11 a8 a9
    (by rw [show sp - 152 + 120 = sp - 32 by omega]; exact st32) (by rw [tr _ _ (by omega)]; exact hb)
    (by rw [tr _ _ (by omega)]; exact ha) hal hbC hbT hS hCend hgr hbd h48 hhb hbs hR (by omega) (by omega) hHTs
    ⟨by omega, by omega⟩ hSb (HeapPages.of_eq hpg ww1) (fun a h1 h2 => by rw [ww1]; exact hst a h1 h2)
  obtain ⟨ω3, r3, d7, d0, d5, d6, d1, -⟩ := al_fail (p := p) (P := P) (R := refineContractK cap env) x ω2 μ2 (sp - 152)
    b1 (by omega) hHTs ⟨by omega, by omega⟩ (HeapPages.wrAt hp2 hhb hst2).rd
  have t2 : ∀ a, sp - 152 + 112 ≤ a → a + 8 ≤ sp → rdN μ2 a 8 = rdN μ1 a 8 := fun a h h' =>
    rdN_frame fun j hj => fr2 _ (by omega) (by omega)
  refine ⟨ω3, μ2, ((r1.trans r2).trans r3).mono (by omega), d7, ?_, ?_, ?_, ?_, hp2, hst2,
    fun a ha h' => (fr2 a ha (by omega)).trans (sf1 a ha h')⟩
  · rw [d0, t2 _ (by omega) (by omega), show sp - 152 + 144 = sp - 8 by omega]; exact rd_restore st0
  · rw [d5, t2 _ (by omega) (by omega), show sp - 152 + 136 = sp - 16 by omega]; exact rd_restore st5
  · rw [d6, t2 _ (by omega) (by omega), show sp - 152 + 128 = sp - 24 by omega]; exact rd_restore st6
  · rw [d1, h1]; congr 1; omega

/-- `alloc_fail_growK` at `hostCostMax`, the cap of `refineContract`. -/
theorem alloc_fail_grow {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (x : RefineCtx)
    (ω : Regs) (μ : Memory) (s : State) (sp req bin C w pb h : Nat) (hbits : BitsOk s.secondary s.primary s.heads)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat 1)
    (h9 : ω[9] = UInt64.ofNat req) (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb : rdN μ 206520 8 = s.base) (hb0 : s.base ≠ 0)
    (hp : rdN μ 206832 8 = s.primary) (hs : ∀ q, q < 38 → rdN μ (q * 8 + 204984 + 1544) 8 = s.secondary q)
    (ha : rdN μ 206840 4 = s.allocated) (hal : s.allocated < 2147483648)
    (hm : req + 1 ≤ 33554432)
    (hbin : (findFirst s (binUp (req + 1))).or (findFirst s (binDown (req + 1))) = some bin)
    (hC : rdN μ (196792 + 4 * bin) 4 = C) (hw : rdN μ (C + 4) 4 = w) (hbT : s.base + 1073741824 < 2147483648)
    (hbC : s.base ≤ C) (hS : req + 1 ≤ w / 2) (hCend : C + 32 * (w / 2) ≤ s.base + 1073741824)
    (hgr : s.allocated < (C - s.base) / 32 + 1 + req + (if w / 2 - req - 1 = 0 then 0 else 1))
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ h) (hhb : h ≤ pb) (hbs : pb < 4294967296)
    (hR : pb < pagesOf (s.base + 32 * ((C - s.base) / 32 + 1 + req + (if w / 2 - req - 1 = 0 then 0 else 1))))
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * h) (hSTk : S0 + 152 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0)
    (hCT : 196608 ≤ C ∧ C + 16 ≤ 4096 * h) (hpg : HeapPages μ 48 pb h)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (refineContract env) 41177 ω μ x 41423 ω' μ' x 200 ∧ ω'[7] = UInt64.ofNat 0 ∧
      ω'[0] = ω[0] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[1] = ω[1] ∧
      HeapPages μ' 48 pb h ∧ (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → (a < sp - 152 ∨ sp ≤ a) → μ'.read a = μ.read a) :=
  alloc_fail_growK (p := p) (P := P) (S0 := S0) (S1 := S1) env hostCostMax (by decide) (by decide)
    x ω μ s sp req bin C w pb h hbits h1 h7 h8 h9 hsp hsp1 hb hb0 hp hs ha hal hm hbin hC hw hbT
    hbC hS hCend hgr hbd h48 hhb hbs hR hHTs hSTk hSb hCT hpg hst

end Services.Bootstrap.Alloc
