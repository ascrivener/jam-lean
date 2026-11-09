import Services.Bootstrap.Alloc.AllocWrapGrow

/-!
# The `alloc` wrapper keeps the heap off the new headers

`alloc_wrap_refines` and `alloc_wrap_refines_growK` with the frame of main's `alloc_refines_hdr`
and `alloc_refines_growK_hdr` carried through the wrapper's lock and unlock: every heap octet off the
headers of the new state keeps its value (`HKeepG`). With `off_hdr_data`, an allocated chunk's data
is such an octet.
-/

namespace Services.Bootstrap.Decode.HeapWrap

open PVM Picoalloc Services.Bootstrap.Code Services.Bootstrap.Alloc JAM

variable {X : Type} {R : HostRel X}

/-- `alloc_wrap_refines`, with the heap frame `HKeepG`. -/
theorem alloc_wrap_refines_hdr {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    {grow : Grow} {hb : Nat} (s s' : State) (sp size al ptr : Nat) (hwf : WF s) (hrep : Rep μ s)
    (h : alloc grow hb 1 ((size + 31) / 32) s = some (ptr, s')) (hng : s'.allocated = s.allocated)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat size) (h8 : ω[8] = UInt64.ofNat al)
    (hal : 1 ≤ al) (hal1 : al ≤ 32) (hs : size + 31 < 68719476736)
    (hsp : 2147483816 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0) {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT)
    (hSTk : S0 + 168 ≤ sp ∧ sp ≤ S1) (hHT : s.base + 32 * s.allocated ≤ HT) (hw : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 40494 ω μ x 40611 ω' μ' x 440 ∧ Rep μ' s' ∧ WF s' ∧
      ω'[7] = UInt64.ofNat ptr ∧ rdN μ' 206848 1 = 0 ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      HKeepG μ μ' (fun a => ∃ c ∈ chunks s', c.addr = a) := by
  obtain ⟨ω1, μ1, r1, a1, a7, a8, a9, a10, a0, a5, -, st8, st16, fr1, ww1, g1⟩ :=
    al_lock (p := p) (P := P) (R := R) x ω μ sp size al h1 h7 h8 hal hal1 hs (by omega) hsp1 hl (by omega)
      ⟨by omega, by omega⟩ hw
  have rep1 : Rep μ1 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 =>
    fr1 a (by omega) (Or.inl (by omega)) (Or.inr (by unfold A0 at ha1; omega)) ha3
  obtain ⟨ω2, μ2, r2, rep2, wf2, e7, e0, e5, e6, e1, ww2, stk2, hk2⟩ :=
    alloc_refines_hdr (p := p) (P := P) (R := R) x ω1 μ1 s s' (sp - 16) _ ptr hwf rep1 h hng a1 a7 a8 a9 a10
      (by omega) (by omega) hb0 hbT hA hfo hHTs ⟨by omega, by omega⟩ hHT (hw.of_eq ww1)
  have rj := al_ret_jump (p := p) (P := P) (R := R) x ω2 μ2 (by rw [e0, a0])
  obtain ⟨ω3, μ3, r3, c0, c5, c1, cl, fr3, ww3, g3⟩ :=
    al_unlock (p := p) (P := P) (R := R) x ω2 μ2 (sp - 16) (by rw [e1, a1]) (by rw [e5, a5]) (by omega)
      (by omega) (by omega) ⟨by omega, by omega⟩ ((hw.of_eq ww1).of_eq ww2)
  have hb' : s'.base = s.base := by
    rw [alloc_one hwf.1] at h; obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := alloc1_eq h; rw [allocPost_base]
  refine ⟨ω3, μ3, (((r1.trans r2).trans rj).trans r3).mono (by omega),
    rep2.congr_lock wf2 (by rw [hb']; exact hb0) (by rw [hb']; exact hbT)
      (fun a ha1 ha2 ha3 => fr3 a (by omega) (by omega)), wf2,
    by rw [fget g3 7 (by decide) (by decide)]; exact e7, cl, fun a => (ww3 a).trans ((ww2 a).trans (ww1 a)),
    fun a ha1 ha2 => ((fr3 a ha1 (by omega)).trans (stk2 a ha1 (by omega))).trans
      (fr1 a ha1 (Or.inr ha2) (Or.inr (by omega)) (Or.inr (by omega))), ?_, ?_, ?_, ?_, ?_⟩
  · rw [c0, rdN_frame (μ := μ1) fun j hj => stk2 _ (by omega) (by omega), show sp - 16 + 8 = sp - 8 by omega]
    unfold rdN; rw [st8, Num.decodeLE_encodeLE]
    rw [Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]
  · rw [c1, h1]; congr 1; omega
  · rw [c5, rdN_frame (μ := μ1) fun j hj => stk2 _ (by omega) (by omega)]
    unfold rdN; rw [st16, Num.decodeLE_encodeLE]
    rw [Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]
  · rw [fget g3 6 (by decide) (by decide), e6, fget g1 6 (by decide) (by decide)]
  · have k1 : HKeepG μ μ1 (fun a => ∃ c ∈ chunks s', c.addr = a) := fun a ⟨ha1, ha2, _⟩ => by
      unfold Glob at ha1; exact
      fr1 a (by omega) (Or.inl (by omega)) (by omega) (by omega)
    have k3 : HKeepG μ2 μ3 (fun a => ∃ c ∈ chunks s', c.addr = a) := fun a ⟨ha1, ha2, _⟩ => by
      unfold Glob at ha1; exact
      fr3 a (by omega) (by omega)
    exact (k1.trans hk2).trans k3

/-- `alloc_wrap_refines_growK`, with the heap frame `HKeepG`. -/
theorem alloc_wrap_refines_growK_hdr {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (cap : Nat) (hcap : cap < 18446744073709551616)
    (x : RefineCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s s' : State) (sp size al ptr pb ph : Nat) (hwf : WF s)
    (hrep : Rep μ s) (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h : alloc (growTo pb) hb 1 ((size + 31) / 32) s = some (ptr, s')) (hgrown : s'.allocated ≠ s.allocated)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat size) (h8 : ω[8] = UInt64.ofNat al)
    (hal : 1 ≤ al) (hal1 : al ≤ 32) (hs : size + 31 < 68719476736)
    (hsp : 2147483816 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0) (hcost : 275 + 121 * (pagesOf (s.base + 32 * s'.allocated) - ph) ≤ cap)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hSTk : S0 + 168 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0)
    (hp : HeapPages μ 48 pb ph) (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true)
    (hHT : s.base + 32 * s.allocated ≤ 4096 * ph) :
    ∃ ω' μ', FreeStepsH p (refineContractK cap env) 40494 ω μ x 40611 ω' μ' x 540 ∧ Rep μ' s' ∧ WF s' ∧
      ω'[7] = UInt64.ofNat ptr ∧ rdN μ' 206848 1 = 0 ∧
      (∃ h', HeapPages μ' 48 pb h' ∧ s'.base + 32 * s'.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      HKeepG μ μ' (fun a => ∃ c ∈ chunks s', c.addr = a) := by
  have hw := HeapPages.wrAt hp hhb hst
  obtain ⟨ω1, μ1, r1, a1, a7, a8, a9, a10, a0, a5, -, st8, st16, fr1, ww1, g1⟩ :=
    al_lock (p := p) (P := P) (R := refineContractK cap env) (S0 := S0) (S1 := S1) x ω μ sp size al h1 h7 h8 hal
      hal1 hs (by omega) hsp1 hl (by omega) ⟨by omega, by omega⟩ hw
  have rep1 : Rep μ1 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 =>
    fr1 a (by omega) (Or.inl (by omega)) (Or.inr (by unfold A0 at ha1; omega)) ha3
  obtain ⟨ω2, μ2, r2, rep2, wf2, e7, e0, e5, e6, e1, ⟨h', hp2, hsp2, hh1, hh2⟩, hst2, stk2, hk2⟩ :=
    alloc_refines_growK_hdr (p := p) (P := P) (S0 := S0) (S1 := S1) env cap hcap x ω1 μ1 s s' (sp - 16) _ ptr pb
      ph hwf rep1 hbd h48 hhb hbs h hgrown a1 a7 a8 a9 a10
      (by omega) (by omega) hb0 hbT hA hfo hcost hHTs ⟨by omega, by omega⟩ hSb (HeapPages.of_eq hp ww1)
      (fun a h1 h2 => by rw [ww1]; exact hst a h1 h2) hHT
  have rj := al_ret_jump (p := p) (P := P) (R := refineContractK cap env) x ω2 μ2 (by rw [e0, a0])
  obtain ⟨ω3, μ3, r3, c0, c5, c1, cl, fr3, ww3, g3⟩ :=
    al_unlock (p := p) (P := P) (R := refineContractK cap env) (S0 := S0) (S1 := S1) x ω2 μ2 (sp - 16)
      (by rw [e1, a1]) (by rw [e5, a5]) (by omega) (by omega) (by omega) ⟨by omega, by omega⟩
      (HeapPages.wrAt hp2 hh2 hst2)
  have hb' : s'.base = s.base := by
    rw [alloc_one hwf.1] at h; obtain ⟨-, -, -, -, -, -, -, rfl⟩ := alloc1_grown h hgrown; rw [allocPost_base]
  refine ⟨ω3, μ3, (((r1.trans r2).trans rj).trans r3).mono (by omega),
    rep2.congr_lock wf2 (by rw [hb']; exact hb0) (by rw [hb']; exact hbT)
      (fun a ha1 ha2 ha3 => fr3 a (by omega) (by omega)), wf2,
    by rw [fget g3 7 (by decide) (by decide)]; exact e7, cl, ⟨h', HeapPages.of_eq hp2 ww3, hsp2, hh1, hh2⟩,
    fun a h1 h2 => by rw [ww3]; exact hst2 a h1 h2,
    fun a ha1 ha2 => ((fr3 a ha1 (by omega)).trans (stk2 a ha1 (by omega))).trans
      (fr1 a ha1 (Or.inr ha2) (Or.inr (by omega)) (Or.inr (by omega))), ?_, ?_, ?_, ?_, ?_⟩
  · rw [c0, rdN_frame (μ := μ1) fun j hj => stk2 _ (by omega) (by omega), show sp - 16 + 8 = sp - 8 by omega]
    unfold rdN; rw [st8, Num.decodeLE_encodeLE]
    rw [Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]
  · rw [c1, h1]; congr 1; omega
  · rw [c5, rdN_frame (μ := μ1) fun j hj => stk2 _ (by omega) (by omega)]
    unfold rdN; rw [st16, Num.decodeLE_encodeLE]
    rw [Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]
  · rw [fget g3 6 (by decide) (by decide), e6, fget g1 6 (by decide) (by decide)]
  · have k1 : HKeepG μ μ1 (fun a => ∃ c ∈ chunks s', c.addr = a) := fun a ⟨ha1, ha2, _⟩ => by
      unfold Glob at ha1; exact
      fr1 a (by omega) (Or.inl (by omega)) (by omega) (by omega)
    have k3 : HKeepG μ2 μ3 (fun a => ∃ c ∈ chunks s', c.addr = a) := fun a ⟨ha1, ha2, _⟩ => by
      unfold Glob at ha1; exact
      fr3 a (by omega) (by omega)
    exact (k1.trans hk2).trans k3

end Services.Bootstrap.Decode.HeapWrap
