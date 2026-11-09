import Services.Bootstrap.Alloc.HeapContract
import Services.Bootstrap.Decode.ReallocOk
import Services.Bootstrap.Decode.LoopA

/-!
# `realloc` keeps the other allocated chunks' data

`OthersData s ptr a`: a lies in the data of an allocated chunk of `s` other than the one at
ptr − 32. A frame of the heap that writes only the headers of `s`'s chunks and octets of free
chunks or of ptr's own chunk keeps every such octet (`keep_of_hkeep`).
-/

namespace Services.Bootstrap.Decode.ReallocKeepAll

open PVM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc JAM
  Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- a lies in the data of an allocated chunk of `s` other than ptr's. -/
def OthersData (s : State) (ptr a : Nat) : Prop :=
  ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≠ ptr ∧ InData c a

/-- The octets h … h + 16 lie in a chunk of `s` that is free or is ptr's. -/
def Spare16 (s : State) (ptr h : Nat) : Prop :=
  ∃ d ∈ chunks s, (d.used = false ∨ d.addr + 32 = ptr) ∧ d.addr ≤ h ∧ h + 16 ≤ d.addr + 32 * d.size

/-- **A heap frame for headers of `s` and spare octets keeps the other chunks' data.** -/
theorem keep_of_hkeep {s : State} (hwf : WF s) (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648)
    {ptr : Nat} {μ μ' : Memory} {G : Nat → Prop}
    (hG : ∀ h, G h → (∃ d ∈ chunks s, d.addr = h) ∨ Spare16 s ptr h ∨ s.base + 1073741824 ≤ h)
    (hk : HKeep μ μ' G) :
    ∀ a, OthersData s ptr a → μ'.read a = μ.read a := by
  intro a ⟨c, hc, hu, hne, hin⟩
  have ht := hwf.2.2.2.1; unfold TilesOk at ht
  have hoff := off_hdr_data hwf hb0 hbT hc hin.1 hin.2
  apply hk
  refine ⟨hoff.1, hoff.2.1, fun h hh => ?_⟩
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hcl := ht.mem_lt c hc
  rcases hG h hh with hd | ⟨d, hd, hdu, h1, h2⟩ | hbey
  · exact hoff.2.2 h hd
  · have hcd : c ≠ d := by
      rintro rfl
      rcases hdu with h' | h'
      · rw [hu] at h'; exact absurd h' (by decide)
      · exact hne h'
    unfold InData at hin
    rcases HeapFrame.Tiles.disjoint ht c hc d hd hcd with h' | h' <;> omega
  · unfold InData at hin; left; omega

/-- `same_refines` with its frame below the stack: memory below sp − 152 is untouched. -/
theorem same_refines_low {p : ByteArray} {P : Program} [HasCode p P] {X : Type} {R : HostRel X} (x : X) (ω : Regs) (μ : Memory)
    (s : State) (sp ptr req : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr : req = usable s ptr)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr)
    (h10 : ω[10] = UInt64.ofNat req) (h0 : ω[0] = UInt64.ofNat 1988)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) {HT S0 S1 : Nat}
    (hHT : s.base + 32 * s.allocated ≤ HT) (hS : S0 + 152 ≤ sp ∧ sp ≤ S1) (hw : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 42980 ω μ x 40805 ω' μ' x 180 ∧ Rep μ' s ∧
      (∀ a, μ'.writable a = μ.writable a) ∧ (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[7] = UInt64.ofNat ptr ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat sp ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ (∀ a, a < sp - 152 → μ'.read a = μ.read a) := by
  obtain ⟨c, hcm, hca, hcu⟩ := hc
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  have hcl := ht.mem_lt c hcm
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hsz : (s.hdr c.addr).size = sizeWord c.size true := by rw [chunks_hdr c hcm, hcu]
  have hca' : c.addr = ptr - 32 := by omega
  have hcT : c.addr + 32 ≤ HT := by
    have hsp' := hwf.2.2.2.2.2.2.2; unfold SpaceOk at hsp'; have := (hsp' c hcm).2; omega
  have hw' : rdN μ (ptr - 28) 4 = 2 * c.size + 1 := by
    rw [show ptr - 28 = c.addr + 4 by omega, hrep.size c hcm, hsz]; unfold sizeWord; simp
  have hus : usable s ptr = c.size - 1 := by
    unfold usable; rw [← hca', hsz, wordSize_sizeWord]
  obtain ⟨ω1, μ1, r1, a1, -, a6, st0, st5, st6, sf1, ww1, g1⟩ := rl_pro (p := p) (P := P) (R := R) x ω μ sp
    ptr (2 * c.size + 1) h1 h8 (by omega) (by omega) hw' (by omega) hsp hsp1 ⟨by omega, by omega⟩ hS hw
  have b := rl_br_same (p := p) (P := P) (R := R) x ω1 μ1 req
    (by rw [fget g1 10 (by decide) (by decide)]; exact h10)
    (by rw [a6, hr, hus]; congr 1; omega)
  have hr1 := (hw.of_eq ww1).rd
  obtain ⟨ω2, r2, e7, e0, e1, e5, e6, -⟩ := rl_ret (p := p) (P := P) (R := R) x ω1 μ1 (sp - 152) ptr
    ω[5].toNat ω[6].toNat a1 (by rw [fget g1 8 (by decide) (by decide)]; exact h8) (by omega) (by omega) (by omega)
    (by rw [show sp - 152 + 144 = sp - 8 by omega, rd_enc st0 (UInt64.toNat_lt _), h0]; rfl)
    (by rw [show sp - 152 + 136 = sp - 16 by omega]; exact rd_enc st5 (UInt64.toNat_lt _))
    (by rw [show sp - 152 + 128 = sp - 24 by omega]; exact rd_enc st6 (UInt64.toNat_lt _))
    ⟨by omega, by omega⟩ hr1
  refine ⟨ω2, μ1, ((r1.trans b).trans r2).mono (by omega),
    hrep.congr_lock hwf hb0 hbT (fun a ha1 ha2 ha3 => sf1 a (by omega) (Or.inl (by omega))), ww1,
    fun a h1 h2 => sf1 a h1 (Or.inr h2), e7, e0, by rw [e1]; congr 1; omega,
    by rw [e5, UInt64.ofNat_toNat], by rw [e6, UInt64.ofNat_toNat], fun a ha => sf1 a (by omega) (Or.inl (by omega))⟩

/-- An octet of another chunk's data lies in the heap, above its base's first header. -/
theorem others_lt {s : State} (hwf : WF s) (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648)
    {ptr a : Nat} (h : OthersData s ptr a) : 206896 ≤ a ∧ a < 2147483648 := by
  obtain ⟨c, hc, hu, -, hin⟩ := h
  have ht := hwf.2.2.2.1; unfold TilesOk at ht
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have := ht.mem_lt c hc
  unfold InData at hin; omega

/-- **`realloc` around a refinement of `realloc_impl`, keeping the other chunks' data**: as
    `realloc_wrap_data`, when `realloc_impl` also keeps every octet of another allocated chunk's data,
    so does `realloc`. -/
theorem realloc_wrap_keep {p : ByteArray} {P : Program} [HasCode p P] {X : Type} {R : HostRel X} (x : X) (ω : Regs) (μ : Memory)
    (s s' : State) (sp ptr al size r n m : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hb' : s'.base = s.base)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hp0 : ptr ≠ 0) (hp1 : ptr < 4294967296)
    (hal : al + 31 < 68719476736) (hs : size + 31 < 68719476736)
    (hsp : 2147483716 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648)
    (hl : rdN μ 206848 1 = 0) {HT S0 S1 : Nat} (hH : 206864 ≤ HT) (hS : S0 + 16 ≤ sp ∧ sp ≤ S1)
    (hw : WrAt μ HT S0 S1)
    (hpm : 206864 ≤ ptr ∧ ptr + m ≤ 2147483648) (hrm : 206864 ≤ r ∧ r + m ≤ 2147483648)
    (impl : ∀ ω1 μ1, Rep μ1 s → WrAt μ1 HT S0 S1 → ω1[1] = UInt64.ofNat (sp - 16) →
      ω1[8] = UInt64.ofNat ptr → ω1[7] = UInt64.ofNat 196792 → ω1[10] = UInt64.ofNat ((size + 31) / 32) →
      ω1[0] = UInt64.ofNat 1988 →
      ∃ ω2 μ2, μ2.readN r m = μ1.readN ptr m ∧ FreeStepsH p R 42980 ω1 μ1 x 40805 ω2 μ2 x n ∧ Rep μ2 s' ∧ WF s' ∧ FirstOk s' ∧
        (∀ a, μ2.writable a = μ1.writable a) ∧ (∀ a, a < 4294967296 → sp - 16 ≤ a → μ2.read a = μ1.read a) ∧
        ω2[7] = UInt64.ofNat r ∧ ω2[1] = UInt64.ofNat (sp - 16) ∧ ω2[5] = ω1[5] ∧ ω2[6] = ω1[6] ∧
        (∀ a, OthersData s ptr a → μ2.read a = μ1.read a)) :
    ∃ ω' μ', μ'.readN r m = μ.readN ptr m ∧ FreeStepsH p R 40701 ω μ x 40821 ω' μ' x (n + 45) ∧ Rep μ' s' ∧ WF s' ∧ FirstOk s' ∧
      ω'[7] = UInt64.ofNat r ∧ rdN μ' 206848 1 = 0 ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      (∀ a, OthersData s ptr a → μ'.read a = μ.read a) := by
  obtain ⟨ω1, μ1, r1, a1, a8, a7, -, a10, a0, a5, -, st8, st16, fr1, ww1, g1⟩ :=
    rw_lock (p := p) (P := P) (R := R) x ω μ sp ptr al size h1 h7 h9 h10 hp0 hp1 hal hs hsp hsp1 hl hH
      hS hw
  have rep1 : Rep μ1 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 =>
    fr1 a (by omega) (Or.inl (by omega)) (Or.inr (by unfold A0 at ha1; omega)) ha3
  obtain ⟨ω2, μ2, dat2, r2, rep2, hwf', hfo', ww2, stk2, e7, e1, e5, e6, kp2⟩ := impl ω1 μ1 rep1 (hw.of_eq ww1) a1 a8 a7 a10 a0
  obtain ⟨ω3, μ3, r3, c0, c5, c1, cl, fr3, ww3, g3⟩ :=
    rw_unlock (p := p) (P := P) (R := R) x ω2 μ2 (sp - 16) e1 (by rw [e5, a5]) (by omega) (by omega) hH
      ⟨by omega, by omega⟩ ((hw.of_eq ww1).of_eq ww2)
  have dat : μ3.readN r m = μ.readN ptr m := by
    have e3 : μ3.readN r m = μ2.readN r m := readN_congr2 fun j hj => fr3 _ (by omega) (by omega)
    rw [e3, dat2]
    exact readN_congr2 fun j hj => fr1 _ (by omega) (Or.inl (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
  refine ⟨ω3, μ3, dat, ((r1.trans r2).trans r3).mono (by omega),
    rep2.congr_lock hwf' (by rw [hb']; exact hb0) (by rw [hb']; exact hbT)
      (fun a ha1 ha2 ha3 => fr3 a (by omega) (by omega)), hwf', hfo',
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
  · intro a ha
    obtain ⟨hl1, hl2⟩ := others_lt hwf hb0 hbT ha
    rw [fr3 a (by omega) (by omega), kp2 a ha]
    exact fr1 a (by omega) (Or.inl (by omega)) (Or.inr (by omega)) (Or.inr (by omega))

theorem realloc_inplace_refines_keep {p : ByteArray} {P : Program} [HasCode p P] {X : Type} {R : HostRel X} (x : X) (ω : Regs) (μ : Memory)
    {grow : Grow} {hb : Nat} (s : State) (sp ptr align req : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr0 : req ≠ 0) (hr : req ≤ usable s ptr)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr) (h7 : ω[7] = UInt64.ofNat 196792)
    (h10 : ω[10] = UInt64.ofNat req) (h0 : ω[0] = UInt64.ofNat 1988)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648)
    (hfo : FirstOk s) {HT S0 S1 : Nat} (hHT : s.base + 32 * s.allocated ≤ HT) (hS : S0 + 152 ≤ sp ∧ sp ≤ S1)
    (hw : WrAt μ HT S0 S1) :
    ∃ s', realloc grow hb s ptr align req = some (ptr, s', false) ∧
      ∃ ω' μ', μ'.readN ptr (32 * req) = μ.readN ptr (32 * req) ∧
        FreeStepsH p R 42980 ω μ x 40805 ω' μ' x 180 ∧ Rep μ' s' ∧ WF s' ∧ FirstOk s' ∧
        (∀ a, μ'.writable a = μ.writable a) ∧ (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[7] = UInt64.ofNat ptr ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat sp ∧
        ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ (∀ a, OthersData s ptr a → μ'.read a = μ.read a) := by
  have hc' := hc
  obtain ⟨c, hcm, hca, hcu⟩ := hc'
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  have hcs := chunk_size_usable hcm hca hcu rfl (ht.mem_lt c hcm).2.2
  refine ⟨_, realloc_inplace hr0 hr, ?_⟩
  by_cases e : req = usable s ptr
  · rw [if_pos e]
    obtain ⟨ω', μ', run, rep, ww, stk, e7, e0, e1, e5, e6, low⟩ := same_refines_low (p := p) (P := P) (R := R)
      x ω μ s sp ptr req hwf hrep hc e h1 h8 h10 h0 hsp hsp1 hb0 hbT hHT hS hw
    have hdl := data_lt hwf hbT hc
    exact ⟨ω', μ', readN_congr2 fun j hj => low _ (by omega), run, rep, hwf, hfo, ww, stk, e7, e0, e1, e5, e6,
      fun a ha => low a (by have := others_lt hwf hb0 hbT ha; omega)⟩
  · rw [if_neg e]
    obtain ⟨ω', μ', hk, run, rep, wf, fo, ww, stk, e7, e0, e1, e5, e6⟩ := shrink_refines_hdr (p := p) (P := P)
      (R := R) x ω μ s sp ptr req hwf hrep hc hr0 (by omega) h1 h8 h7 h10 h0 hsp hsp1 hb0 hbT hfo hHT hS hw
    refine ⟨ω', μ', readN_inplace hwf hb0 hbT hcm hca (by omega) (by omega) hk.hkeep, run, rep, wf, fo, ww, stk, e7, e0,
      e1, e5, e6, keep_of_hkeep hwf hb0 hbT (fun h hh => ?_) hk.hkeep⟩
    rcases hh with hh | hh
    · exact Or.inl hh
    · exact Or.inr (Or.inl ⟨c, hcm, Or.inr hca, by omega, by omega⟩)

theorem realloc_wrap_inplace_keep {p : ByteArray} {P : Program} [HasCode p P] {X : Type} {R : HostRel X} (x : X) (ω : Regs) (μ : Memory)
    {grow : Grow} {hb : Nat} (s : State) (sp ptr al size : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr0 : size ≠ 0)
    (hr : (size + 31) / 32 ≤ usable s ptr)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hal : al + 31 < 68719476736) (hs : size + 31 < 68719476736)
    (hsp : 2147483816 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648)
    (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0) {HT S0 S1 : Nat} (hHT : s.base + 32 * s.allocated ≤ HT)
    (hS : S0 + 168 ≤ sp ∧ sp ≤ S1) (hw : WrAt μ HT S0 S1) :
    ∃ s', realloc grow hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (ptr, s', false) ∧
      ∃ ω' μ', μ'.readN ptr (32 * ((size + 31) / 32)) = μ.readN ptr (32 * ((size + 31) / 32)) ∧ FreeStepsH p R 40701 ω μ x 40821 ω' μ' x 225 ∧ Rep μ' s' ∧ WF s' ∧ FirstOk s' ∧
        ω'[7] = UInt64.ofNat ptr ∧ rdN μ' 206848 1 = 0 ∧ (∀ a, μ'.writable a = μ.writable a) ∧
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
        (∀ a, OthersData s ptr a → μ'.read a = μ.read a) := by
  have hq0 : (size + 31) / 32 ≠ 0 := by omega
  have hc' := hc
  obtain ⟨c, hcm, hca, -⟩ := hc'
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  have hcl := ht.mem_lt c hcm
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hdl := data_lt hwf hbT hc
  refine ⟨_, realloc_inplace hq0 hr, ?_⟩
  exact realloc_wrap_keep (p := p) (P := P) (R := R) x ω μ s _ sp ptr al size ptr 180 (32 * ((size + 31) / 32)) hwf hrep
    (by split <;> simp [shrink_base]) h1 h7 h9 h10 (by omega) (by omega) hal hs (by omega) hsp1 hb0 hbT hl
    (by omega) ⟨by omega, by omega⟩ hw ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (fun ω1 μ1 rep1 W1 a1 a8 a7 a10 a0 => by
      obtain ⟨s'', e, ω2, μ2, dat, run, rep, wf, fo, ww, stk, e7, -, e1, e5, e6, kp⟩ :=
        realloc_inplace_refines_keep (grow := grow) (hb := hb) (p := p) (P := P) (R := R) x ω1 μ1 s (sp - 16) ptr
          ((al + 31) / 32) ((size + 31) / 32) hwf rep1 hc hq0 hr a1 a8 a7 a10 a0 (by omega) (by omega) hb0 hbT
          hfo hHT ⟨by omega, by omega⟩ W1
      rw [realloc_inplace hq0 hr] at e
      simp only [Option.some.injEq, Prod.mk.injEq, true_and, and_true] at e
      subst e
      exact ⟨ω2, μ2, dat, run, rep, wf, fo, ww, stk, e7, e1, e5, e6, kp⟩)

/-- **The header a grow in place writes**: when ptr's chunk (cur units) grows into its free next
    chunk to req + 1 units, the header at ptr − 32 + 32·(req + 1) lies in that free chunk, or is the
    address of the chunk after it, or is past the heap's top. -/
theorem grow_hdr {s : State} (hwf : WF s) {ptr cur req : Nat}
    (hc : (⟨ptr - 32, cur, true⟩ : Chunk) ∈ chunks s) (hlt : cur < req + 1)
    (hT : ptr - 32 + 32 * cur < s.base + 1073741824)
    (hfree : wordUsed (s.hdr (ptr - 32 + 32 * cur)).size = false)
    (hfit : req + 1 ≤ cur + wordSize (s.hdr (ptr - 32 + 32 * cur)).size) :
    (∃ d ∈ chunks s, d.addr = ptr - 32 + 32 * (req + 1)) ∨ Spare16 s ptr (ptr - 32 + 32 * (req + 1)) ∨
      s.base + 1073741824 ≤ ptr - 32 + 32 * (req + 1) := by
  have ht := hwf.2.2.2.1; unfold TilesOk at ht
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  rw [htop] at ht
  obtain ⟨pre, post, hcs⟩ := List.append_of_mem hc
  have ht' := ht; rw [hcs] at ht'
  obtain ⟨-, hhd, hpost, -⟩ := Tiles.around ht'
  cases post with
  | nil =>
    obtain ⟨m, -, hm1, -, hm3⟩ := Tiles.append.mp ht'
    simp only [Tiles] at hm1 hm3; omega
  | cons e es =>
    have he : e.addr = ptr - 32 + 32 * cur := hhd e rfl
    have hem : e ∈ chunks s := by rw [hcs]; simp
    have hsz := chunks_hdr e hem
    rw [he] at hsz
    rw [hsz, wordSize_sizeWord] at hfit
    rw [hsz] at hfree
    have heu : e.used = false := by
      cases hu : e.used
      · rfl
      · rw [hu] at hfree; simp [wordUsed, sizeWord] at hfree
    have hel := ht.mem_lt e hem
    by_cases hN : ptr - 32 + 32 * (req + 1) < e.addr + 32 * e.size
    · exact Or.inr (Or.inl ⟨e, hem, Or.inl heu, by omega, by omega⟩)
    · have hNe : ptr - 32 + 32 * (req + 1) = e.addr + 32 * e.size := by omega
      by_cases hb : e.addr + 32 * e.size < s.base + 1073741824
      · left
        have ht2 : Tiles s.base (s.base + 1073741824) ((pre ++ [⟨ptr - 32, cur, true⟩]) ++ e :: es) := by
          simpa [List.append_assoc] using ht'
        obtain ⟨-, hhd2, -, -⟩ := Tiles.around ht2
        cases es with
        | nil =>
          obtain ⟨m, -, hm1, -, hm3⟩ := Tiles.append.mp ht2
          simp only [Tiles] at hm1 hm3; omega
        | cons f fs =>
          refine ⟨f, by rw [hcs]; simp, ?_⟩
          rw [hhd2 f rfl, hNe]
      · exact Or.inr (Or.inr (by omega))

/-- ptr's chunk, from its data address: ⟨ptr − 32, usable + 1, used⟩. -/
theorem ptr_chunk {s : State} (hwf : WF s) {ptr : Nat} (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) :
    (⟨ptr - 32, usable s ptr + 1, true⟩ : Chunk) ∈ chunks s ∧ wordSize (s.hdr (ptr - 32)).size = usable s ptr + 1 := by
  obtain ⟨c, hcm, hca, hcu⟩ := hc
  have ht := hwf.2.2.2.1; unfold TilesOk at ht
  have hcs := chunk_size_usable hcm hca hcu rfl (ht.mem_lt c hcm).2.2
  have he : c = ⟨ptr - 32, usable s ptr + 1, true⟩ := by
    cases c; simp only at hca hcu hcs ⊢; subst hcu; simp only [Chunk.mk.injEq, and_true]; omega
  subst he
  refine ⟨hcm, ?_⟩
  have := chunks_hdr _ hcm; simp only at this; rw [this, wordSize_sizeWord]

/-- **`realloc_wrap_grow_data`, keeping the other chunks' data.** -/
theorem realloc_wrap_grow_keep {p : ByteArray} {P : Program} [HasCode p P] {X : Type} {R : HostRel X} (x : X) (ω : Regs) (μ : Memory)
    {grow : Grow} {hb : Nat} (s s' : State) (sp ptr al size : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr : usable s ptr < (size + 31) / 32)
    (hr1 : (size + 31) / 32 < 33554431)
    (h : growInplace grow s ptr ((size + 31) / 32) = some s') (hng : s'.allocated = s.allocated)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hal : al + 31 < 68719476736)
    (hsp : 2147483816 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0) {HT S0 S1 : Nat} (hHT : s.base + 32 * s.allocated ≤ HT)
    (hS : S0 + 168 ≤ sp ∧ sp ≤ S1) (hw : WrAt μ HT S0 S1) :
    realloc grow hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (ptr, s', false) ∧
      ∃ ω' μ', μ'.readN ptr (32 * usable s ptr) = μ.readN ptr (32 * usable s ptr) ∧ FreeStepsH p R 40701 ω μ x 40821 ω' μ' x 295 ∧ Rep μ' s' ∧ WF s' ∧ FirstOk s' ∧
        ω'[7] = UInt64.ofNat ptr ∧ rdN μ' 206848 1 = 0 ∧ (∀ a, μ'.writable a = μ.writable a) ∧
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
        (∀ a, OthersData s ptr a → μ'.read a = μ.read a) := by
  obtain ⟨hpc, hcur⟩ := ptr_chunk hwf hc
  obtain ⟨hT, hfr, hfit, -⟩ := growInplace_facts hcur (by omega) h hng
  have hc' := hc
  obtain ⟨c, hcm, hca, hcu⟩ := hc'
  have hca' := hca
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  have hcl := ht.mem_lt c hcm
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hdl := data_lt hwf hbT hc
  have hcs := chunk_size_usable hcm hca hcu rfl hcl.2.2
  refine ⟨realloc_grow hr h, ?_⟩
  exact realloc_wrap_keep (p := p) (P := P) (R := R) x ω μ s s' sp ptr al size ptr 250 (32 * usable s ptr) hwf hrep
    (growInplace_base h) h1 h7 h9 h10 (by omega) (by omega) hal (by omega) (by omega) hsp1 hb0 hbT hl
    (by omega) ⟨by omega, by omega⟩ hw ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (fun ω1 μ1 rep1 W1 a1 a8 a7 a10 a0 => by
      obtain ⟨ω2, μ2, hk, run, rep, wf, fo, ww, stk, e7, -, e1, e5, e6⟩ :=
        grow_refines_hdr (p := p) (P := P) (R := R) x ω1 μ1 s s' (sp - 16) ptr
          ((size + 31) / 32) hwf rep1 hc hr hr1 h hng a1 a8 a7 a10 a0 (by omega) (by omega)
          hb0 hbT hA hfo hHT ⟨by omega, by omega⟩ W1
      refine ⟨ω2, μ2, readN_inplace hwf hb0 hbT hcm hca' (by omega) (by omega) hk.hkeep, run, rep, wf, fo, ww, stk, e7, e1,
        e5, e6, keep_of_hkeep hwf hb0 hbT (fun h hh => ?_) hk.hkeep⟩
      rcases hh with hh | hh
      · exact Or.inl hh
      · rw [hh]; exact grow_hdr hwf hpc (by omega) hT hfr hfit)

/-- **`realloc_wrap_grow_heapK_dataG`, keeping the other chunks' data.** -/
theorem realloc_wrap_grow_heapK_keepG {X : Type} {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X)
    (cap : Nat) (hcap : cap < 18446744073709551616)
    (x : X) (ω : Regs) (μ : Memory) {hb : Nat} (s s' : State) (sp ptr al size : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr : usable s ptr < (size + 31) / 32)
    (hr1 : (size + 31) / 32 < 33554431)
    (pb ph : Nat) (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h : growInplace (growTo pb) s ptr ((size + 31) / 32) = some s') (hgrown : s'.allocated ≠ s.allocated)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hal : al + 31 < 68719476736)
    (hsp : 2147483816 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hcost : 275 + 121 * (pagesOf (s.base + 32 * s'.allocated) - ph) ≤ cap) (hl : rdN μ 206848 1 = 0)
    {S0 S1 : Nat} (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 168 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (ptr, s', false) ∧
      ∃ ω' μ', μ'.readN ptr (32 * usable s ptr) = μ.readN ptr (32 * usable s ptr) ∧ FreeStepsH p (env.rel cap) 40701 ω μ x 40821 ω' μ' x 345 ∧ Rep μ' s' ∧ WF s' ∧
        FirstOk s' ∧ ω'[7] = UInt64.ofNat ptr ∧ rdN μ' 206848 1 = 0 ∧
        (∃ h', HeapPages μ' 48 pb h' ∧ s'.base + 32 * s'.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
        (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
        (∀ a, OthersData s ptr a → μ'.read a = μ.read a) := by
  refine ⟨realloc_grow hr h, ?_⟩
  obtain ⟨hpc, hcur⟩ := ptr_chunk hwf hc
  obtain ⟨hT, hfr, hfit, -⟩ := growInplace_grown hcur (by omega) h hgrown
  have hc' := hc
  obtain ⟨c, hcm, hca, hcu⟩ := hc'
  have hdl := data_lt hwf hbT hc
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  have hcl := ht.mem_lt c hcm
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hwr := HeapPages.wrAt hp hhb hst
  obtain ⟨ω1, μ1, r1, a1, a8, a7, -, a10, a0, a5, -, st8, st16, fr1, ww1, g1⟩ :=
    rw_lock (p := p) (P := P) (R := env.rel cap) x ω μ sp ptr al size h1 h7 h9 h10 (by omega) (by omega)
      hal (by omega) (by omega) hsp1 hl (by omega) ⟨by omega, by omega⟩ hwr
  have rep1 : Rep μ1 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 =>
    fr1 a (by omega) (Or.inl (by omega)) (Or.inr (by unfold A0 at ha1; omega)) ha3
  have hp1 := HeapPages.of_eq hp ww1
  have hst1 : ∀ a, S0 ≤ a → a < S1 → μ1.writable a = true := fun a h1 h2 => by rw [ww1]; exact hst a h1 h2
  obtain ⟨ω2, μ2, hk, r2, rep2, wf2, fo2, ⟨h', hpH, hE', hph, hpb⟩, hst2, stk2, e7, e0, e1, e5, e6⟩ :=
    grow_heap_refinesK_hdrG (p := p) (P := P) env cap hcap x ω1 μ1 s s' (sp - 16) ptr ((size + 31) / 32) hwf rep1 hc hr hr1
      pb ph hbd h48 hhb hbs h hgrown a1 a8 a7 a10 a0 (by omega) (by omega) hb0 hbT hA hfo hcost hHT
      ⟨by omega, by omega⟩ hSb hp1 hst1
  obtain ⟨ω3, μ3, r3, c0, c5, c1, cl, fr3, ww3, g3⟩ :=
    rw_unlock (p := p) (P := P) (R := env.rel cap) x ω2 μ2 (sp - 16) e1 (by rw [e5, a5]) (by omega)
      (by omega) (by omega) ⟨by omega, by omega⟩ (HeapPages.wrAt hpH hpb hst2)
  have hb' : s'.base = s.base := growInplace_base h
  have hcs := chunk_size_usable hcm hca hcu rfl hcl.2.2
  have dat : μ3.readN ptr (32 * usable s ptr) = μ.readN ptr (32 * usable s ptr) := by
    have e3 : μ3.readN ptr (32 * usable s ptr) = μ2.readN ptr (32 * usable s ptr) :=
      readN_congr2 fun j hj => fr3 _ (by omega) (by omega)
    rw [e3, readN_inplace hwf hb0 hbT hcm hca (by omega) (by omega) hk.hkeep]
    exact readN_congr2 fun j hj => fr1 _ (by omega) (Or.inl (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
  refine ⟨ω3, μ3, dat, ((r1.trans r2).trans r3).mono (by omega),
    rep2.congr_lock wf2 (by rw [hb']; exact hb0) (by rw [hb']; exact hbT)
      (fun a ha1 ha2 ha3 => fr3 a (by omega) (by omega)), wf2, fo2,
    by rw [fget g3 7 (by decide) (by decide)]; exact e7, cl,
    ⟨h', HeapPages.of_eq hpH ww3, hE', hph, hpb⟩, fun a h1 h2 => by rw [ww3]; exact hst2 a h1 h2,
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
  · intro a ha
    obtain ⟨hl1, hl2⟩ := others_lt hwf hb0 hbT ha
    have kp := keep_of_hkeep hwf hb0 hbT (fun h hh => by
      rcases hh with hh | hh
      · exact Or.inl hh
      · rw [hh]; exact grow_hdr hwf hpc (by omega) hT hfr hfit) hk.hkeep
    rw [fr3 a (by omega) (by omega), kp a ha]
    exact fr1 a (by omega) (Or.inl (by omega)) (Or.inr (by omega)) (Or.inr (by omega))

/-- `realloc_wrap_grow_heapK_keepG` for the refine contract (`refineHeap env`). -/
theorem realloc_wrap_grow_heapK_keep {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (cap : Nat) (hcap : cap < 18446744073709551616)
    (x : RefineCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s s' : State) (sp ptr al size : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr : usable s ptr < (size + 31) / 32)
    (hr1 : (size + 31) / 32 < 33554431)
    (pb ph : Nat) (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h : growInplace (growTo pb) s ptr ((size + 31) / 32) = some s') (hgrown : s'.allocated ≠ s.allocated)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hal : al + 31 < 68719476736)
    (hsp : 2147483816 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hcost : 275 + 121 * (pagesOf (s.base + 32 * s'.allocated) - ph) ≤ cap) (hl : rdN μ 206848 1 = 0)
    {S0 S1 : Nat} (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 168 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (ptr, s', false) ∧
      ∃ ω' μ', μ'.readN ptr (32 * usable s ptr) = μ.readN ptr (32 * usable s ptr) ∧ FreeStepsH p (refineContractK cap env) 40701 ω μ x 40821 ω' μ' x 345 ∧ Rep μ' s' ∧ WF s' ∧
        FirstOk s' ∧ ω'[7] = UInt64.ofNat ptr ∧ rdN μ' 206848 1 = 0 ∧
        (∃ h', HeapPages μ' 48 pb h' ∧ s'.base + 32 * s'.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
        (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
        (∀ a, OthersData s ptr a → μ'.read a = μ.read a) :=
  realloc_wrap_grow_heapK_keepG (p := p) (P := P) (refineHeap env) cap hcap x ω μ (hb := hb) s s' sp ptr al size hwf hrep hc hr hr1 pb ph hbd h48 hhb hbs h hgrown h1 h7 h9 h10 hal hsp hsp1 hb0 hbT hA hfo hcost hl (S0 := S0) (S1 := S1) hHT hS hSb hp hst

theorem realloc_wrap_grow_heap_keepG {X : Type} {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X)
    (x : X) (ω : Regs) (μ : Memory) {hb : Nat} (s s' : State) (sp ptr al size : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr : usable s ptr < (size + 31) / 32)
    (hr1 : (size + 31) / 32 < 33554431)
    (pb ph : Nat) (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h : growInplace (growTo pb) s ptr ((size + 31) / 32) = some s') (hgrown : s'.allocated ≠ s.allocated)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hal : al + 31 < 68719476736)
    (hsp : 2147483816 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hcost : pagesOf (s.base + 32 * s'.allocated) ≤ ph + 14) (hl : rdN μ 206848 1 = 0)
    {S0 S1 : Nat} (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 168 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (ptr, s', false) ∧
      ∃ ω' μ', μ'.readN ptr (32 * usable s ptr) = μ.readN ptr (32 * usable s ptr) ∧ FreeStepsH p (env.rel hostCostMax) 40701 ω μ x 40821 ω' μ' x 345 ∧ Rep μ' s' ∧ WF s' ∧
        FirstOk s' ∧ ω'[7] = UInt64.ofNat ptr ∧ rdN μ' 206848 1 = 0 ∧
        (∃ h', HeapPages μ' 48 pb h' ∧ s'.base + 32 * s'.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
        (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
        (∀ a, OthersData s ptr a → μ'.read a = μ.read a) :=
  realloc_wrap_grow_heapK_keepG (p := p) (P := P) (hb := hb) (S0 := S0) (S1 := S1)
    env hostCostMax (by decide) x ω μ s s' sp ptr al size hwf hrep hc hr hr1 pb ph hbd h48 hhb hbs
    h hgrown h1 h7 h9 h10 hal hsp hsp1 hb0 hbT hA hfo (by unfold hostCostMax; omega) hl hHT hS hSb
    hp hst

/-- `realloc_wrap_grow_heap_keepG` for the refine contract (`refineHeap env`). -/
theorem realloc_wrap_grow_heap_keep {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (x : RefineCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s s' : State) (sp ptr al size : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr : usable s ptr < (size + 31) / 32)
    (hr1 : (size + 31) / 32 < 33554431)
    (pb ph : Nat) (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h : growInplace (growTo pb) s ptr ((size + 31) / 32) = some s') (hgrown : s'.allocated ≠ s.allocated)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hal : al + 31 < 68719476736)
    (hsp : 2147483816 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hcost : pagesOf (s.base + 32 * s'.allocated) ≤ ph + 14) (hl : rdN μ 206848 1 = 0)
    {S0 S1 : Nat} (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 168 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (ptr, s', false) ∧
      ∃ ω' μ', μ'.readN ptr (32 * usable s ptr) = μ.readN ptr (32 * usable s ptr) ∧ FreeStepsH p (refineContract env) 40701 ω μ x 40821 ω' μ' x 345 ∧ Rep μ' s' ∧ WF s' ∧
        FirstOk s' ∧ ω'[7] = UInt64.ofNat ptr ∧ rdN μ' 206848 1 = 0 ∧
        (∃ h', HeapPages μ' 48 pb h' ∧ s'.base + 32 * s'.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
        (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
        (∀ a, OthersData s ptr a → μ'.read a = μ.read a) :=
  realloc_wrap_grow_heap_keepG (p := p) (P := P) (refineHeap env) x ω μ (hb := hb) s s' sp ptr al size hwf hrep hc hr hr1 pb ph hbd h48 hhb hbs h hgrown h1 h7 h9 h10 hal hsp hsp1 hb0 hbT hA hfo hcost hl (S0 := S0) (S1 := S1) hHT hS hSb hp hst

theorem realloc_wrap_keep0 {p : ByteArray} {P : Program} [HasCode p P] {X : Type} {R : HostRel X} (x : X) (ω : Regs) (μ : Memory)
    (s s' : State) (sp ptr al size r n : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hb' : s'.base = s.base)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hp0 : ptr ≠ 0) (hp1 : ptr < 4294967296)
    (hal : al + 31 < 68719476736) (hs : size + 31 < 68719476736)
    (hsp : 2147483716 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648)
    (hl : rdN μ 206848 1 = 0) {HT S0 S1 : Nat} (hH : 206864 ≤ HT) (hS : S0 + 16 ≤ sp ∧ sp ≤ S1)
    (hw : WrAt μ HT S0 S1)
    (impl : ∀ ω1 μ1, Rep μ1 s → WrAt μ1 HT S0 S1 → ω1[1] = UInt64.ofNat (sp - 16) →
      ω1[8] = UInt64.ofNat ptr → ω1[7] = UInt64.ofNat 196792 → ω1[10] = UInt64.ofNat ((size + 31) / 32) →
      ω1[0] = UInt64.ofNat 1988 →
      ∃ ω2 μ2, FreeStepsH p R 42980 ω1 μ1 x 40805 ω2 μ2 x n ∧ Rep μ2 s' ∧ WF s' ∧ FirstOk s' ∧
        (∀ a, μ2.writable a = μ1.writable a) ∧ (∀ a, a < 4294967296 → sp - 16 ≤ a → μ2.read a = μ1.read a) ∧
        ω2[7] = UInt64.ofNat r ∧ ω2[1] = UInt64.ofNat (sp - 16) ∧ ω2[5] = ω1[5] ∧ ω2[6] = ω1[6] ∧
        (∀ a, OthersData s ptr a → μ2.read a = μ1.read a)) :
    ∃ ω' μ', FreeStepsH p R 40701 ω μ x 40821 ω' μ' x (n + 45) ∧ Rep μ' s' ∧ WF s' ∧ FirstOk s' ∧
      ω'[7] = UInt64.ofNat r ∧ rdN μ' 206848 1 = 0 ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      (∀ a, OthersData s ptr a → μ'.read a = μ.read a) := by
  obtain ⟨ω1, μ1, r1, a1, a8, a7, -, a10, a0, a5, -, st8, st16, fr1, ww1, g1⟩ :=
    rw_lock (p := p) (P := P) (R := R) x ω μ sp ptr al size h1 h7 h9 h10 hp0 hp1 hal hs hsp hsp1 hl hH
      hS hw
  have rep1 : Rep μ1 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 =>
    fr1 a (by omega) (Or.inl (by omega)) (Or.inr (by unfold A0 at ha1; omega)) ha3
  obtain ⟨ω2, μ2, r2, rep2, hwf', hfo', ww2, stk2, e7, e1, e5, e6, kp2⟩ := impl ω1 μ1 rep1 (hw.of_eq ww1) a1 a8 a7 a10 a0
  obtain ⟨ω3, μ3, r3, c0, c5, c1, cl, fr3, ww3, g3⟩ :=
    rw_unlock (p := p) (P := P) (R := R) x ω2 μ2 (sp - 16) e1 (by rw [e5, a5]) (by omega) (by omega) hH
      ⟨by omega, by omega⟩ ((hw.of_eq ww1).of_eq ww2)
  refine ⟨ω3, μ3, ((r1.trans r2).trans r3).mono (by omega),
    rep2.congr_lock hwf' (by rw [hb']; exact hb0) (by rw [hb']; exact hbT)
      (fun a ha1 ha2 ha3 => fr3 a (by omega) (by omega)), hwf', hfo',
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
  · intro a ha
    obtain ⟨hl1, hl2⟩ := others_lt hwf hb0 hbT ha
    rw [fr3 a (by omega) (by omega), kp2 a ha]
    exact fr1 a (by omega) (Or.inl (by omega)) (Or.inr (by omega)) (Or.inr (by omega))

theorem realloc_zero_keep {p : ByteArray} {P : Program} [HasCode p P] {X : Type} {R : HostRel X} (x : X) (ω : Regs) (μ : Memory)
    {grow : Grow} {hb : Nat} (s : State) (sp ptr align : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hu : usable s ptr ≠ 0)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr) (h7 : ω[7] = UInt64.ofNat 196792)
    (h10 : ω[10] = UInt64.ofNat 0) (h0 : ω[0] = UInt64.ofNat 1988)
    (hsp : 2147483852 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648)
    (hfo : FirstOk s) {HT S0 S1 : Nat} (hHT : s.base + 32 * s.allocated ≤ HT) (hS : S0 + 176 ≤ sp ∧ sp ≤ S1)
    (hw : WrAt μ HT S0 S1) :
    realloc grow hb s ptr align 0 = some (0, free s ptr, false) ∧
      ∃ ω' μ', FreeStepsH p R 42980 ω μ x 40805 ω' μ' x 250 ∧ Rep μ' (free s ptr) ∧ WF (free s ptr) ∧
        FirstOk (free s ptr) ∧
        (∀ a, μ'.writable a = μ.writable a) ∧ (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[7] = UInt64.ofNat 0 ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat sp ∧
        ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ (∀ a, OthersData s ptr a → μ'.read a = μ.read a) := by
  refine ⟨realloc_zero hu, ?_⟩
  obtain ⟨c, hcm, hca, hcu⟩ := hc
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  have hcl := ht.mem_lt c hcm
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hsz : (s.hdr c.addr).size = sizeWord c.size true := by rw [chunks_hdr c hcm, hcu]
  have hca' : c.addr = ptr - 32 := by omega
  have hcT : c.addr + 32 ≤ HT := by
    have hsp' := hwf.2.2.2.2.2.2.2; unfold SpaceOk at hsp'; have := (hsp' c hcm).2; omega
  have hw' : rdN μ (ptr - 28) 4 = 2 * c.size + 1 := by
    rw [show ptr - 28 = c.addr + 4 by omega, hrep.size c hcm, hsz]; unfold sizeWord; simp
  have hus : usable s ptr = c.size - 1 := by
    unfold usable; rw [← hca', hsz, wordSize_sizeWord]
  obtain ⟨ω1, μ1, r1, a1, -, a6, st0, st5, st6, sf1, ww1, g1⟩ := rl_pro (p := p) (P := P) (R := R) x ω μ sp
    ptr (2 * c.size + 1) h1 h8 (by omega) (by omega) hw' (by omega) (by omega) hsp1 ⟨by omega, by omega⟩ ⟨by omega, hS.2⟩ hw
  obtain ⟨ω2, r2, b0, g2⟩ := rl_go_zero (p := p) (P := P) (R := R) x ω1 μ1 ((2 * c.size + 1) / 2 - 1)
    (by rw [fget g1 10 (by decide) (by decide)]; exact h10) a6 (by omega) (by omega)
  have rep1 : Rep μ1 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 =>
    sf1 a (by omega) (Or.inl (by unfold A0 at ha1; omega))
  have hc' : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true := ⟨c, hcm, hca, hcu⟩
  obtain ⟨ω3, μ3, r3, rep3, wf3, fo3, ww3, stk3, c0, c1, c5, c6, hk3⟩ := free_refines_hdr (p := p) (P := P) (R := R)
    x ω2 μ1 s (sp - 152) ptr hwf rep1 hc'
    (by rw [fget g2 1 (by decide) (by decide)]; exact a1)
    (by rw [fget g2 8 (by decide) (by decide), fget g1 8 (by decide) (by decide)]; exact h8)
    (by rw [fget g2 7 (by decide) (by decide), fget g1 7 (by decide) (by decide)]; exact h7)
    (by omega) (by omega) hb0 hbT hfo hHT ⟨by omega, by omega⟩ (hw.of_eq ww1)
  have rj := free_ret_realloc (p := p) (P := P) (R := R) x ω3 μ3 (by rw [c0, b0])
  have ww3' : ∀ a, μ3.writable a = μ.writable a := fun a => (ww3 a).trans (ww1 a)
  have stk : ∀ a, a < 4294967296 → sp - 152 ≤ a → μ3.read a = μ1.read a := stk3
  have rd8 : ∀ a v, μ1.readN a 8 = Num.encodeLE 8 v → v < 18446744073709551616 → sp - 152 ≤ a →
      a + 8 ≤ sp → rdN μ3 a 8 = v := fun a v h hv h1 h2 => by
    rw [rdN_frame (μ := μ1) fun j hj => stk _ (by omega) (by omega)]
    exact rd_enc h hv
  obtain ⟨ω4, r4, e7, -, e0, e1, e5, e6, -⟩ := rl_ret_null (p := p) (P := P) (R := R) x ω3 μ3 (sp - 152)
    ω[5].toNat ω[6].toNat c1 (by omega) (by omega)
    (by rw [rd8 _ _ (by rw [show sp - 152 + 144 = sp - 8 by omega]; exact st0) (UInt64.toNat_lt _) (by omega) (by omega), h0]
        rfl)
    (rd8 _ _ (by rw [show sp - 152 + 136 = sp - 16 by omega]; exact st5) (UInt64.toNat_lt _) (by omega) (by omega))
    (rd8 _ _ (by rw [show sp - 152 + 128 = sp - 24 by omega]; exact st6) (UInt64.toNat_lt _) (by omega) (by omega))
    ⟨by omega, by omega⟩ (hw.of_eq ww3').rd
  refine ⟨ω4, μ3, (((r1.trans r2).trans r3).trans (rj.trans r4)).mono (by omega), rep3, wf3, fo3, ww3',
    fun a h1 h2 => (stk a h1 (by omega)).trans (sf1 a h1 (Or.inr h2)), e7, e0,
    by rw [e1]; congr 1; omega, by rw [e5, UInt64.ofNat_toNat], by rw [e6, UInt64.ofNat_toNat], fun a ha => ?_⟩
  have := others_lt hwf hb0 hbT ha
  rw [keep_of_hkeep hwf hb0 hbT (fun h hh => Or.inl hh) hk3.hkeep a ha]
  exact sf1 a (by omega) (Or.inl (by omega))

theorem realloc_wrap_zero_keep {p : ByteArray} {P : Program} [HasCode p P] {X : Type} {R : HostRel X} (x : X) (ω : Regs) (μ : Memory)
    {grow : Grow} {hb : Nat} (s : State) (sp ptr al : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hu : usable s ptr ≠ 0)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat 0) (hal : al + 31 < 68719476736)
    (hsp : 2147483868 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648)
    (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0) {HT S0 S1 : Nat} (hHT : s.base + 32 * s.allocated ≤ HT)
    (hS : S0 + 192 ≤ sp ∧ sp ≤ S1) (hw : WrAt μ HT S0 S1) :
    realloc grow hb s ptr ((al + 31) / 32) 0 = some (0, free s ptr, false) ∧
      ∃ ω' μ', FreeStepsH p R 40701 ω μ x 40821 ω' μ' x 295 ∧ Rep μ' (free s ptr) ∧ WF (free s ptr) ∧
        FirstOk (free s ptr) ∧
        ω'[7] = UInt64.ofNat 0 ∧ rdN μ' 206848 1 = 0 ∧ (∀ a, μ'.writable a = μ.writable a) ∧
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
        (∀ a, OthersData s ptr a → μ'.read a = μ.read a) := by
  have hc' := hc
  obtain ⟨c, hcm, hca, -⟩ := hc'
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  have hcl := ht.mem_lt c hcm
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  refine ⟨realloc_zero hu, ?_⟩
  exact realloc_wrap_keep0 (p := p) (P := P) (R := R) x ω μ s (free s ptr) sp ptr al 0 0 250 hwf hrep
    free_base' h1 h7 h9 h10 (by omega) (by omega) hal (by omega) (by omega) hsp1 hb0 hbT hl
    (by omega) ⟨by omega, by omega⟩ hw (fun ω1 μ1 rep1 W1 a1 a8 a7 a10 a0 => by
      obtain ⟨-, ω2, μ2, run, rep, wf, fo, ww, stk, e7, -, e1, e5, e6, kp⟩ :=
        realloc_zero_keep (grow := grow) (hb := hb) (p := p) (P := P) (R := R) x ω1 μ1 s (sp - 16) ptr
          ((al + 31) / 32) hwf rep1 hc hu a1 a8 a7 (by rw [a10]) a0 (by omega) (by omega)
          hb0 hbT hfo hHT ⟨by omega, by omega⟩ W1
      exact ⟨ω2, μ2, run, rep, wf, fo, ww, stk, e7, e1, e5, e6, kp⟩)

theorem fallback_after_keep {p : ByteArray} {P : Program} [HasCode p P] {X : Type} {R : HostRel X} (x : X) (ω : Regs) (μ : Memory)
    (s1 : State) (sp ptr q u r v5 v6 : Nat) (hwf1 : WF s1) (hrep : Rep μ s1) (hfo1 : FirstOk s1)
    (hc : ∃ c ∈ chunks s1, c.addr + 32 = ptr ∧ c.used = true ∧ c.size = u + 1 ∧
      (c.addr + 32 * c.size ≤ q - 32 ∨ q - 32 + 32 * (r + 1) ≤ c.addr))
    (hnew : (⟨q - 32, r + 1, true⟩ : Chunk) ∈ chunks s1) (hq32 : 32 ≤ q) (hur : u ≤ r)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat q) (h5 : ω[5] = UInt64.ofNat ptr)
    (h6 : ω[6] = UInt64.ofNat u) (h104 : rdN μ (sp + 104) 8 = 196792)
    (s0 : rdN μ (sp + 144) 8 = 1988) (s5 : rdN μ (sp + 136) 8 = v5) (s6 : rdN μ (sp + 128) 8 = v6)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp + 152 < 4294967296) (hsp8 : sp % 8 = 0) (hba : s1.base % 8 = 0)
    (hb0 : 206864 ≤ s1.base) (hbT : s1.base + 1073741824 < 2147483648)
    {HT S0 S1 : Nat} (hHT : s1.base + 32 * s1.allocated ≤ HT)
    (hS : S0 + 152 ≤ sp ∧ sp + 152 ≤ S1) (hw : WrAt μ HT S0 S1) :
    ∃ ω' μ', μ'.readN q (32 * u) = μ.readN ptr (32 * u) ∧
      FreeStepsH p R 43276 ω μ x 40805 ω' μ' x (64 * u + 560) ∧
      Rep μ' (free s1 ptr) ∧ WF (free s1 ptr) ∧ FirstOk (free s1 ptr) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧ (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[7] = UInt64.ofNat q ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat (sp + 152) ∧
      ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 ∧
      (∀ a, OthersData s1 ptr a → (a < q ∨ q + 32 * u ≤ a) → μ'.read a = μ.read a) := by
  obtain ⟨c, hc1, hca, hcu, hcsz, hdis⟩ := hc
  have ht1 := hwf1.2.2.2.1
  unfold TilesOk at ht1
  have htop1 : s1.top = s1.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hcl := ht1.mem_lt c hc1
  have hca' := ht1.aligned c hc1
  have hnl := ht1.mem_lt _ hnew
  have hna := ht1.aligned _ hnew
  simp only at hnl hna
  have hsp1' := hwf1.2.2.2.2.2.2.2
  unfold SpaceOk at hsp1'
  have hnT := (hsp1' _ hnew).1 rfl
  have hcT := (hsp1' c hc1).1 hcu
  simp only at hnT
  -- the copy
  obtain ⟨ω3, r3, c7, c8, c9, c6, c0, g3⟩ := rf_copy (p := p) (P := P) (R := R) x ω μ q u ptr h7 h6 h5
    (by omega) (by omega) (by omega) (by omega)
  obtain ⟨ω4, μ3, r4, d0, d1, d5, d6, dc, dfr, dwr⟩ := rf_memcpy (p := p) (P := P) (R := R)
    x ω3 μ sp q ptr u c0 (by rw [fget g3 1 (by decide) (by decide)]; exact h1) c7 c8 c9 ⟨by omega, by omega, hsp8⟩
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun a h1 h2 => Memory.readable_of_writable (hw a (Or.inl ⟨by omega, by omega⟩)))
    (fun a h1 h2 => hw a (Or.inl ⟨by omega, by omega⟩))
    (fun a h1 h2 => hw a (Or.inr ⟨by omega, by omega⟩))
  have rep3 : Rep μ3 s1 := Rep.congr_data hrep hwf1 hb0 hbT hnew
    (lo := q) (hi := q + 32 * u) (by simp only; omega) (by simp only; omega)
    (fun a ha1 ha2 ha3 => dfr a (by omega) ha3 (Or.inl (by omega)))
  have stk3 : ∀ a, a < 4294967296 → sp ≤ a → μ3.read a = μ.read a := fun a h1 h2 =>
    dfr a h1 (Or.inr (by omega)) (Or.inr h2)
  -- the free of the old chunk
  obtain ⟨ω5, r5, f7, f8, f0, g5⟩ := rf_free_call (p := p) (P := P) (R := R) x ω4 μ3 sp ptr d1
    (by rw [d5, fget g3 5 (by decide) (by decide)]; exact h5)
    (by rw [← h104]; exact rdN_frame fun j hj => stk3 _ (by omega) (by omega)) (by omega) (by omega) hsp1
    ⟨by omega, by omega⟩ ((hw.of_eq dwr).rd)
  obtain ⟨ω6, μ4, r6, rep4, wf4, fo4, ww4, stk4, b0, b1, b5, b6, hk4⟩ := free_refines_hdr (p := p) (P := P) (R := R)
    x ω5 μ3 s1 sp ptr hwf1 rep3 ⟨c, hc1, hca, hcu⟩ (by rw [fget g5 1 (by decide) (by decide)]; exact d1) f8 f7
    (by omega) (by omega) hb0 hbT hfo1 hHT ⟨by omega, by omega⟩ (hw.of_eq dwr)
  have rj2 := free_ret_fallback (p := p) (P := P) (R := R) x ω6 μ4 (by rw [b0, f0])
  have stk : ∀ a, a < 4294967296 → sp ≤ a → μ4.read a = μ.read a := fun a h1 h2 =>
    (stk4 a h1 h2).trans (stk3 a h1 h2)
  have rd : ∀ a v, rdN μ a 8 = v → sp ≤ a → a + 8 ≤ sp + 152 → rdN μ4 a 8 = v := fun a v h h1 h2 => by
    rw [← h]; exact rdN_frame fun j hj => stk _ (by omega) (by omega)
  have W4 := (hw.of_eq dwr).of_eq ww4
  have hq2 : q < 4294967296 := by omega
  obtain ⟨ω7, r7, k7, k0, k1, k5, k6⟩ := rf_ret (p := p) (P := P) (R := R) x ω6 μ4 sp q v5 v6 b1
    (by rw [b6, fget g5 6 (by decide) (by decide), d6, c6]) hq2 (by omega) hsp1
    (rd _ _ s0 (by omega) (by omega)) (rd _ _ s5 (by omega) (by omega)) (rd _ _ s6 (by omega) (by omega)) ⟨by omega, by omega⟩ W4.rd
  have dat : μ4.readN q (32 * u) = μ.readN ptr (32 * u) := by
    rw [← dc]; exact hk4.readN fun j hj => off_hdr_data hwf1 hb0 hbT hnew (by simp only; omega) (by simp only; omega)
  refine ⟨ω7, μ4, dat, (((((r3.trans r4).trans r5).trans r6).trans rj2).trans r7).mono (by omega), rep4, wf4, fo4,
    fun a => (ww4 a).trans (dwr a), stk, k7, k0, k1, k5, k6, fun a ha hq => ?_⟩
  have := others_lt hwf1 hb0 hbT ha
  rw [keep_of_hkeep hwf1 hb0 hbT (fun h hh => Or.inl hh) hk4.hkeep a ha]
  exact dfr a (by omega) hq (Or.inl (by omega))

theorem fallback_tail'_keep {p : ByteArray} {P : Program} [HasCode p P] {X : Type} {R : HostRel X} (x : X) (ω : Regs) (μ : Memory)
    {grow : Grow} {hb : Nat} (s s1 : State) (sp ptr req q u v5 v6 : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hfo : FirstOk s) (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hu : usable s ptr = u) (hur : u < req)
    (h : alloc grow hb 1 req s = some (q, s1)) (hng : s1.allocated = s.allocated)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat ptr)
    (h9 : ω[9] = UInt64.ofNat 1) (h10 : ω[10] = UInt64.ofNat req) (h6 : ω[6] = UInt64.ofNat u)
    (hrq : req < 33554432)
    (s0 : rdN μ (sp + 144) 8 = 1988) (s5 : rdN μ (sp + 136) 8 = v5) (s6 : rdN μ (sp + 128) 8 = v6)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp + 152 < 4294967296) (hsp8 : sp % 8 = 0) (hba : s.base % 8 = 0)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hHT : s.base + 32 * s.allocated ≤ HT)
    (hS : S0 + 152 ≤ sp ∧ sp + 152 ≤ S1) (hw : WrAt μ HT S0 S1) :
    ∃ ω' μ', μ'.readN q (32 * u) = μ.readN ptr (32 * u) ∧
      FreeStepsH p R 43259 ω μ x 40805 ω' μ' x (64 * u + 1000) ∧
      Rep μ' (free s1 ptr) ∧ WF (free s1 ptr) ∧ FirstOk (free s1 ptr) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧ (∀ a, a < 4294967296 → sp + 152 ≤ a → μ'.read a = μ.read a) ∧
      ω'[7] = UInt64.ofNat q ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat (sp + 152) ∧
      ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 ∧
      (∀ a, OthersData s ptr a → μ'.read a = μ.read a) := by
  have hc0 := hc
  obtain ⟨c, hcm, hca, hcu⟩ := hc
  obtain ⟨hkeep, hnew, hq32, hb1⟩ := alloc_keeps hwf h
  obtain ⟨hc1, hdis⟩ := hkeep c hcm hcu
  have hwf1 : WF s1 := alloc_wf hwf h
  have hfo1 : FirstOk s1 := alloc_first hwf hfo h
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  have hcl := ht.mem_lt c hcm
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hcsz : c.size = u + 1 := chunk_size_usable hcm hca hcu hu hcl.2.2
  -- the call to `alloc_impl`
  obtain ⟨ω1, μ1, r1, a5, a8, a9, a10, a0, a104, fr1, ww1, g1⟩ := rf_call (p := p) (P := P) (R := R) x ω μ
    sp ptr 1 req h1 h7 h8 h9 h10 (by omega) (by decide) (by omega) (by omega) hsp1 ⟨by omega, by omega⟩ hw
  have rep1 : Rep μ1 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 => fr1 a (by omega) (Or.inl (by omega))
  obtain ⟨ω2, μ2, r2, rep2, -, e7, e0, e5, e6, e1, ww2, stk2, hk2⟩ :=
    alloc_refines_hdr (p := p) (P := P) (R := R) x ω1 μ1 s s1 sp req q hwf rep1 h hng
      (by rw [fget g1 1 (by decide) (by decide)]; exact h1) (by rw [fget g1 7 (by decide) (by decide)]; exact h7)
      a8 a9 a10 hsp (by omega) hb0 hbT hA hfo hHTs ⟨by omega, by omega⟩ hHT (hw.of_eq ww1)
  have rj := al_ret_realloc (p := p) (P := P) (R := R) x ω2 μ2 (by rw [e0, a0])
  have rd : ∀ a v, rdN μ a 8 = v → sp + 112 ≤ a → a + 8 ≤ sp + 152 → rdN μ2 a 8 = v := fun a v h h1 h2 => by
    rw [← h]; exact rdN_frame fun j hj => (stk2 _ (by omega) (by omega)).trans (fr1 _ (by omega) (Or.inr (by omega)))
  have h104 : rdN μ2 (sp + 104) 8 = 196792 := by
    rw [← a104]; exact rdN_frame fun j hj => stk2 _ (by omega) (by omega)
  obtain ⟨ω3, μ3, dat3, r3, rep3, wf3, fo3, ww3, stk3, k7, k0, k1, k5, k6, kp3⟩ := fallback_after_keep (p := p) (P := P) (R := R)
    x ω2 μ2 s1 sp ptr q u req v5 v6 hwf1 rep2 hfo1 ⟨c, hc1, hca, hcu, hcsz, hdis⟩ hnew hq32 (by omega)
    (by rw [e1, fget g1 1 (by decide) (by decide)]; exact h1) e7 (by rw [e5]; exact a5)
    (by rw [e6, fget g1 6 (by decide) (by decide)]; exact h6) h104
    (rd _ _ s0 (by omega) (by omega)) (rd _ _ s5 (by omega) (by omega)) (rd _ _ s6 (by omega) (by omega))
    hsp hsp1 hsp8 (by rw [hb1]; exact hba) (by rw [hb1]; exact hb0) (by rw [hb1]; exact hbT)
    (by rw [hb1, hng]; exact hHT) hS ((hw.of_eq ww1).of_eq ww2)
  have dat : μ3.readN q (32 * u) = μ.readN ptr (32 * u) := by
    rw [dat3, hk2.readN fun j hj => off_hdr_data hwf1 (by rw [hb1]; exact hb0) (by rw [hb1]; exact hbT) hc1
      (by omega) (by omega)]
    exact readN_congr2 fun j hj => fr1 _ (by omega) (Or.inl (by omega))
  refine ⟨ω3, μ3, dat, (((r1.trans r2).trans rj).trans r3).mono (by omega), rep3, wf3, fo3,
    fun a => (ww3 a).trans ((ww2 a).trans (ww1 a)),
    fun a h1 h2 => ((stk3 a h1 (by omega)).trans (stk2 a h1 (by omega))).trans (fr1 a h1 (Or.inr (by omega))),
    k7, k0, k1, k5, k6, fun a ha => ?_⟩
  obtain ⟨c', hc'm, hc'u, hc'p, hin⟩ := ha
  obtain ⟨hc'1, hc'd⟩ := hkeep c' hc'm hc'u
  have ha1 : OthersData s1 ptr a := ⟨c', hc'1, hc'u, hc'p, hin⟩
  have hbb : s1.base = s.base := hb1
  have := others_lt hwf1 (by rw [hbb]; exact hb0) (by rw [hbb]; exact hbT) ha1
  unfold InData at hin
  rw [kp3 a ha1 (by omega), keep_of_hkeep hwf1 (by rw [hbb]; exact hb0) (by rw [hbb]; exact hbT)
    (fun h hh => Or.inl hh) hk2.hkeep a ha1]
  exact fr1 a (by omega) (Or.inl (by omega))

theorem fallback_tail_heap_keepG {X : Type} {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X) (x : X)
    (ω : Regs) (μ : Memory) {hb : Nat} (s s1 : State) (sp ptr req q u v5 v6 pb ph : Nat) (hwf : WF s)
    (hrep : Rep μ s) (hfo : FirstOk s) (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hu : usable s ptr = u) (hur : u < req)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h : alloc (growTo pb) hb 1 req s = some (q, s1)) (hcost : pagesOf (s.base + 32 * s1.allocated) ≤ ph + 14)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat ptr)
    (h9 : ω[9] = UInt64.ofNat 1) (h10 : ω[10] = UInt64.ofNat req) (h6 : ω[6] = UInt64.ofNat u)
    (hrq : req < 33554432)
    (s0 : rdN μ (sp + 144) 8 = 1988) (s5 : rdN μ (sp + 136) 8 = v5) (s6 : rdN μ (sp + 128) 8 = v6)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp + 152 < 4294967296) (hsp8 : sp % 8 = 0) (hba : s.base % 8 = 0)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 152 ≤ sp ∧ sp + 152 ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', μ'.readN q (32 * u) = μ.readN ptr (32 * u) ∧
      FreeStepsH p (env.rel hostCostMax) 43259 ω μ x 40805 ω' μ' x (64 * u + 1100) ∧
      Rep μ' (free s1 ptr) ∧ WF (free s1 ptr) ∧ FirstOk (free s1 ptr) ∧
      (∃ h', HeapPages μ' 48 pb h' ∧ s1.base + 32 * s1.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → sp + 152 ≤ a → μ'.read a = μ.read a) ∧
      ω'[7] = UInt64.ofNat q ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat (sp + 152) ∧
      ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 ∧
      (∀ a, OthersData s ptr a → μ'.read a = μ.read a) := by
  have hw := HeapPages.wrAt hp hhb hst
  obtain ⟨hkeep, hnew, hq32, hb1⟩ := alloc_keeps hwf h
  by_cases hng : s1.allocated = s.allocated
  · obtain ⟨ω', μ', dat, run, rep, wf, fo, ww, stk, k7, k0, k1, k5, k6, kp⟩ := fallback_tail'_keep (p := p) (P := P)
      (R := env.rel hostCostMax) x ω μ (grow := growTo pb) (hb := hb) s s1 sp ptr req q u v5 v6 hwf hrep hfo hc
      hu hur h hng h1 h7 h8 h9 h10 h6 hrq s0 s5 s6 hsp hsp1 hsp8 hba hb0 hbT hA hHTs hHT hS hw
    exact ⟨ω', μ', dat, run.mono (by omega), rep, wf, fo,
      ⟨ph, HeapPages.of_eq hp ww, by rw [hb1, hng]; exact hHT, Nat.le_refl _, hhb⟩,
      fun a h1 h2 => by rw [ww]; exact hst a h1 h2, stk, k7, k0, k1, k5, k6, kp⟩
  obtain ⟨c, hcm, hca, hcu⟩ := hc
  obtain ⟨hc1, hdis⟩ := hkeep c hcm hcu
  have hwf1 : WF s1 := alloc_wf hwf h
  have hfo1 : FirstOk s1 := alloc_first hwf hfo h
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  have hcl := ht.mem_lt c hcm
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hcsz : c.size = u + 1 := chunk_size_usable hcm hca hcu hu hcl.2.2
  -- the call to `alloc_impl`, which grows the heap
  obtain ⟨ω1, μ1, r1, a5, a8, a9, a10, a0, a104, fr1, ww1, g1⟩ := rf_call (p := p) (P := P)
    (R := env.rel hostCostMax) x ω μ sp ptr 1 req h1 h7 h8 h9 h10 (by omega) (by decide) (by omega) (by omega)
    hsp1 ⟨by omega, by omega⟩ hw
  have rep1 : Rep μ1 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 => fr1 a (by omega) (Or.inl (by omega))
  obtain ⟨ω2, μ2, r2, rep2, -, e7, e0, e5, e6, e1, ⟨h', hpH, hE', hph, hpb⟩, hst2, stk2, hk2⟩ :=
    alloc_refines_grow_hdrG (p := p) (P := P) (S0 := S0) (S1 := S1) env x ω1 μ1 s s1 sp req q pb ph hwf rep1 hbd h48
      hhb hbs h hng (by rw [fget g1 1 (by decide) (by decide)]; exact h1)
      (by rw [fget g1 7 (by decide) (by decide)]; exact h7) a8 a9 a10 hsp (by omega) hb0 hbT hA hfo hcost hHTs
      ⟨by omega, by omega⟩ hSb (HeapPages.of_eq hp ww1) (fun a h1 h2 => by rw [ww1]; exact hst a h1 h2) hHT
  have rj := al_ret_realloc (p := p) (P := P) (R := env.rel hostCostMax) x ω2 μ2 (by rw [e0, a0])
  have rd : ∀ a v, rdN μ a 8 = v → sp + 112 ≤ a → a + 8 ≤ sp + 152 → rdN μ2 a 8 = v := fun a v h h1 h2 => by
    rw [← h]; exact rdN_frame fun j hj => (stk2 _ (by omega) (by omega)).trans (fr1 _ (by omega) (Or.inr (by omega)))
  have h104 : rdN μ2 (sp + 104) 8 = 196792 := by
    rw [← a104]; exact rdN_frame fun j hj => stk2 _ (by omega) (by omega)
  obtain ⟨ω3, μ3, dat3, r3, rep3, wf3, fo3, ww3, stk3, k7, k0, k1, k5, k6, kp3⟩ := fallback_after_keep (p := p) (P := P)
    (R := env.rel hostCostMax) x ω2 μ2 s1 sp ptr q u req v5 v6 hwf1 rep2 hfo1 ⟨c, hc1, hca, hcu, hcsz, hdis⟩ hnew
    hq32 (by omega) (by rw [e1, fget g1 1 (by decide) (by decide)]; exact h1) e7 (by rw [e5]; exact a5)
    (by rw [e6, fget g1 6 (by decide) (by decide)]; exact h6) h104
    (rd _ _ s0 (by omega) (by omega)) (rd _ _ s5 (by omega) (by omega)) (rd _ _ s6 (by omega) (by omega))
    hsp hsp1 hsp8 (by rw [hb1]; exact hba) (by rw [hb1]; exact hb0) (by rw [hb1]; exact hbT)
    hE' hS (HeapPages.wrAt hpH hpb hst2)
  have dat : μ3.readN q (32 * u) = μ.readN ptr (32 * u) := by
    rw [dat3, hk2.readN fun j hj => off_hdr_data hwf1 (by rw [hb1]; exact hb0) (by rw [hb1]; exact hbT) hc1
      (by omega) (by omega)]
    exact readN_congr2 fun j hj => fr1 _ (by omega) (Or.inl (by omega))
  refine ⟨ω3, μ3, dat, (((r1.trans r2).trans rj).trans r3).mono (by omega), rep3, wf3, fo3,
    ⟨h', HeapPages.of_eq hpH ww3, hE', hph, hpb⟩, fun a h1 h2 => by rw [ww3]; exact hst2 a h1 h2,
    fun a h1 h2 => ((stk3 a h1 (by omega)).trans (stk2 a h1 (by omega))).trans (fr1 a h1 (Or.inr (by omega))),
    k7, k0, k1, k5, k6, fun a ha => ?_⟩
  obtain ⟨c', hc'm, hc'u, hc'p, hin⟩ := ha
  obtain ⟨hc'1, hc'd⟩ := hkeep c' hc'm hc'u
  have ha1 : OthersData s1 ptr a := ⟨c', hc'1, hc'u, hc'p, hin⟩
  have hbb : s1.base = s.base := hb1
  have := others_lt hwf1 (by rw [hbb]; exact hb0) (by rw [hbb]; exact hbT) ha1
  unfold InData at hin
  rw [kp3 a ha1 (by omega), keep_of_hkeep hwf1 (by rw [hbb]; exact hb0) (by rw [hbb]; exact hbT)
    (fun h hh => Or.inl hh) hk2.hkeep a ha1]
  exact fr1 a (by omega) (Or.inl (by omega))

/-- `fallback_tail_heap_keepG` for the refine contract (`refineHeap env`). -/
theorem fallback_tail_heap_keep {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (x : RefineCtx)
    (ω : Regs) (μ : Memory) {hb : Nat} (s s1 : State) (sp ptr req q u v5 v6 pb ph : Nat) (hwf : WF s)
    (hrep : Rep μ s) (hfo : FirstOk s) (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hu : usable s ptr = u) (hur : u < req)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h : alloc (growTo pb) hb 1 req s = some (q, s1)) (hcost : pagesOf (s.base + 32 * s1.allocated) ≤ ph + 14)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat ptr)
    (h9 : ω[9] = UInt64.ofNat 1) (h10 : ω[10] = UInt64.ofNat req) (h6 : ω[6] = UInt64.ofNat u)
    (hrq : req < 33554432)
    (s0 : rdN μ (sp + 144) 8 = 1988) (s5 : rdN μ (sp + 136) 8 = v5) (s6 : rdN μ (sp + 128) 8 = v6)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp + 152 < 4294967296) (hsp8 : sp % 8 = 0) (hba : s.base % 8 = 0)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 152 ≤ sp ∧ sp + 152 ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', μ'.readN q (32 * u) = μ.readN ptr (32 * u) ∧
      FreeStepsH p (refineContract env) 43259 ω μ x 40805 ω' μ' x (64 * u + 1100) ∧
      Rep μ' (free s1 ptr) ∧ WF (free s1 ptr) ∧ FirstOk (free s1 ptr) ∧
      (∃ h', HeapPages μ' 48 pb h' ∧ s1.base + 32 * s1.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → sp + 152 ≤ a → μ'.read a = μ.read a) ∧
      ω'[7] = UInt64.ofNat q ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat (sp + 152) ∧
      ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 ∧
      (∀ a, OthersData s ptr a → μ'.read a = μ.read a) :=
  fallback_tail_heap_keepG (p := p) (P := P) (refineHeap env) x ω μ (hb := hb) s s1 sp ptr req q u v5 v6 pb ph hwf hrep hfo hc hu hur hbd h48 hhb hbs h hcost h1 h7 h8 h9 h10 h6 hrq s0 s5 s6 hsp hsp1 hsp8 hba hb0 hbT hA (S0 := S0) (S1 := S1) hHTs hHT hS hSb hp hst

theorem fallback_refines_heap_keepG {X : Type} {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X)
    (x : X) (ω : Regs) (μ : Memory) {hb : Nat} (s s1 : State) (sp ptr req q pb ph : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr : usable s ptr < req) (hr1 : req < 33554431)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (hnone : growInplace (growTo pb) s ptr req = none) (ha : alloc (growTo pb) hb 1 req s = some (q, s1))
    (hcost : pagesOf (s.base + 32 * s1.allocated) ≤ ph + 14)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr) (h7 : ω[7] = UInt64.ofNat 196792)
    (h9 : ω[9] = UInt64.ofNat 1) (h10 : ω[10] = UInt64.ofNat req) (h0 : ω[0] = UInt64.ofNat 1988)
    (hsp : 2147483952 ≤ sp) (hsp1 : sp < 4294967296) (hsp8 : sp % 8 = 0) (hba : s.base % 8 = 0)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 304 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    realloc (growTo pb) hb s ptr 1 req = some (q, free s1 ptr, true) ∧
      ∃ ω' μ', μ'.readN q (32 * usable s ptr) = μ.readN ptr (32 * usable s ptr) ∧
      FreeStepsH p (env.rel hostCostMax) 42980 ω μ x 40805 ω' μ' x (64 * usable s ptr + 1220) ∧
        Rep μ' (free s1 ptr) ∧ WF (free s1 ptr) ∧ FirstOk (free s1 ptr) ∧
        (∃ h', HeapPages μ' 48 pb h' ∧ s1.base + 32 * s1.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
        (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[7] = UInt64.ofNat q ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat sp ∧
        ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ (∀ a, OthersData s ptr a → μ'.read a = μ.read a) := by
  refine ⟨realloc_fallback hr hnone ha, ?_⟩
  obtain ⟨ω1, μ1, r1, rep1, hp1, hst1, fr1, st0, st5, st6, a1, a6, a7, a8, a9, a10⟩ := fallback_entryG
    (p := p) (P := P) env x ω μ s sp ptr req pb ph hwf hrep hc hr hr1 hbd h48 hhb hbs hnone h1 h8 h7 h10
    (by omega) hsp1 hb0 hbT hA hHT ⟨by omega, by omega⟩ hSb hp hst
  have rd : ∀ a v, μ1.readN a 8 = Num.encodeLE 8 v → v < 18446744073709551616 → rdN μ1 a 8 = v :=
    fun a v h hv => rd_enc h hv
  obtain ⟨ω2, μ2, dat2, r2, rep2, wf2, fo2, hpH, hst2, stk2, e7, e0, e1, e5, e6, kp2⟩ := fallback_tail_heap_keepG (p := p)
    (P := P) env x ω1 μ1 (hb := hb) s s1 (sp - 152) ptr req q (usable s ptr) ω[5].toNat ω[6].toNat pb ph hwf
    rep1 hfo hc rfl hr hbd h48 hhb hbs ha hcost a1 a7 a8 (by rw [a9]; exact h9) a10 a6 (by omega)
    (by rw [show sp - 152 + 144 = sp - 8 by omega]; exact (rd _ _ st0 (UInt64.toNat_lt _)).trans (by rw [h0]; rfl))
    (by rw [show sp - 152 + 136 = sp - 16 by omega]; exact rd _ _ st5 (UInt64.toNat_lt _))
    (by rw [show sp - 152 + 128 = sp - 24 by omega]; exact rd _ _ st6 (UInt64.toNat_lt _))
    (by omega) (by omega) (by omega) hba hb0 hbT hA hHTs hHT ⟨by omega, by omega⟩ hSb hp1 hst1
  have hdl := data_lt hwf hbT hc
  have dat : μ2.readN q (32 * usable s ptr) = μ.readN ptr (32 * usable s ptr) := by
    rw [dat2]; exact readN_congr2 fun j hj => fr1 _ (by omega) (Or.inl (by omega))
  refine ⟨ω2, μ2, dat, (r1.trans r2).mono (by omega), rep2, wf2, fo2, hpH, hst2,
    fun a h1 h2 => (stk2 a h1 (by omega)).trans (fr1 a h1 (Or.inr h2)), e7, e0,
    by rw [e1]; congr 1; omega, by rw [e5, UInt64.ofNat_toNat], by rw [e6, UInt64.ofNat_toNat], fun a ha => ?_⟩
  have := others_lt hwf hb0 hbT ha
  rw [kp2 a ha]; exact fr1 a (by omega) (Or.inl (by omega))

/-- `fallback_refines_heap_keepG` for the refine contract (`refineHeap env`). -/
theorem fallback_refines_heap_keep {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (x : RefineCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s s1 : State) (sp ptr req q pb ph : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr : usable s ptr < req) (hr1 : req < 33554431)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (hnone : growInplace (growTo pb) s ptr req = none) (ha : alloc (growTo pb) hb 1 req s = some (q, s1))
    (hcost : pagesOf (s.base + 32 * s1.allocated) ≤ ph + 14)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr) (h7 : ω[7] = UInt64.ofNat 196792)
    (h9 : ω[9] = UInt64.ofNat 1) (h10 : ω[10] = UInt64.ofNat req) (h0 : ω[0] = UInt64.ofNat 1988)
    (hsp : 2147483952 ≤ sp) (hsp1 : sp < 4294967296) (hsp8 : sp % 8 = 0) (hba : s.base % 8 = 0)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 304 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    realloc (growTo pb) hb s ptr 1 req = some (q, free s1 ptr, true) ∧
      ∃ ω' μ', μ'.readN q (32 * usable s ptr) = μ.readN ptr (32 * usable s ptr) ∧
      FreeStepsH p (refineContract env) 42980 ω μ x 40805 ω' μ' x (64 * usable s ptr + 1220) ∧
        Rep μ' (free s1 ptr) ∧ WF (free s1 ptr) ∧ FirstOk (free s1 ptr) ∧
        (∃ h', HeapPages μ' 48 pb h' ∧ s1.base + 32 * s1.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
        (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[7] = UInt64.ofNat q ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat sp ∧
        ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ (∀ a, OthersData s ptr a → μ'.read a = μ.read a) :=
  fallback_refines_heap_keepG (p := p) (P := P) (refineHeap env) x ω μ (hb := hb) s s1 sp ptr req q pb ph hwf hrep hc hr hr1 hbd h48 hhb hbs hnone ha hcost h1 h8 h7 h9 h10 h0 hsp hsp1 hsp8 hba hb0 hbT hA hfo (S0 := S0) (S1 := S1) hHTs hHT hS hSb hp hst

theorem realloc_wrap_fallback_keepG {X : Type} {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X)
    (x : X) (ω : Regs) (μ : Memory) {hb : Nat} (s s1 : State) (sp ptr al size q pb ph : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hr : usable s ptr < (size + 31) / 32) (hr1 : (size + 31) / 32 < 33554431)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (hnone : growInplace (growTo pb) s ptr ((size + 31) / 32) = none)
    (ha : alloc (growTo pb) hb 1 ((size + 31) / 32) s = some (q, s1))
    (hcost : pagesOf (s.base + 32 * s1.allocated) ≤ ph + 14)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hal1 : 1 ≤ al) (hal2 : al ≤ 32)
    (hsp : 2147483968 ≤ sp) (hsp1 : sp < 4294967296) (hsp8 : sp % 8 = 0) (hba : s.base % 8 = 0)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 320 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (q, free s1 ptr, true) ∧
      ∃ ω' μ', μ'.readN q (32 * usable s ptr) = μ.readN ptr (32 * usable s ptr) ∧
      FreeStepsH p (env.rel hostCostMax) 40701 ω μ x 40821 ω' μ' x (64 * usable s ptr + 1270) ∧
        Rep μ' (free s1 ptr) ∧ WF (free s1 ptr) ∧ FirstOk (free s1 ptr) ∧
        ω'[7] = UInt64.ofNat q ∧ rdN μ' 206848 1 = 0 ∧
        (∃ h', HeapPages μ' 48 pb h' ∧ s1.base + 32 * s1.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
        (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
        (∀ a, OthersData s ptr a → μ'.read a = μ.read a) := by
  have hal : (al + 31) / 32 = 1 := by omega
  rw [hal]
  have hc' := hc
  obtain ⟨c, hcm, hca, -⟩ := hc'
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  have hcl := ht.mem_lt c hcm
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hwr := HeapPages.wrAt hp hhb hst
  obtain ⟨ω1, μ1, r1, a1, a8, a7, a9, a10, a0, a5, -, st8, st16, fr1, ww1, g1⟩ :=
    rw_lock (p := p) (P := P) (R := env.rel hostCostMax) x ω μ sp ptr al size h1 h7 h9 h10 (by omega) (by omega)
      (by omega) (by omega) (by omega) hsp1 hl (by omega) ⟨by omega, by omega⟩ hwr
  have rep1 : Rep μ1 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 =>
    fr1 a (by omega) (Or.inl (by omega)) (Or.inr (by unfold A0 at ha1; omega)) ha3
  have hp1 := HeapPages.of_eq hp ww1
  have hst1 : ∀ a, S0 ≤ a → a < S1 → μ1.writable a = true := fun a h1 h2 => by rw [ww1]; exact hst a h1 h2
  obtain ⟨e, ω2, μ2, dat2, r2, rep2, wf2, fo2, ⟨h', hpH, hE', hph, hpb⟩, hst2, stk2, e7, e0, e1, e5, e6, kp2⟩ :=
    fallback_refines_heap_keepG (p := p) (P := P) env x ω1 μ1 (hb := hb) s s1 (sp - 16) ptr ((size + 31) / 32) q pb ph
      hwf rep1 hc hr hr1 hbd h48 hhb hbs hnone ha hcost a1 a8 a7 (by rw [a9, hal]) a10 a0 (by omega) (by omega)
      (by omega) hba hb0 hbT hA hfo hHTs hHT ⟨by omega, by omega⟩ hSb hp1 hst1
  obtain ⟨ω3, μ3, r3, c0, c5, c1, cl, fr3, ww3, g3⟩ :=
    rw_unlock (p := p) (P := P) (R := env.rel hostCostMax) x ω2 μ2 (sp - 16) e1 (by rw [e5, a5]) (by omega)
      (by omega) (by omega) ⟨by omega, by omega⟩ (HeapPages.wrAt hpH hpb hst2)
  have hb' : (free s1 ptr).base = s.base := free_base'.trans (alloc_keeps hwf ha).2.2.2
  have hdl := data_lt hwf hbT hc
  have hq : 206864 ≤ q ∧ q + 32 * usable s ptr < 2147483648 := by
    obtain ⟨-, hnew, hq32, hb1⟩ := alloc_keeps hwf ha
    have ht1 := (alloc_wf hwf ha).2.2.2.1
    unfold TilesOk at ht1
    have := ht1.mem_lt _ hnew
    have htop1 : s1.top = s1.base + 1073741824 := by unfold State.top; rw [maxSize_val]
    simp only at this; omega
  have dat : μ3.readN q (32 * usable s ptr) = μ.readN ptr (32 * usable s ptr) := by
    have e3 : μ3.readN q (32 * usable s ptr) = μ2.readN q (32 * usable s ptr) :=
      readN_congr2 fun j hj => fr3 _ (by omega) (by omega)
    rw [e3, dat2]
    exact readN_congr2 fun j hj => fr1 _ (by omega) (Or.inl (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
  refine ⟨e, ω3, μ3, dat, ((r1.trans r2).trans r3).mono (by omega),
    rep2.congr_lock wf2 (by rw [hb']; exact hb0) (by rw [hb']; exact hbT)
      (fun a ha1 ha2 ha3 => fr3 a (by omega) (by omega)), wf2, fo2,
    by rw [fget g3 7 (by decide) (by decide)]; exact e7, cl,
    ⟨h', HeapPages.of_eq hpH ww3, hE', hph, hpb⟩, fun a h1 h2 => by rw [ww3]; exact hst2 a h1 h2,
    fun a ha1 ha2 => ((fr3 a ha1 (by omega)).trans (stk2 a ha1 (by omega))).trans
      (fr1 a ha1 (Or.inr ha2) (Or.inr (by omega)) (Or.inr (by omega))), ?_, ?_, ?_, ?_, ?_⟩
  · rw [c0, rdN_frame (μ := μ1) fun j hj => stk2 _ (by omega) (by omega), show sp - 16 + 8 = sp - 8 by omega]
    exact rd_restore st8
  · rw [c1, h1]; congr 1; omega
  · rw [c5, rdN_frame (μ := μ1) fun j hj => stk2 _ (by omega) (by omega)]
    exact rd_restore st16
  · rw [fget g3 6 (by decide) (by decide), e6, fget g1 6 (by decide) (by decide)]
  · intro a ha
    obtain ⟨hl1, hl2⟩ := others_lt hwf hb0 hbT ha
    rw [fr3 a (by omega) (by omega), kp2 a ha]
    exact fr1 a (by omega) (Or.inl (by omega)) (Or.inr (by omega)) (Or.inr (by omega))

/-- `realloc_wrap_fallback_keepG` for the refine contract (`refineHeap env`). -/
theorem realloc_wrap_fallback_keep {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (x : RefineCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s s1 : State) (sp ptr al size q pb ph : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hr : usable s ptr < (size + 31) / 32) (hr1 : (size + 31) / 32 < 33554431)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (hnone : growInplace (growTo pb) s ptr ((size + 31) / 32) = none)
    (ha : alloc (growTo pb) hb 1 ((size + 31) / 32) s = some (q, s1))
    (hcost : pagesOf (s.base + 32 * s1.allocated) ≤ ph + 14)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hal1 : 1 ≤ al) (hal2 : al ≤ 32)
    (hsp : 2147483968 ≤ sp) (hsp1 : sp < 4294967296) (hsp8 : sp % 8 = 0) (hba : s.base % 8 = 0)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 320 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (q, free s1 ptr, true) ∧
      ∃ ω' μ', μ'.readN q (32 * usable s ptr) = μ.readN ptr (32 * usable s ptr) ∧
      FreeStepsH p (refineContract env) 40701 ω μ x 40821 ω' μ' x (64 * usable s ptr + 1270) ∧
        Rep μ' (free s1 ptr) ∧ WF (free s1 ptr) ∧ FirstOk (free s1 ptr) ∧
        ω'[7] = UInt64.ofNat q ∧ rdN μ' 206848 1 = 0 ∧
        (∃ h', HeapPages μ' 48 pb h' ∧ s1.base + 32 * s1.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
        (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
        (∀ a, OthersData s ptr a → μ'.read a = μ.read a) :=
  realloc_wrap_fallback_keepG (p := p) (P := P) (refineHeap env) x ω μ (hb := hb) s s1 sp ptr al size q pb ph hwf hrep hc hr hr1 hbd h48 hhb hbs hnone ha hcost h1 h7 h9 h10 hal1 hal2 hsp hsp1 hsp8 hba hb0 hbT hA hfo hl (S0 := S0) (S1 := S1) hHTs hHT hS hSb hp hst

open Services.Bootstrap.Decode.ReallocOk Services.Bootstrap.Decode.VecU8 in
/-- **`realloc_wrap_cases_hdataG`, keeping the other chunks' data**: as `realloc_wrap_cases_hdataG`, and
    whenever the model's `realloc` returns a block, every octet of the data of an allocated chunk of
    `s` other than ptr's is as it was. -/
theorem realloc_wrap_cases_keepG {X : Type} {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X)
    (x : X) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (sp ptr al size pb ph : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hr1 : (size + 31) / 32 < 33554431) (hz : size = 0 → usable s ptr ≠ 0)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (hcost : pb ≤ ph + 14)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hal1 : 1 ≤ al) (hal2 : al ≤ 32)
    (hsp : 2147483968 ≤ sp) (hsp1 : sp < 4294967296) (hsp8 : sp % 8 = 0) (hba : s.base % 8 = 0)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 320 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', (∀ r s' b, realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (r, s', b) →
        r ≠ 0 → μ'.readN r (32 * min (usable s ptr) ((size + 31) / 32)) =
          μ.readN ptr (32 * min (usable s ptr) ((size + 31) / 32))) ∧
      (∀ r s' b, realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (r, s', b) →
        r ≠ ptr → r ≠ 0 → μ'.readN r (32 * usable s ptr) = μ.readN ptr (32 * usable s ptr)) ∧
      FreeStepsH p (env.rel hostCostMax) 40701 ω μ x 40821 ω' μ' x (64 * usable s ptr + 1300) ∧
      rdN μ' 206848 1 = 0 ∧ (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      (∀ r s' b, realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (r, s', b) →
        ω'[7] = UInt64.ofNat r ∧ Rep μ' s' ∧ WF s' ∧ FirstOk s' ∧ s'.base = s.base ∧
        ∃ h', HeapPages μ' 48 pb h' ∧ s'.base + 32 * s'.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
      (realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = none →
        ω'[7] = UInt64.ofNat 0 ∧ Rep μ' s ∧ HeapPages μ' 48 pb ph) ∧
      (∀ r s' b, realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (r, s', b) →
        ∀ a, OthersData s ptr a → μ'.read a = μ.read a) := by
  have hwr := HeapPages.wrAt hp hhb hst
  have hal : al + 31 < 68719476736 := by omega
  by_cases hin : (size + 31) / 32 ≤ usable s ptr ∧ size ≠ 0
  · -- in place (the same usable size, or shrunk)
    obtain ⟨s', e, ω', μ', dat, run, rep, wf, fo, e7, cl, ww, stk, e0, e1, e5, e6, kp⟩ :=
      realloc_wrap_inplace_keep (p := p) (P := P) (R := env.rel hostCostMax) (grow := growTo pb) (hb := hb) x ω μ s sp ptr al size hwf hrep hc
        hin.2 hin.1 h1 h7 h9 h10 hal (by omega) (by omega) hsp1 hb0 hbT hfo hl hHT ⟨by omega, by omega⟩ hwr
    exact ⟨ω', μ',
      fun r s'' b hrr _ => by rw [e] at hrr; cases hrr; rw [Nat.min_eq_right hin.1]; exact dat,
      fun r s'' b hrr hn1 _ => by rw [e] at hrr; cases hrr; exact absurd rfl hn1,
      run.mono (by omega), cl, fun a h1 h2 => by rw [ww]; exact hst a h1 h2, stk, e0, e1, e5, e6,
      fun r s'' b hrr => by
        rw [e] at hrr; cases hrr; obtain ⟨eb, ea⟩ := realloc_inplace_state hin.1 (by omega) e; exact ⟨e7, rep, wf, fo, eb, ph, HeapPages.of_eq hp ww, by rw [eb, ea]; exact hHT, Nat.le_refl _, hhb⟩,
      fun hrr => (by rw [e] at hrr; cases hrr), fun _ _ _ _ => kp⟩
  by_cases hs0 : size = 0
  · -- to size 0: freed, null
    subst hs0
    obtain ⟨e, ω', μ', run, rep, wf, fo, e7, cl, ww, stk, e0, e1, e5, e6, kp⟩ :=
      realloc_wrap_zero_keep (p := p) (P := P) (R := env.rel hostCostMax) (grow := growTo pb) (hb := hb) x ω μ s sp ptr al hwf hrep hc
        (hz rfl) h1 h7 h9 h10 hal (by omega) hsp1 hb0 hbT hfo hl hHT ⟨by omega, by omega⟩ hwr
    exact ⟨ω', μ',
      fun r s'' b hrr hn => by
        rw [show (0 + 31) / 32 = 0 from rfl, e] at hrr; cases hrr; exact absurd rfl hn,
      fun r s'' b hrr _ hn2 => by
        rw [show (0 + 31) / 32 = 0 from rfl, e] at hrr; cases hrr; exact absurd rfl hn2,
      run.mono (by omega), cl, fun a h1 h2 => by rw [ww]; exact hst a h1 h2, stk, e0, e1, e5, e6,
      fun r s'' b hrr => by
        rw [show (0 + 31) / 32 = 0 from rfl, e] at hrr; cases hrr
        exact ⟨e7, rep, wf, fo, free_base', ph, HeapPages.of_eq hp ww, by rw [free_base', free_allocated]; exact hHT, Nat.le_refl _, hhb⟩,
      fun hrr => (by rw [show (0 + 31) / 32 = 0 from rfl, e] at hrr; cases hrr), fun _ _ _ _ => kp⟩
  have hr : usable s ptr < (size + 31) / 32 := by omega
  cases hg : growInplace (growTo pb) s ptr ((size + 31) / 32) with
  | some s' =>
    by_cases hng : s'.allocated = s.allocated
    · -- grown in place
      obtain ⟨e, ω', μ', dat, run, rep, wf, fo, e7, cl, ww, stk, e0, e1, e5, e6, kp⟩ :=
        realloc_wrap_grow_keep (p := p) (P := P) (R := env.rel hostCostMax) (hb := hb) x ω μ s s' sp ptr al size hwf hrep hc hr hr1 hg hng
          h1 h7 h9 h10 hal (by omega) hsp1 hb0 hbT hA hfo hl hHT ⟨by omega, by omega⟩ hwr
      exact ⟨ω', μ',
      fun r s'' b hrr _ => by rw [e] at hrr; cases hrr; rw [Nat.min_eq_left (Nat.le_of_lt hr)]; exact dat,
      fun r s'' b hrr hn1 _ => by rw [e] at hrr; cases hrr; exact absurd rfl hn1,
      run.mono (by omega), cl, fun a h1 h2 => by rw [ww]; exact hst a h1 h2, stk, e0, e1, e5, e6,
        fun r s'' b hrr => by
          rw [e] at hrr; cases hrr; exact ⟨e7, rep, wf, fo, growInplace_base hg, ph, HeapPages.of_eq hp ww, by rw [growInplace_base hg, hng]; exact hHT, Nat.le_refl _, hhb⟩,
        fun hrr => (by rw [e] at hrr; cases hrr), fun _ _ _ _ => kp⟩
    · -- grown in place, the heap grown
      obtain ⟨e, ω', μ', dat, run, rep, wf, fo, e7, cl, ⟨h', hpH, hB, hph, hpb⟩, hst', stk, e0, e1, e5, e6, kp⟩ :=
        realloc_wrap_grow_heap_keepG (p := p) (P := P) (hb := hb) env x ω μ s s' sp ptr al size hwf hrep hc hr hr1 pb ph hbd h48 hhb hbs hg
          hng h1 h7 h9 h10 hal (by omega) hsp1 hb0 hbT hA hfo
          (Nat.le_trans (growInplace_pages hr hg hng) hcost) hl hHT ⟨by omega, by omega⟩ hSb hp hst
      exact ⟨ω', μ',
      fun r s'' b hrr _ => by rw [e] at hrr; cases hrr; rw [Nat.min_eq_left (Nat.le_of_lt hr)]; exact dat,
      fun r s'' b hrr hn1 _ => by rw [e] at hrr; cases hrr; exact absurd rfl hn1,
      run.mono (by omega), cl, hst', stk, e0, e1, e5, e6,
        fun r s'' b hrr => by rw [e] at hrr; cases hrr; exact ⟨e7, rep, wf, fo, growInplace_base hg, h', hpH, hB, hph, hpb⟩,
        fun hrr => (by rw [e] at hrr; cases hrr), fun _ _ _ _ => kp⟩
  | none =>
    cases ha : alloc (growTo pb) hb 1 ((size + 31) / 32) s with
    | some qs =>
      obtain ⟨q, s1⟩ := qs
      have hc1 : pagesOf (s.base + 32 * s1.allocated) ≤ ph + 14 := by
        by_cases hng : s1.allocated = s.allocated
        · rw [hng]; exact Nat.le_trans (pagesOf_le hHT) (by omega)
        · exact Nat.le_trans (alloc_pages hwf ha hng) hcost
      obtain ⟨e, ω', μ', dat, run, rep, wf, fo, e7, cl, ⟨h', hpH, hB, hph, hpb⟩, hst', stk, e0, e1, e5, e6, kp⟩ :=
        realloc_wrap_fallback_keepG (p := p) (P := P) (hb := hb) env x ω μ s s1 sp ptr al size q pb ph hwf hrep hc hr hr1 hbd h48 hhb hbs hg
          ha hc1 h1 h7 h9 h10 hal1 hal2 hsp hsp1 hsp8 hba hb0 hbT hA hfo hl hHTs hHT hS hSb hp hst
      exact ⟨ω', μ',
      fun r s'' b hrr _ => by rw [e] at hrr; cases hrr; rw [Nat.min_eq_left (Nat.le_of_lt hr)]; exact dat,
      fun r s'' b hrr _ _ => by rw [e] at hrr; cases hrr; exact dat,
      run.mono (by omega), cl, hst', stk, e0, e1, e5, e6,
        fun r s'' b hrr => by rw [e] at hrr; cases hrr; exact ⟨e7, rep, wf, fo, by rw [free_base', (alloc_block hwf hbT ha).1], h', hpH, by rw [free_base', free_allocated]; exact hB, hph, hpb⟩,
        fun hrr => (by rw [e] at hrr; cases hrr), fun _ _ _ _ => kp⟩
    | none =>
      obtain ⟨e, ω', μ', run, rep, e7, cl, hp', hst', fr, -, e0, e1, e5, e6⟩ :=
        realloc_wrap_fallback_failG (p := p) (P := P) (hb := hb) env x ω μ s sp ptr al size pb ph hwf hrep hc hr hr1 hbd h48 hhb hbs hg
          ha h1 h7 h9 h10 hal1 hal2 hsp hsp1 hb0 hbT hA hl hHTs hHT hS hSb hp hst
      exact ⟨ω', μ',
      fun r s'' b hrr => (by rw [e] at hrr; cases hrr),
      fun r s'' b hrr => (by rw [e] at hrr; cases hrr),
      run.mono (by omega), cl, hst',
        fun a h1 h2 => fr a h1 (Or.inr h2) (Or.inr (by omega)) (Or.inr (by omega)), e0, e1, e5, e6,
        fun r s'' b hrr => (by rw [e] at hrr; cases hrr), fun _ => ⟨e7, rep, hp'⟩,
        fun r s'' b hrr => (by rw [e] at hrr; cases hrr)⟩

open Services.Bootstrap.Decode.ReallocOk Services.Bootstrap.Decode.VecU8 in
/-- `realloc_wrap_cases_keepG` for the refine contract (`refineHeap env`). -/
theorem realloc_wrap_cases_keep {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (x : RefineCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (sp ptr al size pb ph : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hr1 : (size + 31) / 32 < 33554431) (hz : size = 0 → usable s ptr ≠ 0)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (hcost : pb ≤ ph + 14)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hal1 : 1 ≤ al) (hal2 : al ≤ 32)
    (hsp : 2147483968 ≤ sp) (hsp1 : sp < 4294967296) (hsp8 : sp % 8 = 0) (hba : s.base % 8 = 0)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 320 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', (∀ r s' b, realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (r, s', b) →
        r ≠ 0 → μ'.readN r (32 * min (usable s ptr) ((size + 31) / 32)) =
          μ.readN ptr (32 * min (usable s ptr) ((size + 31) / 32))) ∧
      (∀ r s' b, realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (r, s', b) →
        r ≠ ptr → r ≠ 0 → μ'.readN r (32 * usable s ptr) = μ.readN ptr (32 * usable s ptr)) ∧
      FreeStepsH p (refineContract env) 40701 ω μ x 40821 ω' μ' x (64 * usable s ptr + 1300) ∧
      rdN μ' 206848 1 = 0 ∧ (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      (∀ r s' b, realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (r, s', b) →
        ω'[7] = UInt64.ofNat r ∧ Rep μ' s' ∧ WF s' ∧ FirstOk s' ∧ s'.base = s.base ∧
        ∃ h', HeapPages μ' 48 pb h' ∧ s'.base + 32 * s'.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
      (realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = none →
        ω'[7] = UInt64.ofNat 0 ∧ Rep μ' s ∧ HeapPages μ' 48 pb ph) ∧
      (∀ r s' b, realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (r, s', b) →
        ∀ a, OthersData s ptr a → μ'.read a = μ.read a) :=
  realloc_wrap_cases_keepG (p := p) (P := P) (refineHeap env) x ω μ (hb := hb) s sp ptr al size pb ph hwf hrep hc hr1 hz hbd h48 hhb hbs hcost h1 h7 h9 h10 hal1 hal2 hsp hsp1 hsp8 hba hb0 hbT hA hfo hl (S0 := S0) (S1 := S1) hHTs hHT hS hSb hp hst


end Services.Bootstrap.Decode.ReallocKeepAll
