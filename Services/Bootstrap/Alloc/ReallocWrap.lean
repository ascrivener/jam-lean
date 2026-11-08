import Services.Bootstrap.Alloc.ReallocGrowRefines
import Services.Bootstrap.Alloc.ReallocInplace
import Services.Bootstrap.Alloc.ReallocZero
import Services.Bootstrap.Alloc.Dealloc

/-!
# The binary's `realloc`

`realloc` (40701): ω₇ the data address, ω₉ the alignment and ω₁₀ the new size, in octets. A null
address, or an alignment or size above 2³⁷ − 32, gives null at once. Otherwise it takes the
allocator's lock (as `dealloc` does), calls `realloc_impl` (42980, returning to 40805) with the
address, the alignment and the size in 32-octet units, and clears the lock.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- `growInplace` keeps the heap's base. -/
theorem growInplace_base {grow : Grow} {s s' : State} {ptr req : Nat}
    (h : growInplace grow s ptr req = some s') : s'.base = s.base := by
  unfold growInplace at h
  simp only [bind, Option.bind, pure] at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; simp [freeFinal_base]; done)
    | (simp at h; done)
    | skip
  all_goals
    rename_i a hq
    have ha : a.base = s.base := by split at hq <;> cases hq <;> rfl
    simp only at h; cases h; simp [freeFinal_base, ha]

/-- **40701 … 40724, a null address**: null at once, nothing written. -/
theorem rw_null_ptr {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (h7 : ω[7] = UInt64.ofNat 0) :
    ∃ ω', FreeStepsH p R 40701 ω μ x 40724 ω' μ x 2 ∧ ω'[7] = UInt64.ofNat 0 ∧
      ∀ j : Fin 13, j.val ∉ [7] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h7]
  case post => exact ⟨by reg_val, by reg_frame⟩

/-- **40701 … 40724, an alignment or size above 2³⁷ − 32**: null at once, nothing written. -/
theorem rw_null_big {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (ptr al size : Nat) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hp0 : ptr ≠ 0) (hp1 : ptr < 4294967296)
    (hal : al < 18446744073709551616) (hs : size < 18446744073709551616)
    (hbig : 137438953440 < al ∨ 137438953440 < size) :
    ∃ ω', FreeStepsH p R 40701 ω μ x 40724 ω' μ x 6 ∧ ω'[7] = UInt64.ofNat 0 ∧
      ∀ j : Fin 13, j.val ∉ [7, 8] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  by_cases ha : 137438953440 < al
  · refine ⟨?ω', ?run, ?post⟩
    case run => pvm_go [h7, h9, hp0, ha]
    case post => exact ⟨by reg_val, by reg_frame⟩
  · have hs' : ¬ 137438953440 ≥ size := by omega
    refine ⟨?ω', ?run, ?post⟩
    case run => pvm_go [h7, h9, h10, hp0, ha, hs']
    case post => exact ⟨by reg_val, by reg_frame⟩

/-- **40701 … 42980**: the bounds, the frame, the lock taken, the units, and the call. -/
theorem rw_lock {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp ptr al size : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr)
    (h9 : ω[9] = UInt64.ofNat al) (h10 : ω[10] = UInt64.ofNat size) (hp0 : ptr ≠ 0)
    (hp1 : ptr < 4294967296) (hal : al + 31 < 68719476736) (hs : size + 31 < 68719476736)
    (hsp : 2147483716 ≤ sp) (hsp1 : sp < 4294967296)
    (hl : rdN μ 206848 1 = 0) {HT S0 S1 : Nat} (hH : 206864 ≤ HT) (hS : S0 + 16 ≤ sp ∧ sp ≤ S1)
    (hwr : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 40701 ω μ x 42980 ω' μ' x 40 ∧
      ω'[1] = UInt64.ofNat (sp - 16) ∧ ω'[8] = UInt64.ofNat ptr ∧ ω'[7] = UInt64.ofNat 196792 ∧
      ω'[9] = UInt64.ofNat ((al + 31) / 32) ∧ ω'[10] = UInt64.ofNat ((size + 31) / 32) ∧
      ω'[0] = UInt64.ofNat 1988 ∧ ω'[5] = UInt64.ofNat 196792 ∧ ω'[4] = ω[4] ∧
      μ'.readN (sp - 8) 8 = Num.encodeLE 8 ω[0].toNat ∧ μ'.readN (sp - 16) 8 = Num.encodeLE 8 ω[5].toNat ∧
      (∀ a, a < 4294967296 → (a < sp - 16 ∨ sp ≤ a) → (a < 196608 ∨ 196616 ≤ a) →
        (a < 206848 ∨ 206852 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧
      ∀ j : Fin 13, j.val ∉ [0, 1, 4, 5, 7, 8, 9, 10, 11, 12] → ω'[j] = ω[j] := by
  have hr := hwr.rd
  have hand := lock_test (w := rdN μ 206848 4) (by rw [rdN4_mod]; exact hl)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h7, h9, h10, hp0, hand, show ¬ 137438953440 < al by omega,
    show 137438953440 ≥ size by omega, hwr, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, by reg_val, by reg_val, ?_, ?_, by reg_val, by reg_val, ?_, ?_, ?_,
      fun a ha h1 h2 h3 => ?_, fun a => ?_, by reg_frame⟩
    · reg_val
    · reg_val
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some',
        List.lookup_nil, Option.getD_none]
      rd_simp []
      simp
    · rw [show sp - 8 = sp - 16 + 8 by omega]; rd_simp []; rfl
    · rd_simp []; rfl
    · rd_simp []
    · rd_simp [hwr]

/-- **40805 … 40821**: the lock byte cleared, the frame popped; at the return's `jumpInd`. -/
theorem rw_unlock {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat 196792)
    (hsp : 2147483648 ≤ sp) (hsp1 : sp + 16 < 4294967296) {HT S0 S1 : Nat} (hH : 206864 ≤ HT)
    (hS : S0 ≤ sp ∧ sp + 16 ≤ S1) (hwr : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 40805 ω μ x 40821 ω' μ' x 5 ∧
      ω'[0] = UInt64.ofNat (rdN μ (sp + 8) 8) ∧ ω'[5] = UInt64.ofNat (rdN μ sp 8) ∧
      ω'[1] = UInt64.ofNat (sp + 16) ∧ rdN μ' 206848 1 = 0 ∧
      (∀ a, a < 4294967296 → a ≠ 206848 → μ'.read a = μ.read a) ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      ∀ j : Fin 13, j.val ∉ [0, 1, 5, 8] → ω'[j] = ω[j] := by
  have hr := hwr.rd
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, hwr, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, by reg_val, by reg_val, ?_, fun a ha ha' => ?_, fun a => ?_, by reg_frame⟩
    · rd_simp []; rfl
    · rd_simp []
    · rd_simp [hwr]

/-- **`realloc` around a refinement of `realloc_impl`**: when every run of `realloc_impl` (42980)
    from memory holding `s`, with the lock's frame, returns into `realloc` (40805) with memory
    holding `s'` and ω₇ = r, `realloc` (40701) reaches its return (the `jumpInd` at 40821) with
    ω₇ = r, memory holding `s'`, the lock byte clear again, the caller's ω₀, ω₁, ω₅, ω₆ restored and
    the stack from sp up untouched. -/
theorem realloc_wrap {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
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
        ω2[7] = UInt64.ofNat r ∧ ω2[1] = UInt64.ofNat (sp - 16) ∧ ω2[5] = ω1[5] ∧ ω2[6] = ω1[6]) :
    ∃ ω' μ', FreeStepsH p R 40701 ω μ x 40821 ω' μ' x (n + 45) ∧ Rep μ' s' ∧ WF s' ∧ FirstOk s' ∧
      ω'[7] = UInt64.ofNat r ∧ rdN μ' 206848 1 = 0 ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  obtain ⟨ω1, μ1, r1, a1, a8, a7, -, a10, a0, a5, -, st8, st16, fr1, ww1, g1⟩ :=
    rw_lock (p := p) (P := P) (R := R) x ω μ sp ptr al size h1 h7 h9 h10 hp0 hp1 hal hs hsp hsp1 hl hH
      hS hw
  have rep1 : Rep μ1 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 =>
    fr1 a (by omega) (Or.inl (by omega)) (Or.inr (by unfold A0 at ha1; omega)) ha3
  obtain ⟨ω2, μ2, r2, rep2, hwf', hfo', ww2, stk2, e7, e1, e5, e6⟩ := impl ω1 μ1 rep1 (hw.of_eq ww1) a1 a8 a7 a10 a0
  obtain ⟨ω3, μ3, r3, c0, c5, c1, cl, fr3, ww3, g3⟩ :=
    rw_unlock (p := p) (P := P) (R := R) x ω2 μ2 (sp - 16) e1 (by rw [e5, a5]) (by omega) (by omega) hH
      ⟨by omega, by omega⟩ ((hw.of_eq ww1).of_eq ww2)
  refine ⟨ω3, μ3, ((r1.trans r2).trans r3).mono (by omega),
    rep2.congr_lock hwf' (by rw [hb']; exact hb0) (by rw [hb']; exact hbT)
      (fun a ha1 ha2 ha3 => fr3 a (by omega) (by omega)), hwf', hfo',
    by rw [fget g3 7 (by decide) (by decide)]; exact e7, cl, fun a => (ww3 a).trans ((ww2 a).trans (ww1 a)),
    fun a ha1 ha2 => ((fr3 a ha1 (by omega)).trans (stk2 a ha1 (by omega))).trans
      (fr1 a ha1 (Or.inr ha2) (Or.inr (by omega)) (Or.inr (by omega))), ?_, ?_, ?_, ?_⟩
  · rw [c0, rdN_frame (μ := μ1) fun j hj => stk2 _ (by omega) (by omega), show sp - 16 + 8 = sp - 8 by omega]
    unfold rdN; rw [st8, Num.decodeLE_encodeLE]
    rw [Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]
  · rw [c1, h1]; congr 1; omega
  · rw [c5, rdN_frame (μ := μ1) fun j hj => stk2 _ (by omega) (by omega)]
    unfold rdN; rw [st16, Num.decodeLE_encodeLE]
    rw [Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]
  · rw [fget g3 6 (by decide) (by decide), e6, fget g1 6 (by decide) (by decide)]

/-- **The binary's `realloc` refines the model's `realloc`, in place**: from memory holding a
    well-formed `s` (its first chunk's `prev` 0), the lock byte clear, ω₇ the data address of an
    allocated chunk, ω₉ = `al` and ω₁₀ = `size` octets with `⌈size/32⌉` units nonzero and at most
    the usable size, the model's `realloc` keeps the address, and `realloc` (40701) reaches its
    return (the `jumpInd` at 40821) with ω₇ = ptr, memory holding the model's result, the lock byte
    clear again, the caller's ω₀, ω₁, ω₅, ω₆ restored and the stack from sp up untouched. -/
theorem realloc_wrap_inplace {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
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
      ∃ ω' μ', FreeStepsH p R 40701 ω μ x 40821 ω' μ' x 225 ∧ Rep μ' s' ∧ WF s' ∧ FirstOk s' ∧
        ω'[7] = UInt64.ofNat ptr ∧ rdN μ' 206848 1 = 0 ∧ (∀ a, μ'.writable a = μ.writable a) ∧
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have hq0 : (size + 31) / 32 ≠ 0 := by omega
  have hc' := hc
  obtain ⟨c, hcm, hca, -⟩ := hc'
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  have hcl := ht.mem_lt c hcm
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  refine ⟨_, realloc_inplace hq0 hr, ?_⟩
  exact realloc_wrap (p := p) (P := P) (R := R) x ω μ s _ sp ptr al size ptr 180 hwf hrep
    (by split <;> simp [shrink_base]) h1 h7 h9 h10 (by omega) (by omega) hal hs (by omega) hsp1 hb0 hbT hl
    (by omega) ⟨by omega, by omega⟩ hw (fun ω1 μ1 rep1 W1 a1 a8 a7 a10 a0 => by
      obtain ⟨s'', e, ω2, μ2, run, rep, wf, fo, ww, stk, e7, -, e1, e5, e6⟩ :=
        realloc_inplace_refines (grow := grow) (hb := hb) (p := p) (P := P) (R := R) x ω1 μ1 s (sp - 16) ptr
          ((al + 31) / 32) ((size + 31) / 32) hwf rep1 hc hq0 hr a1 a8 a7 a10 a0 (by omega) (by omega) hb0 hbT
          hfo hHT ⟨by omega, by omega⟩ W1
      rw [realloc_inplace hq0 hr] at e
      simp only [Option.some.injEq, Prod.mk.injEq, true_and, and_true] at e
      subst e
      exact ⟨ω2, μ2, run, rep, wf, fo, ww, stk, e7, e1, e5, e6⟩)

/-- **The binary's `realloc` refines the model's `realloc`, growing in place**: as
    `realloc_wrap_inplace`, for `⌈size/32⌉` units above the usable size (below 2²⁵ − 1) when the
    model's `growInplace` succeeds without changing the allocated space. -/
theorem realloc_wrap_grow {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
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
      ∃ ω' μ', FreeStepsH p R 40701 ω μ x 40821 ω' μ' x 295 ∧ Rep μ' s' ∧ WF s' ∧ FirstOk s' ∧
        ω'[7] = UInt64.ofNat ptr ∧ rdN μ' 206848 1 = 0 ∧ (∀ a, μ'.writable a = μ.writable a) ∧
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have hc' := hc
  obtain ⟨c, hcm, hca, -⟩ := hc'
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  have hcl := ht.mem_lt c hcm
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  refine ⟨realloc_grow hr h, ?_⟩
  exact realloc_wrap (p := p) (P := P) (R := R) x ω μ s s' sp ptr al size ptr 250 hwf hrep
    (growInplace_base h) h1 h7 h9 h10 (by omega) (by omega) hal (by omega) (by omega) hsp1 hb0 hbT hl
    (by omega) ⟨by omega, by omega⟩ hw (fun ω1 μ1 rep1 W1 a1 a8 a7 a10 a0 => by
      obtain ⟨-, ω2, μ2, run, rep, wf, fo, ww, stk, e7, -, e1, e5, e6⟩ :=
        realloc_grow_refines (grow := grow) (hb := hb) (p := p) (P := P) (R := R) x ω1 μ1 s s' (sp - 16) ptr
          ((al + 31) / 32) ((size + 31) / 32) hwf rep1 hc hr hr1 h hng a1 a8 a7 a10 a0 (by omega) (by omega)
          hb0 hbT hA hfo hHT ⟨by omega, by omega⟩ W1
      exact ⟨ω2, μ2, run, rep, wf, fo, ww, stk, e7, e1, e5, e6⟩)

/-- **The binary's `realloc` refines the model's `realloc`, to size 0**: as
    `realloc_wrap_inplace`, for a size of 0 octets (and a nonzero usable size): the model frees the
    chunk and gives null, and `realloc` returns with ω₇ = 0 and memory holding `free s ptr`. -/
theorem realloc_wrap_zero {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
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
        ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have hc' := hc
  obtain ⟨c, hcm, hca, -⟩ := hc'
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  have hcl := ht.mem_lt c hcm
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  refine ⟨realloc_zero hu, ?_⟩
  exact realloc_wrap (p := p) (P := P) (R := R) x ω μ s (free s ptr) sp ptr al 0 0 250 hwf hrep
    free_base' h1 h7 h9 h10 (by omega) (by omega) hal (by omega) (by omega) hsp1 hb0 hbT hl
    (by omega) ⟨by omega, by omega⟩ hw (fun ω1 μ1 rep1 W1 a1 a8 a7 a10 a0 => by
      obtain ⟨-, ω2, μ2, run, rep, wf, fo, ww, stk, e7, -, e1, e5, e6⟩ :=
        realloc_zero_refines (grow := grow) (hb := hb) (p := p) (P := P) (R := R) x ω1 μ1 s (sp - 16) ptr
          ((al + 31) / 32) hwf rep1 hc hu a1 a8 a7 (by rw [a10]) a0 (by omega) (by omega)
          hb0 hbT hfo hHT ⟨by omega, by omega⟩ W1
      exact ⟨ω2, μ2, run, rep, wf, fo, ww, stk, e7, e1, e5, e6⟩)

end Services.Bootstrap.Alloc
