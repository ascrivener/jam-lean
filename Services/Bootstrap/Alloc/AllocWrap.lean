import Services.Bootstrap.Alloc.AllocRefines

/-!
# The binary's `alloc`

`alloc` (40494): ω₇ the size and ω₈ the alignment in octets. Either above 2³⁷ − 32 gives null.
Otherwise it takes the allocator's lock (as `dealloc` does), calls `alloc_impl` (41177, returning to
40595) with the size and alignment in 32-octet units, and clears the lock.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **40494 … 41177**: the bounds, the frame, the lock taken, the units, and the call. -/
theorem al_lock {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp size al : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat size)
    (h8 : ω[8] = UInt64.ofNat al) (hal : 1 ≤ al) (hal1 : al ≤ 32) (hs : size + 31 < 68719476736)
    (hsp : 2147483716 ≤ sp) (hsp1 : sp < 4294967296)
    (hl : rdN μ 206848 1 = 0) {HT S0 S1 : Nat} (hH : 206864 ≤ HT) (hS : S0 + 16 ≤ sp ∧ sp ≤ S1)
    (hwr : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 40494 ω μ x 41177 ω' μ' x 30 ∧
      ω'[1] = UInt64.ofNat (sp - 16) ∧ ω'[7] = UInt64.ofNat 196792 ∧ ω'[8] = UInt64.ofNat 1 ∧
      ω'[9] = UInt64.ofNat ((size + 31) / 32) ∧ ω'[10] = UInt64.ofNat 0 ∧ ω'[0] = UInt64.ofNat 1984 ∧
      ω'[5] = UInt64.ofNat 196792 ∧ ω'[4] = ω[4] ∧
      μ'.readN (sp - 8) 8 = Num.encodeLE 8 ω[0].toNat ∧ μ'.readN (sp - 16) 8 = Num.encodeLE 8 ω[5].toNat ∧
      (∀ a, a < 4294967296 → (a < sp - 16 ∨ sp ≤ a) → (a < 196608 ∨ 196616 ≤ a) →
        (a < 206848 ∨ 206852 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧
      ∀ j : Fin 13, j.val ∉ [0, 1, 4, 5, 7, 8, 9, 10, 11] → ω'[j] = ω[j] := by
  have hr := hwr.rd
  have hand := lock_test (w := rdN μ 206848 4) (by rw [rdN4_mod]; exact hl)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h7, h8, hand, show ¬ 137438953440 < al by omega, show 137438953440 ≥ size by omega,
    hwr, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, by reg_val, ?_, ?_, by reg_val, by reg_val, by reg_val, ?_, ?_, ?_, fun a ha h1 h2 h3 => ?_,
      fun a => ?_, by reg_frame⟩
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

/-- **40595 … 40611**: the lock byte cleared, the frame popped; at the return's `jumpInd`. -/
theorem al_unlock {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat 196792)
    (hsp : 2147483648 ≤ sp) (hsp1 : sp + 16 < 4294967296) {HT S0 S1 : Nat} (hH : 206864 ≤ HT)
    (hS : S0 ≤ sp ∧ sp + 16 ≤ S1) (hwr : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 40595 ω μ x 40611 ω' μ' x 5 ∧
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

/-- 41423: `alloc_impl`'s return, through the jump table, to 40595. -/
theorem al_ret_jump {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (h0 : ω[0] = UInt64.ofNat 1984) : FreeStepsH p R 41423 ω μ x 40595 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0]

/-- **The binary's `alloc` refines the model's `alloc`**: from memory holding a well-formed `s`, the
    lock byte clear, ω₇ = `size` and ω₈ = `align` octets (1 … 32), when the model allocates the
    `⌈size/32⌉` units without growing the heap, `alloc` (40494) reaches its return (the `jumpInd`
    at 40611) with the model's address in ω₇, memory holding the model's result, the lock byte clear
    again, the caller's ω₀, ω₁, ω₅, ω₆ restored and the stack from sp up untouched. -/
theorem alloc_wrap_refines {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
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
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  obtain ⟨ω1, μ1, r1, a1, a7, a8, a9, a10, a0, a5, -, st8, st16, fr1, ww1, g1⟩ :=
    al_lock (p := p) (P := P) (R := R) x ω μ sp size al h1 h7 h8 hal hal1 hs (by omega) hsp1 hl (by omega) ⟨by omega, by omega⟩ hw
  have rep1 : Rep μ1 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 =>
    fr1 a (by omega) (Or.inl (by omega)) (Or.inr (by unfold A0 at ha1; omega)) ha3
  obtain ⟨ω2, μ2, r2, rep2, wf2, e7, e0, e5, e6, e1, ww2, stk2⟩ :=
    alloc_refines (p := p) (P := P) (R := R) x ω1 μ1 s s' (sp - 16) _ ptr hwf rep1 h hng a1 a7 a8 a9 a10
      (by omega) (by omega) hb0 hbT hA hfo hHTs ⟨by omega, by omega⟩ hHT (hw.of_eq ww1)
  have rj := al_ret_jump (p := p) (P := P) (R := R) x ω2 μ2 (by rw [e0, a0])
  obtain ⟨ω3, μ3, r3, c0, c5, c1, cl, fr3, ww3, g3⟩ :=
    al_unlock (p := p) (P := P) (R := R) x ω2 μ2 (sp - 16) (by rw [e1, a1]) (by rw [e5, a5]) (by omega) (by omega) (by omega) ⟨by omega, by omega⟩
      ((hw.of_eq ww1).of_eq ww2)
  have hb' : s'.base = s.base := by
    rw [alloc_one hwf.1] at h; obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := alloc1_eq h; rw [allocPost_base]
  refine ⟨ω3, μ3, (((r1.trans r2).trans rj).trans r3).mono (by omega),
    rep2.congr_lock wf2 (by rw [hb']; exact hb0) (by rw [hb']; exact hbT)
      (fun a ha1 ha2 ha3 => fr3 a (by omega) (by omega)), wf2,
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

end Services.Bootstrap.Alloc
