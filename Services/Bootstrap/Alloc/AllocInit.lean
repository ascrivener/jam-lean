import Services.Bootstrap.Alloc.AllocGrowRefines

/-!
# The binary's `initialize`

`initialize` (42165, called by `alloc_impl` at 42142 on the first use, ω₀ = 1998): the heap's base is
206880 (the allocator's end rounded up to 32); the host grows the heap over its first chunk's header
(51 pages); then the base, one unit allocated, the top bin's head, its bits, and the first chunk's
header — one free chunk of 2²⁵ units — are written.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code JAM

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **42165 … 42211**: the frame, the heap's base 206880 in ω₅, and the 51 pages to grow to. -/
theorem ii_pre {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp)
    (hsp0 : 2147483680 ≤ sp) (hsp : sp < 4294967296) (hwr : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 42165 ω μ x 42211 ω' μ' x 20 ∧
      ω'[1] = UInt64.ofNat (sp - 32) ∧ ω'[5] = UInt64.ofNat 206880 ∧ ω'[6] = UInt64.ofNat 51 ∧
      ω'[7] = UInt64.ofNat 51 ∧
      μ'.readN (sp - 8) 8 = Num.encodeLE 8 ω[0].toNat ∧ μ'.readN (sp - 16) 8 = Num.encodeLE 8 ω[5].toNat ∧
      μ'.readN (sp - 24) 8 = Num.encodeLE 8 ω[6].toNat ∧ μ'.readN (sp - 32) 8 = Num.encodeLE 8 ω[7].toNat ∧
      (∀ a, a < 4294967296 → (a < sp - 32 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) ∧ ∀ j : Fin 13, j.val ∉ [1, 5, 6, 7, 8] → ω'[j] = ω[j] := by
  have hr : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hwr a)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, hwr, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, by reg_frame⟩
    · rw [show sp - 8 = sp - 32 + 24 by omega]; rd_simp []; rfl
    · rw [show sp - 16 = sp - 32 + 16 by omega]; rd_simp []; rfl
    · rw [show sp - 24 = sp - 32 + 8 by omega]; rd_simp []; rfl
    · rd_simp []; rfl
    · rd_simp []
    · rd_simp [hwr]

/-- **42211, `ecalli 1`**, every page writable: the call returns the heap's bound b. -/
theorem ii_call {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (x : RefineCtx) (ω : Regs)
    (μ : Memory) (a b : Nat) (hb : heapBounds env.code = (a, b)) (hab : a ≤ b) (hbs : b < 4294967296)
    (hw : ∀ a, μ.writable a = true) :
    FreeStepsH p (refineContract env) 42211 ω μ x 42213 (setR7 ω b) (μ.setPages a (b - a) (some .write)) x 1 := by
  have ht : growTop (reg ω 7) b b = b := by unfold growTop; rw [if_pos (by omega)]
  have hp : HeapPages μ a b b := fun q h1 h2 => by
    have h' : (μ.pages.get? q == some .write) = true := by
      have := hw (q * pageSize); unfold Memory.writable at this
      rwa [Nat.mul_div_cancel _ (show 0 < pageSize by unfold pageSize; decide)] at this
    rw [h']; simp [h2]
  rw [← ht]
  exact FreeStepsH.growHeap env _ (d_42211 (p := p) (P := P)) hb hp hab (Nat.le_refl b) hbs rfl
    (by rw [ht]; simp only [Nat.sub_self, Nat.zero_mul, Nat.add_zero]; decide) FreeStepsH.refl

/-- **42213 … 42325**, the heap reaching the 51 pages: the base, one unit allocated, the top bin
    (2431)'s head and bits, and the first chunk's header written; ω₇ = 1, the frame popped. -/
theorem ii_post {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp t w pri : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat t) (h6 : ω[6] = UInt64.ofNat 51)
    (h5 : ω[5] = UInt64.ofNat 206880) (h0 : rdN μ sp 8 = 196792) (ht : 51 ≤ t) (ht1 : t < 4294967296)
    (hw : rdN μ 206824 8 = w) (hp : rdN μ 206832 8 = pri)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 32 < 4294967296) (hwr : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 42213 ω μ x 42325 ω' μ' x 30 ∧
      rdN μ' 206516 4 = 206880 ∧ rdN μ' 206520 8 = 206880 ∧ rdN μ' 206824 8 = w ||| 2 ^ 63 ∧
      rdN μ' 206832 8 = pri ||| 2 ^ 37 ∧ rdN μ' 206840 4 = 1 ∧ rdN μ' 206880 4 = 0 ∧
      rdN μ' 206884 4 = sizeWord 33554432 false ∧ rdN μ' 206888 4 = 0 ∧ rdN μ' 206892 4 = 0 ∧
      ω'[7] = UInt64.ofNat 1 ∧ ω'[0] = UInt64.ofNat (rdN μ (sp + 24) 8) ∧
      ω'[5] = UInt64.ofNat (rdN μ (sp + 16) 8) ∧ ω'[6] = UInt64.ofNat (rdN μ (sp + 8) 8) ∧
      ω'[1] = UInt64.ofNat (sp + 32) ∧
      (∀ a, a < 4294967296 → (a < 206516 ∨ 206528 ≤ a) → (a < 206824 ∨ 206844 ≤ a) →
        (a < 206880 ∨ 206896 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) ∧ ∀ j : Fin 13, j.val ∉ [0, 1, 5, 6, 7, 8, 9, 10, 11] → ω'[j] = ω[j] := by
  have hr : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hwr a)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h7, h6, h5, h0, hw, hp, Nat.mod_eq_of_lt ht1, show 51 ≤ t from ht, hwr, hr,
    rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    have hw64 : w < 2 ^ 64 := by rw [← hw]; exact rdN_lt64 μ _
    have hp64 : pri < 2 ^ 64 := by rw [← hp]; exact rdN_lt64 μ _
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by reg_val, by reg_val, by reg_val, by reg_val, by reg_val,
      fun a ha h1 h2 h3 => ?_, fun a => ?_, by reg_frame⟩
    all_goals try rd_simp [hwr]
    all_goals try decide
    · rw [show (9223372036854775808 : Nat) = 2 ^ 63 % 18446744073709551616 from rfl]
      exact or_word _ _ hw64 (by decide)
    · rw [show (137438953472 : Nat) = 2 ^ 37 % 18446744073709551616 from rfl]
      exact or_word' _ _ hp64 (by decide)
    all_goals try (simp only [Num.decodeLE, Memory.readN, List.range, List.range.loop, List.map, Nat.add_zero]
                   simp (disch := pvm_arith) only [PVM.Memory.read_writeN, PVM.reduceEncodeLE, PVM.Num.length_encodeLE,
                     List.length_cons, List.length_nil, PVM.two32, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff,
                     Nat.reduceLT, and_true, true_and, and_false, false_and, ↓reduceIte, List.getElem!_cons_zero,
                     List.getElem!_cons_succ, UInt8.reduceOfNat]
                   decide)

/-- **42131 … 42165**: `alloc_impl` saves ω₇ and ω₈, keeps ω₉ in ω₅, and calls `initialize`. -/
theorem ai_call {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296)
    (hwr : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 42131 ω μ x 42165 ω' μ' x 6 ∧ ω'[0] = UInt64.ofNat 1998 ∧ ω'[5] = ω[9] ∧
      ω'[7] = ω[7] ∧ μ'.readN (sp + 48) 8 = Num.encodeLE 8 ω[7].toNat ∧
      μ'.readN (sp + 104) 8 = Num.encodeLE 8 ω[8].toNat ∧
      (∀ a, a < 4294967296 → (a < sp + 48 ∨ sp + 56 ≤ a) → (a < sp + 104 ∨ sp + 112 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) ∧ ∀ j : Fin 13, j.val ∉ [0, 5, 7] → ω'[j] = ω[j] := by
  have hr : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hwr a)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, hwr, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, by reg_val; rfl, ?_, ?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_, by reg_frame⟩
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some',
        List.lookup_nil, Option.getD_none]
      rd_simp []; simp
    all_goals try (rd_simp []; rfl)
    · rd_simp []
    · rd_simp [hwr]

/-- 42325: `initialize`'s return, through the jump table, to 42147. -/
theorem ii_ret {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (h0 : ω[0] = UInt64.ofNat 1998) : FreeStepsH p R 42325 ω μ x 42147 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0]

/-- **42147 … 41221**, `initialize` succeeded (ω₇ = 1): ω₈ and ω₇ restored, ω₉ from ω₅; on to the
    bins at 41221. -/
theorem ai_back {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 1) (hsp : sp + 152 < 4294967296)
    (hr : ∀ a, μ.readable a = true) :
    ∃ ω', FreeStepsH p R 42147 ω μ x 41221 ω' μ x 6 ∧ ω'[8] = UInt64.ofNat (rdN μ (sp + 104) 8) ∧
      ω'[9] = ω[5] ∧ ω'[7] = UInt64.ofNat (rdN μ (sp + 48) 8) ∧ ω'[11] = UInt64.ofNat 1 ∧
      ∀ j : Fin 13, j.val ∉ [7, 8, 9, 11] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, h7, hr, ↓rdN_fold, ↓loadI_fold]
  case post => exact ⟨by reg_val, by reg_val; rfl, by reg_val, by reg_val, by reg_frame⟩

theorem binDown_max : binDown maxSize = 2431 := by
  rw [maxSize_val, binDown_big (by decide), show min 33554432 33554432 = 2 ^ 25 from rfl, Nat.log2_two_pow]

/-- **`init` against memory**: memory holding the allocator's fields of a zeroed `s` (base 0), with
    `initialize`'s writes, holds the model's `init` result, its first chunk at 206880. -/
theorem init_rep {μ μ' : Memory} {s s' : State} {grow : Grow} (h : RepAt μ s (fun _ => False) (fun _ => False))
    (hb : s.base = 0) (hinit : init grow 206880 s = some s')
    (w1 : rdN μ' 206516 4 = 206880) (w2 : rdN μ' 206520 8 = 206880)
    (w3 : rdN μ' 206824 8 = rdN μ 206824 8 ||| 2 ^ 63) (w4 : rdN μ' 206832 8 = rdN μ 206832 8 ||| 2 ^ 37)
    (w5 : rdN μ' 206840 4 = 1) (w6 : rdN μ' 206880 4 = 0) (w7 : rdN μ' 206884 4 = sizeWord 33554432 false)
    (w8 : rdN μ' 206888 4 = 0) (w9 : rdN μ' 206892 4 = 0)
    (wf : ∀ a, a < 2147483648 → (a < 206516 ∨ 206528 ≤ a) → (a < 206824 ∨ 206844 ≤ a) →
      (a < 206880 ∨ 206896 ≤ a) → μ'.read a = μ.read a) :
    RepAt μ' s' (fun a => a = 206880) (fun a => a = 206880) := by
  unfold init at hinit
  simp only [hb, ne_eq, not_true_eq_false, ↓reduceIte] at hinit
  split at hinit
  · simp at hinit
  simp only [Option.some.injEq] at hinit
  subst hinit
  rw [binDown_max]
  have hsec := h.sec 37 (by decide)
  have hpri := h.pri
  unfold A0 at hsec hpri
  refine ⟨fun b hb' => ?_, fun q hq => ?_, ?_, ?_, ?_, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_,
    fun a ha => ?_⟩
  · simp only [upd, setHdr_heads, setBit_heads]
    split
    · rename_i e; subst e; unfold A0; exact w1
    · rw [← h.heads b hb']; unfold A0; unfold binCount at hb'
      exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega) (by omega)
  · simp only [setBit, setHdr, upd, show 2431 / 64 = 37 by decide, show 2431 % 64 = 63 by decide]
    split
    · rename_i e; subst e; unfold A0; rw [show 196792 + 9736 + 8 * 37 = 206824 by decide, w3, hsec]
    · rw [← h.sec q hq]; unfold A0
      exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega) (by omega)
  · simp only [setBit, setHdr, show 2431 / 64 = 37 by decide]; unfold A0
    rw [show 196792 + 10040 = 206832 by decide, w4, hpri]
  · unfold A0; exact w2
  · unfold A0; exact w5
  · subst ha; simp [setBit, setHdr, upd]; exact w6
  · subst ha; simp [setBit, setHdr, upd]; rw [maxSize_val]; exact w7
  · subst ha; simp [setBit, setHdr, upd]; exact w8
  · subst ha; simp [setBit, setHdr, upd]; exact w9

end Services.Bootstrap.Alloc
