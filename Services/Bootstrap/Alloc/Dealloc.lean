import Services.Bootstrap.Alloc.FreeRefines

/-!
# The binary's `dealloc`

`dealloc` (40613) takes the allocator's lock — a byte at 206848, set by a 32-bit or of 1 into its
word, retried while the old byte is nonzero — calls the free path (42327, returning to 40681) and
clears the lock byte. With the lock word 0 the retry loop runs once.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- A word's low octet is its first. -/
theorem rdN4_mod (μ : Memory) (a : Nat) : rdN μ a 4 % 256 = rdN μ a 1 := by
  simp only [rdN, Memory.readN, List.range, List.range.loop, List.map, Num.decodeLE, Nat.add_zero]
  have := (μ.read a).toNat_lt
  omega

/-- The lock test: the old word, sign-extended, and 255 is its low octet. -/
theorem lock_test {w : Nat} (h0 : w % 256 = 0) :
    Exec.bitwise (· && ·) (sxw 4 w % 18446744073709551616) 255 % 18446744073709551616 = 0 := by
  have key : ∀ v : Nat, v % 256 = 0 → Exec.bitwise (· && ·) v 255 % 18446744073709551616 = 0 := by
    intro v hv
    rw [bitwise_and_land _ _ (by omega), show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  apply key
  simp only [sxw, Exec.u64, Num.unsigned, Num.signed, Nat.reduceMul, Nat.reducePow, Nat.reduceSub]
  split <;> simp only [Int.reducePow] <;> omega

/-- **40613 … 42327**: the frame, the lock taken, and the call into the free path. -/
theorem dl_lock {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp ptr : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (hp0 : ptr ≠ 0)
    (hp1 : ptr < 4294967296) (hsp : 2147483716 ≤ sp) (hsp1 : sp < 4294967296)
    (hl : rdN μ 206848 1 = 0) {HT S0 S1 : Nat} (hH : 206864 ≤ HT) (hS : S0 + 16 ≤ sp ∧ sp ≤ S1)
    (hwr : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 40613 ω μ x 42327 ω' μ' x 22 ∧
      ω'[1] = UInt64.ofNat (sp - 16) ∧ ω'[8] = UInt64.ofNat ptr ∧ ω'[7] = UInt64.ofNat 196792 ∧
      ω'[0] = UInt64.ofNat 1986 ∧ ω'[5] = UInt64.ofNat 196792 ∧ ω'[4] = ω[4] ∧
      μ'.readN (sp - 8) 8 = Num.encodeLE 8 ω[0].toNat ∧ μ'.readN (sp - 16) 8 = Num.encodeLE 8 ω[5].toNat ∧
      (∀ a, a < 4294967296 → (a < sp - 16 ∨ sp ≤ a) → (a < 196608 ∨ 196616 ≤ a) →
        (a < 206848 ∨ 206852 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧
      ∀ j : Fin 13, j.val ∉ [0, 1, 4, 5, 7, 8, 9, 10] → ω'[j] = ω[j] := by
  have hr := hwr.rd
  have hand := lock_test (w := rdN μ 206848 4) (by rw [rdN4_mod]; exact hl)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h7, hp0, hand, hwr, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, by reg_val, ?_, ?_, ?_, fun a ha h1 h2 h3 => ?_,
      fun a => ?_, by reg_frame⟩
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some',
        List.lookup_nil, Option.getD_none]
      rd_simp []
      simp
    · rw [show sp - 8 = sp - 16 + 8 by omega]; rd_simp []; rfl
    · rd_simp []; rfl
    · rd_simp []
    · rd_simp [hwr]

/-- 42978: the free path's return, through the jump table, to `dealloc` (40681). -/
theorem free_ret_dealloc {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (h0 : ω[0] = UInt64.ofNat 1986) : FreeStepsH p R 42978 ω μ x 40681 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0]

/-- **40681 … 40697**: the lock byte cleared, the frame popped; at the return's `jumpInd`. -/
theorem dl_unlock {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat 196792)
    (hsp : 2147483648 ≤ sp) (hsp1 : sp + 16 < 4294967296) {HT S0 S1 : Nat} (hH : 206864 ≤ HT)
    (hS : S0 ≤ sp ∧ sp + 16 ≤ S1) (hwr : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 40681 ω μ x 40697 ω' μ' x 5 ∧
      ω'[0] = UInt64.ofNat (rdN μ (sp + 8) 8) ∧ ω'[5] = UInt64.ofNat (rdN μ sp 8) ∧
      ω'[1] = UInt64.ofNat (sp + 16) ∧ rdN μ' 206848 1 = 0 ∧
      (∀ a, a < 4294967296 → a ≠ 206848 → μ'.read a = μ.read a) ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      ∀ j : Fin 13, j.val ∉ [0, 1, 5, 7] → ω'[j] = ω[j] := by
  have hr := hwr.rd
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, hwr, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, by reg_val, by reg_val, ?_, fun a ha ha' => ?_, fun a => ?_, by reg_frame⟩
    · rd_simp []; rfl
    · rd_simp []
    · rd_simp [hwr]

/-- `Rep` reads the allocator's fields and the heap's headers, none of them in the lock word. -/
theorem Rep.congr_lock {μ μ' : Memory} {s : State} (h : Rep μ s) (hwf : WF s) (hb0 : 206864 ≤ s.base)
    (hbT : s.base + 1073741824 < 2147483648)
    (wf : ∀ a, A0 ≤ a → a < 2147483648 → (a < 206848 ∨ 206852 ≤ a) → μ'.read a = μ.read a) : Rep μ' s := by
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hc : ∀ c ∈ chunks s, s.base ≤ c.addr ∧ c.addr + 16 < 2147483648 := fun c hc => by
    have := ht.mem_lt c hc; omega
  refine ⟨fun b hb => ?_, fun q hq => ?_, ?_, ?_, ?_, fun c hc' => ?_, fun c hc' => ?_, fun c hc' _ => ?_,
    fun c hc' _ => ?_⟩
  · rw [← h.heads b hb]; unfold A0; unfold binCount at hb
    exact rdN_frame fun j hj => wf _ (by unfold A0; omega) (by omega) (by omega)
  · rw [← h.sec q hq]; unfold A0; exact rdN_frame fun j hj => wf _ (by unfold A0; omega) (by omega) (by omega)
  · rw [← h.pri]; unfold A0; exact rdN_frame fun j hj => wf _ (by unfold A0; omega) (by omega) (by omega)
  · rw [← h.base]; unfold A0; exact rdN_frame fun j hj => wf _ (by unfold A0; omega) (by omega) (by omega)
  · rw [← h.alloc]; unfold A0; exact rdN_frame fun j hj => wf _ (by unfold A0; omega) (by omega) (by omega)
  · have := hc c hc'; rw [← h.prev c hc']
    exact rdN_frame fun j hj => wf _ (by unfold A0; omega) (by omega) (by omega)
  · have := hc c hc'; rw [← h.size c hc']
    exact rdN_frame fun j hj => wf _ (by unfold A0; omega) (by omega) (by omega)
  · have := hc c hc'; rw [← h.next c hc' ‹_›]
    exact rdN_frame fun j hj => wf _ (by unfold A0; omega) (by omega) (by omega)
  · have := hc c hc'; rw [← h.prevL c hc' ‹_›]
    exact rdN_frame fun j hj => wf _ (by unfold A0; omega) (by omega) (by omega)

theorem free_base' {s : State} {ptr : Nat} : (free s ptr).base = s.base := by
  rw [free_eq]
  generalize s.top = T
  generalize hm : mergePrev s (ptr - 32) (wordSize (s.hdr (ptr - 32)).size) (s.hdr (ptr - 32)).prev = m
  generalize hq : mergeNext m.1 m.2.1 m.2.2.1 T = q
  obtain ⟨-, -, hb1, -⟩ := mergePrev_prev (hm.trans (rfl : m = (m.1, m.2.1, m.2.2.1, m.2.2.2))) rfl
  obtain ⟨s2, total⟩ := q
  obtain ⟨-, hb2, -⟩ := mergeNext_prev hq
  rw [freeFinal_base, hb2, hb1]

/-- **The binary's `dealloc` refines the model's `free`**: from memory holding a well-formed `s`, the
    lock byte clear and ω₇ the data address of an allocated chunk, `dealloc` (40613) reaches its
    return (the `jumpInd` at 40697) with memory holding `free s ptr`, the lock byte clear again,
    the caller's ω₀, ω₁, ω₅, ω₆ restored and the stack from sp up untouched. -/
theorem dealloc_refines {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (sp ptr : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr)
    (hsp : 2147483716 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648)
    (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0) {HT S0 S1 : Nat} (hHT : s.base + 32 * s.allocated ≤ HT)
    (hS : S0 + 40 ≤ sp ∧ sp ≤ S1) (hw : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 40613 ω μ x 40697 ω' μ' x 248 ∧ Rep μ' (free s ptr) ∧ WF (free s ptr) ∧
      FirstOk (free s ptr) ∧ rdN μ' 206848 1 = 0 ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have hc' := hc
  obtain ⟨c, hcm, hca, -⟩ := hc'
  have hcl : s.base ≤ c.addr ∧ c.addr + 32 * c.size ≤ s.top ∧ 0 < c.size := by
    have ht := hwf.2.2.2.1
    unfold TilesOk at ht
    exact ht.mem_lt c hcm
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  obtain ⟨ω1, μ1, r1, a1, a8, a7, a0, a5, a4, st8, st16, fr1, ww1, g1⟩ :=
    dl_lock (p := p) (P := P) (R := R) x ω μ sp ptr h1 h7 (by omega) (by omega) hsp hsp1 hl (by omega)
      ⟨by omega, by omega⟩ hw
  have rep1 : Rep μ1 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 =>
    fr1 a (by omega) (Or.inl (by omega)) (Or.inr (by unfold A0 at ha1; omega)) ha3
  obtain ⟨ω2, μ2, r2, rep2, wf2, fo2, ww2, stk2, b0, b1, b5, b6⟩ :=
    free_refines (p := p) (P := P) (R := R) x ω1 μ1 s (sp - 16) ptr hwf rep1 hc a1 a8 a7 (by omega)
      (by omega) hb0 hbT hfo hHT ⟨by omega, by omega⟩ (hw.of_eq ww1)
  have rj := free_ret_dealloc (p := p) (P := P) (R := R) x ω2 μ2 (by rw [b0, a0])
  obtain ⟨ω3, μ3, r3, c0, c5, c1, cl, fr3, ww3, g3⟩ :=
    dl_unlock (p := p) (P := P) (R := R) x ω2 μ2 (sp - 16) b1 (by rw [b5, a5]) (by omega) (by omega) (by omega)
      ⟨by omega, by omega⟩ ((hw.of_eq ww1).of_eq ww2)
  have hb' : (free s ptr).base = s.base := free_base'
  refine ⟨ω3, μ3, (((r1.trans r2).trans rj).trans r3).mono (by omega),
    rep2.congr_lock wf2 (by rw [hb']; exact hb0) (by rw [hb']; exact hbT)
      (fun a ha1 ha2 ha3 => fr3 a (by omega) (by omega)), wf2, fo2, cl,
    fun a => (ww3 a).trans ((ww2 a).trans (ww1 a)),
    fun a ha1 ha2 => ((fr3 a ha1 (by omega)).trans (stk2 a ha1 (by omega))).trans
      (fr1 a ha1 (Or.inr ha2) (Or.inr (by omega)) (Or.inr (by omega))), ?_, ?_, ?_, ?_⟩
  · rw [c0, rdN_frame (μ := μ1) fun j hj => stk2 _ (by omega) (by omega), show sp - 16 + 8 = sp - 8 by omega]
    unfold rdN; rw [st8, Num.decodeLE_encodeLE]
    rw [Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]
  · rw [c1, h1]; congr 1; omega
  · rw [c5, rdN_frame (μ := μ1) fun j hj => stk2 _ (by omega) (by omega)]
    unfold rdN; rw [st16, Num.decodeLE_encodeLE]
    rw [Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]
  · rw [fget g3 6 (by decide) (by decide), b6, fget g1 6 (by decide) (by decide)]

end Services.Bootstrap.Alloc
