import Services.Bootstrap.Alloc.ReallocInplace

/-!
# The binary's `realloc_impl` for a request of 0 units

A request of 0 units with a nonzero usable size: `realloc_impl` calls the free path (42327, with
ω₀ = 2000, returning to 43145) and returns null. The model's `realloc` gives
`(0, free s ptr, false)` for it.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 42978: the free path's return, through the jump table, to `realloc_impl` (43145). -/
theorem free_ret_realloc {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (h0 : ω[0] = UInt64.ofNat 2000) : FreeStepsH p R 42978 ω μ x 43145 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0]

/-- The model's `realloc` for a request of 0 units below a nonzero usable size: the allocation is
    freed and the address is null. -/
theorem realloc_zero {grow : Grow} {hb : Nat} {s : State} {ptr align : Nat} (hu : usable s ptr ≠ 0) :
    realloc grow hb s ptr align 0 = some (0, free s ptr, false) := by
  unfold realloc
  have e1 : (0 : Nat) ≠ usable s ptr := fun h => hu h.symm
  simp [e1]

/-- **The binary's `realloc_impl` refines the model's `realloc` for a request of 0 units**: from
    memory holding a well-formed `s` (its first chunk's `prev` 0), the data address `ptr` of an
    allocated chunk with a nonzero usable size, and a request of 0, the model's `realloc` gives
    `(0, free s ptr, false)` and `realloc_impl` (42980) frees the chunk through the free path and
    returns into `realloc` (40805) with ω₇ = 0 (null) and memory holding `free s ptr`, itself
    well-formed with its first chunk's `prev` 0, the caller's ω₀, ω₁, ω₅, ω₆ restored and the
    stack from sp up untouched. -/
theorem realloc_zero_refines {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
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
        ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
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
    ptr (2 * c.size + 1) h1 h8 (by omega) (by omega) hw' (by omega) (by omega) hsp1 ⟨by omega, by omega⟩ hS hw
  obtain ⟨ω2, r2, b0, g2⟩ := rl_go_zero (p := p) (P := P) (R := R) x ω1 μ1 ((2 * c.size + 1) / 2 - 1)
    (by rw [fget g1 10 (by decide) (by decide)]; exact h10) a6 (by omega) (by omega)
  have rep1 : Rep μ1 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 =>
    sf1 a (by omega) (Or.inl (by unfold A0 at ha1; omega))
  have hc' : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true := ⟨c, hcm, hca, hcu⟩
  obtain ⟨ω3, μ3, r3, rep3, wf3, fo3, ww3, stk3, c0, c1, c5, c6⟩ := free_refines (p := p) (P := P) (R := R)
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
    by rw [e1]; congr 1; omega, by rw [e5, UInt64.ofNat_toNat], by rw [e6, UInt64.ofNat_toNat]⟩

end Services.Bootstrap.Alloc
