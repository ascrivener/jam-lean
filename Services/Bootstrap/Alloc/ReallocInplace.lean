import Services.Bootstrap.Alloc.ReallocRefines

/-!
# The binary's `realloc_impl` without moving: the same size, or a shrink

`realloc_impl` (42980) for a nonzero request up to the usable size of the allocation: the model's
`realloc` keeps the address (no copy), with the state unchanged for the same size and `shrink`
below it. Both are what the binary does, up to the return into `realloc` (40805).
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **The binary's `realloc_impl` for the same size**: the request equal to the usable size, the
    address comes back and the allocator's memory is untouched. -/
theorem same_refines {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (sp ptr req : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr : req = usable s ptr)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr)
    (h10 : ω[10] = UInt64.ofNat req) (h0 : ω[0] = UInt64.ofNat 1988)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hw : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 42980 ω μ x 40805 ω' μ' x 180 ∧ Rep μ' s ∧
      (∀ a, μ'.writable a = true) ∧ (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[7] = UInt64.ofNat ptr ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat sp ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  obtain ⟨c, hcm, hca, hcu⟩ := hc
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  have hcl := ht.mem_lt c hcm
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hsz : (s.hdr c.addr).size = sizeWord c.size true := by rw [chunks_hdr c hcm, hcu]
  have hca' : c.addr = ptr - 32 := by omega
  have hw' : rdN μ (ptr - 28) 4 = 2 * c.size + 1 := by
    rw [show ptr - 28 = c.addr + 4 by omega, hrep.size c hcm, hsz]; unfold sizeWord; simp
  have hus : usable s ptr = c.size - 1 := by
    unfold usable; rw [← hca', hsz, wordSize_sizeWord]
  obtain ⟨ω1, μ1, r1, a1, -, a6, st0, st5, st6, sf1, ww1, g1⟩ := rl_pro (p := p) (P := P) (R := R) x ω μ sp
    ptr (2 * c.size + 1) h1 h8 (by omega) (by omega) hw' (by omega) hsp hsp1 hw
  have b := rl_br_same (p := p) (P := P) (R := R) x ω1 μ1 req
    (by rw [fget g1 10 (by decide) (by decide)]; exact h10)
    (by rw [a6, hr, hus]; congr 1; omega)
  have hr1 : ∀ a, μ1.readable a = true := fun a => Memory.readable_of_writable (ww1 a)
  obtain ⟨ω2, r2, e7, e0, e1, e5, e6, -⟩ := rl_ret (p := p) (P := P) (R := R) x ω1 μ1 (sp - 152) ptr
    ω[5].toNat ω[6].toNat a1 (by rw [fget g1 8 (by decide) (by decide)]; exact h8) (by omega) (by omega) (by omega)
    (by rw [show sp - 152 + 144 = sp - 8 by omega, rd_enc st0 (UInt64.toNat_lt _), h0]; rfl)
    (by rw [show sp - 152 + 136 = sp - 16 by omega]; exact rd_enc st5 (UInt64.toNat_lt _))
    (by rw [show sp - 152 + 128 = sp - 24 by omega]; exact rd_enc st6 (UInt64.toNat_lt _)) hr1
  refine ⟨ω2, μ1, ((r1.trans b).trans r2).mono (by omega),
    hrep.congr_lock hwf hb0 hbT (fun a ha1 ha2 ha3 => sf1 a (by omega) (Or.inl (by omega))), ww1,
    fun a h1 h2 => sf1 a h1 (Or.inr h2), e7, e0, by rw [e1]; congr 1; omega,
    by rw [e5, UInt64.ofNat_toNat], by rw [e6, UInt64.ofNat_toNat]⟩

/-- The model's `realloc` for a nonzero request up to the usable size keeps the address: the state
    unchanged for the same size, `shrink` below it; no copy. -/
theorem realloc_inplace {grow : Grow} {hb : Nat} {s : State} {ptr align req : Nat} (hr0 : req ≠ 0)
    (hr : req ≤ usable s ptr) :
    realloc grow hb s ptr align req =
      some (ptr, (if req = usable s ptr then s else shrink s ptr req), false) := by
  unfold realloc
  by_cases e : req = usable s ptr
  · simp [e]
  · have e3 : req < usable s ptr := by omega
    simp [e, hr0, e3]

/-- **The binary's `realloc_impl` refines the model's `realloc`, without moving**: from memory
    holding a well-formed `s` (its first chunk's `prev` 0), the data address `ptr` of an allocated
    chunk and a request `req` of 1 … `usable s ptr` units, the model's `realloc` (alignment
    arbitrary) gives `(ptr, s', false)` and `realloc_impl` (42980) returns into `realloc` (40805)
    with ω₇ = ptr and memory holding `s'`, itself well-formed with its first chunk's `prev` 0, the
    caller's ω₀, ω₁, ω₅, ω₆ restored and the stack from sp up untouched. -/
theorem realloc_inplace_refines {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    {grow : Grow} {hb : Nat} (s : State) (sp ptr align req : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr0 : req ≠ 0) (hr : req ≤ usable s ptr)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr) (h7 : ω[7] = UInt64.ofNat 196792)
    (h10 : ω[10] = UInt64.ofNat req) (h0 : ω[0] = UInt64.ofNat 1988)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648)
    (hfo : FirstOk s) (hw : ∀ a, μ.writable a = true) :
    ∃ s', realloc grow hb s ptr align req = some (ptr, s', false) ∧
      ∃ ω' μ', FreeStepsH p R 42980 ω μ x 40805 ω' μ' x 180 ∧ Rep μ' s' ∧ WF s' ∧ FirstOk s' ∧
        (∀ a, μ'.writable a = true) ∧ (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[7] = UInt64.ofNat ptr ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat sp ∧
        ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  refine ⟨_, realloc_inplace hr0 hr, ?_⟩
  by_cases e : req = usable s ptr
  · rw [if_pos e]
    obtain ⟨ω', μ', run, rep, ww, stk, e7, e0, e1, e5, e6⟩ := same_refines (p := p) (P := P) (R := R) x ω μ s
      sp ptr req hwf hrep hc e h1 h8 h10 h0 hsp hsp1 hb0 hbT hw
    exact ⟨ω', μ', run, rep, hwf, hfo, ww, stk, e7, e0, e1, e5, e6⟩
  · rw [if_neg e]
    exact shrink_refines (p := p) (P := P) (R := R) x ω μ s sp ptr req hwf hrep hc hr0 (by omega) h1 h8 h7 h10
      h0 hsp hsp1 hb0 hbT hfo hw

end Services.Bootstrap.Alloc
