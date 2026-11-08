import Services.Bootstrap.Alloc.ReallocFallbackTail
import Services.Bootstrap.Memcpy

/-!
# The binary's `realloc_impl`: the fallback's copy and free, for any usable size

After `alloc_impl` gives the new block q (at 43276), the fallback copies the old usable size u
(`copy_nonoverlapping` of u·32 octets, `memcpy` at 68729), frees the old chunk and returns q
(`fallback_tail`). `memcpy` takes its byte-loop path for fewer than 16 octets, so a chunk with no
usable unit (u = 0, an allocation of 0 units) copies nothing through `memcpy_small`; for u ≥ 1 it
takes the word path (`memcpy_big_aligned`). `rf_memcpy` covers both, so the fallback's tail
(`fallback_after`) holds for every u.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **68729 … 43295, the fallback's copy, any size**: `memcpy` of u·32 octets from ptr to q
    (both 8-aligned, disjoint and below the stack frame), returning to 43295 with ω₀, ω₁, ω₅, ω₆
    kept; q's first u·32 octets are ptr's, and memory changes only there and in the frame below sp.
    For u = 0 this is `memcpy`'s byte loop with nothing to copy (`memcpy_small`), else its word
    path (`memcpy_big_aligned`). -/
theorem rf_memcpy {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp q ptr u : Nat) (h0 : ω[0] = UInt64.ofNat 2004) (h1 : ω[1] = UInt64.ofNat sp)
    (h7 : ω[7] = UInt64.ofNat q) (h8 : ω[8] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat (32 * u))
    (hsp : 65536 + 48 ≤ sp ∧ sp < 4294967296 ∧ sp % 8 = 0) (hq : 65536 ≤ q) (hp : 65536 ≤ ptr)
    (hqe : q + 32 * u + 16 < 4294967296) (hpe : ptr + 32 * u + 16 < 4294967296)
    (hqa : q % 8 = 0) (hpa : ptr % 8 = 0)
    (hdj : q + 32 * u ≤ ptr ∨ ptr + 32 * u ≤ q) (hfd : q + 32 * u ≤ sp - 48) (hfs : ptr + 32 * u ≤ sp - 48)
    (hr : ∀ a, ptr ≤ a → a < ptr + 32 * u → μ.readable a = true)
    (hw : ∀ a, q ≤ a → a < q + 32 * u → μ.writable a = true)
    (hwf : ∀ a, sp - 48 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 68729 ω μ x 43295 ω' μ' x (64 * u + 320) ∧
      ω'[0] = UInt64.ofNat 2004 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      μ'.readN q (32 * u) = μ.readN ptr (32 * u) ∧
      (∀ a, a < 4294967296 → (a < q ∨ q + 32 * u ≤ a) → (a < sp - 48 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) := by
  by_cases hu : u = 0
  · subst hu
    obtain ⟨ω', run, g0, g1, g5, g6, -⟩ := memcpy_small (p := p) (P := P) (R := R) x ω μ 2004 43295 sp q ptr 0
      h0 h1 h7 h8 (by simpa using h9) (by decide) (by decide)
      (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_1001]) bs_43295 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ (by omega) (Or.inl (by omega)) (Or.inl (by omega)) hwf
      (fun a h1 h2 => absurd h2 (by omega)) (fun a h1 h2 => absurd h2 (by omega))
    refine ⟨ω', _, run.mono (by omega), by rw [g0, h0], by rw [g1, h1], g5, g6, ?_, fun a ha h1 h2 => ?_,
      fun a => ?_⟩
    · rfl
    · rw [show μ.readN ptr 0 = [] from rfl, Memory.writeN_nil]
      simp (disch := pvm_arith) only [memcpyFrame, PVM.Memory.read_writeN_disjoint, PVM.Num.length_encodeLE,
        PVM.two32]
    · rw [show μ.readN ptr 0 = [] from rfl, Memory.writeN_nil]
      simp only [memcpyFrame, Memory.writable_writeN]
  · obtain ⟨ω', μ', run, d0, d1, d5, d6, dc, dfr, -, dwr⟩ := memcpy_big_aligned (p := p) (P := P) (R := R)
      x ω μ 2004 43295 sp q ptr (32 * u) h0 h1 h7 h8 h9 (by decide)
      (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_1001]) bs_43295 hsp (by omega)
      (by omega) (by omega) hpa hqa hdj (Or.inr hfd) (Or.inr hfs) hr hw hwf
    exact ⟨ω', μ', run.mono (by omega), d0, d1, d5, d6, dc, dfr, dwr⟩

/-- **43276 … 40805, the fallback after the allocation**: from memory holding a well-formed `s₁`
    (its first chunk's `prev` 0) in which the old chunk (u + 1 units, at ptr − 32) and the new block
    q (r + 1 ≥ u + 1 units, at q − 32) are disjoint allocated chunks, with ω₇ = q, ω₅ = ptr, ω₆ = u
    and the frame at sp: the binary copies the old usable size to q, frees ptr and returns q into
    `realloc` (40805), the memory holding `free s₁ ptr` and the stack from sp up untouched. -/
theorem fallback_after {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
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
    ∃ ω' μ', FreeStepsH p R 43276 ω μ x 40805 ω' μ' x (64 * u + 560) ∧
      Rep μ' (free s1 ptr) ∧ WF (free s1 ptr) ∧ FirstOk (free s1 ptr) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧ (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[7] = UInt64.ofNat q ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat (sp + 152) ∧
      ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 := by
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
  obtain ⟨ω4, μ3, r4, d0, d1, d5, d6, -, dfr, dwr⟩ := rf_memcpy (p := p) (P := P) (R := R)
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
  obtain ⟨ω6, μ4, r6, rep4, wf4, fo4, ww4, stk4, b0, b1, b5, b6⟩ := free_refines (p := p) (P := P) (R := R)
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
  exact ⟨ω7, μ4, (((((r3.trans r4).trans r5).trans r6).trans rj2).trans r7).mono (by omega), rep4, wf4, fo4,
    fun a => (ww4 a).trans (dwr a), stk, k7, k0, k1, k5, k6⟩

end Services.Bootstrap.Alloc
