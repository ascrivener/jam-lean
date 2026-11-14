import Services.Bootstrap.Encode.WriterGrowSteps
import Services.Bootstrap.Decode.GrowOne

/-!
# `Vec<u8>::extend_from_slice` (58508) with growth, under the refine contract

`Writer.extend_ok` covers `extend_from_slice` when the vector `{cap, ptr, len}` at v has room for the
n octets (`len + n ≤ cap`). Here the other case, `cap − len < n` (`extend_grow`), and both together
(`extend_any`), for a vector whose buffer is an allocated chunk c of picoalloc's state
(`c.addr + 32 = ptr`, `cap ≤ 32 · (c.size − 1)`), under `refineContractK K env` (K ≥ 2²⁷) with the
allocator's context `HeapCtx`.

On the grow path `RawVec<u8>::reserve` (58251) asks `finish_grow` (58327) for the capacity
nc = `newCap cap len n` = max(max(len + n, 8), 2 · cap), and `finish_grow` calls picoalloc's `realloc`
wrapper (40701) for the old buffer (cap > 0; the `alloc` branch for cap = 0 is not covered). Either:
* `realloc` returns a block r: the vector becomes `{nc, r, len + n}`, r the data of an allocated chunk d
  of the new state s' with nc ≤ 32 · (d.size − 1), holding the old len octets followed by the n new ones;
  the context is kept for s', every other allocated chunk of s is kept with its data, and memory at or
  above sp is kept but for the vector; or
* the model's `realloc` fails and the wrapper returns null to `finish_grow` (58363): `ExhaustsW`.
  (`finish_grow` then returns `Err` and `reserve` traps at 58326, `handle_alloc_error`.)

## The failure predicate

`LoopA.AllocFail` names the two return points where a run has seen a failed allocator call: 40611 (the
`alloc` wrapper's return) and 33055 (`finish_grow<Instruction>`'s return from `realloc`). The writer's
`realloc` returns to another point, 58363. `AllocFailW pb j` is `AllocFail pb j` or `j = 58363` with a
failing model `realloc`; `ExhaustsW` is `LoopA.Exhausts` with `AllocFailW` (same shape: the run reaches
j with null in ω₇). `Exhausts.toW` lifts every `Exhausts` to it.

The source octets lie at or above sp (`StackSrc`) or in the data of an allocated chunk of s other than
the buffer's (`HeapSrc`): `realloc` keeps both.
-/

namespace Services.Bootstrap.Encode.WriterGrow

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX
  Services.Bootstrap.CodeA Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Decode.ReallocCall
  Services.Bootstrap.Decode.ReallocKeepAll Services.Bootstrap.Decode.VecU8 Services.Bootstrap.Decode.GrowOne
  Services.Bootstrap.Encode.Writer

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-! ## The failure predicate -/

/-- **A failed allocator call**, generalising `LoopA.AllocFail` by the writer's `realloc`: one of
    `AllocFail`'s points (40611, 33055), or the return of the `realloc` wrapper to the writer's
    `finish_grow` (58363) where the model's `realloc` fails. At each the wrapper has returned null. -/
def AllocFailW (pb j : Nat) : Prop :=
  AllocFail pb j ∨
  (j = 58363 ∧ ∃ (s : State) (hb ptr al r : Nat), realloc (growTo pb) hb s ptr al r = none)

/-- The run reaches a failed allocator call (`AllocFailW`), the wrapper having returned null:
    `LoopA.Exhausts` with `AllocFailW` for `AllocFail`. -/
def ExhaustsW (env : RefineHost.Env) (cap pb : Nat) (p : ByteArray) (P : Program) (i : Nat) (ω : Regs)
    (μ : Memory) (x : RefineCtx) (n : Nat) : Prop :=
  ∃ (ω' : Regs) (μ' : Memory) (j : Nat),
    FreeStepsH p (refineContractK cap env) i ω μ x j ω' μ' x n ∧ ω'[7] = UInt64.ofNat 0 ∧ AllocFailW pb j

theorem AllocFailW.of {pb j : Nat} (h : AllocFail pb j) : AllocFailW pb j := Or.inl h

/-- **Every `Exhausts` is an `ExhaustsW`.** -/
theorem Exhausts.toW {env : RefineHost.Env} {cap pb : Nat} {p : ByteArray} {P : Program} {i : Nat}
    {ω : Regs} {μ : Memory} {x : RefineCtx} {n : Nat} (h : Exhausts env cap pb p P i ω μ x n) :
    ExhaustsW env cap pb p P i ω μ x n := by
  obtain ⟨ω', μ', j, run, e7, ha⟩ := h
  exact ⟨ω', μ', j, run, e7, Or.inl ha⟩

/-- A run before a failed allocator call is still one. -/
theorem ExhaustsW.pre {env : RefineHost.Env} {cap pb : Nat} {p : ByteArray} {P : Program} {i j : Nat}
    {ω ω1 : Regs} {μ μ1 : Memory} {x : RefineCtx} {n m : Nat}
    (run : FreeStepsH p (refineContractK cap env) i ω μ x j ω1 μ1 x n)
    (h : ExhaustsW env cap pb p P j ω1 μ1 x m) : ExhaustsW env cap pb p P i ω μ x (n + m) := by
  obtain ⟨ω', μ', k, run', e7, ha⟩ := h
  exact ⟨ω', μ', k, run.trans run', e7, ha⟩

theorem ExhaustsW.mono {env : RefineHost.Env} {cap pb : Nat} {p : ByteArray} {P : Program} {i : Nat}
    {ω : Regs} {μ : Memory} {x : RefineCtx} {n m : Nat} (h : ExhaustsW env cap pb p P i ω μ x n)
    (hnm : n ≤ m) : ExhaustsW env cap pb p P i ω μ x m := by
  obtain ⟨ω', μ', k, run', e7, ha⟩ := h
  exact ⟨ω', μ', k, run'.mono hnm, e7, ha⟩

/-! ## Sources -/

/-- The n octets at src, on the stack at or above sp, readable, apart from the vector v. -/
def StackSrc (sp v src n : Nat) (μ : Memory) : Prop :=
  sp ≤ src ∧ src + n + 16 < 4294967296 ∧ (src + n ≤ v ∨ v + 24 ≤ src) ∧
    ∀ a, src ≤ a → a < src + n → μ.readable a = true

/-- The n octets at src, in the data of an allocated chunk of s other than the one at ptr − 32. -/
def HeapSrc (s : State) (ptr src n : Nat) : Prop :=
  ∃ e ∈ chunks s, e.used = true ∧ e.addr + 32 ≠ ptr ∧ e.addr + 32 ≤ src ∧ src + n ≤ e.addr + 32 * e.size

/-! ## The grow path -/

/-- **`Vec<u8>::extend_from_slice` with growth** (58508, cap − len < n), under `refineContractK K env`
    (K ≥ 2²⁷) with the allocator's context `HeapCtx env pb S0 S1 μ s`: the vector `{cap, ptr, len}` at v
    (on the stack at or above sp), its buffer the data of an allocated chunk c of s (`c.addr + 32 = ptr`,
    0 < cap ≤ 32 · (c.size − 1)), and the n octets at src on the stack or in another allocated chunk's data.
    Either `realloc` gives a block r and the function returns to t with the vector
    `{nc, r, len + n}` (nc = `newCap cap len n`), r the data of an allocated chunk d of the new state s' of
    ⌈nc/32⌉ + 1 units, holding the old len octets then the n new ones; the context kept for s'; every other
    allocated chunk of s kept with its data; r either ptr or the data of no allocated chunk of s; the pages
    outside the heap, memory at or above sp but for the vector, memory below 196608 (with its access), the
    allocator's globals and the stack's access kept; ω₀, ω₁, ω₅, ω₆ restored. Or the run reaches a failed
    `realloc` (`ExhaustsW`, at 58363). Gas 7·n + 64·(c.size − 1) + 1800. -/
theorem extend_grow {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (x : RefineCtx) (ω : Regs) (μ : Memory) (s : State) (c : Chunk)
    (sp v src n cap ptr len ret t pb S0 S1 : Nat)
    (H : HeapCtx env pb S0 S1 μ s) (hc : c ∈ chunks s) (hcu : c.used = true) (hcp : c.addr + 32 = ptr)
    (hcc : cap ≤ 32 * (c.size - 1)) (hcap0 : 0 < cap) (hlc : len ≤ cap) (hgrow : cap < len + n)
    (hbig : 2 * cap < 1073741760 ∧ len + n < 1073741760)
    (hsp : S0 + 424 ≤ sp ∧ sp ≤ S1 ∧ 2147484072 ≤ sp ∧ sp % 8 = 0) (hv : sp ≤ v ∧ v + 24 ≤ S1)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat v)
    (h8 : ω[8] = UInt64.ofNat src) (h9 : ω[9] = UInt64.ofNat n)
    (vc : μ.readN v 8 = Num.encodeLE 8 cap) (vp : μ.readN (v + 8) 8 = Num.encodeLE 8 ptr)
    (vl : μ.readN (v + 16) 8 = Num.encodeLE 8 len)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hsrc : StackSrc sp v src n μ ∨ HeapSrc s ptr src n) :
    (∃ r s' ω' μ', FreeStepsH p (refineContractK K env) 58508 ω μ x t ω' μ' x
        (7 * n + 64 * (c.size - 1) + 1800) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      μ'.readN v 8 = Num.encodeLE 8 (newCap cap len n) ∧ μ'.readN (v + 8) 8 = Num.encodeLE 8 r ∧
      μ'.readN (v + 16) 8 = Num.encodeLE 8 (len + n) ∧
      μ'.readN r len = μ.readN ptr len ∧ μ'.readN (r + len) n = μ.readN src n ∧
      HeapCtx env pb S0 S1 μ' s' ∧
      (∃ d ∈ chunks s', d.used = true ∧ d.addr + 32 = r ∧ d.size = (newCap cap len n + 31) / 32 + 1) ∧
      (∀ e ∈ chunks s, e.used = true → e.addr + 32 ≠ ptr →
        e ∈ chunks s' ∧ ∀ a, InData e a → μ'.read a = μ.read a) ∧
      (r = ptr ∨ ∀ e ∈ chunks s, e.used = true → e.addr + 32 ≠ r) ∧
      PagesOut 48 pb μ μ' ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < v ∨ v + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) ∧ (∀ a, S0 ≤ a → μ'.writable a = μ.writable a)) ∨
    ExhaustsW env K pb p P 58508 ω μ x (7 * n + 64 * (c.size - 1) + 1800) := by
  have hb0 := H.hb0
  have hbT := H.hbT
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst := H.st
  have hba : s.base % 8 = 0 := by have := H.wf.2.1; omega
  obtain ⟨hc0, -, hcT⟩ := chunk_in H.wf hc hcu
  have hu : usable s ptr = c.size - 1 := by rw [← hcp, usable_of_chunk hc]
  obtain ⟨hnc1, hnc2, hnc3⟩ := newCap_ge cap len n
  have hncB : newCap cap len n < 1073741760 := by unfold newCap; omega
  generalize hnc : newCap cap len n = nc at hnc1 hnc2 hnc3 hncB
  have h5 : ω[5] = UInt64.ofNat ω[5].toNat := UInt64.ofNat_toNat.symm
  have h6 : ω[6] = UInt64.ofNat ω[6].toNat := UInt64.ofNat_toNat.symm
  have h5' := UInt64.toNat_lt ω[5]
  have h6' := UInt64.toNat_lt ω[6]
  unfold StackSrc HeapSrc at hsrc
  have hsrcB : (65536 ≤ src ∧ src + n < 2147483648) ∨ sp ≤ src := by
    rcases hsrc with ⟨h, -⟩ | ⟨e, he, heu, -, h1, h2⟩
    · exact Or.inr h
    · have := chunk_in H.wf he heu; exact Or.inl ⟨by omega, by omega⟩
  have hsrc64 : src + n + 16 < 4294967296 := by
    rcases hsrc with ⟨-, h, -⟩ | ⟨e, he, heu, -, -, h2⟩
    · exact h
    · have := (chunk_in H.wf he heu).2.2; omega
  -- 58508 … 58586: the room test fails, reserve called
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, aS, a0', a5', a6', fr1, rd1, wr1⟩ :=
    g1 (p := p) (P := P) (R := refineContractK K env) x ω μ sp v src n cap len ret ω[5].toNat ω[6].toNat
      ⟨by omega, by omega⟩ h0 h1 h5 h6 h7 h8 h9 (by omega) (by omega) h5' h6' (by omega) (by omega) hlc hgrow
      (by omega) vc vl (Or.inr hv.1)
      (fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)))
      (fun a h1 h2 => hst a (by omega) (by omega))
  -- 58251 … 58357: reserve, finish_grow, the realloc call
  have k1 : ∀ a, v ≤ a → a < v + 24 → μ1.read a = μ.read a := fun a h1 h2 => fr1 a (by omega) (Or.inr (by omega))
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b9, b10, m8, m16, m24, m56, m64, m72, fr2, rd2, wr2⟩ :=
    g2 (p := p) (P := P) (R := refineContractK K env) x ω1 μ1 (sp - 32) v n cap ptr len ⟨by omega, by omega⟩
      a0 a1 a5 a6 a7 a8 a9 (by omega) (Or.inr (by omega)) ⟨hcap0, by omega⟩ (by omega) (by omega)
      (by rw [Memory.readN_congr (fun j hj => k1 _ (by omega) (by omega))]; exact vc)
      (by rw [Memory.readN_congr (fun j hj => k1 _ (by omega) (by omega))]; exact vp)
      (fun a h1 h2 => by rw [rd1]; exact Memory.readable_of_writable (hst a (by omega) (by omega)))
      (fun a h1 h2 => by rw [wr1]; exact hst a (by omega) (by omega))
  rw [hnc] at b6 b10 m72
  have hlow : ∀ a, a < 4294967296 → (a < sp - 104 ∨ sp ≤ a) → μ2.read a = μ.read a := fun a h0 h1 =>
    (fr2 a h0 (by omega)).trans (fr1 a h0 (by omega))
  have wr12 : ∀ a, μ2.writable a = μ.writable a := fun a => by rw [wr2, wr1]
  have rd12 : ∀ a, μ2.readable a = μ.readable a := fun a => by rw [rd2, rd1]
  have H2 : HeapCtx env pb S0 S1 μ2 s := ctx_high H (fun a h => hlow a (by omega) (Or.inl (by omega))) wr12
  -- realloc
  rcases realloc_call (p := p) (P := P) (hb := 0) env K hK1 hK x ω2 μ2 s (sp - 104) ptr 1 nc pb S0 S1 H2
      ⟨c, hc, hcp, hcu⟩ (by omega) (by omega) hba b1 b7 b9 b10 (Nat.le_refl _) (by decide)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ with
    ⟨r, s', bb, ω3, μ3, hR, run3, e7, H3, dat3, keep3, ⟨d, hdm, hda, hdu, hds⟩, kp3, stk3, -, wst3, e0, e1,
      e5, e6, gl3, hbase, fresh⟩ |
    ⟨hR, ω3, μ3, run3, e7, -, -, e0, -, -, -, -⟩
  rotate_left
  · rw [hu] at run3
    have run4 := rret (p := p) (P := P) (R := refineContractK K env) x ω3 μ3 (by rw [e0, b0])
    exact Or.inr ⟨ω3, μ3, 58363, (run1.trans (run2.trans (run3.trans run4))).mono (by omega), e7,
      Or.inr ⟨rfl, s, 0, ptr, (1 + 31) / 32, (nc + 31) / 32, hR⟩⟩
  rw [hu] at run3 dat3
  obtain ⟨hd0, -, hdT⟩ := chunk_in H3.wf hdm hdu
  rw [hbase] at hd0 hdT
  have hdn : nc ≤ 32 * (d.size - 1) := by rw [hds]; omega
  have run4 := rret (p := p) (P := P) (R := refineContractK K env) x ω3 μ3 (by rw [e0, b0])
  have hF : ∀ a, sp - 104 ≤ a → a < 4294967296 → μ3.read a = μ2.read a := fun a h1 h2 => stk3 a h2 h1
  have wst : ∀ a, S0 ≤ a → a < S1 → μ3.writable a = true := fun a h1 h2 => by
    rw [wst3 a h1, wr12]; exact hst a h1 h2
  -- finish_grow's success path
  obtain ⟨ω5, μ5, run5, c0, c1, c5, c6, cr0, cr8, fr5, rd5, wr5⟩ :=
    g3 (p := p) (P := P) (R := refineContractK K env) x ω3 μ3 (sp - 104) r nc v ⟨by omega, by omega⟩
      (by rw [e1, b1]; congr 1 <;> omega) (by rw [e5, b5]; congr 1 <;> omega) (by rw [e6, b6]) e7 ⟨by omega, by omega⟩ (by omega)
      (by omega)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]
          rw [show sp - 104 + 16 = sp - 32 - 56 by omega]; exact m56)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]
          rw [show sp - 104 + 8 = sp - 32 - 64 by omega]; exact m64)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]
          rw [show sp - 104 = sp - 32 - 72 by omega]; exact m72)
      (fun a h1 h2 => wst a (by omega) (by omega))
  have k53 : ∀ a, sp - 56 ≤ a → a < 4294967296 → μ5.read a = μ2.read a := fun a h1 h2 =>
    (fr5 a h2 (Or.inr (by omega))).trans (hF a (by omega) h2)
  -- reserve stores the new buffer
  obtain ⟨ω6, μ6, run6, d0, d1, d5, d6, dv0, dv8, fr6, rd6, wr6⟩ :=
    g4 (p := p) (P := P) (R := refineContractK K env) x ω5 μ5 (sp - 80) v r nc n ⟨by omega, by omega⟩
      (by rw [c1]; congr 1; omega) c5 c6 (by omega) (Or.inr (by omega)) (by omega) (by omega) (by omega) (by omega)
      (by rw [show sp - 104 + 24 = sp - 80 by omega] at cr0; exact cr0)
      (by rw [show sp - 104 + 32 = sp - 80 + 8 by omega] at cr8; exact cr8)
      (by rw [Memory.readN_congr (fun j hj => k53 _ (by omega) (by omega))]
          rw [show sp - 80 + 40 = sp - 32 - 8 by omega]; exact m8)
      (by rw [Memory.readN_congr (fun j hj => k53 _ (by omega) (by omega))]
          rw [show sp - 80 + 32 = sp - 32 - 16 by omega]; exact m16)
      (by rw [Memory.readN_congr (fun j hj => k53 _ (by omega) (by omega))]
          rw [show sp - 80 + 24 = sp - 32 - 24 by omega]; exact m24)
      (fun a h1 h2 => by rw [rd5]; exact Memory.readable_of_writable (wst a (by omega) (by omega)))
      (fun a h1 h2 => by rw [wr5]; exact wst a (by omega) (by omega))
  -- the frame at S = sp − 32 and the vector's length, from μ1
  have k61 : ∀ a, sp - 32 ≤ a → a < 4294967296 → (a < v ∨ v + 16 ≤ a) → μ6.read a = μ1.read a :=
    fun a h1 h2 h3 => (fr6 a h2 h3).trans ((k53 a (by omega) h2).trans (fr2 a h2 (Or.inr (by omega))))
  obtain ⟨ω7, μ7, run7, f0, f1, f5, f6, f7, f8, f9, fl, fr7, rd7, wr7⟩ :=
    g5 (p := p) (P := P) (R := refineContractK K env) x ω6 μ6 (sp - 32) v src len r n ⟨by omega, by omega⟩
      (by rw [d1]; congr 1; omega) d5 d6 (by omega) (Or.inr (by omega)) (by omega) (by omega) (by omega)
      (by omega) (by omega)
      (by rw [Memory.readN_congr (fun j hj => k61 _ (by omega) (by omega) (Or.inl (by omega)))]; exact aS)
      dv8
      (by rw [Memory.readN_congr (fun j hj => k61 _ (by omega) (by omega) (Or.inr (by omega))),
            Memory.readN_congr (fun j hj => k1 _ (by omega) (by omega))]; exact vl)
      (fun a h1 h2 => by rw [wr6, wr5]; exact wst a (by omega) (by omega))
      (fun a h1 h2 => by rw [rd6, rd5]; exact Memory.readable_of_writable (wst a (by omega) (by omega)))
  -- the source is as at entry
  have ksrc : ∀ a, src ≤ a → a < src + n → μ7.read a = μ.read a ∧ μ7.readable a = true := by
    intro a h1 h2
    rcases hsrc with ⟨hs1, -, hs3, hs4⟩ | ⟨e, he, heu, hne, he1, he2⟩
    · refine ⟨?_, ?_⟩
      · rw [fr7 a (by omega) (Or.inr (by omega)), k61 a (by omega) (by omega) (by omega)]
        exact fr1 a (by omega) (Or.inr (by omega))
      · rw [rd7, rd6, rd5]
        have po := FreeStepsH.pagesOut H.bd run3
        rw [po.readable (Or.inr (by omega)), rd12]
        exact hs4 a h1 h2
    · have hin : InData e a := ⟨by omega, by omega⟩
      have hei := chunk_in H.wf he heu
      refine ⟨?_, ?_⟩
      · rw [fr7 a (by omega) (Or.inl (by omega)), fr6 a (by omega) (Or.inl (by omega)),
          fr5 a (by omega) (Or.inl (by omega)), kp3 a ⟨e, he, heu, hne, hin⟩]
        exact hlow a (by omega) (Or.inl (by omega))
      · rw [rd7, rd6, rd5]
        exact Memory.readable_of_writable (heap_writable H3 (keep3 e he heu hne) heu hin)
  -- the new block is apart from the source
  have hdj : r + len + n + 24 ≤ src ∨ src + n + 24 ≤ r + len := by
    rcases hsrc with ⟨hs1, -⟩ | ⟨e, he, heu, hne, he1, he2⟩
    · left; omega
    · have he' := keep3 e he heu hne
      have hed : e ≠ d := by
        intro h
        have hea : e.addr + 32 = r := by rw [h]; exact hda
        rcases fresh with hr | hr
        · exact hne (by omega)
        · exact hr e he heu hea
      have ht := H3.wf.2.2.2.1
      unfold TilesOk at ht
      rcases Services.Bootstrap.Decode.HeapFrame.Tiles.disjoint ht e he' d hdm hed with h | h
      · right; omega
      · left; omega
  clear hsrc
  obtain ⟨ω8, μ8, run8, k0, k1', k5, k6, kd, kfr, krd, kwr⟩ :=
    memcpy_any (p := p) (P := P) (R := refineContractK K env) x ω7 μ7 2552 58554 (sp - 32) (r + len) src n
      f0 f1 f7 f8 f9 (by decide) jte_1275 bs_58554 ⟨by omega, by omega, by omega⟩
      ⟨by rcases hsrcB with h | h <;> omega, by omega⟩ ⟨by omega, by omega⟩ hdj (Or.inr (by omega))
      (by rcases hsrcB with h | h <;> omega)
      (fun a h1 h2 => (ksrc a h1 h2).2)
      (fun a h1 h2 => by rw [wr7, wr6, wr5]; exact heap_writable H3 hdm hdu ⟨by omega, by omega⟩)
      (fun a h1 h2 => by rw [wr7, wr6, wr5]; exact wst a (by omega) (by omega))
  have k87 : ∀ a, sp - 32 ≤ a → a < 4294967296 → μ8.read a = μ7.read a := fun a h1 h2 =>
    kfr a h2 (Or.inr (by omega)) (Or.inr (by omega))
  obtain ⟨ω9, run9, l9, l0, l1, l5, l6⟩ :=
    w2 (p := p) (P := P) (R := refineContractK K env) x ω8 μ8 (sp - 32) len (by omega) k1' (by omega)
      (by rw [Memory.readN_congr (fun j hj => k87 _ (by omega) (by omega))]; exact fl)
      (fun a h1 h2 => by rw [krd, rd7, rd6, rd5]; exact Memory.readable_of_writable (wst a (by omega) (by omega)))
  have k81 : ∀ a, sp - 32 + 8 ≤ a → a < sp → μ8.read a = μ1.read a := fun a h1 h2 =>
    (k87 a (by omega) (by omega)).trans ((fr7 a (by omega) (Or.inr (by omega))).trans
      (k61 a (by omega) (by omega) (Or.inl (by omega))))
  obtain ⟨ω10, μ10, run10, e0', e1', e5', e6', el, efr, erd, ewr⟩ :=
    w3 (p := p) (P := P) (R := refineContractK K env) x ω9 μ8 (sp - 32) v n len ret t ω[5].toNat ω[6].toNat
      ⟨by omega, by omega⟩ (l1.trans k1') (l5.trans (k5.trans f5)) (l6.trans (k6.trans f6)) l9 (by omega)
      (Or.inr (by omega)) (by omega)
      (by rw [Memory.readN_congr (fun j hj => k81 _ (by omega) (by omega)), show sp - 32 + 24 = sp - 8 by omega]
          exact a0')
      (by rw [Memory.readN_congr (fun j hj => k81 _ (by omega) (by omega)), show sp - 32 + 16 = sp - 16 by omega]
          exact a5')
      (by rw [Memory.readN_congr (fun j hj => k81 _ (by omega) (by omega)), show sp - 32 + 8 = sp - 24 by omega]
          exact a6')
      h5' h6' hret hjt hbt
      (fun a h1 h2 => by rw [krd, rd7, rd6, rd5]; exact Memory.readable_of_writable (wst a (by omega) (by omega)))
      (fun a h1 h2 => by rw [kwr, wr7, wr6, wr5]; exact wst a (by omega) (by omega))
  have run := run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans
    (run8.trans (run9.trans run10))))))))
  -- what the steps after realloc keep
  have late : ∀ a, a < 2147483648 → (a < r + len ∨ r + len + n ≤ a) → μ10.read a = μ3.read a := by
    intro a h0 h1
    rw [efr a (by omega) (Or.inl (by omega)), kfr a (by omega) h1 (Or.inl (by omega)),
      fr7 a (by omega) (Or.inl (by omega)), fr6 a (by omega) (Or.inl (by omega)),
      fr5 a (by omega) (Or.inl (by omega))]
  have wr10 : ∀ a, μ10.writable a = μ3.writable a := fun a => by rw [ewr, kwr, wr7, wr6, wr5]
  subst hnc
  refine Or.inl ⟨r, s', ω10, μ10, run.mono (by omega), e0', by rw [e1']; congr 1; omega,
    by rw [e5', ← h5], by rw [e6', ← h6], ?_, ?_, el, ?_, ?_, ?_, ⟨d, hdm, hdu, hda, hds⟩, ?_, fresh,
    FreeStepsH.pagesOut H.bd run, ?_, ?_, ?_, ?_⟩
  · rw [Memory.readN_congr (fun j hj => efr _ (by omega) (Or.inl (by omega))),
      Memory.readN_congr (fun j hj => kfr _ (by omega) (Or.inr (by omega)) (Or.inr (by omega))),
      Memory.readN_congr (fun j hj => fr7 _ (by omega) (Or.inr (by omega)))]
    exact dv0
  · rw [Memory.readN_congr (fun j hj => efr _ (by omega) (Or.inl (by omega))),
      Memory.readN_congr (fun j hj => kfr _ (by omega) (Or.inr (by omega)) (Or.inr (by omega))),
      Memory.readN_congr (fun j hj => fr7 _ (by omega) (Or.inr (by omega)))]
    exact dv8
  · have hmin : len ≤ 32 * min (c.size - 1) ((newCap cap len n + 31) / 32) := by
      rcases Nat.le_total (c.size - 1) ((newCap cap len n + 31) / 32) with h | h
      · rw [Nat.min_eq_left h]; omega
      · rw [Nat.min_eq_right h]; omega
    rw [Memory.readN_congr (fun j hj => late _ (by omega) (Or.inl (by omega))), readN_prefix hmin dat3]
    exact Memory.readN_congr (fun j hj => hlow (ptr + j) (by omega) (Or.inl (by omega)))
  · rw [Memory.readN_congr (fun j hj => efr _ (by omega) (Or.inl (by omega))), kd]
    exact Memory.readN_congr (fun j hj => (ksrc _ (by omega) (by omega)).1)
  · exact ctx_congr_data H3 hdm (fun a h0 h1 => late a h0 (by omega)) wr10
  · intro e he heu hne
    have he' := keep3 e he heu hne
    have hed : e ≠ d := by
      intro h
      have hea : e.addr + 32 = r := by rw [h]; exact hda
      rcases fresh with hr | hr
      · exact hne (by omega)
      · exact hr e he heu hea
    refine ⟨he', fun a ha => ?_⟩
    have hca := ha
    unfold InData at hca
    have := (chunk_in H.wf he heu).2.2
    have hdd := data_disj H3.wf he' hdm hed ha
    rw [late a (by omega) (by omega), kp3 a ⟨e, he, heu, hne, ha⟩]
    exact hlow a (by omega) (Or.inl (by omega))
  · intro a h0 h1 h2
    rw [efr a h0 (by omega), kfr a h0 (Or.inr (by omega)) (Or.inr (by omega)),
      fr7 a h0 (Or.inr (by omega)), k61 a (by omega) h0 (by omega)]
    exact fr1 a h0 (Or.inr h1)
  · intro a ha'
    obtain ⟨kp, kr⟩ := FreeStepsH.keepRO H.bd run
    refine ⟨kr a (by unfold two32; omega) (Or.inl (by unfold pageSize; omega)) (H.ro a ha'), ?_⟩
    unfold Memory.readable
    rw [kp _ (Or.inl (by unfold pageSize; omega))]
  · intro a ha'
    have hg := ha'
    unfold Glob at hg
    rw [late a (by omega) (Or.inl (by omega)), gl3 a ha']
    exact hlow a (by omega) (Or.inl (by omega))
  · intro a ha'
    obtain ⟨kp, -⟩ := FreeStepsH.keepRO H.bd run
    unfold Memory.writable
    rw [kp _ (Or.inr (by unfold pageSize; omega))]

/-! ## Either path -/

/-- **`Vec<u8>::extend_from_slice`, with or without growth** (58508): `extend_grow`'s hypotheses
    without cap − len < n. Either the function returns to t with the vector `{cap', r, len + n}`
    (len + n ≤ cap'), r the data of an allocated chunk d of the new state s' with
    cap' ≤ 32 · (d.size − 1), holding the old len octets then the n new ones, and the rest as in
    `extend_grow` (without growth: cap' = cap, r = ptr, s' = s, from `Writer.extend_ok`); or the run
    reaches a failed `realloc` (`ExhaustsW`). Gas 7·n + 64·(c.size − 1) + 1800. -/
theorem extend_any {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (x : RefineCtx) (ω : Regs) (μ : Memory) (s : State) (c : Chunk)
    (sp v src n cap ptr len ret t pb S0 S1 : Nat)
    (H : HeapCtx env pb S0 S1 μ s) (hc : c ∈ chunks s) (hcu : c.used = true) (hcp : c.addr + 32 = ptr)
    (hcc : cap ≤ 32 * (c.size - 1)) (hcap0 : 0 < cap) (hlc : len ≤ cap)
    (hbig : 2 * cap < 1073741760 ∧ len + n < 1073741760)
    (hsp : S0 + 424 ≤ sp ∧ sp ≤ S1 ∧ 2147484072 ≤ sp ∧ sp % 8 = 0) (hv : sp ≤ v ∧ v + 24 ≤ S1)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat v)
    (h8 : ω[8] = UInt64.ofNat src) (h9 : ω[9] = UInt64.ofNat n)
    (vc : μ.readN v 8 = Num.encodeLE 8 cap) (vp : μ.readN (v + 8) 8 = Num.encodeLE 8 ptr)
    (vl : μ.readN (v + 16) 8 = Num.encodeLE 8 len)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hsrc : StackSrc sp v src n μ ∨ HeapSrc s ptr src n) :
    (∃ cap' r s' ω' μ', FreeStepsH p (refineContractK K env) 58508 ω μ x t ω' μ' x
        (7 * n + 64 * (c.size - 1) + 1800) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      μ'.readN v 8 = Num.encodeLE 8 cap' ∧ μ'.readN (v + 8) 8 = Num.encodeLE 8 r ∧
      μ'.readN (v + 16) 8 = Num.encodeLE 8 (len + n) ∧ len + n ≤ cap' ∧
      μ'.readN r len = μ.readN ptr len ∧ μ'.readN (r + len) n = μ.readN src n ∧
      HeapCtx env pb S0 S1 μ' s' ∧
      (∃ d ∈ chunks s', d.used = true ∧ d.addr + 32 = r ∧ cap' ≤ 32 * (d.size - 1)) ∧
      (∀ e ∈ chunks s, e.used = true → e.addr + 32 ≠ ptr →
        e ∈ chunks s' ∧ ∀ a, InData e a → μ'.read a = μ.read a) ∧
      (r = ptr ∨ ∀ e ∈ chunks s, e.used = true → e.addr + 32 ≠ r) ∧
      PagesOut 48 pb μ μ' ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < v ∨ v + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) ∧ (∀ a, S0 ≤ a → μ'.writable a = μ.writable a)) ∨
    ExhaustsW env K pb p P 58508 ω μ x (7 * n + 64 * (c.size - 1) + 1800) := by
  by_cases hroom : len + n ≤ cap
  rotate_left
  · rcases extend_grow env K hK1 hK x ω μ s c sp v src n cap ptr len ret t pb S0 S1 H hc hcu hcp hcc hcap0 hlc
        (by omega) hbig hsp hv h0 h1 h7 h8 h9 vc vp vl hret hjt hbt hsrc with
      ⟨r, s', ω', μ', run, e0, e1, e5, e6, ev, ev8, el, eo, ed, H', ⟨d, hdm, hdu, hda, hds⟩, rest⟩ | hx
    · obtain ⟨hnc1, -, -⟩ := newCap_ge cap len n
      refine Or.inl ⟨newCap cap len n, r, s', ω', μ', run, e0, e1, e5, e6, ev, ev8, el, hnc1, eo, ed, H',
        ⟨d, hdm, hdu, hda, by rw [hds]; omega⟩, rest⟩
    · exact Or.inr hx
  have hb0 := H.hb0
  have hbT := H.hbT
  have hSb := H.hSb
  have hS1 := H.hS1
  have hst := H.st
  obtain ⟨hc0, -, hcT⟩ := chunk_in H.wf hc hcu
  unfold StackSrc HeapSrc at hsrc
  have hsrcB : (65536 ≤ src ∧ src + n < 2147483648) ∨ sp ≤ src := by
    rcases hsrc with ⟨h, -⟩ | ⟨e, he, heu, -, h1, h2⟩
    · exact Or.inr h
    · have := chunk_in H.wf he heu; exact Or.inl ⟨by omega, by omega⟩
  have hsrc64 : src + n + 16 < 4294967296 := by
    rcases hsrc with ⟨-, h, -⟩ | ⟨e, he, heu, -, -, h2⟩
    · exact h
    · have := (chunk_in H.wf he heu).2.2; omega
  have hdj : ptr + len + n + 24 ≤ src ∨ src + n + 24 ≤ ptr + len := by
    rcases hsrc with ⟨hs1, -⟩ | ⟨e, he, heu, hne, he1, he2⟩
    · left; omega
    · have hce : c ≠ e := fun h => hne (by rw [← h]; exact hcp)
      have ht := H.wf.2.2.2.1
      unfold TilesOk at ht
      rcases Services.Bootstrap.Decode.HeapFrame.Tiles.disjoint ht c hc e he hce with h | h
      · left; omega
      · right; omega
  have hsp' : 65536 + 128 ≤ sp ∧ sp < 4294967296 ∧ sp % 8 = 0 := ⟨by omega, by omega, hsp.2.2.2⟩
  have hdst : 65536 ≤ ptr + len ∧ ptr + len + n + 16 < 4294967296 := ⟨by omega, by omega⟩
  have hsrc' : 65536 ≤ src ∧ src + n + 16 < 4294967296 := ⟨by rcases hsrcB with h | h <;> omega, hsrc64⟩
  have hfs : sp ≤ src ∨ src + n + 16 ≤ sp - 80 := by rcases hsrcB with h | h <;> omega
  have hrv : ∀ a, v ≤ a → a < v + 24 → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (hst a (by omega) (by omega))
  have hwv : ∀ a, v + 16 ≤ a → a < v + 24 → μ.writable a = true := fun a h1 h2 => hst a (by omega) (by omega)
  have hr : ∀ a, src ≤ a → a < src + n → μ.readable a = true := by
    intro a h1 h2
    rcases hsrc with ⟨-, -, -, hs4⟩ | ⟨e, he, heu, -, he1, he2⟩
    · exact hs4 a h1 h2
    · exact Memory.readable_of_writable (heap_writable H he heu (show InData e a from ⟨by omega, by omega⟩))
  clear hsrc
  have hwd : ∀ a, ptr + len ≤ a → a < ptr + len + n → μ.writable a = true := fun a h1 h2 =>
    heap_writable H hc hcu (show InData c a from ⟨by omega, by omega⟩)
  have hw : ∀ a, sp - 80 ≤ a → a < sp → μ.writable a = true := fun a h1 h2 => hst a (by omega) (by omega)
  obtain ⟨ω', μ', run, e0, e1, e5, e6, ed, el, efr, erd, ewr⟩ :=
    extend_ok (p := p) (P := P) (R := refineContractK K env) x ω μ sp v src n cap ptr len ret t
      hsp' h0 h1 h7 h8 h9 hroom (by omega) vc vp vl (by omega) (Or.inr hv.1) hdst hsrc' hdj (Or.inr (by omega))
      hfs (Or.inr (by omega)) hret hjt hbt hrv hwv hr hwd hw
  refine Or.inl ⟨cap, ptr, s, ω', μ', run.mono (by omega), e0, e1, e5, e6, ?_, ?_, el, hroom, ?_, ed,
    ctx_congr_data H hc (fun a h0 h1 => efr a (by omega) (Or.inl (by omega)) (by omega) (Or.inl (by omega)))
      ewr,
    ⟨c, hc, hcu, hcp, hcc⟩, ?_, Or.inl rfl, FreeStepsH.pagesOut H.bd run, ?_, ?_, ?_, fun a _ => ewr a⟩
  · rw [show μ'.readN v 8 = μ.readN v 8 from Memory.readN_congr (fun j hj => efr (v + j) (by omega)
      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)))]
    exact vc
  · rw [show μ'.readN (v + 8) 8 = μ.readN (v + 8) 8 from Memory.readN_congr (fun j hj => efr (v + 8 + j)
      (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)))]
    exact vp
  · apply Memory.readN_congr; intro j hj; exact efr (ptr + j) (by omega) (Or.inl (by omega)) (Or.inl (by omega))
      (Or.inl (by omega))
  · intro e he heu hne
    have hec : e ≠ c := fun h => hne (by rw [h]; exact hcp)
    refine ⟨he, fun a ha => ?_⟩
    have hca := ha
    unfold InData at hca
    have := (chunk_in H.wf he heu).2.2
    have hdd := data_disj H.wf he hc hec ha
    exact efr a (by omega) (Or.inl (by omega)) (by omega) (Or.inl (by omega))
  · intro a h0 h1 h2
    exact efr a h0 (Or.inr (by omega)) (Or.inr (by omega)) (by omega)
  · intro a ha
    exact ⟨efr a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)), erd a⟩
  · intro a ha
    unfold Glob at ha
    exact efr a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))

end Services.Bootstrap.Encode.WriterGrow
