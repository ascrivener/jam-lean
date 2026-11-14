import Services.Bootstrap.Fmt.ReallocCopy
import Services.Bootstrap.Fmt.OracleRefine
import Services.Bootstrap.Decode.ReallocCall
import Services.Bootstrap.Acc.HeapHost

/-!
# The allocator's call contracts for any host fit for the allocator

`allocOkC_heapHost` / `reallocCopyOkC_heapHost`: under `env.rel cap` of any `HeapHost` with a cap
of at least 2²⁷ (so any growth of the heap is within it), one call of the `alloc` wrapper meets
`AllocOkC` and one call of the `realloc` wrapper meets `ReallocCopyOkC`, from
`HeapCtx.alloc_callG` and `Services.Bootstrap.Decode.ReallocCall.realloc_callG`. The data copy comes from `realloc_callG`'s
`readN` equality over 32 · min(usable, ⌈size/32⌉) octets, where `usable s ptr` is c.size − 1 for
the chunk c at ptr − 32.

Specialisations: refine's contract (`refineHeap env`), and accumulate's `Acc.accContractK cap env`
(through `accHeapHost env`, whose `accGrowK` runs lift to `accContractK`), the latter for any
refine host `envH` with the same code (as `AccFmt` states its hypotheses).
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA Services.Bootstrap.Decode.ReallocOk

/-- **`AllocOkC` for any host fit for the allocator**, cap ≥ 2²⁷. -/
theorem allocOkC_heapHost {X : Type} {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X)
    (cap pb S0 S1 : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) :
    AllocOkC p (env.rel cap) env.code pb S0 S1 := by
  intro ω μ x s sp size al H h1 h7 h8 hal hal1 hs hsp hS0 hS1
  rcases alloc_callG (p := p) (P := P) (hb := 0) env cap hcap1 hcap x ω μ s sp size al pb S0 S1 H h1 h7 h8
      hal hal1 hs hsp ⟨hS0, hS1⟩ with
    ⟨ptr, s', ω', μ', ha, run, H', keep, hnew, hfresh, hk, e7, efr, e0, e1, e5, e6⟩ |
    ⟨ha, ω', μ', run, e7, -, -, -, -, -⟩
  · left
    have hb' := alloc_base H.wf ha
    have hwf' := H'.wf
    have ht' := hwf'.2.2.2.1
    unfold TilesOk at ht'
    have hcb := ht'.mem_lt _ hnew
    have hG : ∀ b, (fun a => ∃ c ∈ chunks s', c.addr = a) b → b + 16 ≤ 196616 ∨ 196792 ≤ b := by
      rintro b ⟨c, hc, rfl⟩
      have := ht'.mem_lt c hc
      have := H'.hb0
      right; omega
    have kro := HeapHost.keepRO H.bd run
    refine ⟨ptr, s', ω', μ', x, run, H', hb', ⟨⟨fun b hb => ?_,
      fun b hb hq hw => kro.2 b hb hq hw,
      fun a ha hb _ => efr a hb ha, HKeepG.glob hk hG⟩, keep, fun c hc hu a ha => ?_⟩,
      hnew, fun d hd hu e => ?_, by simp only at hcb; have := H'.hb0; omega, e7, e0, e1, e5, e6⟩
    · have e := kro.1 (b / pageSize) hb
      unfold Memory.readable Memory.writable
      rw [e]; exact ⟨rfl, rfl⟩
    · have hc' := keep c hc hu
      unfold InData at ha
      exact hk.hkeep a (off_hdr_data hwf' H'.hb0 H'.hbT hc' ha.1 ha.2)
    · have hd' := keep d hd hu
      have := Tiles.addr_inj ht' d hd' _ hnew (by simp only; exact e)
      exact hfresh d hd hu this
  · right
    exact ⟨ω', μ', x, run, e7, 0, ha⟩

/-- `usable s ptr` is c.size − 1 for the chunk c whose data starts at ptr. -/
theorem usable_eq_of_chunk {s : State} {c : Chunk} {ptr : Nat} (hc : c ∈ chunks s) (hp : c.addr + 32 = ptr) :
    usable s ptr = c.size - 1 := by
  have := chunks_hdr c hc
  unfold usable
  rw [show ptr - 32 = c.addr by omega, this, wordSize_sizeWord]

/-- **`ReallocCopyOkC` for any host fit for the allocator**, cap ≥ 2²⁷. -/
theorem reallocCopyOkC_heapHost {X : Type} {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X)
    (cap pb S0 S1 : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) :
    ReallocCopyOkC p (env.rel cap) env.code pb S0 S1 := by
  intro ω μ x s sp ptr al size c H hba hc hcu hcp hsz hsz' h1 h7 h9 h10 hal1 hal2 hsp hsp8 hS0 hS1
  have hu := usable_eq_of_chunk hc hcp
  have ht := H.wf.2.2.2.1
  unfold TilesOk at ht
  rcases Services.Bootstrap.Decode.ReallocCall.realloc_callG (p := p) (P := P) (hb := 0) env cap hcap1 hcap x ω μ s sp ptr al size pb S0 S1 H
      ⟨c, hc, hcp, hcu⟩ hsz (by omega) hba h1 h7 h9 h10 hal1 hal2 ⟨hsp, hsp8⟩ ⟨hS0, hS1⟩ with
    ⟨r, s', b, ω', μ', hrl, run, e7, H', dat, keep, ⟨d, hdm, hda, hdu, hds⟩, kp, stk, -, -, e0, e1, e5, e6,
      gl, hbase, fresh⟩ |
    ⟨hrl, ω', μ', run, e7, -, -, -, -, -, -, -⟩
  · left
    rw [hu] at run dat
    have kro := HeapHost.keepRO H.bd run
    refine ⟨r, s', ω', μ', x, run, H', hbase, ⟨fun q hq => ?_, fun q hq hq' hw => kro.2 q hq hq' hw,
      fun a ha hb _ => stk a hb ha, gl⟩, fun e he heu hne => ?_, ⟨d, hdm, hdu, hda, hds, ?_⟩,
      fun i hi => ?_, e7, e0, e1, e5, e6⟩
    · have e := kro.1 (q / pageSize) hq
      unfold Memory.readable Memory.writable
      rw [e]; exact ⟨rfl, rfl⟩
    · have hep : e.addr + 32 ≠ ptr := fun h => hne (Tiles.addr_inj ht e he c hc (by omega))
      exact ⟨keep e he heu hep, fun a ha => kp a ⟨e, he, heu, hep, ha⟩⟩
    · rcases fresh with h | h
      · left; omega
      · right; intro e he heu hea; exact h e he heu (by omega)
    · have hi' : i < 32 * min (c.size - 1) ((size + 31) / 32) := by
        rcases Nat.le_total (c.size - 1) ((size + 31) / 32) with h | h
        · rw [Nat.min_eq_left h]; have := Nat.min_le_left (32 * (c.size - 1)) size; omega
        · rw [Nat.min_eq_right h]; have := Nat.min_le_right (32 * (c.size - 1)) size; omega
      rw [Memory.read_of_readN dat i hi', Memory.read_of_readN rfl i hi']
  · right
    rw [hu] at run
    exact ⟨ω', μ', x, run, e7, 0, hrl⟩

/-- **`ReallocOkC` for any host fit for the allocator**, cap ≥ 2²⁷. -/
theorem reallocOkC_heapHost {X : Type} {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X)
    (cap pb S0 S1 : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) :
    ReallocOkC p (env.rel cap) env.code pb S0 S1 :=
  (reallocCopyOkC_heapHost (p := p) (P := P) env cap pb S0 S1 hcap1 hcap).toReallocOkC

/-! ## Refine's contract -/

/-- **`AllocOk` under refine's contract**, from `allocOkC_heapHost` at `refineHeap env`. -/
theorem allocOk_refine' {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap pb S0 S1 : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) :
    AllocOk p (refineContractK cap env) env pb S0 S1 :=
  allocOkC_heapHost (p := p) (P := P) (refineHeap env) cap pb S0 S1 hcap1 hcap

/-- **`ReallocCopyOk` under refine's contract.** -/
theorem reallocCopyOk_refine {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (cap pb S0 S1 : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) :
    ReallocCopyOk p (refineContractK cap env) env pb S0 S1 :=
  reallocCopyOkC_heapHost (p := p) (P := P) (refineHeap env) cap pb S0 S1 hcap1 hcap

/-- **`ReallocOk` under refine's contract.** -/
theorem reallocOk_refine {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (cap pb S0 S1 : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) :
    ReallocOk p (refineContractK cap env) env pb S0 S1 :=
  (reallocCopyOk_refine (p := p) (P := P) env cap pb S0 S1 hcap1 hcap).toReallocOk

/-! ## Weakening the host relation -/

theorem AllocOkC.weaken {p : ByteArray} {X : Type} {R R' : HostRel X} {code : ByteArray} {pb S0 S1 : Nat}
    (hR : ∀ h ω μ x ω' μ' x', R h ω μ x .cont ω' μ' x' → R' h ω μ x .cont ω' μ' x')
    (h : AllocOkC p R code pb S0 S1) : AllocOkC p R' code pb S0 S1 := by
  intro ω μ x s sp size al H1 H2 H3 H4 H5 H6 H7 H8 H9 H10
  rcases h ω μ x s sp size al H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 with
    ⟨ptr, s', ω', μ', x', run, rest⟩ | ⟨ω', μ', x', run, rest⟩
  · exact Or.inl ⟨ptr, s', ω', μ', x', run.weaken hR, rest⟩
  · exact Or.inr ⟨ω', μ', x', run.weaken hR, rest⟩

theorem ReallocCopyOkC.weaken {p : ByteArray} {X : Type} {R R' : HostRel X} {code : ByteArray}
    {pb S0 S1 : Nat}
    (hR : ∀ h ω μ x ω' μ' x', R h ω μ x .cont ω' μ' x' → R' h ω μ x .cont ω' μ' x')
    (h : ReallocCopyOkC p R code pb S0 S1) : ReallocCopyOkC p R' code pb S0 S1 := by
  intro ω μ x s sp ptr al size c H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17
  rcases h ω μ x s sp ptr al size c H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 with
    ⟨r, s', ω', μ', x', run, rest⟩ | ⟨ω', μ', x', run, rest⟩
  · exact Or.inl ⟨r, s', ω', μ', x', run.weaken hR, rest⟩
  · exact Or.inr ⟨ω', μ', x', run.weaken hR, rest⟩

/-! ## Accumulate's contract -/

/-- **`AllocOkC` under accumulate's contract**, at its code, cap ≥ 2²⁷. -/
theorem allocOkC_acc {p : ByteArray} {P : Program} [HasCode p P] (env : AccEnv) (cap pb S0 S1 : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) :
    AllocOkC p (Acc.accContractK cap env) env.code pb S0 S1 :=
  (allocOkC_heapHost (p := p) (P := P) (Acc.accHeapHost env) cap pb S0 S1 hcap1 hcap).weaken
    fun _ _ _ _ _ _ _ hr => hr.2

/-- **`ReallocCopyOkC` under accumulate's contract**, at its code, cap ≥ 2²⁷. -/
theorem reallocCopyOkC_acc {p : ByteArray} {P : Program} [HasCode p P] (env : AccEnv)
    (cap pb S0 S1 : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) :
    ReallocCopyOkC p (Acc.accContractK cap env) env.code pb S0 S1 :=
  (reallocCopyOkC_heapHost (p := p) (P := P) (Acc.accHeapHost env) cap pb S0 S1 hcap1 hcap).weaken
    fun _ _ _ _ _ _ _ hr => hr.2

/-- **`AllocOk` under accumulate's contract** in `AccFmt`'s form: for any refine host `envH` with
    accumulate's code. -/
theorem allocOk_acc {p : ByteArray} {P : Program} [HasCode p P] (env : AccEnv) (envH : RefineHost.Env)
    (he : envH.code = env.code) (cap pb S0 S1 : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) :
    AllocOk p (Acc.accContractK cap env) envH pb S0 S1 := by
  rw [AllocOk_iff, he]; exact allocOkC_acc (p := p) (P := P) env cap pb S0 S1 hcap1 hcap

/-- **`ReallocCopyOk` under accumulate's contract**, for any refine host `envH` with its code. -/
theorem reallocCopyOk_acc {p : ByteArray} {P : Program} [HasCode p P] (env : AccEnv)
    (envH : RefineHost.Env) (he : envH.code = env.code) (cap pb S0 S1 : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) :
    ReallocCopyOk p (Acc.accContractK cap env) envH pb S0 S1 := by
  unfold ReallocCopyOk; rw [he]; exact reallocCopyOkC_acc (p := p) (P := P) env cap pb S0 S1 hcap1 hcap

/-- **`ReallocOk` under accumulate's contract** in `AccFmt`'s form. -/
theorem reallocOk_acc {p : ByteArray} {P : Program} [HasCode p P] (env : AccEnv) (envH : RefineHost.Env)
    (he : envH.code = env.code) (cap pb S0 S1 : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) :
    ReallocOk p (Acc.accContractK cap env) envH pb S0 S1 :=
  (reallocCopyOk_acc (p := p) (P := P) env envH he cap pb S0 S1 hcap1 hcap).toReallocOk

end Services.Bootstrap.Fmt
