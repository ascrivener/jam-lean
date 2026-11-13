import Services.Bootstrap.Fmt.OracleRefine

/-!
# The allocator interface under refine's contract, keeping the context

Logging changes no state (the settled scope: the log path is left out of the spec), and the format
code makes one kind of host call, the allocator's `grow_heap` (Ω_♊, GP v0.8.0 Appendix B), which
keeps refine's context. The Fmt theorems are generic in the contract R, so a caller that tracks the
context across a formatting call instantiates them at `refineKeep cap env`: refine's contract with
every continuing host call keeping the context.

- `HeapHost.keepX H`: H's contracts, each call also keeping the context; still a host fit for the
  allocator.
- `FreeStepsH.of_keepX`: a run under such a contract keeps the context and is a run under the
  original one.
- `allocOk_refineK`: `AllocOk` under `refineKeep cap env`.
-/

namespace Services.Bootstrap.Alloc

open PVM JAM

variable {X : Type}

/-- **A host's contracts, each continuing call also keeping the context**: still a host fit for the
    allocator (`grow_heap` keeps the context). -/
def HeapHost.keepX (H : HeapHost X) : HeapHost X where
  code := H.code
  rel cap h ω μ x r ω' μ' x' := H.rel cap h ω μ x r ω' μ' x' ∧ x' = x
  grow cap hc a pb hbd ω μ x h hp ha hb hcost := ⟨H.grow cap hc a pb hbd ω μ x h hp ha hb hcost, rfl⟩
  keep cap pb hbd h ω μ x ω' μ' x' hr := H.keep cap pb hbd h ω μ x ω' μ' x' hr.1
  le cap h1 h2 h ω μ x ω' μ' x' hr := ⟨H.le cap h1 h2 h ω μ x ω' μ' x' hr.1, hr.2⟩

end Services.Bootstrap.Alloc

namespace PVM.FreeStepsH

variable {X : Type} {p : ByteArray} {R : HostRel X}

/-- **A run whose every continuing host call keeps the context keeps it**, and is a run under the
    contract without that condition. -/
theorem of_keepX {i ω μ x i' ω' μ' x' n}
    (h : FreeStepsH p (fun h ω μ x r ω' μ' x' => R h ω μ x r ω' μ' x' ∧ x' = x) i ω μ x i' ω' μ' x' n) :
    x' = x ∧ FreeStepsH p R i ω μ x i' ω' μ' x' n := by
  induction h with
  | refl => exact ⟨rfl, .refl⟩
  | pad _ ih => exact ⟨ih.1, .pad ih.2⟩
  | next hn hc _ ih => exact ⟨ih.1, .next hn hc ih.2⟩
  | host hP hc hs hr _ ih => exact ⟨ih.1.trans hr.2, .host hP hc hs hr.1 ih.2⟩

end PVM.FreeStepsH

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

/-- **Refine's contract, every continuing host call keeping the context** (`refineContractK cap env`
    under `HeapHost.keepX`). -/
def refineKeep (cap : Nat) (env : RefineHost.Env) : HostRel RefineCtx :=
  (refineHeap env).keepX.rel cap

/-- A run under `refineKeep` keeps the context and is a run under refine's contract. -/
theorem refineKeep_run {p : ByteArray} {cap : Nat} {env : RefineHost.Env} {i i' n : Nat} {ω ω' : Regs}
    {μ μ' : Memory} {x x' : RefineCtx} (h : FreeStepsH p (refineKeep cap env) i ω μ x i' ω' μ' x' n) :
    x' = x ∧ FreeStepsH p (refineContractK cap env) i ω μ x i' ω' μ' x' n :=
  FreeStepsH.of_keepX (R := refineContractK cap env) h

/-- **`AllocOk` under refine's contract keeping the context**, for any cap from 2²⁷. -/
theorem allocOk_refineK {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap pb S0 S1 : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) :
    AllocOk p (refineKeep cap env) env pb S0 S1 := by
  intro ω μ x s sp size al H h1 h7 h8 hal hal1 hs hsp hS0 hS1
  rcases alloc_callG (p := p) (P := P) (hb := 0) (refineHeap env).keepX cap hcap1 hcap x ω μ s sp size al pb
      S0 S1 H h1 h7 h8 hal hal1 hs hsp ⟨hS0, hS1⟩ with
    ⟨ptr, s', ω', μ', ha, run, H', keep, hnew, hfresh, hk, e7, efr, e0, e1, e5, e6⟩ |
    ⟨ha, ω', μ', run, e7, -, -, -, -, -⟩
  · left
    have run0 := (refineKeep_run run).2
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
    refine ⟨ptr, s', ω', μ', x, run, H', hb', ⟨⟨access_of_keepRO H.bd run0,
      fun b hb hq hw => (FreeStepsH.keepRO H.bd run0).2 b hb hq hw,
      fun a ha hb _ => efr a hb ha, HKeepG.glob hk hG⟩, keep, fun c hc hu a ha => ?_⟩,
      hnew, fun d hd hu e => ?_, by simp only at hcb; have := H'.hb0; omega, e7, e0, e1, e5, e6⟩
    · have hc' := keep c hc hu
      unfold InData at ha
      exact hk.hkeep a (off_hdr_data hwf' H'.hb0 H'.hbT hc' ha.1 ha.2)
    · have hd' := keep d hd hu
      have := Tiles.addr_inj ht' d hd' _ hnew (by simp only; exact e)
      exact hfresh d hd hu this
  · right
    exact ⟨ω', μ', x, run, e7, 0, ha⟩

end Services.Bootstrap.Fmt
