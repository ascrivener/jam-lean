import Services.Bootstrap.Fmt.Frame
import Services.Bootstrap.Alloc.ReallocFallbackTail

/-!
# The allocator interface under refine's host contract

`allocOk_refine`: one call of the `alloc` wrapper under `refineContractK cap env` (cap ≥ 2²⁷) meets
`AllocOk`, from `HeapCtx.alloc_call`. That theorem gives the run, the context, the heap frame
`HKeepG` and the stack. `FreeStepsH.keepRO` gives the page access and the read-only octets outside
the heap.
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

/-- Under the refine contract, every page outside the heap keeps its access: readability and
    writability of each octet there. -/
theorem access_of_keepRO {p : ByteArray} {cap : Nat} {env : RefineHost.Env} {pb i i' n : Nat}
    {ω ω' : Regs} {μ μ' : Memory} {x x' : RefineCtx} (hbd : heapBounds env.code = (48, pb))
    (run : FreeStepsH p (refineContractK cap env) i ω μ x i' ω' μ' x' n) :
    ∀ b, (b / pageSize < 48 ∨ pb ≤ b / pageSize) →
      μ'.readable b = μ.readable b ∧ μ'.writable b = μ.writable b := fun b hb => by
  have e := (FreeStepsH.keepRO hbd run).1 (b / pageSize) hb
  unfold Memory.readable Memory.writable
  rw [e]; exact ⟨rfl, rfl⟩

/-- **`AllocOk` under refine's contract**, for any cap from 2²⁷ (so any growth of the heap fits). -/
theorem allocOk_refine {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap pb S0 S1 : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) :
    AllocOk p (refineContractK cap env) env pb S0 S1 := by
  intro ω μ x s sp size al H h1 h7 h8 hal hal1 hs hsp hS0 hS1
  rcases alloc_call (p := p) (P := P) (hb := 0) env cap hcap1 hcap x ω μ s sp size al pb S0 S1 H h1 h7 h8 hal
      hal1 hs hsp ⟨hS0, hS1⟩ with
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
    refine ⟨ptr, s', ω', μ', x, run, H', hb', ⟨⟨access_of_keepRO H.bd run,
      fun b hb hq hw => (FreeStepsH.keepRO H.bd run).2 b hb hq hw,
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
