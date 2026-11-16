import Services.Bootstrap.Acc.Handlers.InstrLoopHyp
import Services.Bootstrap.Acc.Handlers.RowElevenFront

/-!
# R5, the instruction loop: the invariant at the head (8540)

Spec `onWorkItem`'s `for i in is do …` (GP v0.8.0 Appendix B, Ω_W; bootstrap's own loop), with `is`
split into the instructions done and the instructions left `is`, and `rs` the results so far.

`LoopAt` is what holds at the head 8540 (memory μ, allocator state st):
- the allocator's context, and the stack room of `DropInstrsH` and the R5 hypotheses;
- the `IntoIter` at sp + 472 owns the instructions left (`IterOwn`);
- row 11's premises for the results so far: `TailHyp` (the results owned as `ResultsOwn`, the frame's
  three buffers), `ResultsAvoid` against the `IntoIter`'s buffers, and `(iterFree ++ tailFree).Nodup`;
  the results' count at sp + 464, within the cap at sp + 448;
- the `Zombify` flag at sp + 160 is 1 iff a `Zombify` was among the instructions done (zs);
- the frame constants (2⁶³ at sp + 184, 2⁶³ + 1 at sp + 216, the formatter word 678 at sp + 200).

At the exit (15028, `il_head_end`: cur = end, so `is = []` by `IterOwn.hend`) these are `row_eleven`'s
premises, except `LoopHyp`'s size bounds.
-/

namespace Services.Bootstrap.Acc.Handlers.InstrLoop

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.Alloc Services.Bootstrap.Acc Services.Bootstrap.Spec Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Acc.Handlers.Results Services.Bootstrap.Acc.Handlers.InstrRep
  Services.Bootstrap.Acc.Handlers.RowEleven Services.Bootstrap.Acc.Handlers.ResultsDrop

/-- **The instruction loop's invariant at the head 8540** (see the module doc), for the instructions left
    `is`, the results so far `rs` and the `Zombify` flag zs. -/
structure LoopAt (B : InstrRep) (code : ByteArray) (pb S0 S1 sp : Nat) (is : List Spec.Instr)
    (rs : List Spec.Result) (zs : Bool) (μ : Memory) (st : State) : Prop where
  H : HeapCtxC code pb S0 S1 μ st
  hsp : 2147483648 + 4096 ≤ sp ∧ S0 + 4096 ≤ sp ∧ sp + 1632 ≤ S1
  I : IterOwn B μ st (sp + 472) is
  T : TailHyp code pb S0 S1 μ st sp
  hn : rdN μ (sp + 464) 8 = rs.length
  hcap : rs.length ≤ rdN μ (sp + 448) 8
  hav : ResultsAvoid μ st (rdN μ (sp + 456) 8) rs (iterFree B μ (sp + 472) is.length)
  hnd : (iterFree B μ (sp + 472) is.length ++ tailFree μ sp).Nodup
  flag : rdN μ (sp + 160) 8 = if zs then 1 else 0
  c184 : rdN μ (sp + 184) 8 = 9223372036854775808
  c216 : rdN μ (sp + 216) 8 = 9223372036854775809
  c200 : rdN μ (sp + 200) 8 = 678

/-- At the end (cur = end) no instruction is left. -/
theorem LoopAt.nil_of_end {B : InstrRep} {code : ByteArray} {pb S0 S1 sp : Nat} {is : List Spec.Instr}
    {rs : List Spec.Result} {zs : Bool} {μ : Memory} {st : State} (L : LoopAt B code pb S0 S1 sp is rs zs μ st)
    (he : rdN μ (sp + 472 + 8) 8 = rdN μ (sp + 472 + 24) 8) : is = [] := by
  have h := L.I.hend
  rw [← he] at h
  exact List.length_eq_zero_iff.1 (by omega)

end Services.Bootstrap.Acc.Handlers.InstrLoop
