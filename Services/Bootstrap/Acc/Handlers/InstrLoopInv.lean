import Services.Bootstrap.Acc.Handlers.InstrLoopOwn
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
- the results' payloads avoid those buffers and the results buffer (`PayAvoid`, for the push), an empty
  results `Vec`'s pointer is no chunk's data address, and a non-empty one's chunk has room for its cap;
- the `Zombify` flag at sp + 160 is 1 iff a `Zombify` was among the instructions done (zs);
- the frame constants (2⁶³ at sp + 184, 2⁶³ + 1 at sp + 216, the formatter word 678 at sp + 200).

At the exit (15028, `il_head_end`: cur = end, so `is = []` by `IterOwn.hend`) these are `row_eleven`'s
premises.
-/

namespace Services.Bootstrap.Acc.Handlers.InstrLoop

open JAM.Codec (fixed)
open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.Alloc Services.Bootstrap.Acc Services.Bootstrap.Spec Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Acc.Handlers.Results Services.Bootstrap.Acc.Handlers.InstrRep
  Services.Bootstrap.Acc.Handlers.RowEleven Services.Bootstrap.Acc.Handlers.ResultsDrop
  Services.Bootstrap.CodeX Services.Bootstrap.Acc.Handlers.KeyEnc Services.Bootstrap.Acc.Handlers.ResultsInit
  Services.Bootstrap.Acc.Handlers.ResStore Services.Bootstrap.Acc.Handlers.RecentSlotWrite

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
  /-- The results' payloads avoid the `IntoIter`'s buffers and the results buffer (the push writes there). -/
  hpay : PayAvoid μ st (rdN μ (sp + 456) 8) rs
    (iterFree B μ (sp + 472) is.length ++ optBuf (rdN μ (sp + 448) 8) (rdN μ (sp + 456) 8))
  /-- An empty results `Vec`'s dangling pointer is below 32, so it is no chunk's data address. -/
  hrp0 : rdN μ (sp + 448) 8 = 0 → rdN μ (sp + 456) 8 < 32
  /-- A results buffer (cap ≠ 0) is the data of an allocated chunk with room for cap items. -/
  hroom : rdN μ (sp + 448) 8 ≠ 0 → ∃ d ∈ chunks st, d.used = true ∧ d.addr + 32 = rdN μ (sp + 456) 8 ∧
    rdN μ (sp + 456) 8 + 144 * rdN μ (sp + 448) 8 ≤ d.addr + 32 * d.size
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

/-- **The loop's exit into row 11** (8540 → 15028 → 6766): at the head with cur = end, the run implements
    `if zs then pure () else store (Key.results package item) (encodeResults rs)` (GP v0.8.0 Appendix B,
    Ω_W; quirk Q4) and ends in `R7Post` with `iterFree ++ tailFree` freed, as `row_eleven`, from
    `LoopAt` and `row_eleven`'s remaining premises (`LoopHyp`'s bounds, the item index, the key-size
    word, `set`'s error table, `StoreFit`). -/
theorem loop_exit {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : AccEnv) {pb S0 S1 : Nat} (hE : ExtendH p P env pb S0 S1) (hO : OkEncH p P env pb S0 S1)
    (B : InstrRep) (hD : DropInstrsH B p P env.code pb S0 S1)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    (Ab : St Stream → Prop) (hAb1 : ∀ s : St Stream, s.i = 36528 → Ab s)
    (hAb2 : ∀ s : St Stream, s.i = 34070 → Ab s) (hAbX : ∀ s : St Stream, (s.i = 40611 ∨ s.i = 40821) ∧ s.ω[7] = UInt64.ofNat 0 → Ab s)
    (s : St Stream) (st : State) (sp item kc : Nat) (is : List Spec.Instr) (rs : List Spec.Result) (zs : Bool)
    (hi : s.i = 8540) (h1 : s.ω[1] = UInt64.ofNat sp)
    (LA : LoopAt B env.code pb S0 S1 sp is rs zs s.μ st)
    (he : rdN s.μ (sp + 480) 8 = rdN s.μ (sp + 496) 8)
    (L : LoopHyp pb S0 S1 sp (rdN s.μ (sp + 456) 8) (rdN s.μ (sp + 464) 8) rs st s.μ)
    (hitem : s.μ.readN (sp + 176) 2 = fixed 2 item)
    (mc : s.μ.readN 68696 8 = Num.encodeLE 8 kc) (hkc : 35 ≤ kc ∧ kc + 31 < 68719476736)
    (ht8 : rdN s.μ 69072 4 = 4294900408) (ht4 : rdN s.μ 69056 4 = 4294900402)
    (hro : ∀ a, 68680 ≤ a → a < 69076 → s.μ.readable a = true) (hvals : StoreFit s.c) :
    Impl p (accContractS env) env Ab
      (if zs then pure () else store (.results (s.μ.readN (sp + 312) 32) item) (encodeResults rs))
      (fun _ => R7Post env.code pb S0 S1 sp s.ω[5] st s.μ
        (iterFree B s.μ (sp + 472) is.length ++ tailFree s.μ sp)) s := by
  obtain ⟨i, ω, μ, c0, f⟩ := s
  dsimp only at hi h1 LA he L hitem mc ht8 ht4 hro hvals ⊢
  subst hi
  have hT := LA.H.hS1
  obtain ⟨hs1, hs2, hs3⟩ := LA.hsp
  have hSt := LA.H.st
  obtain ⟨ω1, run1, a1, a5⟩ := il_head_end (R := KeepCtx (accContractS env)) (P := P) (c0, f) ω μ sp
    (rdN μ (sp + 496) 8) h1 ⟨by omega, by omega⟩ (rdN_lt8 μ _) (by rw [← he]; exact readN_enc μ _ 8)
    (readN_enc μ _ 8) (fun a h1 h2 => Memory.readable_of_writable (hSt a (by omega) (by omega)))
  have R11 := row_eleven env hE hO B hD cap hcap1 hcap Ab hAb1 hAb2 hAbX ⟨15028, ω1, μ, c0, f⟩ st sp
    (if zs then 1 else 0) item kc rs is zs rfl (a1.trans h1) hs1 hs2 LA.I LA.T L hs3 LA.hnd LA.hav LA.flag
    (by cases zs <;> decide) hitem mc hkc ht8 ht4 hro hvals
  dsimp only at R11
  rw [a5] at R11
  exact Impl.pre _ _ (s' := ⟨15028, ω1, μ, c0, f⟩) ⟨_, run1⟩ rfl R11

end Services.Bootstrap.Acc.Handlers.InstrLoop
