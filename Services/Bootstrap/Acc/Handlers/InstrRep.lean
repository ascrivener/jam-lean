import Services.Bootstrap.Acc.Handlers.ResultsDropRun

/-!
# The instructions' representation (`InstrRep`) and the instructions' drop (`DropInstrsH`)

Plan B (Adam, decision 23): T2 is stated with named hypotheses. `InstrRep` is the parameter shared by
the R3 (output decode) and R6 (per-handler) hypotheses and by R5/R7: how a decoded `Spec.Instr` sits in
its 232-octet slot of the instructions' `Vec` (GP v0.8.0 Appendix B, Ω_W's input `is`), with the heap
buffers the slot owns. Its fields: `rep` (the representation), `foot` (the buffers' data addresses,
in the order the slot's drop frees them) and `frame` (`rep` survives any change that keeps those
buffers' chunks with their data), `tag` (the slot's first word decodes to the instruction's index) and
`notNone` (that word is not `Option::None`'s niche). **Obligation:** T1's per-kind `Rep`s discharge
it, `tag` and `notNone` included.

`DropInstrsH` (decided by the parent, option (A) for R7's drops) is the named, frame-only hypothesis
for 33214, the drop of the instructions' `IntoIter` (buf at v, cur at v + 8, cap at v + 16, end at
v + 24; the remaining slots [cur, end), 232 octets each; per-kind drops through the table at 68312):
it frees each remaining slot's `foot`, then the buffer if its cap is not 0, keeps every other allocated
chunk with its data, and keeps the memory from the caller's sp up. It is listed in
`docs/whats-proven.md` and `docs/t2-remaining.md`.
-/

namespace Services.Bootstrap.Acc.Handlers.InstrRep

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Acc.Handlers.ResultsDrop

/-- The buffer freed at a cap word c with pointer q: none if c = 0. -/
def optBuf (c q : Nat) : List Nat := if c = 0 then [] else [q]

/-- The constructor index of an instruction (`Instruction`'s codec tag, GP v0.8.0 Appendix B;
    bootstrap's declaration order, `Spec.Instr`): `createService` = 0, …, `assignForGasCost` = 24. -/
def instrIdx : Spec.Instr → Nat
  | .createService .. => 0 | .upgrade .. => 1 | .transfer .. => 2 | .zombify .. => 3 | .eject .. => 4
  | .deleteItems .. => 5 | .solicit .. => 6 | .forget .. => 7 | .lookup .. => 8 | .importSegs .. => 9
  | .exportSegs .. => 10 | .bless .. => 11 | .assign .. => 12 | .designate .. => 13 | .yield .. => 14
  | .checkpoint => 15 | .panic => 16 | .provide .. => 17 | .lookedUp .. => 18 | .imported .. => 19
  | .exported .. => 20 | .randomStorageRefine .. => 21 | .randomStorageAccumulate .. => 22
  | .benchmark => 23 | .assignForGasCost .. => 24

/-- The tag the instruction loop decodes from a slot's first word w (8627, `InstrLoop.slotTag`):
    w − 2⁶³ + 1 for w in the niche [2⁶³, 2⁶³ + 24), else 0 (the dataful variant). -/
def wordTag (w : Nat) : Nat :=
  if 9223372036854775808 ≤ w ∧ w < 9223372036854775832 then w - 9223372036854775807 else 0

/-- **The instructions' representation** (see the module doc). -/
structure InstrRep where
  /-- The slot's 232 octets b, with the heap buffers they point to in μ, represent the instruction. -/
  rep : Spec.Instr → List UInt8 → Memory → Prop
  /-- The data addresses of the heap buffers the slot b owns, in the order its drop frees them. -/
  foot : List UInt8 → List Nat
  /-- `rep` survives a change that keeps each owned buffer's chunk (allocated in some state st) with
      its data. -/
  frame : ∀ (i : Spec.Instr) (b : List UInt8) (μ μ' : Memory) (st : State), rep i b μ →
    (∀ q ∈ foot b, ∃ d ∈ chunks st, d.used = true ∧ d.addr + 32 = q ∧
      ∀ a, InData d a → μ'.read a = μ.read a) →
    rep i b μ'
  /-- The slot's first word decodes to the instruction's index (the loop's tag decode, 8627, and the
      dispatch, 8822). -/
  tag : ∀ (i : Spec.Instr) (b : List UInt8) (μ : Memory), rep i b μ → wordTag (Num.decodeLE (b.take 8)) = instrIdx i
  /-- The slot's first word is not `Option::None`'s niche 2⁶⁴ − 2 (the loop's end test, 8564). -/
  notNone : ∀ (i : Spec.Instr) (b : List UInt8) (μ : Memory), rep i b μ →
    Num.decodeLE (b.take 8) ≠ 18446744073709551614

/-- The slot of the k-th remaining instruction (cursor cur). -/
def slot (μ : Memory) (cur k : Nat) : List UInt8 := μ.readN (cur + 232 * k) 232

/-- The buffers the drop of the `IntoIter` at v with m remaining instructions frees, in order: each
    remaining slot's `foot`, then the buffer (at v) if its cap (at v + 16) is not 0. -/
def iterFree (B : InstrRep) (μ : Memory) (v m : Nat) : List Nat :=
  ((List.range m).flatMap fun k => B.foot (slot μ (rdN μ (v + 8) 8) k)) ++
    optBuf (rdN μ (v + 16) 8) (rdN μ v 8)

/-- **The `IntoIter`'s ownership** (at v, against the allocator state st), with the remaining
    instructions `is`: end = cur + 232·|is|; each slot represents its instruction; the freed buffers are
    pairwise distinct, each the data of an allocated chunk; if is ≠ [], the cap is not 0 and the slots
    lie in the buffer's chunk. -/
structure IterOwn (B : InstrRep) (μ : Memory) (st : State) (v : Nat) (is : List Spec.Instr) : Prop where
  hend : rdN μ (v + 24) 8 = rdN μ (v + 8) 8 + 232 * is.length
  rep : ∀ k (h : k < is.length), B.rep is[k] (slot μ (rdN μ (v + 8) 8) k) μ
  nodup : (iterFree B μ v is.length).Nodup
  owned : ∀ q ∈ iterFree B μ v is.length, ∃ d ∈ chunks st, d.used = true ∧ d.addr + 32 = q
  slots : is ≠ [] → rdN μ (v + 16) 8 ≠ 0 ∧ ∃ d ∈ chunks st, d.used = true ∧ d.addr + 32 = rdN μ v 8 ∧
    rdN μ v 8 ≤ rdN μ (v + 8) 8 ∧ rdN μ (v + 24) 8 ≤ d.addr + 32 * d.size

/-- **`DropInstrsH`, the instructions' drop (33214), frame-only** (a named hypothesis, see the module
    doc): from ω₇ = v an `IntoIter` owned as `IterOwn` says, under any host relation, with sp's room
    (2³¹ + 4096 ≤ sp, S0 + 4096 ≤ sp, the iterator at or above sp) and a return address ω₀ that `djump`
    resolves to t, the call returns to t having freed `iterFree` (allocator state
    `(iterFree B μ v |is|).foldl free st`), with every other allocated chunk kept with its data (`Kept`),
    the memory from sp up, the globals and the octets that are not writable kept with the same access
    (`Frm`), and ω₁, ω₅, ω₆ kept. -/
def DropInstrsH (B : InstrRep) (p : ByteArray) (P : Program) (code : ByteArray) (pb S0 S1 : Nat) : Prop :=
  ∀ {X : Type} (R : HostRel X) (x : X) (ω : Regs) (μ : Memory) (st : State) (sp v ret t : Nat)
    (is : List Spec.Instr),
    HeapCtxC code pb S0 S1 μ st → IterOwn B μ st v is →
    ω[0] = UInt64.ofNat ret → ω[1] = UInt64.ofNat sp → ω[7] = UInt64.ofNat v →
    2147483648 + 4096 ≤ sp → S0 + 4096 ≤ sp → sp ≤ v → v + 32 ≤ S1 →
    (0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) → P.jumpTable.getD (ret / 2 - 1) 0 = t →
    P.isBlockStart t = true →
    ∃ ω' μ' N, FreeStepsH p R 33214 ω μ x t ω' μ' x N ∧
      HeapCtxC code pb S0 S1 μ' ((iterFree B μ v is.length).foldl free st) ∧
      Kept st μ (iterFree B μ v is.length) μ' ((iterFree B μ v is.length).foldl free st) ∧
      Frm μ sp μ' ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6]

end Services.Bootstrap.Acc.Handlers.InstrRep
