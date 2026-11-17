import Services.Bootstrap.Acc.Transfer.Trap

/-!
# T2's abort reason `AccAbort` and its well-formedness premise `ValuesFit`

**`AccAbort`** (`docs/bootstrap-target.md`, T2) is the one reason for which bootstrap's accumulate
may end ☇ where `Spec.accumulate` does not: **heap exhaustion** (Adam's standing decision). This
covers a failed allocation, and a request too large for the allocator (more than 2³⁷ − 32 octets,
or a size computation that overflows). Panics the spec itself makes (`orPanic` on FULL, Q18's
`remove` on FULL) are not aborts: there `Spec.accumulate` panics too.

As a state predicate, `AccAbort s` holds at
- a failed allocator call: the `alloc` wrapper's return 40611 or `realloc`'s return 40821 with
  ω₇ = 0 (as `Fmt.Exhausts` / `ExhaustsP`); or
- one of the blob's allocation-failure traps (`HeapTrapPc`).

**`HeapTrapPc`** lists every `trap` the program reaches after a null allocation. It is the whole
program's list, found from the disassembly (`scripts/allocfail/`: `table.tsv`, `chains.tsv`,
`chains2.tsv`), so later summaries do not need to change it. Each listed pc is a `trap` whose only
predecessors are
- the null test right after an allocation (`branch_eq_imm r 0 t` / `branch_ne_imm 7 0 t` on the
  allocator's result), or the `Err` test after one of the growth helpers 32989, 50146, 58327, 58717
  or `finish_grow` 40852, whose `Err` means only a size computation overflowed or the allocation
  returned null (32989: `mul_upper` ≠ 0 or a size above 2⁶³ at 33003 … 33031, else the null result of
  `realloc` / `alloc` at 33061 / 33096); or
- the fall-through of an allocation-size check (47977, 47554, 49325, 49639: a request above
  2³⁷ − 32; 48354, 49074: the same on ω₆; 40234: `alloc_zeroed`'s check), or 58631's second check
  `len + n` overflowing: requests too large, which also count as heap exhaustion.

`format_inner`'s trap 59710 is left out: it is also reached when a formatter returns `Err` (59665).
A formatting call's failed allocation is covered by the failed-call states instead.

**`ValuesFit`** is T2's premise on the octet strings the SDK reads with a length (decided
2026-11-15): each is shorter than 2⁶³ octets. That covers this service's storage values (`read`, the
SDK's `get`), every service's preimages (`lookup`, 49263) and the encoded inputs (`fetch` kind 14,
47490). The SDK reads a length of 2⁶⁴ − 1 as NONE and traps on lengths from 2⁶³.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap

/-- **The allocation-failure traps of the blob**: every `trap` reached after an allocation returned
    null, or after an allocation-size check failed (see the module docstring). -/
def HeapTrapPc (i : Nat) : Prop :=
  i ∈ ([481, 906, 1299, 1763, 2199, 2726, 3099, 3472, 3715, 3895, 4002, 6376,
    15362, 15363, 15364, 15365, 15366, 15367, 15368, 22838, 25652, 26396, 30284, 30373,
    32584, 32726, 32755, 32784, 32858, 32887, 32916, 32988, 34070, 34178, 35071, 35072,
    36528, 40234, 40851, 44914, 45642, 45975, 46299, 47554, 47977, 48354, 49074, 49325,
    49639, 50111, 50145, 58326, 58631] : List Nat)

instance (i : Nat) : Decidable (HeapTrapPc i) := by unfold HeapTrapPc; infer_instance

/-- **T2's abort reason: heap exhaustion.** A failed allocator call (40611 / 40821 with ω₇ = 0), or
    an allocation-failure trap (`HeapTrapPc`). -/
def AccAbort {Qu : Type} (s : St Qu) : Prop :=
  HeapTrapPc s.i ∨ ((s.i = 40611 ∨ s.i = 40821) ∧ s.ω[7] = UInt64.ofNat 0)

/-- `on_transfer`'s trap pcs are allocation-failure traps. -/
theorem heapTrapPc_of_heapTrapT {i : Nat} (h : HeapTrapT i) : HeapTrapPc i := by
  unfold HeapTrapT at h; unfold HeapTrapPc
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- `on_transfer`'s abort states are `AccAbort` states. -/
theorem accAbort_of_heapFailT {Qu : Type} {s : St Qu} (h : HeapFailT s) : AccAbort s := by
  rcases h with h | h
  · exact .inl (heapTrapPc_of_heapTrapT h)
  · exact .inr h

/-- **T2's premise on lengths**: this service's storage values, every service's preimages and the
    encoded inputs (`fetch` kind 14) are shorter than 2⁶³ octets. -/
def ValuesFit (env : AccEnv) (x : Implications) : Prop :=
  (∀ k w, x.self.storage.get? k = some w → w.length < 2 ^ 63) ∧
  (∀ s a h q, x.state.accounts.get? s = some a → a.preimages.get? h = some q → q.length < 2 ^ 63) ∧
  (Codec.varSeq AccumulateInput.encode env.inputs).length < 2 ^ 63

/-- `ValuesFit` gives `get`'s premise (`hfit` of `get_call`, `gk_call`, `tr_impl`). -/
theorem ValuesFit.storage {env : AccEnv} {x : Implications} (h : ValuesFit env x) :
    ∀ k w, x.self.storage.get? k = some w → w.length < 2 ^ 63 := h.1

end Services.Bootstrap.Acc
