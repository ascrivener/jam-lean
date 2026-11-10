import Services.Bootstrap.Refine.Pass
import Services.Bootstrap.Decode.GrowOne

/-!
# Refine's transform loop: an instruction passed through when the output is full

As `Pass.pass_elem`, for `len = cap`: before the copy the loop grows the output with
`RawVec::grow_one` (`Decode.GrowOne.grow_one_call`), to `max (2 len) 4` elements in a fresh chunk q holding
the old elements. Under refine's host contract (`refineContractK`), the step either reaches 5042 again
with the allocator's context kept (`HeapCtx`), or the heap is exhausted (`Exhausts`).
-/

namespace Services.Bootstrap.Refine.PassGrow

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeR
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Refine.Pass Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.HeapCtx

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **One instruction passed through, with the output full** (5042 … 5042, `len = cap`): the output grows
    to `max (2 len) 4` elements in a fresh chunk q (the old `len` elements moved there), the element's 232
    octets are copied unchanged to `q + 232 len`, and `cur + 232`, `len + 1` are stored; or the heap is
    exhausted. -/
theorem pass_elem_grow {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P]
    (env : RefineHost.Env) (cap0 : Nat) (hcap1 : 134217728 ≤ cap0) (hcap0 : cap0 < 18446744073709551616)
    (x : RefineCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (M cur en t len ptr pb S0 S1 : Nat)
    (H : HeapCtx env pb S0 S1 μ s) (ht : PassIdx t)
    (hold : len = 0 ∨ ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true ∧ c.size = (232 * len + 31) / 32 + 1)
    (hlen : len ≤ 2097152)
    (hM : S0 + 456 ≤ M ∧ M + 632 + 16 ≤ S1 ∧ 2147484104 ≤ M ∧ M % 8 = 0)
    (hcur : 65536 ≤ cur ∧ cur + 232 + 24 < 2147483648)
    (hne : cur ≠ en) (hen : en < 18446744073709551616) (hptr : ptr < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat M)
    (s144 : μ.readN (M + 144) 8 = Num.encodeLE 8 cur) (s120 : μ.readN (M + 120) 8 = Num.encodeLE 8 en)
    (sD : μ.readN cur 8 = Num.encodeLE 8 (9223372036854775807 + t))
    (s128 : μ.readN (M + 128) 8 = Num.encodeLE 8 9223372036854775832)
    (s136 : μ.readN (M + 136) 8 = Num.encodeLE 8 9223372036854775809)
    (sc : μ.readN (M + 248) 8 = Num.encodeLE 8 len) (sp : μ.readN (M + 256) 8 = Num.encodeLE 8 ptr)
    (sl : μ.readN (M + 264) 8 = Num.encodeLE 8 len)
    (hrc : ∀ a, cur ≤ a → a < cur + 232 → μ.readable a = true) :
    (∃ q s' ω' μ', FreeStepsH p (refineContractK cap0 env) 5042 ω μ x 5042 ω' μ' x
        (64 * ((232 * len + 31) / 32) + 5000) ∧
      ω'[1] = UInt64.ofNat M ∧
      μ'.readN (M + 144) 8 = Num.encodeLE 8 (cur + 232) ∧ μ'.readN (M + 264) 8 = Num.encodeLE 8 (len + 1) ∧
      μ'.readN (M + 248) 8 = Num.encodeLE 8 (max (2 * len) 4) ∧ μ'.readN (M + 256) 8 = Num.encodeLE 8 q ∧
      (⟨q - 32, (232 * max (2 * len) 4 + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      μ'.readN q (232 * len) = μ.readN ptr (232 * len) ∧
      μ'.readN (q + 232 * len) 232 = μ.readN cur 232 ∧
      μ'.readN (M + 120) 8 = Num.encodeLE 8 en ∧
      μ'.readN (M + 128) 8 = Num.encodeLE 8 9223372036854775832 ∧
      μ'.readN (M + 136) 8 = Num.encodeLE 8 9223372036854775809 ∧
      HeapCtx env pb S0 S1 μ' s' ∧
      (∀ c ∈ chunks s, c.used = true → c.addr + 32 ≠ ptr →
        c ∈ chunks s' ∧ ∀ a, InData c a → μ'.read a = μ.read a) ∧
      (∀ d ∈ chunks s, d.used = true → d.addr + 32 ≠ ptr → d.addr + 32 ≠ q)) ∨
    Exhausts env cap0 pb p P 5042 ω μ x (64 * ((232 * len + 31) / 32) + 5000) := by
  sorry

end Services.Bootstrap.Refine.PassGrow
