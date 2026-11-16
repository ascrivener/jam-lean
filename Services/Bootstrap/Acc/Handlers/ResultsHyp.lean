import Services.Bootstrap.Acc.Handlers.ResultsAt
import Services.Bootstrap.Acc.Transfer.Hyp
import Services.Bootstrap.Encode.WriterGrow

/-!
# Named hypotheses for the results encoding (R8 and R9 of `docs/t2-remaining.md`)

Plan B (Adam, decision 23): T2 is stated with these as named hypotheses, each to be proved later
from the blob without changing T2. Both are stated under accumulate's contract `accContractS` with the
context and the stream kept, and both allow the heap-exhaustion outcome `ExhaustsP` (a failed
allocator call, then ☇, keeping (x, y)).

- **`ExtendH` (R8, the HeapHost writer step):** `Vec<u8>::extend_from_slice` at 58508 appends n octets
  to the vector at v, growing its buffer if needed. This is refine's `Encode.WriterGrow.extend_any`
  restated for accumulate's allocator context `HeapCtxC` (the code is the same; refine proves it under
  `refineContractK`).
- **`OkEncH` (R9, the results encoder 36299, per item):** for an item at a holding `Ok r` (`OkAt`), the
  encoder appends `(Result.encode (.ok r)).drop 1` (r's index octet and fields; the leading 0 is
  appended by the caller) to the vector at v.
-/

namespace Services.Bootstrap.Acc.Handlers.Results

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Spec
  Services.Bootstrap.Acc Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Encode.Writer Services.Bootstrap.Encode.WriterGrow

/-- What a writer call leaves, from (μ, s) with the vector `{cap, ptr, len}` at v and the stack from sp
    up: the vector `{cap', r, len + |bs|}` at v with len + |bs| ≤ cap' ≤ max(cap, 8, 2·(len + |bs|)), its buffer r the data of an
    allocated chunk d of s′ (cap′ ≤ 32·(d.size − 1)) holding the old len octets then bs; every other
    allocated chunk of s kept, with its data; r either the old buffer or fresh; the stack from sp up
    kept off the vector, read-only data (with its access) and the globals kept. -/
def WriterPost (code : ByteArray) (pb S0 S1 : Nat) (μ : Memory) (s : State) (sp v cap ptr len : Nat)
    (bs : List UInt8) (μ' : Memory) (s' : State) : Prop :=
  ∃ cap' r, μ'.readN v 8 = Num.encodeLE 8 cap' ∧ μ'.readN (v + 8) 8 = Num.encodeLE 8 r ∧
    μ'.readN (v + 16) 8 = Num.encodeLE 8 (len + bs.length) ∧ len + bs.length ≤ cap' ∧
    cap' ≤ max cap (max 8 (2 * (len + bs.length))) ∧ μ'.readN r len = μ.readN ptr len ∧ μ'.readN (r + len) bs.length = bs ∧
    HeapCtxC code pb S0 S1 μ' s' ∧
    (∃ d ∈ chunks s', d.used = true ∧ d.addr + 32 = r ∧ cap' ≤ 32 * (d.size - 1)) ∧
    (∀ e ∈ chunks s, e.used = true → e.addr + 32 ≠ ptr →
      e ∈ chunks s' ∧ ∀ a, InData e a → μ'.read a = μ.read a) ∧
    (r = ptr ∨ ∀ e ∈ chunks s, e.used = true → e.addr + 32 ≠ r) ∧
    (∀ a, a < 4294967296 → sp ≤ a → (a < v ∨ v + 24 ≤ a) → μ'.read a = μ.read a) ∧
    (∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a) ∧
    (∀ a, Glob a → μ'.read a = μ.read a)

/-- The vector `{cap, ptr, len}` at v (on the stack at or above sp), its buffer the data of an
    allocated chunk ch of s with room for cap octets, len ≤ cap, 0 < cap, and both below 2³⁰. -/
def WriterPre (μ : Memory) (s : State) (sp v cap ptr len S1 : Nat) : Prop :=
  sp ≤ v ∧ v + 24 ≤ S1 ∧ μ.readN v 8 = Num.encodeLE 8 cap ∧ μ.readN (v + 8) 8 = Num.encodeLE 8 ptr ∧
    μ.readN (v + 16) 8 = Num.encodeLE 8 len ∧ len ≤ cap ∧ 0 < cap ∧ 2 * cap < 1073741760 ∧
    ∃ ch ∈ chunks s, ch.used = true ∧ ch.addr + 32 = ptr ∧ cap ≤ 32 * (ch.size - 1)

/-- **R8, the HeapHost writer step (named hypothesis).** From 58508 with ω₀ = ret (resolved by the jump
    table to t), ω₁ = sp, ω₇ = v, ω₈ = src, ω₉ = n, the vector at v (`WriterPre`), and the n source
    octets on the stack above sp off the vector (`StackSrc`) or in another allocated chunk (`HeapSrc`):
    the call returns to t with ω₀, ω₁, ω₅, ω₆ kept and `WriterPost` for the n octets at src, or
    exhausts the heap (`ExhaustsP`). -/
def ExtendH (p : ByteArray) (P : Program) (env : AccEnv) (pb S0 S1 : Nat) : Prop :=
  ∀ (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory) (s : State) (sp v src n cap ptr len ret t : Nat),
    HeapCtxC env.code pb S0 S1 μ s → WriterPre μ s sp v cap ptr len S1 → len + n < 1073741760 →
    S0 + 424 ≤ sp ∧ sp ≤ S1 ∧ 2147484072 ≤ sp ∧ sp % 8 = 0 →
    ω[0] = UInt64.ofNat ret → ω[1] = UInt64.ofNat sp → ω[7] = UInt64.ofNat v → ω[8] = UInt64.ofNat src →
    ω[9] = UInt64.ofNat n →
    (0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) → P.jumpTable.getD (ret / 2 - 1) 0 = t → P.isBlockStart t = true →
    (StackSrc sp v src n μ ∨ HeapSrc s ptr src n) →
    (∃ ω' μ' s' N, FreeStepsH p (KeepCtx (accContractS env)) 58508 ω μ (c, f) t ω' μ' (c, f) N ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      WriterPost env.code pb S0 S1 μ s sp v cap ptr len (μ.readN src n) μ' s') ∨
    ExhaustsP p env pb 58508 ω μ c f

/-- **R9, the results encoder 36299, per `Ok` item (named hypothesis).** From 36299 with ω₀ = ret
    (resolved to t), ω₁ = sp, ω₇ = a, ω₈ = v, the item at a holding `Ok r` against an allocator state st₀
    whose allocated chunks are all still allocated in s and none is the vector's buffer, and the vector
    at v (`WriterPre`, len + |ℰ| < 2³⁰): the call returns to t with ω₁, ω₅, ω₆ kept and `WriterPost` for
    the octets `(Result.encode (.ok r)).drop 1`, or exhausts the heap (`ExhaustsP`). -/
def OkEncH (p : ByteArray) (P : Program) (env : AccEnv) (pb S0 S1 : Nat) : Prop :=
  ∀ (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory) (s st₀ : State) (r : Ret)
    (sp v a cap ptr len ret t : Nat),
    HeapCtxC env.code pb S0 S1 μ s → WriterPre μ s sp v cap ptr len S1 →
    len + (Spec.Result.encode (.ok r)).length < 1073741760 →
    S0 + 424 ≤ sp ∧ sp ≤ S1 ∧ 2147484072 ≤ sp ∧ sp % 8 = 0 →
    OkAt μ st₀ a r → InHeap st₀ a 144 →
    (∀ d ∈ chunks st₀, d.used = true → d ∈ chunks s ∧ d.addr + 32 ≠ ptr) →
    ω[0] = UInt64.ofNat ret → ω[1] = UInt64.ofNat sp → ω[7] = UInt64.ofNat a → ω[8] = UInt64.ofNat v →
    (0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) → P.jumpTable.getD (ret / 2 - 1) 0 = t → P.isBlockStart t = true →
    (∃ ω' μ' s' N, FreeStepsH p (KeepCtx (accContractS env)) 36299 ω μ (c, f) t ω' μ' (c, f) N ∧
      ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      WriterPost env.code pb S0 S1 μ s sp v cap ptr len ((Spec.Result.encode (.ok r)).drop 1) μ' s') ∨
    ExhaustsP p env pb 36299 ω μ c f

end Services.Bootstrap.Acc.Handlers.Results
