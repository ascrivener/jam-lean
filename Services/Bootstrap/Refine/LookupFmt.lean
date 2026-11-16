import Services.Bootstrap.Refine.ExportSeg

/-!
# `Lookup`'s log line (5398), as a named hypothesis

After `foreign_historical_lookup` (49015) returns, refine's eager `Lookup` handler formats its result,
`format!("…{:?}", result)` with `result : Option<Vec<u8>>` at M + 560 (template 66506, one argument (M + 560, 668),
the `Debug` function of `Option<Vec<u8>>`), into the `String` at M + 584, logs it (5428) and frees it (5441). The
`format!` call (59375 → 5405) is a named hypothesis, `LookupFmtOk`, in the pattern of `ExportSeg.ExportFmtOk`, to be
discharged by the fmt summaries. The text of the line is not specified (logging decision).
-/

namespace Services.Bootstrap.Refine.LookupFmt

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Refine.PassLoop

/-- The `Option<Vec<u8>>` at o as `foreign_historical_lookup` leaves it: `None` (the niche word 2^64 − 1), or
    `Some(Vec)` {cap, ptr, len} with len ≤ cap < 2^63 and its len octets readable below 2^32. -/
def OptVecAt (μ : Memory) (o : Nat) : Prop :=
  μ.readN o 8 = Num.encodeLE 8 18446744073709551615 ∨
  ∃ cap ptr len, μ.readN o 8 = Num.encodeLE 8 cap ∧ μ.readN (o + 8) 8 = Num.encodeLE 8 ptr ∧
    μ.readN (o + 16) 8 = Num.encodeLE 8 len ∧ len ≤ cap ∧ cap < 9223372036854775808 ∧ ptr + len < 4294967296 ∧
    ∀ a, ptr ≤ a → a < ptr + len → μ.readable a = true

/-- **`Lookup`'s log line** (59375 … 5405), as a hypothesis: `format!` of the result `Option<Vec<u8>>` at M + 560
    (template 66506, arguments at M + 536: (M + 560, 668)) into the `String` at M + 584, from refine's frame at M with
    the allocator's context and the result laid out (`OptVecAt`): the run returns to 5405 with the context unchanged,
    ω₁, ω₅, ω₆ kept, the allocator's context for some heap s', every allocated chunk of s kept with its data, the stack
    from M up kept apart from the `String`, and the `String` `{cap, ptr, len}` at M + 584, its buffer a fresh chunk
    when cap ≠ 0; or an allocation fails. To be discharged by the fmt summaries (`FmtCall` and the `Debug` of
    `Option<Vec<u8>>`). -/
def LookupFmtOk (p : ByteArray) (cap0 : Nat) (env : RefineHost.Env) (pb S0 S1 : Nat) (ro : List UInt8) : Prop :=
  ∀ (x : RefineCtx) (ω : Regs) (μ : Memory) (s : State) (M : Nat),
    HeapCtx env pb S0 S1 μ s → RoData.RoIs ro μ → S0 + 7560 ≤ M → M + 632 ≤ S1 → M % 8 = 0 →
    ω[0] = UInt64.ofNat 172 → ω[1] = UInt64.ofNat M → ω[7] = UInt64.ofNat (M + 584) →
    ω[8] = UInt64.ofNat 66506 → ω[9] = UInt64.ofNat (M + 536) →
    μ.readN (M + 536) 8 = Num.encodeLE 8 (M + 560) → μ.readN (M + 544) 8 = Num.encodeLE 8 668 →
    OptVecAt μ (M + 560) →
    (∃ (ω' : Regs) (μ' : Memory) (s' : State) (N cap ptr len : Nat),
      FreeStepsH p (refineContractK cap0 env) 59375 ω μ x 5405 ω' μ' x N ∧ HeapCtx env pb S0 S1 μ' s' ∧
      ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      (∀ a, a < 4294967296 → M ≤ a → (a < M + 584 ∨ M + 608 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ d ∈ chunks s, d.used = true → d ∈ chunks s' ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
      μ'.readN (M + 584) 8 = Num.encodeLE 8 cap ∧ μ'.readN (M + 592) 8 = Num.encodeLE 8 ptr ∧
      μ'.readN (M + 600) 8 = Num.encodeLE 8 len ∧ cap < 536870912 ∧ ptr < 4294967296 ∧ len ≤ cap ∧
      (cap = 0 ∨ ∃ c ∈ chunks s', c.used = true ∧ c.addr + 32 = ptr ∧ ∀ d ∈ chunks s, d.used = true → d ≠ c)) ∨
    ∃ N, ExhaustsX env cap0 pb p 59375 ω μ x N

end Services.Bootstrap.Refine.LookupFmt
