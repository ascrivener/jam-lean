import Services.Bootstrap.Acc.Transfer.GetKeyCall
import Services.Bootstrap.Fmt.Frame

/-!
# Named hypotheses for `on_transfer`'s two formatting-area calls

`on_transfer` (Spec `onTransfer`) calls two functions of the formatting area whose facts are being
proved elsewhere (the symbolic-executor session). Until then the tail of `on_transfer` is stated
against these:
- `KeyFmt`: `format!("transfer{}", n)` at 7792 (`alloc::fmt::format_inner`, 59375, template 66607,
  n a u32 shown by `<u32 as Display>`, formatter 2800) leaves at sp + 512 a `String` whose text is
  `s!"transfer{n}"` — the storage key of Spec `onTransfer`'s second write. Logging is frame-only
  (Adam's decision); this key's text is needed because it names a storage entry.
- `LogFmt`: the log line's `format!` at 7692 (template 66221), frame-only: the message's `String` at
  sp + 744, the text not stated. For the log-sites work (ArgsAt-style arguments).
- `Utf8Call`: `core::str::from_utf8` (60681) on the memo's 128-octet copy at 7447, for the log line
  only: it writes only its frame and the 24-octet result, whose tag is 0 (`Ok`, the input slice) or 1.

Both are stated for the call sites' registers, under `KeepCtx (accContractS env)` (no context
change), with the allocator's context `HeapCtxC`.

**Allocation failure** (`ExhaustsP`, Adam's decision 2026-11-15): the failure disjunct of `KeyFmt` and
`LogFmt` is `Fmt.Exhausts` (a failed allocator call, the run at 40611 with ω₇ = 0) *strengthened* by
"from that state the run ends ☇, keeping (x, y)" — `handle_alloc_error`'s path to a trap. This is a blob
obligation for whoever discharges these hypotheses (as T1's "allocation failure ends in ☇"); it lets
`Impl` count the failure as an early ☇ for the `heap` reason.
-/

namespace Services.Bootstrap.Acc
open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Picoalloc Services.Bootstrap.Decode.HeapCtx

/-- **A failed allocation inside a call, then ☇**: from (i, ω, μ) the run reaches a failed allocator
    call (as `Fmt.Exhausts`: 40611 with ω₇ = 0 after a failed `alloc`, or 40821 after a failed
    `realloc`), keeping the context, and from that state the run ends ☇, keeping the context. -/
def ExhaustsP (p : ByteArray) (env : AccEnv) (pb i : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) (f : Stream) :
    Prop :=
  ∃ (ω' : Regs) (μ' : Memory) (q' : Stream) (j N : Nat),
    FreeStepsH p (KeepCtx (accContractS env)) i ω μ (c, f) j ω' μ' (c, q') N ∧
    ω'[7] = UInt64.ofNat 0 ∧
    ((j = 40611 ∧ ∃ (s : State) (hb r : Nat), alloc (growTo pb) hb 1 r s = none) ∨
     (j = 40821 ∧ ∃ (s : State) (hb ptr al r : Nat), realloc (growTo pb) hb s ptr al r = none)) ∧
    ∃ (ω'' : Regs) (μ'' : Memory) (q'' : Stream),
      FreeRunH p (KeepCtx (accContractS env)) j ω' μ' (c, q') .panic ω'' μ'' (c, q'')

/-- **`format!("transfer{}", n)` at 7792** (`format_inner`, 59375, returning to 7799): from the
    call's registers (ω₀ = 268, ω₁ = sp, ω₇ = sp + 512, ω₈ = 66607 the template, ω₉ = sp + 1568 the
    argument pair (sp + 1496, 2800), n the u32 at sp + 1496), either the run returns to 7799 with
    ω₁, ω₅, ω₆ kept, the `String` { kc, kp, len } at sp + 512 holding `s!"transfer{n}"`, its len
    octets the data of a live chunk (at kp − 32) fresh against s₀ (so readable and below 2³¹, as
    `set` needs; Adam, 2026-11-15), every allocated chunk of s₀ and its data kept, the
    allocator's context for the new state, and from sp up only sp + 512 … sp + 536 changed; or it
    reaches a failed allocator call and then ends ☇ (`ExhaustsP`, a blob obligation). The context and the stream are kept. -/
def KeyFmt (p : ByteArray) (env : AccEnv) (pb S0 S1 : Nat) : Prop :=
  ∀ (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory) (s₀ : State) (sp n : Nat),
    HeapCtxC env.code pb S0 S1 μ s₀ →
    ω[0] = UInt64.ofNat 268 → ω[1] = UInt64.ofNat sp → ω[7] = UInt64.ofNat (sp + 512) →
    ω[8] = UInt64.ofNat 66607 → ω[9] = UInt64.ofNat (sp + 1568) →
    S0 + 4096 ≤ sp → sp + 1856 ≤ S1 → 2147483648 ≤ sp →
    rdN μ (sp + 1568) 8 = sp + 1496 → rdN μ (sp + 1576) 8 = 2800 →
    rdN μ (sp + 1496) 4 = n → n < 4294967296 →
    (∃ (s' : State) (ω' : Regs) (μ' : Memory) (N kc kp : Nat),
      FreeStepsH p (KeepCtx (accContractS env)) 59375 ω μ (c, f) 7799 ω' μ' (c, f) N ∧
      HeapCtxC env.code pb S0 S1 μ' s' ∧
      ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      rdN μ' (sp + 512) 8 = kc ∧ rdN μ' (sp + 520) 8 = kp ∧
      rdN μ' (sp + 528) 8 = (s!"transfer{n}").toUTF8.toList.length ∧
      μ'.readN kp (s!"transfer{n}").toUTF8.toList.length = (s!"transfer{n}").toUTF8.toList ∧
      (∃ ch ∈ chunks s', ch.used = true ∧ ch.addr + 32 = kp ∧
        (∀ d ∈ chunks s₀, d.used = true → d ≠ ch) ∧
        ∀ a, kp ≤ a → a < kp + (s!"transfer{n}").toUTF8.toList.length → InDataA ch a) ∧
      (∀ d ∈ chunks s₀, d.used = true → d ∈ chunks s' ∧ ∀ a, InDataA d a → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < sp + 512 ∨ sp + 536 ≤ a) → μ'.read a = μ.read a)) ∨
    ExhaustsP p env pb 59375 ω μ c f

/-- **`core::str::from_utf8` at 7447** (60681, returning to 7454): from the call's registers
    (ω₀ = 256, ω₁ = sp, ω₇ = out = sp + 744, ω₈ = ptr, ω₉ = 128) with the 128 octets at ptr
    readable, the run returns to 7454 with ω₁, ω₅, ω₆ kept and the allocator's context kept, writing
    only below sp and out … out + 24; the result's tag is 0 (`Ok`, then the slice is (ptr, 128)) or 1
    (`Err`). The context and the stream are kept. -/
def Utf8Call (p : ByteArray) (env : AccEnv) (pb S0 S1 : Nat) : Prop :=
  ∀ (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory) (s₀ : State) (sp ptr : Nat),
    HeapCtxC env.code pb S0 S1 μ s₀ →
    ω[0] = UInt64.ofNat 256 → ω[1] = UInt64.ofNat sp → ω[7] = UInt64.ofNat (sp + 744) →
    ω[8] = UInt64.ofNat ptr → ω[9] = UInt64.ofNat 128 →
    S0 + 4096 ≤ sp → sp + 1856 ≤ S1 → 65536 ≤ ptr → ptr + 128 ≤ 2147483648 →
    (∀ a, ptr ≤ a → a < ptr + 128 → μ.readable a = true) →
    ∃ (ω' : Regs) (μ' : Memory) (N : Nat),
      FreeStepsH p (KeepCtx (accContractS env)) 60681 ω μ (c, f) 7454 ω' μ' (c, f) N ∧
      HeapCtxC env.code pb S0 S1 μ' s₀ ∧
      ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ((rdN μ' (sp + 744) 8 = 0 ∧ rdN μ' (sp + 752) 8 = ptr ∧ rdN μ' (sp + 760) 8 = 128) ∨
        rdN μ' (sp + 744) 8 = 1) ∧
      (∀ a, a < 4294967296 → (a < sp - 4096 ∨ sp ≤ a) → (a < sp + 744 ∨ sp + 768 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a)

/-- **The log line's `format!` at 7692** (`format_inner`, 59375, returning to 7699), frame-only:
    from the call's registers (ω₀ = 262, ω₁ = sp, ω₇ = sp + 744, ω₈ = 66221 the template, ω₉ =
    sp + 1568 the argument pairs: (sp + 472, 2800) for the u32 source, (sp + 1000, 2804) for the u64
    amount, (sp + 512, 678) for the shown `String` (the formatter words spilled at sp + 208, sp + 136 by
    6547 / 6559 and at sp + 200 by 6782), whose `len` octets at its buffer are readable), either the run returns to 7699 with
    ω₁, ω₅, ω₆ kept, a `String` { kc, kp, _ } at sp + 744 whose buffer (if kc ≠ 0) is a chunk fresh
    against s₀, every allocated chunk of s₀ and its data kept, the allocator's context for the new
    state, and from sp up only sp + 744 … sp + 768 changed; or it reaches a failed allocator call and
    then ends ☇ (`ExhaustsP`, a blob obligation). The
    message's text is not stated (logging is frame-only). -/
def LogFmt (p : ByteArray) (env : AccEnv) (pb S0 S1 : Nat) : Prop :=
  ∀ (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory) (s₀ : State) (sp : Nat),
    HeapCtxC env.code pb S0 S1 μ s₀ →
    ω[0] = UInt64.ofNat 262 → ω[1] = UInt64.ofNat sp → ω[7] = UInt64.ofNat (sp + 744) →
    ω[8] = UInt64.ofNat 66221 → ω[9] = UInt64.ofNat (sp + 1568) →
    S0 + 4096 ≤ sp → sp + 1856 ≤ S1 → 2147483648 ≤ sp →
    rdN μ (sp + 1568) 8 = sp + 472 → rdN μ (sp + 1576) 8 = 2800 →
    rdN μ (sp + 1584) 8 = sp + 1000 → rdN μ (sp + 1592) 8 = 2804 →
    rdN μ (sp + 1600) 8 = sp + 512 → rdN μ (sp + 1608) 8 = 678 →
    (∀ a, rdN μ (sp + 520) 8 ≤ a → a < rdN μ (sp + 520) 8 + rdN μ (sp + 528) 8 → μ.readable a = true) →
    (∃ (s' : State) (ω' : Regs) (μ' : Memory) (N kc kp : Nat),
      FreeStepsH p (KeepCtx (accContractS env)) 59375 ω μ (c, f) 7699 ω' μ' (c, f) N ∧
      HeapCtxC env.code pb S0 S1 μ' s' ∧
      ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      rdN μ' (sp + 744) 8 = kc ∧ rdN μ' (sp + 752) 8 = kp ∧
      (kc = 0 ∨ ∃ ch ∈ chunks s', ch.used = true ∧ ch.addr + 32 = kp ∧
        ∀ d ∈ chunks s₀, d.used = true → d ≠ ch) ∧
      (∀ d ∈ chunks s₀, d.used = true → d ∈ chunks s' ∧ ∀ a, InDataA d a → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < sp + 744 ∨ sp + 768 ≤ a) → μ'.read a = μ.read a)) ∨
    ExhaustsP p env pb 59375 ω μ c f

end Services.Bootstrap.Acc
