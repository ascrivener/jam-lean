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
-/

namespace Services.Bootstrap.Acc
open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Picoalloc Services.Bootstrap.Decode.HeapCtx

/-- **`format!("transfer{}", n)` at 7792** (`format_inner`, 59375, returning to 7799): from the
    call's registers (ω₀ = 268, ω₁ = sp, ω₇ = sp + 512, ω₈ = 66607 the template, ω₉ = sp + 1568 the
    argument pair (sp + 1496, 2800), n the u32 at sp + 1496), either the run returns to 7799 with
    ω₁, ω₅, ω₆ kept, the `String` { kc, kp, len } at sp + 512 holding `s!"transfer{n}"`, its buffer
    (if kc ≠ 0) a chunk fresh against s₀, every allocated chunk of s₀ and its data kept, the
    allocator's context for the new state, and from sp up only sp + 512 … sp + 536 changed; or it
    reaches a failed allocator call (`Fmt.Exhausts`). The context and the stream are kept. -/
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
      (kc = 0 ∨ ∃ ch ∈ chunks s', ch.used = true ∧ ch.addr + 32 = kp ∧
        ∀ d ∈ chunks s₀, d.used = true → d ≠ ch) ∧
      (∀ d ∈ chunks s₀, d.used = true → d ∈ chunks s' ∧ ∀ a, InDataA d a → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < sp + 512 ∨ sp + 536 ≤ a) → μ'.read a = μ.read a)) ∨
    ∃ N, Fmt.Exhausts p (KeepCtx (accContractS env)) pb 59375 ω μ (c, f) N

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
    sp + 1568 the argument pairs: (sp + 472, the formatter at sp + 208) for the u32 source,
    (sp + 1000, the one at sp + 136) for the u64 amount, (sp + 512, the one at sp + 200) for the shown
    `String`, whose `len` octets at its buffer are readable), either the run returns to 7699 with
    ω₁, ω₅, ω₆ kept, a `String` { kc, kp, _ } at sp + 744 whose buffer (if kc ≠ 0) is a chunk fresh
    against s₀, every allocated chunk of s₀ and its data kept, the allocator's context for the new
    state, and from sp up only sp + 744 … sp + 768 changed; or it reaches a failed allocator call. The
    message's text is not stated (logging is frame-only). -/
def LogFmt (p : ByteArray) (env : AccEnv) (pb S0 S1 : Nat) : Prop :=
  ∀ (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory) (s₀ : State) (sp : Nat),
    HeapCtxC env.code pb S0 S1 μ s₀ →
    ω[0] = UInt64.ofNat 262 → ω[1] = UInt64.ofNat sp → ω[7] = UInt64.ofNat (sp + 744) →
    ω[8] = UInt64.ofNat 66221 → ω[9] = UInt64.ofNat (sp + 1568) →
    S0 + 4096 ≤ sp → sp + 1856 ≤ S1 → 2147483648 ≤ sp →
    rdN μ (sp + 1568) 8 = sp + 472 → rdN μ (sp + 1576) 8 = rdN μ (sp + 208) 8 →
    rdN μ (sp + 1584) 8 = sp + 1000 → rdN μ (sp + 1592) 8 = rdN μ (sp + 136) 8 →
    rdN μ (sp + 1600) 8 = sp + 512 → rdN μ (sp + 1608) 8 = rdN μ (sp + 200) 8 →
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
    ∃ N, Fmt.Exhausts p (KeepCtx (accContractS env)) pb 59375 ω μ (c, f) N

end Services.Bootstrap.Acc
