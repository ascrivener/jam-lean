import Services.Bootstrap.Acc.Handlers.InstrLoopTail
import Services.Bootstrap.Acc.Handlers.ResultsAvoid
import Services.Bootstrap.Acc.Handlers.RowElevenCore
import Services.Bootstrap.Acc.Handlers.Dispatch

/-!
# R5, the instruction loop: its named hypotheses (Plan B, decision 23)

Approved by the parent on 2026-11-16, within decision 23's categories (R6, R8, G4). Each is stated
minimally and frame-only, like `LogFmt`, and listed in `docs/whats-proven.md` and
`docs/t2-remaining.md`:
- **`InstrLogH`** (G4): the instruction's Debug log line, `format!` at 8772 (59375 → 8779);
- **`ResultLogH`** (G4): the result's log line, `format!` at 14369 (59375 → 14376);
- **`HandlerH`** (R6): from the dispatch at 8822, the handler of any instruction i implements
  `onInstr C now i` (GP v0.8.0 Appendix B, Ω_W's per-instruction step; bootstrap's own semantics,
  `Spec.onInstr`) and ends at the shared tail 14278 with the `Result` at sp + 1000;
- **`PushH`** (R8): `finish_grow` with an old buffer for the results `Vec` (14431 → 14485).

The text of log lines is never specified (Adam's standing decision). Every frame keeps sp + 184 …
sp + 224 (the constants 2⁶³ at sp + 184 and 2⁶³ + 1 at sp + 216, set once before the item loop), as
T2 inputs requires.
-/

namespace Services.Bootstrap.Acc.Handlers.InstrLoop

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.Alloc Services.Bootstrap.Acc Services.Bootstrap.Spec Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Acc.Handlers.Results Services.Bootstrap.Acc.Handlers.InstrRep
  Services.Bootstrap.Acc.Handlers.RowEleven

/-- The frame words of accumulate's item step that the instruction loop and what follows it need
    (from sp): the tail's buffers (sp + 104 … sp + 136, sp + 264 … sp + 280), the `Zombify` flag, the
    item index, the constants and the formatter word (sp + 160 … sp + 224), the package hash
    (sp + 312 … sp + 344), the results `Vec`, the `IntoIter` and the counter (sp + 448 … sp + 512), the
    index (sp + 736), the instruction's `String` (sp + 976 … sp + 1000), and the caller's frames
    (from sp + 1632). -/
def LoopKeep (sp a : Nat) : Prop :=
  (sp + 104 ≤ a ∧ a < sp + 136) ∨ (sp + 160 ≤ a ∧ a < sp + 224) ∨ (sp + 264 ≤ a ∧ a < sp + 280) ∨
  (sp + 312 ≤ a ∧ a < sp + 344) ∨ (sp + 448 ≤ a ∧ a < sp + 512) ∨ (sp + 736 ≤ a ∧ a < sp + 744) ∨
  (sp + 976 ≤ a ∧ a < sp + 1000) ∨ sp + 1632 ≤ a

/-- A `String` { kc, kp, _ } just made by `format!` against s₀, in state s′: no buffer (kc = 0), or the
    data of an allocated chunk of s′ that is none of s₀'s allocated chunks. -/
def FreshBuf (s₀ s' : State) (kc kp : Nat) : Prop :=
  kc = 0 ∨ ∃ ch ∈ chunks s', ch.used = true ∧ ch.addr + 32 = kp ∧ ∀ d ∈ chunks s₀, d.used = true → d ≠ ch

/-- **The instruction's log line's `format!` at 8772** (59375, returning to 8779), frame-only (G4):
    from the call's registers (ω₀ = 302, ω₁ = sp, ω₇ = sp + 1568, ω₈ = 66194 the template, ω₉ =
    sp + 1144 the argument pair (sp + 1000, 2272): the pointer sp + 744 to the instruction's copy, which
    represents some i), either the run returns to 8779 with ω₁, ω₅, ω₆ kept, a `String` { kc, kp, _ }
    at sp + 1568 (`FreshBuf`), every allocated chunk of s₀ kept with its data, the allocator's context
    for the new state, and from sp up only sp + 1568 … sp + 1592 changed; or it reaches a failed
    allocator call and then ends ☇ (`ExhaustsP`). The message's text is not stated. -/
def InstrLogH (B : InstrRep) (p : ByteArray) (env : AccEnv) (pb S0 S1 : Nat) : Prop :=
  ∀ (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory) (s₀ : State) (sp : Nat) (i : Spec.Instr),
    HeapCtxC env.code pb S0 S1 μ s₀ →
    ω[0] = UInt64.ofNat 302 → ω[1] = UInt64.ofNat sp → ω[7] = UInt64.ofNat (sp + 1568) →
    ω[8] = UInt64.ofNat 66194 → ω[9] = UInt64.ofNat (sp + 1144) →
    S0 + 4096 ≤ sp → sp + 1632 ≤ S1 → 2147483648 + 4096 ≤ sp →
    rdN μ (sp + 1144) 8 = sp + 1000 → rdN μ (sp + 1152) 8 = 2272 → rdN μ (sp + 1000) 8 = sp + 744 →
    B.rep i (μ.readN (sp + 744) 232) μ →
    (∃ (s' : State) (ω' : Regs) (μ' : Memory) (N kc kp : Nat),
      FreeStepsH p (KeepCtx (accContractS env)) 59375 ω μ (c, f) 8779 ω' μ' (c, f) N ∧
      HeapCtxC env.code pb S0 S1 μ' s' ∧
      ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      rdN μ' (sp + 1568) 8 = kc ∧ rdN μ' (sp + 1576) 8 = kp ∧ FreshBuf s₀ s' kc kp ∧
      (∀ d ∈ chunks s₀, d.used = true → d ∈ chunks s' ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < sp + 1568 ∨ sp + 1592 ≤ a) → μ'.read a = μ.read a)) ∨
    ExhaustsP p env pb 59375 ω μ c f

/-- **The result's log line's `format!` at 14369** (59375, returning to 14376), frame-only (G4): from
    the call's registers (ω₀ = 534, ω₁ = sp, ω₇ = sp + 1144, ω₈ = 66359 the template, ω₉ = sp + 1568
    the argument pairs (sp + 736, 2804) the index, (sp + 976, 678) the instruction's `String` (its len
    octets at its buffer readable), (sp + 1496, 680) the `Result` view { e, payload } with the result r
    at sp + 1000), either the run returns to 14376 with ω₁, ω₅, ω₆ kept, a `String` { kc, kp, _ } at
    sp + 1144 (`FreshBuf`), every allocated chunk of s₀ kept with its data, the allocator's context for
    the new state, and from sp up only sp + 1144 … sp + 1168 changed; or `ExhaustsP`. -/
def ResultLogH (p : ByteArray) (env : AccEnv) (pb S0 S1 : Nat) : Prop :=
  ∀ (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory) (s₀ : State) (sp : Nat) (r : Spec.Result),
    HeapCtxC env.code pb S0 S1 μ s₀ →
    ω[0] = UInt64.ofNat 534 → ω[1] = UInt64.ofNat sp → ω[7] = UInt64.ofNat (sp + 1144) →
    ω[8] = UInt64.ofNat 66359 → ω[9] = UInt64.ofNat (sp + 1568) →
    S0 + 4096 ≤ sp → sp + 1632 ≤ S1 → 2147483648 + 4096 ≤ sp →
    rdN μ (sp + 1568) 8 = sp + 736 → rdN μ (sp + 1576) 8 = 2804 →
    rdN μ (sp + 1584) 8 = sp + 976 → rdN μ (sp + 1592) 8 = 678 →
    rdN μ (sp + 1600) 8 = sp + 1496 → rdN μ (sp + 1608) 8 = 680 →
    (∀ a, rdN μ (sp + 984) 8 ≤ a → a < rdN μ (sp + 984) 8 + rdN μ (sp + 992) 8 → μ.readable a = true) →
    ResultAt μ s₀ (sp + 1000) r →
    rdN μ (sp + 1496) 8 = (if rdN μ (sp + 1000) 1 = 255 then 1 else 0) →
    rdN μ (sp + 1504) 8 = (if rdN μ (sp + 1000) 1 = 255 then sp + 1001 else sp + 1000) →
    (∃ (s' : State) (ω' : Regs) (μ' : Memory) (N kc kp : Nat),
      FreeStepsH p (KeepCtx (accContractS env)) 59375 ω μ (c, f) 14376 ω' μ' (c, f) N ∧
      HeapCtxC env.code pb S0 S1 μ' s' ∧
      ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      rdN μ' (sp + 1144) 8 = kc ∧ rdN μ' (sp + 1152) 8 = kp ∧ FreshBuf s₀ s' kc kp ∧
      (∀ d ∈ chunks s₀, d.used = true → d ∈ chunks s' ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < sp + 1144 ∨ sp + 1168 ≤ a) → μ'.read a = μ.read a)) ∨
    ExhaustsP p env pb 59375 ω μ c f

/-- The chunks a handler's result may occupy, against the states st (at the dispatch) and st′: an
    allocated chunk of st′ that is either none of st's allocated chunks, or one of the instruction's
    own buffers F (moved into the result). -/
def ResC (st st' : State) (F : List Nat) (d : Chunk) : Prop :=
  d ∈ chunks st' ∧ d.used = true ∧ ((∀ d0 ∈ chunks st, d0.used = true → d0 ≠ d) ∨ d.addr + 32 ∈ F)

/-- The state a handler ends in (14278), against the dispatch state (memory μ, allocator state st,
    stack pointer sp, the instruction's buffers F): ω₁ = sp; the allocator's context for some st′; the
    result r at sp + 1000 in chunks `ResC`; every allocated chunk of st not in F kept with its data;
    the frame words `LoopKeep` and the globals kept; the octets below 196608 kept, and every octet's
    access kept. -/
def HandlerPost (code : ByteArray) (pb S0 S1 sp : Nat) (st : State) (μ : Memory) (F : List Nat)
    (r : Spec.Result) (s' : St Stream) : Prop :=
  s'.i = 14278 ∧ s'.ω[1] = UInt64.ofNat sp ∧
  ∃ st', HeapCtxC code pb S0 S1 s'.μ st' ∧ ResultAtP s'.μ (ResC st st' F) (sp + 1000) r ∧
    (∀ d ∈ chunks st, d.used = true → d.addr + 32 ∉ F → d ∈ chunks st' ∧
      ∀ a, InData d a → s'.μ.read a = μ.read a) ∧
    (∀ a, a < 4294967296 → LoopKeep sp a → s'.μ.read a = μ.read a) ∧
    (∀ a, Glob a → s'.μ.read a = μ.read a) ∧ (∀ a, a < 196608 → s'.μ.read a = μ.read a) ∧
    (∀ a, s'.μ.readable a = μ.readable a) ∧ (∀ a, s'.μ.writable a = μ.writable a)

/-- **The handlers (R6), from the dispatch at 8822 to the shared tail 14278**: for every instruction i
    whose copy at sp + 1144 represents it (`B.rep`) with its buffers (`B.foot`) allocated, under the
    frame constants (2⁶³ at sp + 184, 2⁶³ + 1 at sp + 216, the formatter word 678 at sp + 200), the
    dispatch table at 65736, the allocator's context and the stack room, the run implements
    `onInstr C now i` (GP v0.8.0 Appendix B, Ω_W; `Spec.onInstr`) under `accContractS`, with abort
    reasons Ab, ending in `HandlerPost`. -/
def HandlerH (B : InstrRep) (p : ByteArray) (env : AccEnv) (C : Consts) (now pb S0 S1 : Nat)
    (Ab : St Stream → Prop) : Prop :=
  ∀ (i : Spec.Instr) (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory) (st : State) (sp : Nat),
    HeapCtxC env.code pb S0 S1 μ st → ω[1] = UInt64.ofNat sp →
    S0 + 4096 ≤ sp → sp + 1632 ≤ S1 → 2147483648 + 4096 ≤ sp →
    B.rep i (μ.readN (sp + 1144) 232) μ →
    (∀ q ∈ B.foot (μ.readN (sp + 1144) 232), ∃ d ∈ chunks st, d.used = true ∧ d.addr + 32 = q) →
    rdN μ (sp + 184) 8 = 9223372036854775808 → rdN μ (sp + 216) 8 = 9223372036854775809 →
    rdN μ (sp + 200) 8 = 678 →
    μ.readN 65736 100 = jumpTab → (∀ a, 65736 ≤ a → a < 65836 → μ.readable a = true) →
    StoreFit c →
    Impl p (accContractS env) env Ab (onInstr C now i)
      (HandlerPost env.code pb S0 S1 sp st μ (B.foot (μ.readN (sp + 1144) 232))) ⟨8822, ω, μ, c, f⟩

/-- **`finish_grow` for the results `Vec` (R8), 14431 → 14485**: the `Vec` at sp + 448 full (cap = len
    = n, buffer rp, the data of an allocated chunk if n ≠ 0, holding 144·n octets), either the run
    returns to 14485 with ω₁ = sp, ω₅ = n, a new cap cp > n and buffer rp′ at sp + 448 / sp + 456 (len
    kept), the 144·n octets moved to rp′, rp′ the data of an allocated chunk d′ of the new state with
    room for cp items, every other allocated chunk of st kept with its data and none equal to d′, the
    allocator's context, the memory from sp up kept but at sp + 448 … sp + 464; or `ExhaustsP`. -/
def PushH (p : ByteArray) (env : AccEnv) (pb S0 S1 : Nat) : Prop :=
  ∀ (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory) (st : State) (sp rp n : Nat),
    HeapCtxC env.code pb S0 S1 μ st → ω[1] = UInt64.ofNat sp → ω[5] = UInt64.ofNat n →
    S0 + 4096 ≤ sp → sp + 1632 ≤ S1 → 2147483648 + 4096 ≤ sp →
    rdN μ (sp + 448) 8 = n → rdN μ (sp + 456) 8 = rp → rdN μ (sp + 464) 8 = n →
    (n ≠ 0 → ∃ d ∈ chunks st, d.used = true ∧ d.addr + 32 = rp ∧ rp + 144 * n ≤ d.addr + 32 * d.size) →
    (∃ (st' : State) (ω' : Regs) (μ' : Memory) (N cp rp' : Nat),
      FreeStepsH p (KeepCtx (accContractS env)) 14431 ω μ (c, f) 14485 ω' μ' (c, f) N ∧
      HeapCtxC env.code pb S0 S1 μ' st' ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧
      rdN μ' (sp + 448) 8 = cp ∧ n < cp ∧ rdN μ' (sp + 456) 8 = rp' ∧
      μ'.readN rp' (144 * n) = μ.readN rp (144 * n) ∧
      (∃ d' ∈ chunks st', d'.used = true ∧ d'.addr + 32 = rp' ∧ rp' + 144 * cp ≤ d'.addr + 32 * d'.size ∧
        ∀ d ∈ chunks st, d.used = true → d.addr + 32 ≠ rp → d ≠ d' ∧ d ∈ chunks st' ∧
          ∀ a, InData d a → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < sp + 448 ∨ sp + 464 ≤ a) → μ'.read a = μ.read a)) ∨
    ExhaustsP p env pb 14431 ω μ c f

end Services.Bootstrap.Acc.Handlers.InstrLoop
