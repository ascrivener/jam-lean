import Services.Bootstrap.Acc.Handlers.InstrLoopRowEleven
import Services.Bootstrap.Acc.ItemsLoop.Err

/-!
# The work output's decode (R3), a named hypothesis

Spec `onWorkItem` (GP v0.8.0 Appendix B, Ω_W's input) starts with `decode (Dec.output C) out`: the
instructions `is` (a `Vec<Instruction>`, `Dec.vec (Dec.instr C)`) then the work item's index (`u16`).
The binary inlines `BootstrapWorkOutput::decode` at 7050 … (a 72-octet frame below sp, the `u32` length
at 31894, the elements, the `u16`; its returns at 22248 / 22268 / 22305 restore ω₅, ω₆ and jump to
7080 through the return address 238). Its argument: the reader { ptr, len } at sp + 1144 over the
work output's octets; its result: at sp + 1568 the `Vec` { cap, ptr, len } and at sp + 1592 the
`u16`, or −1 at sp + 1568 for a decode error.

**`OutDecH`** (Plan B, Adam's decision 23: R3's success path as a named hypothesis; the decode-error
branch is an open obligation stated with it): from 7050 the run reaches 7080 keeping ω₁, ω₅, ω₆, the
allocator's context (for some state keeping every allocated chunk of the old one with its data), the
memory from sp up but the reader (sp + 1144 … 1160) and the result (sp + 1568 … 1600), the statics
and the octets below 196608 with their access; and
- if `decode (Dec.output C) out = some (is, item)`: the result is the `Vec` { c ≠ −1, b, |is| } with
  `VecOwn` (each 232-octet slot represents its instruction, `InstrRep`), b 8-aligned, the slots below
  2⁶⁴, the instructions' buffers fresh (none an old allocated chunk), and ℰ₂(item) at sp + 1592;
- if it is `none`: −1 at sp + 1568;

or the decode runs out of heap (`ExhaustsP`).
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx Picoalloc Services.Bootstrap.Acc.Handlers.InstrRep
  Services.Bootstrap.Acc.Handlers.InstrLoop
open JAM.Codec (fixed)

/-- The decode's result words at sp + 1568 for `decode (Dec.output C) out` (see the module doc). -/
def OutDecRes (B : InstrRep) (C : Spec.Consts) (out : List UInt8) (μ : Memory) (st₀ st : State)
    (sp : Nat) : Prop :=
  match Spec.decode (Spec.Dec.output C) out with
  | some (is, item) => ∃ b c, rdN μ (sp + 1568) 8 = c ∧ c ≠ 18446744073709551615 ∧
      rdN μ (sp + 1576) 8 = b ∧ rdN μ (sp + 1584) 8 = is.length ∧
      μ.readN (sp + 1592) 2 = fixed 2 item ∧ VecOwn B μ st b c is ∧ b % 8 = 0 ∧
      b + 232 * is.length < 2 ^ 64 ∧
      ∀ q ∈ vecFree B μ b c is.length, ∀ d ∈ chunks st₀, d.used = true → d.addr + 32 ≠ q
  | none => rdN μ (sp + 1568) 8 = 18446744073709551615

/-- **The work output's decode, 7050 → 7080** (named hypothesis R3; see the module doc). -/
def OutDecH (B : InstrRep) (C : Spec.Consts) (p : ByteArray) (env : AccEnv) (pb S0 S1 : Nat) : Prop :=
  ∀ (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory) (st : State) (sp ptr : Nat) (out : List UInt8),
    HeapCtxC env.code pb S0 S1 μ st →
    ω[1] = UInt64.ofNat sp → ω[5] = UInt64.ofNat 18446744073709551615 →
    ω[7] = UInt64.ofNat (sp + 1568) → ω[8] = UInt64.ofNat (sp + 1144) →
    S0 + 4096 ≤ sp → sp + 1856 ≤ S1 → 2147483648 ≤ sp → sp % 8 = 0 →
    rdN μ (sp + 1144) 8 = ptr → rdN μ (sp + 1152) 8 = out.length → μ.readN ptr out.length = out →
    (∀ a, ptr ≤ a → a < ptr + out.length → μ.readable a = true) →
    (∃ (st' : State) (ω' : Regs) (μ' : Memory) (N : Nat),
      FreeStepsH p (KeepCtx (accContractS env)) 7050 ω μ (c, f) 7080 ω' μ' (c, f) N ∧
      HeapCtxC env.code pb S0 S1 μ' st' ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      (∀ d ∈ chunks st, d.used = true → d ∈ chunks st' ∧ ∀ a, InDataA d a → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < sp + 1144 ∨ sp + 1160 ≤ a) →
        (a < sp + 1568 ∨ sp + 1600 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) ∧
      (∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a) ∧
      OutDecRes B C out μ' st st' sp) ∨
    ExhaustsP p env pb 7050 ω μ c f

end Services.Bootstrap.Acc
