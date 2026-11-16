import Services.Bootstrap.Acc.Transfer.ImplTr
import Services.Bootstrap.Acc.Inputs.Inputs
import Services.Bootstrap.Acc.Items.Disp
import Services.Bootstrap.Acc.Items.Exit
import Services.Bootstrap.Acc.ValuesFitStep
import Services.Bootstrap.SpecLemmas.Items

/-!
# The items loop's invariant (R1)

`Spec.accumulate` runs `for it in items do …` over the decoded inputs (`specItem`s, GP v0.8.0 §12).
The binary runs it as the loop at 6766: the `IntoIter` of the decoded `Vec<AccumulateItem>` keeps the
current slot at sp + 168 and the end at sp + 144, over 184-octet slots in the buffer at q (sp + 16)
of capacity cap (sp + 32). Each iteration dispatches on the slot's first word at 6782: −1 is a
transfer (7159, `tr_impl`), anything else (but −2, never a decoded slot) an operand (6827).

**`ItemsInv`** is the state at the loop head for the inputs `ins` still to run. It carries what every
arm needs and keeps:
- the stack frame: sp in ω₁, the iterator's words, the prologue's formatter words (sp + 208 / 136,
  `tr_impl`), the saved return address (sp + 1848, the halt), and the words R5 reads at sp + 184 /
  216 (stored once at 6746 / 6760);
- the allocator's context `HeapCtxC` for some state st, with the slot buffer an allocated chunk;
- each slot left holds its input (`itemOf`) for any memory agreeing with this one on the allocated
  chunks' data (as `inputs_decode` states it), so a frame that keeps those chunks keeps the slots;
- the read-only data `tr_impl` reads (`TrRO`), the parameter statics (`Glob`, equal to a base memory
  μ₀'s), and `ValuesFit` of the context (T2's premise, kept by every operation: `ValuesFit.step`).
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx Picoalloc

/-- The read-only data `tr_impl` reads: the key "transfer-count" at 65956 and `set`'s error table at
    69056 … 69076 (`accRoBytes`). -/
def TrRO (μ : Memory) : Prop :=
  μ.readN 65956 14 = trKey ∧ (∀ a, 65956 ≤ a → a < 65970 → μ.readable a = true) ∧
  rdN μ 69072 4 = 4294900408 ∧ rdN μ 69056 4 = 4294900402 ∧
  (∀ a, 69056 ≤ a → a < 69076 → μ.readable a = true)

/-- `TrRO` reads only below 196608. -/
theorem TrRO.keep {μ μ' : Memory} (h : TrRO μ)
    (hk : ∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a) : TrRO μ' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, fun a ha hb => ?_, ?_, ?_, fun a ha hb => ?_⟩
  · rw [Memory.readN_congr fun j hj => (hk _ (by omega)).1]; exact h1
  · rw [(hk a (by omega)).2]; exact h2 a ha hb
  · rw [rdN_frame fun j hj => (hk _ (by omega)).1]; exact h3
  · rw [rdN_frame fun j hj => (hk _ (by omega)).1]; exact h4
  · rw [(hk a (by omega)).2]; exact h5 a ha hb

/-- **The items loop's state at its head 6766** with the inputs `ins` still to run (see the module
    docstring). The frame: sp, the slot buffer q of capacity cap, the end e; μ₀ fixes the statics. -/
structure ItemsInv (env : AccEnv) (pb S0 S1 sp q cap e : Nat) (μ₀ : Memory)
    (ins : List AccumulateInput) (s : St Stream) : Prop where
  pc : s.i = 6766
  r1 : s.ω[1] = UInt64.ofNat sp
  hsp : 2147483992 ≤ sp ∧ sp % 8 = 0
  hstk : S0 + 4096 ≤ sp ∧ sp + 1856 ≤ S1
  cur : rdN s.μ (sp + 168) 8 + 184 * ins.length = e
  m144 : rdN s.μ (sp + 144) 8 = e
  m16 : rdN s.μ (sp + 16) 8 = q
  m32 : rdN s.μ (sp + 32) 8 = cap
  m208 : rdN s.μ (sp + 208) 8 = 2800
  m136 : rdN s.μ (sp + 136) 8 = 2804
  m184 : rdN s.μ (sp + 184) 8 = 2 ^ 63
  m216 : rdN s.μ (sp + 216) 8 = 2 ^ 63 + 1
  m1848 : rdN s.μ (sp + 1848) 8 = 4294901760
  hcap : ins.length ≤ cap
  heap : ∃ st, HeapCtxC env.code pb S0 S1 s.μ st ∧
    (cap ≠ 0 → ∃ d ∈ chunks st, d.used = true ∧ d.addr + 32 = q ∧
      ∀ a, rdN s.μ (sp + 168) 8 ≤ a → a < e → InDataA d a) ∧
    (∀ (j : Nat) (i : AccumulateInput), ins[j]? = some i →
      ∀ μ'' : Memory, (∀ d ∈ chunks st, d.used = true → ∀ a, InDataA d a → μ''.read a = s.μ.read a) →
        (itemOf i).2 (μ''.readN (rdN s.μ (sp + 168) 8 + 184 * j) 184) μ'')
  ro : TrRO s.μ
  glob : ∀ a, Glob a → s.μ.read a = μ₀.read a
  fit : ValuesFit env s.c.1
  sized : ∀ i ∈ ins, InputSized i

end Services.Bootstrap.Acc
