import Services.Bootstrap.Decode.HeapCtx
import Services.Bootstrap.Alloc.Dealloc

/-!
# One call of the `dealloc` wrapper, on the allocator's context

The counterpart of `HeapCtx.alloc_callG` for freeing. From the allocator's context `HeapCtxC`
holding picoalloc's state `s`, with ω₇ the data address of an allocated chunk of `s`, the
`dealloc` wrapper (40613) reaches its return (the `jumpInd` at 40697) with the context kept for
`free s ptr`. The stack from sp up is untouched, and ω₀, ω₁, ω₅, ω₆ are restored.
`dealloc` makes no host call, so this holds under any contract (`dealloc_callG`, from
`Alloc.dealloc_refines`).
-/

namespace Services.Bootstrap.Decode.HeapCtx

open PVM Picoalloc Services.Bootstrap.Code Services.Bootstrap.Alloc JAM

/-- `free` keeps the allocated size of the heap. -/
theorem free_allocated (s : State) (ptr : Nat) : (free s ptr).allocated = s.allocated := by
  unfold free freeFinal mergeNext mergePrev
  dsimp only
  repeat' split
  all_goals simp

/-- **One call of the `dealloc` wrapper**, from 40613 with ω₇ = ptr, the data address of an
    allocated chunk of `s`, and the stack pointer in S0 + 40 … S1: the wrapper returns at 40697
    with the allocator's context kept for `free s ptr`, the stack from sp up untouched and ω₀, ω₁,
    ω₅, ω₆ restored. Under any host contract: `dealloc` makes no host call. -/
theorem dealloc_callG {X : Type} {R : HostRel X} {p : ByteArray} {P : Program} [HasCode p P]
    (code : ByteArray) (x : X) (ω : Regs) (μ : Memory) (s : State) (sp ptr pb S0 S1 : Nat)
    (H : HeapCtxC code pb S0 S1 μ s) (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr)
    (hsp : 2147483716 ≤ sp) (hSTk : S0 + 40 ≤ sp ∧ sp ≤ S1) :
    ∃ ω' μ', FreeStepsH p R 40613 ω μ x 40697 ω' μ' x 248 ∧
      HeapCtxC code pb S0 S1 μ' (free s ptr) ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  obtain ⟨ph, h48, hhb, hp, hHTs, hHT⟩ := H.pages
  have hsp1 : sp < 4294967296 := by have := H.hS1; omega
  obtain ⟨ω', μ', run, rep', wf', fo', lk, ww, efr, e0, e1, e5, e6⟩ :=
    dealloc_refines (p := p) (P := P) (R := R) x ω μ s sp ptr H.wf H.rep hc h1 h7 hsp hsp1 H.hb0 H.hbT
      H.fo H.lock (HT := 4096 * ph) (S0 := S0) (S1 := S1) hHT hSTk (HeapPages.wrAt hp hhb H.st)
  have hb' : (free s ptr).base = s.base := free_base'
  have ha' : (free s ptr).allocated = s.allocated := free_allocated s ptr
  refine ⟨ω', μ', run, ⟨wf', rep', fo', lk, by rw [hb']; exact H.hb0, by rw [hb']; exact H.hbT,
    by rw [ha']; exact H.hA, H.bd, ⟨ph, h48, hhb, HeapPages.of_eq hp ww, hHTs, by rw [hb', ha']; exact hHT⟩,
    H.hSb, H.hS1, fun a h1 h2 => by rw [ww]; exact H.st a h1 h2, fun a ha => by rw [ww]; exact H.ro a ha⟩,
    efr, e0, e1, e5, e6⟩

/-- `dealloc_callG` for the refine contract. -/
theorem dealloc_call {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap : Nat)
    (x : RefineCtx) (ω : Regs) (μ : Memory) (s : State) (sp ptr pb S0 S1 : Nat)
    (H : HeapCtx env pb S0 S1 μ s) (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr)
    (hsp : 2147483716 ≤ sp) (hSTk : S0 + 40 ≤ sp ∧ sp ≤ S1) :
    ∃ ω' μ', FreeStepsH p (refineContractK cap env) 40613 ω μ x 40697 ω' μ' x 248 ∧
      HeapCtx env pb S0 S1 μ' (free s ptr) ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] :=
  dealloc_callG env.code x ω μ s sp ptr pb S0 S1 H hc h1 h7 hsp hSTk

end Services.Bootstrap.Decode.HeapCtx
