import Services.Bootstrap.Acc.Impl.Impl
import Services.Bootstrap.Acc.Inputs.FetchVec
import Services.Bootstrap.Acc.Transfer.Hyp

/-!
# `on_transfer`'s traps and its `heap` abort sites

Every failed allocation on `on_transfer`'s path ends at a `trap` (GP v0.8.0 §A.5.1, ☇):
- 3895: `alloc` returned null in the copied-key helpers (`get` at 40494 → 3820, `set` → 3896);
- 47977: `get`'s own allocation failed (`get_call`, `get_huge`);
- 15362, 15363: `alloc` of the memo copy (7413) and of the log line's buffer (7544) returned null;
- 34178: `alloc` in the record encoder (`enc_call`) returned null.

`HeapTrapT` names these pcs. On_transfer's `Impl` statement takes the abort reason `Ab` as a parameter
and assumes only that a state at one of these pcs satisfies it (`aborts_of_trap`). The FULL results
(7386 / 7915 → 15361) are not aborts: there the spec's `orPanic` panics too.
-/

namespace Services.Bootstrap.Acc
open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA

/-- The pcs of `on_transfer`'s allocation-failure traps (the `heap` abort reason). -/
def HeapTrapT (i : Nat) : Prop := i = 3895 ∨ i = 47977 ∨ i = 15362 ∨ i = 15363 ∨ i = 34178

/-- A `trap` at t: the run ends ☇ there, registers, memory and context as they are. -/
theorem trap_run {X : Type} {R : HostRel X} {p : ByteArray} {P : Program} (t : Nat)
    (hd : deblob p t = some P ∧ P.decode t = some (.noArgs .trap)) (x : X) (ω : Regs) (μ : Memory) :
    FreeRunH p R t ω μ x .panic ω μ x := by
  have hs : P.freeStep t ω μ = (.panic, P.next t, ω, μ) := by
    simp [Program.freeStep, hd.2, Program.exec, Program.finalState, memoryException]
  have := FreeExit.step (p := p) hd.1 hs (by decide)
  exact .exit (FreeRun.exit (by simpa using this)) (by simp)

/-- Each of `HeapTrapT`'s pcs is a `trap`. -/
theorem heapTrapT_run {X : Type} {R : HostRel X} {p : ByteArray} {P : Program} [HasCodeA p P] {t : Nat}
    (ht : HeapTrapT t) (x : X) (ω : Regs) (μ : Memory) : FreeRunH p R t ω μ x .panic ω μ x := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact trap_run _ ⟨(d_3895 (p := p) (P := P)).1, (d_3895 (p := p) (P := P)).2.1⟩ x ω μ
  · exact trap_run _ ⟨(d_47977 (p := p) (P := P)).1, (d_47977 (p := p) (P := P)).2.1⟩ x ω μ
  · exact trap_run _ ⟨(d_15362 (p := p) (P := P)).1, (d_15362 (p := p) (P := P)).2.1⟩ x ω μ
  · exact trap_run _ ⟨(d_15363 (p := p) (P := P)).1, (d_15363 (p := p) (P := P)).2.1⟩ x ω μ
  · exact trap_run _ ⟨(d_34178 (p := p) (P := P)).1, (d_34178 (p := p) (P := P)).2.1⟩ x ω μ

/-- The trap at 15361 (every `unwrap` and `orPanic` failure). -/
theorem trap15361_run {X : Type} {R : HostRel X} {p : ByteArray} {P : Program} [HasCodeA p P]
    (x : X) (ω : Regs) (μ : Memory) : FreeRunH p R 15361 ω μ x .panic ω μ x :=
  trap_run _ ⟨(d_15361 (p := p) (P := P)).1, (d_15361 (p := p) (P := P)).2.1⟩ x ω μ

/-- **A run reaching a heap trap, keeping the context, is an allowed early ☇**, if the trap pcs
    satisfy the abort reason `Ab`. -/
theorem aborts_of_trap {Qu : Type} {p : ByteArray} {P : Program} [HasCodeA p P]
    {R : HostRel (AccCtx × Qu)} {Ab : St Qu → Prop} (hAb : ∀ s : St Qu, HeapTrapT s.i → Ab s)
    (s : St Qu) {t : Nat} {ω' : Regs} {μ' : Memory} {q' : Qu} {n : Nat} (ht : HeapTrapT t)
    (run : FreeStepsH p (KeepCtx R) s.i s.ω s.μ (s.c, s.q) t ω' μ' (s.c, q') n) :
    Aborts p (KeepCtx R) Ab s s.c :=
  ⟨⟨t, ω', μ', s.c, q'⟩, ⟨n, run⟩, hAb _ ht, ⟨ω', μ', q', heapTrapT_run (P := P) ht _ ω' μ'⟩⟩

/-- **`on_transfer`'s `heap` abort states**: a heap trap, or a failed allocator call (40611 / 40821 with
    ω₇ = 0) inside a formatting call (`ExhaustsP`). -/
def HeapFailT {Qu : Type} (s : St Qu) : Prop :=
  HeapTrapT s.i ∨ ((s.i = 40611 ∨ s.i = 40821) ∧ s.ω[7] = UInt64.ofNat 0)

/-- **A formatting call's allocation failure (`ExhaustsP`) is an allowed early ☇**, if the abort
    reason holds at the failed call. -/
theorem aborts_of_exhaustsP {p : ByteArray} {env : AccEnv} {pb : Nat}
    {Ab : St Stream → Prop} (hAb : ∀ s : St Stream, HeapFailT s → Ab s)
    (s : St Stream) (h : ExhaustsP p env pb s.i s.ω s.μ s.c s.q) :
    Aborts p (KeepCtx (accContractS env)) Ab s s.c := by
  obtain ⟨ω', μ', q', j, N, run, h7, hj, ω'', μ'', q'', hr⟩ := h
  refine ⟨⟨j, ω', μ', s.c, q'⟩, ⟨N, run⟩, hAb _ (.inr ⟨?_, h7⟩), ⟨ω'', μ'', q'', hr⟩⟩
  rcases hj with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact .inl rfl
  · exact .inr rfl

/-- **A run reaching 15361, keeping the context, ends ☇ with it.** -/
theorem ends_of_15361 {Qu : Type} {p : ByteArray} {P : Program} [HasCodeA p P]
    {R : HostRel (AccCtx × Qu)} (s : St Qu) {ω' : Regs} {μ' : Memory} {q' : Qu} {n : Nat}
    (run : FreeStepsH p (KeepCtx R) s.i s.ω s.μ (s.c, s.q) 15361 ω' μ' (s.c, q') n) :
    Ends p (KeepCtx R) s .panic s.c :=
  ⟨ω', μ', q', FreeRunH.prepend run (trap15361_run (P := P) _ ω' μ')⟩

end Services.Bootstrap.Acc
