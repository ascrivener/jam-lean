import Services.Bootstrap.Acc.ItemsLoop.Tr

/-!
# The items loop as `Impl.forIn` (R1)

`Spec.accumulate`'s loop `for it in items do …` (GP v0.8.0 §12, the inputs decoded as `Spec.specItem`s)
against the binary's loop at 6766, with the loop invariant `ItemsInv`:
- a transfer: `loop_tr` (6766 → 7159 → 6766, `tr_impl`);
- an operand with a work output: the operand arm (R2), a parameter here (`OpArm`);
- an operand with a work error: the skip arm, a parameter here (`ErrArm`);
- no input left: the loop's end halts with (ω₇, ω₈) = (0, 0) (`loop_end`, from `items_halt`).
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx Picoalloc

/-- The body of `Spec.accumulate`'s loop over the items. -/
def accBody (C : Spec.Consts) (now : Nat) : Spec.Item → PUnit → Spec.Prog Spec.AOp (ForInStep PUnit) :=
  fun it _ =>
    match it with
    | .work p (some out) => do
      Spec.onWorkItem C now p out
      pure (ForInStep.yield PUnit.unit)
    | .work _ none => pure (ForInStep.yield PUnit.unit)
    | .transfer s a m => do
      Spec.onTransfer s a m
      pure (ForInStep.yield PUnit.unit)

/-- **The operand arm** (R2's statement): from the loop head with an operand with work output b
    next, the run implements `onWorkItem C now p b` then `yield`, and returns to the loop head with
    `ItemsInv` for the rest. -/
def OpArm (p : ByteArray) (env : AccEnv) (Ab : St Stream → Prop) (C : Spec.Consts) (now : Nat)
    (pb S0 S1 sp q nc e : Nat) (μ₀ : Memory) : Prop :=
  ∀ (o : OperandTuple) (b : ByteArray) (rest : List AccumulateInput) (s : St Stream)
    (Q : ForInStep PUnit → St Stream → Prop), o.result = .ok b →
    (∀ s', ItemsInv env pb S0 S1 sp q nc e μ₀ rest s' → Q (.yield ⟨⟩) s') →
    ItemsInv env pb S0 S1 sp q nc e μ₀ (.operand o :: rest) s →
    Impl p (accContractS env) env Ab
      (Spec.Prog.bind (Spec.onWorkItem C now o.packageHash.toList b.toList)
        fun _ => pure (ForInStep.yield PUnit.unit)) Q s

/-- **The work-error arm**: from the loop head with an operand with a work error next, the run
    returns to the loop head with `ItemsInv` for the rest, keeping the context (`pure`). -/
def ErrArm (p : ByteArray) (env : AccEnv) (Ab : St Stream → Prop) (pb S0 S1 sp q nc e : Nat)
    (μ₀ : Memory) : Prop :=
  ∀ (o : OperandTuple) (er : WorkError) (rest : List AccumulateInput) (s : St Stream)
    (Q : ForInStep PUnit → St Stream → Prop), o.result = .err er →
    (∀ s', ItemsInv env pb S0 S1 sp q nc e μ₀ rest s' → Q (.yield ⟨⟩) s') →
    ItemsInv env pb S0 S1 sp q nc e μ₀ (.operand o :: rest) s →
    Impl p (accContractS env) env Ab (pure (ForInStep.yield PUnit.unit)) Q s

/-- **The loop's end halts**: from the loop head with no input left, the slot buffer is freed and the
    run halts with ω₈ = 0, keeping the context. -/
theorem loop_end {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : AccEnv)
    {pb S0 S1 sp q nc e : Nat} {μ₀ : Memory} (s : St Stream)
    (hI : ItemsInv env pb S0 S1 sp q nc e μ₀ [] s) : Halts p (accContractS env) () s := by
  obtain ⟨st, H, hbuf, -⟩ := hI.heap
  have hS1 := H.hS1
  have hsp := hI.hsp
  have hstk := hI.hstk
  have hc := hI.cur
  simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at hc
  obtain ⟨ω', μ', run, h8⟩ := items_halt (p := p) (P := P) (R := KeepCtx (accContractS env)) env.code pb
    S0 S1 (s.c, s.q) s.ω s.μ st sp e q nc H hI.r1 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hc
    hI.m144 hI.m32 hI.m16 hI.m1848
    (fun hn => by obtain ⟨d, hd, hu, hq, -⟩ := hbuf hn; exact ⟨d, hd, hu, hq⟩)
  refine ⟨ω', μ', s.q, ?_, h8⟩
  rw [hI.pc]; exact run

set_option maxRecDepth 20000 in
/-- **R1, the items loop**: from the loop head with `ItemsInv` for the inputs `ins`, the run
    implements `Spec.accumulate`'s loop over `ins.map Spec.specItem`, then halts with ω₈ = 0. The
    operand arm (`OpArm`, R2) and the work-error arm (`ErrArm`) are premises; the transfer arm is
    `loop_tr` (named hypotheses `Utf8Call`, `LogFmt`, `KeyFmt`). Early ☇ for any `Ab` holding at
    `HeapFailT` states. -/
theorem items_loop (env : AccEnv) (gcap pb : Nat) (hcap1 : 134217728 ≤ gcap)
    (hcap : gcap < 18446744073709551616)
    {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] {Ab : St Stream → Prop} {S0 S1 : Nat}
    (hAb : ∀ s : St Stream, HeapFailT s → Ab s) (hU : Utf8Call p env pb S0 S1)
    (hL : LogFmt p env pb S0 S1) (hK : KeyFmt p env pb S0 S1) (C : Spec.Consts) (now : Nat)
    {sp q nc e : Nat} {μ₀ : Memory}
    (hop : OpArm p env Ab C now pb S0 S1 sp q nc e μ₀) (herr : ErrArm p env Ab pb S0 S1 sp q nc e μ₀) :
    ∀ (ins : List AccumulateInput) (s : St Stream), ItemsInv env pb S0 S1 sp q nc e μ₀ ins s →
      Impl p (accContractS env) env Ab
        (Spec.Prog.bind (forIn (ins.map Spec.specItem) PUnit.unit (accBody C now)) fun _ => pure ())
        (Halts p (accContractS env)) s := by
  intro ins s hI
  refine Impl.bind _ (Halts p (accContractS env)) _ _ ?_
  refine Impl.forIn (accBody C now) (fun _ s => Impl p (accContractS env) env Ab (pure ()) (Halts p (accContractS env)) s)
    (fun xs _ s => ∃ ins', xs = ins'.map Spec.specItem ∧ ItemsInv env pb S0 S1 sp q nc e μ₀ ins' s)
    ?_ ?_ (ins.map Spec.specItem) PUnit.unit s ⟨ins, rfl, hI⟩
  · intro x xs _ s ⟨ins', hx, hI'⟩
    cases ins' with
    | nil => cases hx
    | cons i rest =>
      simp only [List.map_cons, List.cons.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      cases i with
      | transfer t =>
        exact loop_tr env gcap pb hcap1 hcap (P := P) hAb hU hL hK t rest s _
          (fun s' h => ⟨rest, rfl, h⟩) hI'
      | operand o =>
        cases hr : o.result with
        | ok b =>
          simp only [Spec.specItem, hr, accBody]
          refine hop o b rest s _ hr ?_ hI'
          exact fun s' h => ⟨rest, rfl, h⟩
        | err er =>
          simp only [Spec.specItem, hr, accBody]
          refine herr o er rest s _ hr ?_ hI'
          exact fun s' h => ⟨rest, rfl, h⟩
  · intro _ s ⟨ins', hx, hI'⟩
    cases ins' with
    | cons _ _ => cases hx
    | nil => exact Impl.pure_of (loop_end (P := P) env s hI')

end Services.Bootstrap.Acc
