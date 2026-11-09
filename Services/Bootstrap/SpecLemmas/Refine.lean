import Services.Bootstrap.SpecLemmas.Codec

/-!
# Refine keeps instructions well-formed

`refineInstr` turns a well-formed instruction into a well-formed one, provided the host's replies
are within the sizes ℰ can carry. With `decode_output` (`SpecLemmas.Codec`) this says that the work
output bootstrap's refine produces decodes in accumulate to the instructions refine wrote.
-/

namespace Services.Bootstrap.Spec

namespace Prog

/-- Every value `p` can return satisfies `Q`, when each reply `b` to an operation `o` satisfies
    `ok o b`. A panic returns nothing, so it satisfies every `Q`. -/
def Returns {E : Type → Type} {α : Type} (ok : {β : Type} → E β → β → Prop) (Q : α → Prop) :
    Prog E α → Prop
  | .pure a => Q a
  | .call o k => ∀ b, ok o b → Returns ok Q (k b)
  | .panic => True

variable {E : Type → Type} {ok : {β : Type} → E β → β → Prop}

theorem Returns.pure {α : Type} {Q : α → Prop} {a : α} (h : Q a) : Returns ok Q (Pure.pure a : Prog E α) := h

theorem Returns.panic {α : Type} {Q : α → Prop} : Returns ok Q (Prog.panic : Prog E α) := trivial

theorem Returns.op {β : Type} {Q : β → Prop} {o : E β} (h : ∀ b, ok o b → Q b) :
    Returns ok Q (Prog.op o) := h

theorem Returns.bind {α β : Type} {R : α → Prop} {Q : β → Prop} {p : Prog E α} {f : α → Prog E β}
    (hp : Returns ok R p) (hf : ∀ a, R a → Returns ok Q (f a)) : Returns ok Q (p >>= f) := by
  induction p with
  | pure a => exact hf a hp
  | call o k ih => exact fun b hb => ih b (hp b hb)
  | panic => trivial

theorem Returns.mono {α : Type} {R Q : α → Prop} {p : Prog E α} (hp : Returns ok R p)
    (h : ∀ a, R a → Q a) : Returns ok Q p := by
  induction p with
  | pure a => exact h a hp
  | call o k ih => exact fun b hb => ih b (hp b hb)
  | panic => trivial

/-- Any program satisfies a postcondition that always holds. -/
theorem Returns.true {α : Type} (p : Prog E α) : Returns ok (fun _ => True) p := by
  induction p with
  | pure a => trivial
  | call o k ih => exact fun b _ => ih b
  | panic => trivial

theorem Returns.mapM_loop {α β : Type} {R : β → Prop} (f : α → Prog E β)
    (as : List α) (hf : ∀ a ∈ as, Returns ok R (f a)) (bs : List β) (hbs : ∀ b ∈ bs, R b) :
    Returns ok (fun out => out.length = bs.length + as.length ∧ ∀ b ∈ out, R b)
      (List.mapM.loop f as bs) := by
  induction as generalizing bs with
  | nil => exact Returns.pure (by simpa using hbs)
  | cons a as ih =>
    simp only [List.mapM.loop]
    refine Returns.bind (hf a (by simp)) fun b hb => ?_
    refine (ih (fun a' ha' => hf a' (by simp [ha'])) (b :: bs) ?_).mono ?_
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hb
      · exact hbs x hx
    · intro out ⟨h1, h2⟩; exact ⟨by simp only [List.length_cons] at *; omega, h2⟩

/-- `mapM` returns as many values as it was given, each satisfying what `f` guarantees. -/
theorem Returns.mapM {α β : Type} {R : β → Prop} (f : α → Prog E β) (as : List α)
    (hf : ∀ a ∈ as, Returns ok R (f a)) :
    Returns ok (fun out => out.length = as.length ∧ ∀ b ∈ out, R b) (as.mapM f) :=
  (Returns.mapM_loop f as hf [] (by simp)).mono fun _ ⟨h1, h2⟩ => ⟨by simpa using h1, h2⟩

end Prog

/-- Host replies to refine's operations that ℰ can carry: looked-up preimages and imported segments
    shorter than 2^32 octets. (On chain a segment is 𝖶_G = 4104 octets, GP appendix I.) -/
def ROp.Ok : {β : Type} → ROp β → β → Prop
  | _, .histLookup _ _, d => ∀ x ∈ d, short x
  | _, .importSeg _, d => ∀ x ∈ d, short x
  | _, .exportSeg _, _ => True

/-- The keys `randomKeys` generates are 32 octets each, and fewer than 2^32 of them. -/
def Consts.KeysWF (C : Consts) : Prop :=
  ∀ seed n, short (C.randomKeys seed n) ∧ ∀ k ∈ C.randomKeys seed n, k.length = 32

/-- **`refineInstr` keeps instructions well-formed**: whatever refine returns for a well-formed
    instruction is well-formed, given replies that ℰ can carry and well-formed random keys. -/
theorem refineInstr_wf (C : Consts) (hkeys : C.KeysWF) (x : Instr) (hx : x.WF C) :
    Prog.Returns ROp.Ok (Instr.WF C) (refineInstr C x) := by
  cases x with
  | lookup s h e =>
    cases e with
    | true => exact Prog.Returns.bind (Prog.Returns.op fun d hd => hd) fun d hd => hd
    | false => exact hx
  | randomStorageRefine seed n =>
    intro l hl; cases hl; exact hkeys seed n
  | exportSegs ds =>
    refine Prog.Returns.bind (Prog.Returns.true _) fun _ _ => ?_
    show fits 8 ds.length
    have : ds.length < 2 ^ 32 := hx.1
    unfold fits; omega
  | importSegs items =>
    refine Prog.Returns.bind (Prog.Returns.mapM (R := fun seg : Bytes => short seg) _ items ?_) ?_
    · intro ⟨i, l⟩ _
      refine Prog.Returns.bind (Prog.Returns.op (Q := fun d => ∀ x ∈ d, short x) fun d hd => hd) ?_
      intro d hd
      cases d with
      | none => exact Prog.Returns.panic
      | some seg =>
        show short (seg.take l)
        have := hd seg rfl
        unfold short at *; simp; omega
    · intro segs ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      have := hx.1
      unfold short at *; omega
  | _ => exact hx

/-- **Refine, end to end.** For a payload ℰ(`Instructions { is, salt }`) ⌢ rest with well-formed
    instructions, every output refine returns (under replies ℰ can carry) decodes, as accumulate
    decodes it, to as many well-formed instructions and the work-item index mod 2^16. -/
theorem refine_output (C : Consts) (hkeys : C.KeysWF) (item : Nat) (is : List Instr) (salt rest : Bytes)
    (hwf : ∀ x ∈ is, x.WF C) (hn : is.length < 2 ^ 32) (hsalt : salt.length = 32) :
    Prog.Returns ROp.Ok
      (fun out => ∃ is', decode (Dec.output C) out = some (is', item % 2 ^ 16) ∧
        is'.length = is.length ∧ ∀ x ∈ is', x.WF C)
      (refine C item (encodePayload is salt ++ rest)) := by
  simp only [refine, decode_payload C is salt rest hwf hn hsalt]
  refine Prog.Returns.bind
    (Prog.Returns.mapM (R := Instr.WF C) _ is fun x hx => refineInstr_wf C hkeys x (hwf x hx)) ?_
  intro out ⟨hlen, hout⟩
  refine Prog.Returns.pure ⟨out, ?_, hlen, hout⟩
  simpa using decode_output' C out item [] hout (hlen ▸ hn)

end Services.Bootstrap.Spec
