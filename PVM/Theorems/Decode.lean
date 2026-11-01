import PVM.Instr

/-!
# Decoding agrees with the opcode

`Program.decode` produces an instruction whose opcode is ζ_ı (`decode_opcode`), and it
succeeds exactly when ζ_ı ∈ U (`decode_isSome_iff`).
-/

namespace PVM

/-- For each opcode enumeration `X`, `X.ofOpcode?` inverts `X.opcode`. -/
macro "opcode_lemmas" X:ident : command => do
  let ofOp := Lean.mkIdent (X.getId ++ `ofOpcode?)
  let op := Lean.mkIdent (X.getId ++ `opcode)
  let l1 := Lean.mkIdent (X.getId ++ `opcode_of_ofOpcode?)
  let l2 := Lean.mkIdent (X.getId ++ `ofOpcode?_opcode)
  `(theorem $l1:ident {n : Nat} {o : $X} (h : $ofOp n = some o) : $op o = n := by
      unfold $ofOp:ident at h; split at h <;> cases h <;> rfl
    @[simp] theorem $l2:ident (o : $X) : $ofOp ($op o) = some o := by cases o <;> rfl)

opcode_lemmas NoArgsOp
opcode_lemmas OneImmOp
opcode_lemmas RegExtImmOp
opcode_lemmas TwoImmOp
opcode_lemmas OneOffsetOp
opcode_lemmas RegImmOp
opcode_lemmas RegTwoImmOp
opcode_lemmas RegImmOffsetOp
opcode_lemmas TwoRegOp
opcode_lemmas TwoRegImmOp
opcode_lemmas TwoRegOffsetOp
opcode_lemmas TwoRegTwoImmOp
opcode_lemmas ThreeRegOp

/-- A decoded instruction's opcode is ζ_ı. -/
theorem Program.decode_opcode {P : Program} {i : Nat} {ins : Instr} (h : P.decode i = some ins) :
    ins.opcode = P.zeta i := by
  unfold Program.decode at h
  dsimp only at h
  split at h
  · cases h
  all_goals
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨o, ho, rfl⟩ := h
    first
    | exact NoArgsOp.opcode_of_ofOpcode? ho
    | exact OneImmOp.opcode_of_ofOpcode? ho
    | exact RegExtImmOp.opcode_of_ofOpcode? ho
    | exact TwoImmOp.opcode_of_ofOpcode? ho
    | exact OneOffsetOp.opcode_of_ofOpcode? ho
    | exact RegImmOp.opcode_of_ofOpcode? ho
    | exact RegTwoImmOp.opcode_of_ofOpcode? ho
    | exact RegImmOffsetOp.opcode_of_ofOpcode? ho
    | exact TwoRegOp.opcode_of_ofOpcode? ho
    | exact TwoRegImmOp.opcode_of_ofOpcode? ho
    | exact TwoRegOffsetOp.opcode_of_ofOpcode? ho
    | exact TwoRegTwoImmOp.opcode_of_ofOpcode? ho
    | exact ThreeRegOp.opcode_of_ofOpcode? ho

end PVM
