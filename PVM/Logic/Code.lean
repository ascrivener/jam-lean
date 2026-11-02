import PVM.Logic.Det

/-!
# Code facts: what a proof needs to know about a program, as one checkable list

A proof that follows a large program through Ψ₁ needs only a few facts about it: that the blob
passes 𝔳_blob, and, at each index it visits, the decoded instruction and ı + 1 + skip(ı); for
branches and jumps, whether the targets are block starts; for `jump_ind`/`load_imm_jump_ind`, the
jump table. `checkCode p fs` checks a list of such facts against the blob `p` in one `Bool`.

`checkCode_sound` turns `checkCode p fs = true` into the facts themselves, with `deblob p i = some P`
at each listed index. So a theorem about a program can take `checkCode p fs = true` as a hypothesis
and be proved from the list alone, whatever evaluates the hypothesis (the kernel, or compiled code
for blobs too large for the kernel).
-/

namespace PVM

/-- One fact about a program. -/
inductive CodeFact where
  /-- At index i: 𝔳_inst, the decoded instruction, and ı + 1 + skip(ı). -/
  | instr (i : Nat) (ins : Instr) (next : Nat)
  /-- Whether n ∈ ϖ (a basic-block start). -/
  | blockStart (n : Nat) (b : Bool)
  /-- |**j**|. -/
  | jumpTableSize (n : Nat)
  /-- **j**_k = t. -/
  | jumpEntry (k t : Nat)
  deriving DecidableEq, Repr

/-- Whether a fact holds of a program. -/
def CodeFact.holds (P : Program) : CodeFact → Bool
  | .instr i ins n => P.vInst i && P.decode i == some ins && P.next i == n
  | .blockStart n b => P.isBlockStart n == b
  | .jumpTableSize n => P.jumpTable.size == n
  | .jumpEntry k t => P.jumpTable.getD k 0 == t

/-- The blob deblobs, passes 𝔳_blob, and every listed fact holds. -/
def checkCode (p : ByteArray) (fs : List CodeFact) : Bool :=
  match Blob.parse? p with
  | some P => P.vBlob && fs.all (·.holds P)
  | none => false

/-- What `checkCode` establishes. -/
structure CodeOk (p : ByteArray) (fs : List CodeFact) (P : Program) : Prop where
  parse : Blob.parse? p = some P
  vBlob : P.vBlob = true
  facts : ∀ f ∈ fs, f.holds P = true

theorem checkCode_sound {p : ByteArray} {fs : List CodeFact} (h : checkCode p fs = true) :
    ∃ P, CodeOk p fs P := by
  unfold checkCode at h
  split at h
  · rename_i P hP
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    exact ⟨P, hP, h.1, h.2⟩
  · cases h

namespace CodeOk

variable {p : ByteArray} {fs : List CodeFact} {P : Program}

theorem instr (h : CodeOk p fs P) {i : Nat} {ins : Instr} {n : Nat}
    (hm : CodeFact.instr i ins n ∈ fs) :
    deblob p i = some P ∧ P.decode i = some ins ∧ P.next i = n := by
  have hf := h.facts _ hm
  simp only [CodeFact.holds, Bool.and_eq_true, beq_iff_eq] at hf
  refine ⟨?_, hf.1.2, hf.2⟩
  simp [deblob, h.parse, h.vBlob, hf.1.1]

theorem blockStart (h : CodeOk p fs P) {n : Nat} {b : Bool} (hm : CodeFact.blockStart n b ∈ fs) :
    P.isBlockStart n = b := by
  have hf := h.facts _ hm
  simpa [CodeFact.holds] using hf

theorem jumpTableSize (h : CodeOk p fs P) {n : Nat} (hm : CodeFact.jumpTableSize n ∈ fs) :
    P.jumpTable.size = n := by
  have hf := h.facts _ hm
  simpa [CodeFact.holds] using hf

theorem jumpEntry (h : CodeOk p fs P) {k t : Nat} (hm : CodeFact.jumpEntry k t ∈ fs) :
    P.jumpTable.getD k 0 = t := by
  have hf := h.facts _ hm
  simpa [CodeFact.holds] using hf

end CodeOk

/-- A gas-free step at a listed instruction is the instruction's mutation, with ε^μ. -/
theorem Program.freeStep_of_decode {P : Program} {i : Nat} {ins : Instr} (ω : Regs) (μ : Memory)
    (h : P.decode i = some ins) :
    P.freeStep i ω μ =
      let m := P.exec i ins ω μ
      finalState .cont i ω μ m (memoryException μ m.reads m.writes) := by
  simp [Program.freeStep, h]

end PVM
