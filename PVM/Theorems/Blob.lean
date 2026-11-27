import PVM.Blob

/-!
# Facts about skip, $\varpi$ and $\mathfrak{v}_{\text{blob}}$

* `skip_le`: $\text{skip}(i) \le 24$ (GP eq. `skip`).
* `followsTerminator_iff`, `isBlockStart_iff`: the bounded search used for $\varpi$ is exactly the
  paper's set comprehension (GP §A.3).
* `vBlobAux_fuel`: the fuel given to $\mathfrak{v}_{\text{blob}}$ is enough, so `vBlob` is the paper's recursion.
-/

namespace PVM.Program

theorem skip_le (P : Program) (i : Nat) : P.skip i ≤ 24 := by
  unfold skip
  cases h : (List.range 24).find? (fun j => P.maskExt (i + 1 + j)) with
  | none => simp
  | some j =>
    have := List.mem_of_find?_eq_some h
    simp at this ⊢; omega

/-- The window search of `followsTerminator` is the paper's
    $\exists m \in \mathbb{N}_{|c|} : \mathbf{k}_m = 1 \wedge \mathbf{c}_m \in T \wedge m + 1 + \text{skip}(m) = n$. -/
theorem followsTerminator_iff (P : Program) (n : Nat) :
    P.followsTerminator n = true ↔
      ∃ m, m < P.code.size ∧ P.maskAt m = true ∧ isTerminator (P.zeta m) = true ∧ P.next m = n := by
  unfold followsTerminator
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨d, -, hd, ⟨⟨hm, hk⟩, ht⟩, hn⟩
    exact ⟨_, hm, hk, ht, hn⟩
  · rintro ⟨m, hm, hk, ht, hn⟩
    have hs := P.skip_le m
    unfold next at hn
    refine ⟨P.skip m, by omega, by omega, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;>
      rw [show n - 1 - P.skip m = m by omega] <;> first | assumption | (unfold next; omega)

/-- `isBlockStart` is membership in the paper's $\varpi$ (GP §A.3):
    $n \in (\{0\} \cup \{m + 1 + \text{skip}(m) \mid m \in \mathbb{N}_{|c|} \wedge \mathbf{k}_m = 1 \wedge \mathbf{c}_m \in T\})
    \cap \{n \mid \mathbf{k}_n = 1 \wedge \mathbf{c}_n \in U\}$. -/
theorem isBlockStart_iff (P : Program) (n : Nat) :
    P.isBlockStart n = true ↔
      (n = 0 ∨ ∃ m, m < P.code.size ∧ P.maskAt m = true ∧ isTerminator (P.zeta m) = true ∧
          P.next m = n) ∧
        (n < P.code.size ∧ P.maskAt n = true ∧ isValidOpcode (P.zeta n) = true) := by
  rw [← followsTerminator_iff]
  simp [isBlockStart, isInstrStart, and_assoc]

/-- $\mathfrak{v}_{\text{blob}}$'s recursion visits strictly increasing indices, so fuel `f` at
    index `i` with $|\mathbf{k}| + 1 \le f + i$ suffices: any further fuel gives the same answer. -/
theorem vBlobAux_fuel (P : Program) :
    ∀ f i, P.mask.size + 1 ≤ f + i → 0 < f → ∀ k, P.vBlobAux (f + k) i = P.vBlobAux f i := by
  intro f
  induction f with
  | zero => intros; omega
  | succ f ih =>
    intro i hfi _ k
    rw [show f + 1 + k = (f + k) + 1 by omega]
    simp only [vBlobAux]
    split
    · rfl
    · split
      · rfl
      · split
        · rename_i hv
          have hi : i < P.mask.size := by
            simp only [vInst, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hv; omega
          have := P.skip_le i
          exact ih _ (by unfold next; omega) (by omega) k
        · rfl

/-- `vBlob` gives $\mathfrak{v}_{\text{blob}}$ enough fuel: more fuel does not change the result. -/
theorem vBlob_eq (P : Program) (k : Nat) : P.vBlobAux (P.mask.size + 1 + k) 0 = P.vBlob :=
  P.vBlobAux_fuel _ 0 (by omega) (by omega) k

end PVM.Program
