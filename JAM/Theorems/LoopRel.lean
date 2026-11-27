/-!
# Relating two `Id` loops step by step

`forIn_forIn'` relates a plain `for x in l` loop to a `for h : x in l` loop (whose body may use the
membership proof, e.g. to index in bounds) through a relation between their states that every step
preserves. Used by `JAM.Theorems.CheckedIndex` to prove the spec definitions with checked indexing
equal to their earlier forms with `a[i]!`.
-/

namespace JAM.Theorems.LoopRel

universe u
variable {α β γ δ ε : Type u}
/-- Two `Id` loop steps related by `R`: both continue, or both stop, with related states. -/
def StepRel (R : β → γ → Prop) : ForInStep β → ForInStep γ → Prop
  | .yield x, .yield y => R x y
  | .done x, .done y => R x y
  | _, _ => False

theorem forIn_forIn' {l : List α} (R : β → γ → Prop) (f : α → β → Id (ForInStep β))
    (g : (a : α) → a ∈ l → γ → Id (ForInStep γ)) (b : β) (c : γ) (h0 : R b c)
    (step : ∀ a (ha : a ∈ l) b c, R b c → StepRel R (f a b).run (g a ha c).run) :
    R (forIn (m := Id) l b f).run (forIn' (m := Id) l c g).run := by
  induction l generalizing b c with
  | nil => simpa using h0
  | cons x xs ih =>
    rw [List.forIn_cons, List.forIn'_cons]
    have hs := step x (List.mem_cons_self ..) b c h0
    revert hs
    cases f x b <;> cases g x (List.mem_cons_self ..) c <;> intro hs <;> simp only [StepRel] at hs
    · exact hs
    · exact hs.elim
    · exact hs.elim
    · exact ih (g := fun a ha => g a (List.mem_cons_of_mem _ ha)) _ _ hs
        (fun a ha => step a (List.mem_cons_of_mem _ ha))
theorem bind_rel {x : Id β} {y : Id γ} {f : β → Id δ} {g : γ → Id ε} (R1 : β → γ → Prop)
    (R2 : δ → ε → Prop) (h : R1 x.run y.run) (hfg : ∀ a b, R1 a b → R2 (f a).run (g b).run) :
    R2 (x >>= f).run (y >>= g).run := hfg _ _ h
/-- Two plain `for x in l` loops related by `R`. -/
theorem forIn_forIn {l : List α} (R : β → γ → Prop) (f : α → β → Id (ForInStep β))
    (g : α → γ → Id (ForInStep γ)) (b : β) (c : γ) (h0 : R b c)
    (step : ∀ a, a ∈ l → ∀ b c, R b c → StepRel R (f a b).run (g a c).run) :
    R (forIn (m := Id) l b f).run (forIn (m := Id) l c g).run := by
  induction l generalizing b c with
  | nil => simpa using h0
  | cons x xs ih =>
    rw [List.forIn_cons, List.forIn_cons]
    have hs := step x (List.mem_cons_self ..) b c h0
    revert hs
    cases f x b <;> cases g x c <;> intro hs <;> simp only [StepRel] at hs
    · exact hs
    · exact hs.elim
    · exact hs.elim
    · exact ih _ _ hs (fun a ha => step a (List.mem_cons_of_mem _ ha))

/-! ## Reading and writing a `Vector` through its array -/

theorem getV {n : Nat} (v : Vector UInt64 n) (k : Nat) (hk : k < n) : v.toArray[k]! = v[k] := by
  simp [getElem!_pos, hk]

theorem setV {n : Nat} (v : Vector UInt64 n) (k : Nat) (hk : k < n) (x : UInt64) :
    v.toArray.set! k x = (v.set k x hk).toArray := by
  simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hk]

end JAM.Theorems.LoopRel
