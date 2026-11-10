import PVM.SymExec.Core

/-!
# Soundness of the symbolic executor (spike)

`srun_sound`: if `srun` follows a stretch from a state described by σ to `target` in `k` steps,
ending in σ', then the gas-free machine (GP v0.8.0 §A.4, `Program.freeStep`) takes the same `k`
steps through the listed instructions, as a `FreeStepsH` chain, to a state described by σ'.
-/

namespace PVM.SymExec

open Num Exec

variable {E : Env} {st : Static}

theorem pow8 (n : Nat) : 2 ^ (8 * n) = 256 ^ n := by
  rw [Nat.pow_mul]

theorem two32_eq : (two32 : Nat) = 4294967296 := rfl
theorem two64_eq : (two64 : Nat) = 18446744073709551616 := rfl

/-! ## Addresses -/

theorem lo_le (hpre : Pre E st) (a : Aff) : a.lo st ≤ a.eval E := by
  obtain ⟨base, off⟩ := a
  cases base with
  | none => simp [Aff.lo, Aff.eval]
  | some k =>
    simp only [Aff.lo, Aff.eval]
    cases h : st.lb[k]? with
    | none => simp; omega
    | some b => have := hpre.2.1 k b h; simp; omega

theorem le_hi (hpre : Pre E st) {a : Aff} {h : Int} (hh : a.hi st = some h) : a.eval E ≤ h := by
  obtain ⟨base, off⟩ := a
  cases base with
  | none => simp [Aff.hi] at hh; simp [Aff.eval]; omega
  | some k =>
    simp only [Aff.hi] at hh
    cases hu : st.ub[k]? with
    | none => rw [hu] at hh; cases hh
    | some u =>
      rw [hu] at hh; simp at hh; subst hh
      have := hpre.1 k u hu
      simp only [Aff.eval]; omega

theorem eval_sub {a b : Aff} (h : a.base = b.base) : a.eval E - b.eval E = a.off - b.off := by
  obtain ⟨ba, oa⟩ := a; obtain ⟨bb, ob⟩ := b
  simp only at h; subst h
  cases ba <;> simp [Aff.eval] <;> omega

theorem valid_sound (hpre : Pre E st) {a : Aff} {n : Nat} (h : valid st a n = true) :
    0 ≤ a.eval E ∧ a.eval E + n ≤ two32 ∧ a.eval E < two32 := by
  simp only [valid, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  have := lo_le hpre a
  split at h2
  · rename_i hv hh
    have := le_hi hpre hh
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    omega
  · cases h2

theorem within_sound (hpre : Pre E st) {a : Aff} {n : Nat} {r : Aff × Nat}
    (h : within st a n r = true) : ∀ t, InReg E (a, n) t → InReg E r t := by
  intro t ht
  simp only [InReg] at ht ⊢
  simp only [within, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  rcases h with ⟨⟨hb, h1⟩, h2⟩ | ⟨⟨hb, h1⟩, h2⟩
  · have := eval_sub (E := E) hb; omega
  · have hl := lo_le hpre a
    have hr : r.1.eval E = r.1.off := by
      rcases r with ⟨⟨b, o⟩, l⟩; simp only at hb; subst hb; simp [Aff.eval]
    split at h2
    · rename_i hv hh
      have := le_hi hpre hh
      simp only [decide_eq_true_eq] at h2
      omega
    · cases h2

theorem disj_sound (hpre : Pre E st) {a : Aff} {n : Nat} {b : Aff} {m : Nat}
    (h : disj st a n b m = true) : ∀ t, InReg E (a, n) t → ¬ InReg E (b, m) t := by
  intro t ha hb
  simp only [InReg] at ha hb
  simp only [disj, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq,
    List.any_eq_true] at h
  rcases h with ((((h | h) | ⟨hbase, h | h⟩) | h) | h) | ⟨p, hp, h⟩
  · omega
  · omega
  · have := eval_sub (E := E) hbase; omega
  · have := eval_sub (E := E) hbase; omega
  · split at h
    · rename_i hv hh
      have := le_hi hpre hh; have := lo_le hpre b
      simp only [decide_eq_true_eq] at h; omega
    · cases h
  · split at h
    · rename_i hv hh
      have := le_hi hpre hh; have := lo_le hpre a
      simp only [decide_eq_true_eq] at h; omega
    · cases h
  · have hs := hpre.2.2.2.2 p hp t
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hs (within_sound hpre h1 t ha) (within_sound hpre h2 t hb)
    · exact hs (within_sound hpre h2 t hb) (within_sound hpre h1 t ha)


/-! ## Values -/

theorem bnd_sound (hpre : Pre E st) : ∀ (v : SVal) b, v.bnd st = some b → v.eval E < b := by
  intro v b h
  cases v with
  | const n => simp only [SVal.bnd, Option.some.injEq] at h; subst h; simp [SVal.eval]
  | var k => exact hpre.1 k b h
  | reg0 r => simp only [SVal.bnd, Option.some.injEq] at h; subst h; exact UInt64.toNat_lt _
  | mem0 a n =>
    simp only [SVal.bnd, Option.some.injEq] at h; subst h
    have := decodeLE_lt (E.μ.readN (a.eval E).toNat n)
    simpa [SVal.eval] using this
  | mod v m =>
    simp only [SVal.bnd] at h
    split at h
    · cases h; exact Nat.mod_lt _ ‹_›
    · cases h
  | addr a =>
    simp only [SVal.bnd] at h
    split at h
    · rename_i hl
      cases hh : a.hi st with
      | none => rw [hh] at h; cases h
      | some hv =>
        rw [hh] at h; simp only [Option.map, Option.some.injEq] at h; subst h
        have h1 := le_hi hpre hh; have h2 := lo_le hpre a
        simp only [SVal.eval]; omega
    · cases h
  | sx k w =>
    simp only [SVal.bnd, Option.some.injEq] at h; subst h
    simp only [SVal.eval, u64, unsigned]
    have h1 := Int.emod_lt_of_pos (2 ^ (8 * 8) + signed k (w.eval E)) (show (0 : Int) < 2 ^ (8 * 8) by decide)
    have h0 := Int.emod_nonneg (2 ^ (8 * 8) + signed k (w.eval E)) (show (2 ^ (8 * 8) : Int) ≠ 0 by decide)
    simp only [two64]
    omega
  | _ => simp [SVal.bnd] at h

theorem bnd_any (hpre : Pre E st) {v : SVal} {m : Nat} (h : (v.bnd st).any (· ≤ m) = true) :
    v.eval E < m := by
  cases hb : v.bnd st with
  | none => rw [hb] at h; cases h
  | some b =>
    rw [hb] at h; simp only [Option.any, decide_eq_true_eq] at h
    have := bnd_sound hpre v b hb; omega

theorem sx_mod {k w m : Nat} (hk : k = 2 ∨ k = 4) (hm : m = 256 ^ k) (hw : w < 2 ^ (8 * k)) :
    u64 (signed k w) % m = w % m := by
  subst hm; exact sxw_mod k w hk hw

theorem mkMod_eval (hpre : Pre E st) (v : SVal) (m : Nat) :
    (mkMod st v m).eval E = v.eval E % m := by
  unfold mkMod
  split
  · rfl
  · rename_i k w
    split
    · rename_i hc
      obtain ⟨hk, hm, hb⟩ := hc
      have hw := bnd_any hpre hb
      simp only [SVal.eval]
      rw [sx_mod hk hm hw]
      split
      · rename_i h; exact (Nat.mod_eq_of_lt (bnd_any hpre h)).symm
      · rfl
    · split
      · rename_i h; exact (Nat.mod_eq_of_lt (bnd_any hpre h)).symm
      · rfl
  · split
    · rename_i h; exact (Nat.mod_eq_of_lt (bnd_any hpre h)).symm
    · rfl

theorem asAff_sound {v : SVal} {a : Aff} (h : asAff v = some a) (hlo : 0 ≤ a.lo st)
    (hpre : Pre E st) : (v.eval E : Int) = a.eval E := by
  cases v with
  | const n => simp only [asAff, Option.some.injEq] at h; subst h; simp [SVal.eval, Aff.eval]
  | var k => simp only [asAff, Option.some.injEq] at h; subst h; simp [SVal.eval, Aff.eval]
  | addr a' =>
    simp only [asAff, Option.some.injEq] at h; subst h
    have := lo_le hpre a'
    simp only [SVal.eval]; omega
  | _ => simp [asAff] at h

theorem addAff_sound (hpre : Pre E st) {a a' : Aff} {x M : Nat} (hM : 0 < M)
    (h : addAff st a x M = some a') :
    (((a.eval E).toNat + x) % M : Nat) = (a'.eval E).toNat ∧ 0 ≤ a'.eval E ∧ a'.eval E < M ∧
      0 ≤ a.eval E ∧ 0 ≤ a.lo st := by
  unfold addAff at h
  by_cases hc : affOk st a ⟨a.base, a.off + shift x M⟩ M = true
  · rw [ite_eq_left hc] at h
    cases h
    simp only [affOk, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    have hl := lo_le hpre a
    have hl' := lo_le hpre (st := st) (E := E) ⟨a.base, a.off + shift x M⟩
    cases hh : Aff.hi st ⟨a.base, a.off + shift x M⟩ with
    | none => rw [hh] at h3; cases h3
    | some hv =>
      rw [hh] at h3; simp only [Option.any, decide_eq_true_eq] at h3
      have hu := le_hi hpre hh
      have hs := eval_sub (E := E) (a := ⟨a.base, a.off + shift x M⟩) (b := a) rfl
      simp only at hs
      have hxm : x % M < M := Nat.mod_lt _ hM
      have hmod : ((a.eval E).toNat + x) % M = ((a.eval E).toNat + x % M) % M :=
        (Nat.add_mod_mod _ _ _).symm
      have hsh : shift x M = ((x % M : Nat) : Int) ∨ shift x M = ((x % M : Nat) : Int) - M := by
        unfold shift; split
        · exact Or.inl rfl
        · exact Or.inr rfl
      refine ⟨?_, by omega, by omega, by omega, h1⟩
      rw [hmod]
      rcases hsh with hsh | hsh
      · rw [Nat.mod_eq_of_lt (by omega)]; omega
      · rw [show (a.eval E).toNat + x % M = (Aff.eval E ⟨a.base, a.off + shift x M⟩).toNat + M by
            omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · rw [ite_eq_right hc] at h; cases h

theorem addv_eval (hpre : Pre E st) (v : SVal) (x : Nat) (f : SVal)
    (hf : f.eval E = (v.eval E + x) % two64) : (addv st v x f).eval E = (v.eval E + x) % two64 := by
  unfold addv
  split
  · rfl
  · split
    · rename_i a' h
      cases ha : asAff v with
      | none => rw [ha] at h; cases h
      | some a =>
        rw [ha] at h
        simp only [Option.bind] at h
        obtain ⟨h1, h2, h3, h4, hlo⟩ := addAff_sound hpre (by decide) h
        have := asAff_sound ha hlo hpre
        simp only [SVal.eval]
        rw [← h1]; congr 2; omega
    · exact hf

theorem alu2i_noA (op : TwoRegImmOp) (h : usesA op = false) (a b x : Nat) :
    twoRegImmAlu op a b x = twoRegImmAlu op 0 b x := by
  cases op <;> first | rfl | simp [usesA] at h

theorem alu3_noD (op : ThreeRegOp) (h : usesD op = false) (a b d : Nat) :
    threeRegAlu op a b d = threeRegAlu op a b 0 := by
  cases op <;> first | rfl | simp [usesD] at h

theorem foldAlu2i_eval (op : TwoRegImmOp) (a b : SVal) (x : Nat) :
    (foldAlu2i op a b x).eval E = (twoRegImmAlu op (a.eval E) (b.eval E) x).getD 0 := by
  unfold foldAlu2i; split <;> rfl

theorem foldAlu3_eval (op : ThreeRegOp) (a b d : SVal) :
    (foldAlu3 op a b d).eval E = threeRegAlu op (a.eval E) (b.eval E) (d.eval E) := by
  unfold foldAlu3; split <;> rfl

theorem mkAlu2i_eval (hpre : Pre E st) (op : TwoRegImmOp) (a b : SVal) (x : Nat) :
    (mkAlu2i st op a b x).eval E = (twoRegImmAlu op (a.eval E) (b.eval E) x).getD 0 := by
  unfold mkAlu2i
  split
  · rename_i hop; subst hop
    rw [addv_eval hpre]
    · rfl
    · rw [foldAlu2i_eval]; rfl
  · rw [foldAlu2i_eval]
    cases hu : usesA op
    · simp only [Bool.false_eq_true, ite_false, SVal.eval]; rw [alu2i_noA op hu (a.eval E)]
    · simp

theorem mkAlu3_eval (hpre : Pre E st) (op : ThreeRegOp) (a b d : SVal) :
    (mkAlu3 st op a b d).eval E = threeRegAlu op (a.eval E) (b.eval E) (d.eval E) := by
  have hf : (foldAlu3 op a b (if usesD op then d else .const 0)).eval E =
      threeRegAlu op (a.eval E) (b.eval E) (d.eval E) := by
    rw [foldAlu3_eval]
    cases hu : usesD op
    · simp only [Bool.false_eq_true, ite_false, SVal.eval]; rw [alu3_noD op hu _ _ (d.eval E)]
    · simp
  unfold mkAlu3
  dsimp only
  split
  · rename_i q
    rw [addv_eval hpre _ _ _ (by rw [hf]; rfl)]; rfl
  · rename_i q
    split
    · rename_i hq
      rw [addv_eval hpre _ _ _ (by rw [hf]; simp only [threeRegAlu, SVal.eval]; congr 1; omega)]
      simp only [threeRegAlu, SVal.eval]
      congr 1; omega
    · exact hf
  · exact hf

theorem mkAlu2_eval (op : TwoRegOp) (a : SVal) :
    (mkAlu2 op a).eval E = twoRegAlu op (a.eval E) := by
  unfold mkAlu2; split <;> rfl

theorem u64_signed_small {k x : Nat} (hk : 0 < k) (hk8 : k ≤ 8) (hx : x < 2 ^ (8 * k - 1)) :
    u64 (signed k x) = x := by
  have h1 : 2 ^ (8 * k - 1) ≤ 2 ^ 63 := Nat.pow_le_pow_right (by omega) (by omega)
  simp only [u64, unsigned, signed, hx, ↓reduceIte]
  have h2 : (x : Int) < 2 ^ (8 * 8) := by
    have : x < 2 ^ 64 := by omega
    exact_mod_cast this
  rw [Int.add_comm, Int.add_emod_right, Int.emod_eq_of_lt (by omega) h2]
  simp

theorem mkSx_eval (hpre : Pre E st) (k : Nat) (v : SVal) :
    (mkSx st k v).eval E = if k = 0 then v.eval E else u64 (signed k (v.eval E)) := by
  unfold mkSx
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, ite_false]
    split
    · rfl
    · split
      · rename_i b hb
        split
        · rename_i hc
          exact (u64_signed_small (by omega) hc.2
            (Nat.lt_of_lt_of_le (bnd_sound hpre _ _ hb) hc.1)).symm
        · rfl
      · rfl

/-! ## Registers -/

theorem rdv_eval (hpre : Pre E st) {σ : SState} {ω : Regs}
    (hr : ∀ r : Fin 13, ω.get r = UInt64.ofNat ((σ.regs.getD r.val (.const 0)).eval E))
    (r : Fin 13) : (rdv st σ r.val).eval E = (ω.get r).toNat := by
  rw [rdv, mkMod_eval hpre, hr r]
  simp

theorem setv_inv {σ : SState} {ω : Regs} {μ : Memory} (h : Inv E σ ω μ) (r : Fin 13) (v : SVal) :
    Inv E (setv σ r.val v) (ω.set r (UInt64.ofNat (v.eval E))) μ := by
  obtain ⟨hl, hr, hc, hf, hp⟩ := h
  refine ⟨by simp [setv, hl], ?_, hc, hf, hp⟩
  intro j
  simp only [Regs.get, setv, Fin.getElem_fin, Vector.getElem_set]
  by_cases hj : r.val = j.val
  · rw [ite_eq_left hj, ← hj]
    simp [List.getD_eq_getElem?_getD, hl, r.isLt]
  · rw [ite_eq_right hj]
    have := hr j
    simp only [Regs.get, Fin.getElem_fin] at this
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne hj]

/-! ## Memory -/

theorem memEx_none {μ : Memory} {r w : List Nat} (hr : ∀ i ∈ r, μ.readable (i % two32) = true)
    (hw : ∀ i ∈ w, μ.writable (i % two32) = true) : memoryException μ r w = none := by
  unfold memoryException
  have h1 : r.filter (fun i => !μ.readable (i % two32)) = [] := by
    rw [List.filter_eq_nil_iff]; intro i hi; simp [hr i hi]
  have h2 : w.filter (fun i => !μ.writable (i % two32)) = [] := by
    rw [List.filter_eq_nil_iff]; intro i hi; simp [hw i hi]
  simp only [h1, h2, List.append_nil]
  rfl

theorem indices_mod {A n : Nat} (h : A % two32 + n ≤ two32) :
    ∀ i ∈ indices A n, ∃ k, k < n ∧ i % two32 = A % two32 + k := by
  intro i hi
  simp only [indices, List.mem_map, List.mem_range] at hi
  obtain ⟨k, hk, rfl⟩ := hi
  refine ⟨k, hk, ?_⟩
  rw [Nat.add_mod, Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem readable_pages {μ μ' : Memory} (h : μ.pages = μ'.pages) (a : Nat) :
    μ.readable a = μ'.readable a := by simp [Memory.readable, h]

theorem writable_pages {μ μ' : Memory} (h : μ.pages = μ'.pages) (a : Nat) :
    μ.writable a = μ'.writable a := by simp [Memory.writable, h]

theorem readN_mod (μ : Memory) (A n : Nat) : μ.readN A n = μ.readN (A % two32) n := by
  by_cases h : two32 ≤ A
  · exact Memory.readN_wrap μ A n h
  · rw [Nat.mod_eq_of_lt (by omega)]

/-- Octets read inside a cell. -/
theorem readN_inside {μ : Memory} {c m v a n : Nat} (h : μ.readN c m = encodeLE m v)
    (h1 : c ≤ a) (h2 : a + n ≤ c + m) : μ.readN a n = encodeLE n (v / 256 ^ (a - c)) := by
  apply List.ext_getElem
  · simp
  · intro i hi1 hi2
    simp only [Memory.length_readN] at hi1
    have hr : (μ.readN c m)[a - c + i]'(by simp; omega) = μ.read (a + i) := by
      simp only [Memory.readN, List.getElem_map, List.getElem_range]
      congr 1; omega
    have hr' : (μ.readN a n)[i] = μ.read (a + i) := by
      simp only [Memory.readN, List.getElem_map, List.getElem_range]
    rw [hr', ← hr]
    simp only [h, Num.getElem_encodeLE]
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]

/-- A read of octets none of which a write touches. -/
theorem readN_writeN_apart (μ : Memory) (A : Nat) (bs : List UInt8) (C m : Nat)
    (h : ∀ t, C ≤ t → t < C + m → t + 1 ≤ A ∨ A + bs.length ≤ t) (hA : A + bs.length ≤ two32)
    (hC : C + m ≤ two32) : (μ.writeN A bs).readN C m = μ.readN C m := by
  apply Memory.readN_congr
  intro j hj
  rcases h (C + j) (by omega) (by omega) with h1 | h1
  · exact Memory.read_writeN_disjoint _ _ _ _ (Or.inr h1) hA (by omega)
  · exact Memory.read_writeN_disjoint _ _ _ _ (Or.inl h1) hA (by omega)

theorem mkAddr_sound (hpre : Pre E st) {v : SVal} {x n : Nat} {a : Aff}
    (h : mkAddr st v x n = some a) :
    (v.eval E + x) % two32 = (a.eval E).toNat ∧ 0 ≤ a.eval E ∧ a.eval E + n ≤ two32 := by
  unfold mkAddr at h
  dsimp only at h
  split at h
  · rename_i a' ha'
    split at h
    · rename_i hv
      cases h
      obtain ⟨h1, h2, -⟩ := valid_sound hpre hv
      refine ⟨?_, h1, h2⟩
      split at ha'
      · rename_i c
        cases ha'
        simp only [SVal.eval, Aff.eval, Int.zero_add, Int.toNat_natCast]
      · cases hb : asAff v with
        | none => rw [hb] at ha'; cases ha'
        | some b =>
          rw [hb] at ha'; simp only [Option.bind] at ha'
          obtain ⟨e1, -, -, -, hlo⟩ := addAff_sound hpre (by decide) ha'
          have := asAff_sound hb hlo hpre
          rw [← e1]; congr 2; omega
    · cases h
  · cases h

theorem cellsT {μ : Memory} {cells : List (Aff × Nat × SVal)}
    (hc : ∀ c ∈ cells, 0 ≤ c.1.eval E ∧ c.1.eval E + c.2.1 ≤ two32 ∧
      μ.readN (c.1.eval E).toNat c.2.1 = encodeLE c.2.1 (c.2.2.eval E)) :
    ∀ fuel (a : Aff) n w, assemble cells fuel a n = some w → 0 ≤ a.eval E →
      μ.readN (a.eval E).toNat n = encodeLE n w := by
  intro fuel
  induction fuel with
  | zero =>
    intro a n w h _
    simp only [assemble] at h
    split at h
    · subst_vars; rfl
    · cases h
  | succ fuel ih =>
    intro a n w h ha0
    simp only [assemble] at h
    split at h
    · subst_vars; rfl
    rename_i hn
    split at h
    · rename_i c m v hf
      cases hr : assemble cells fuel ⟨a.base, a.off + (min (c.off + m - a.off).toNat n : Nat)⟩
          (n - min (c.off + m - a.off).toNat n)
      · rw [hr] at h; cases h
      · rw [hr] at h; cases h
        rename_i r
        have hm := List.mem_of_find?_eq_some hf
        have hp := List.find?_some hf
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
        obtain ⟨⟨⟨hb, ho1⟩, ho2⟩, -⟩ := hp
        obtain ⟨hc0, hc1, hcell⟩ := hc _ hm
        dsimp only at hc0 hc1 hcell
        simp only [SVal.eval] at hcell
        have hs := eval_sub (E := E) hb
        have hk : 0 < min (c.off + m - a.off).toNat n := by omega
        generalize hK : min (c.off + m - a.off).toNat n = k at hk hr ⊢
        have hkn : k ≤ n := by omega
        have hkm : (a.eval E).toNat + k ≤ (c.eval E).toNat + m := by omega
        have h1 := readN_inside hcell (by omega) hkm
        have he : (Aff.eval E ⟨a.base, a.off + (k : Int)⟩) = a.eval E + k := by
          have := eval_sub (E := E) (a := ⟨a.base, a.off + (k : Int)⟩) (b := a) rfl
          simp only at this; omega
        have h2 := ih _ _ _ hr (by omega)
        rw [he, show (a.eval E + k).toNat = (a.eval E).toNat + k by omega] at h2
        have hlo : v / 256 ^ (a.off - c.off).toNat % 256 ^ k < 256 ^ k :=
          Nat.mod_lt _ (Nat.pow_pos (by omega))
        have hpos : 0 < 256 ^ k := Nat.pow_pos (by omega)
        rw [show (a.eval E).toNat - (c.eval E).toNat = (a.off - c.off).toNat by omega] at h1
        rw [show n = k + (n - k) by omega, Memory.readN_split, h1, h2, Num.encodeLE_split]
        congr 1
        · rw [← encodeLE_mod k (v / 256 ^ (a.off - c.off).toNat),
            ← encodeLE_mod k (v / 256 ^ (a.off - c.off).toNat % 256 ^ k + 256 ^ k * r),
            Nat.add_mul_mod_self_left, Nat.mod_mod]
        · rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hlo, Nat.zero_add]
    · cases h

theorem frags_sound {μ : Memory} {a : Aff} {n : Nat} {c : Aff × Nat × SVal}
    (hc : 0 ≤ c.1.eval E ∧ c.1.eval E + c.2.1 ≤ two32 ∧
      μ.readN (c.1.eval E).toNat c.2.1 = encodeLE c.2.1 (c.2.2.eval E)) :
    ∀ f ∈ frags a n c, (0 ≤ f.1.eval E ∧ f.1.eval E + f.2.1 ≤ two32 ∧
      μ.readN (f.1.eval E).toNat f.2.1 = encodeLE f.2.1 (f.2.2.eval E)) ∧
      ∀ t, InReg E (f.1, f.2.1) t → ¬ InReg E (a, n) t := by
  intro f hf
  obtain ⟨c, m, v⟩ := c
  cases v with
  | const v =>
    simp only [frags] at hf
    obtain ⟨hc0, hc1, hcell⟩ := hc
    simp only [SVal.eval] at hcell hc0 hc1
    split at hf
    · rename_i hb
      simp only [beq_iff_eq] at hb
      have hs := eval_sub (E := E) hb
      rcases List.mem_append.1 hf with hf | hf
      · split at hf
        · simp only [List.mem_singleton] at hf; subst hf
          simp only [InReg]
          refine ⟨⟨hc0, by omega, ?_⟩, fun t h1 h2 => by omega⟩
          have := readN_inside hcell (Nat.le_refl _)
            (show (c.eval E).toNat + (min (a.off - c.off) m).toNat ≤ (c.eval E).toNat + m by omega)
          simp only [Nat.sub_self, Nat.pow_zero, Nat.div_one] at this
          simpa [SVal.eval] using this
        · cases hf
      · split at hf
        · simp only [List.mem_singleton] at hf; subst hf
          simp only [InReg]
          have he : Aff.eval E ⟨a.base, max (a.off + n) c.off⟩ = c.eval E + (max (a.off + n) c.off - c.off) := by
            have := eval_sub (E := E) (a := ⟨a.base, max (a.off + n) c.off⟩) (b := c) hb.symm
            simp only at this; omega
          refine ⟨⟨by omega, by omega, ?_⟩, fun t h1 h2 => by omega⟩
          have := readN_inside hcell
            (a := (Aff.eval E ⟨a.base, max (a.off + n) c.off⟩).toNat)
            (n := (c.off + m - max (a.off + n) c.off).toNat) (by omega) (by omega)
          rw [show (Aff.eval E ⟨a.base, max (a.off + n) c.off⟩).toNat - (c.eval E).toNat =
            (max (a.off + n) c.off - c.off).toNat by omega] at this
          simpa [SVal.eval] using this
        · cases hf
    · cases hf
  | _ => simp [frags] at hf

/-- What `loadVal` returns is what the octets at the address decode to. -/
theorem loadVal_sound (hpre : Pre E st) {σ : SState} {ω : Regs} {μ : Memory} (h : Inv E σ ω μ)
    {a : Aff} {n : Nat} (ha0 : 0 ≤ a.eval E) (han : a.eval E + n ≤ two32) {v : SVal}
    (hv : loadVal st σ a n = some v) : v.eval E = decodeLE (μ.readN (a.eval E).toNat n) := by
  obtain ⟨_, _, hc, hf, _⟩ := h
  unfold loadVal at hv
  split at hv
  · rename_i c hfc
    cases hv
    have hm := List.mem_of_find?_eq_some hfc
    have hp := List.find?_some hfc
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨h1, h2⟩ := hp
    rw [mkMod_eval hpre, ← h1, ← h2, (hc c hm).2.2, decodeLE_encodeLE]
  · split at hv
    · rename_i w hw
      cases hv
      rw [cellsT hc _ _ _ _ hw ha0, decodeLE_encodeLE, pow8]
      rfl
    split at hv
    · cases hv
      rename_i hcl
      simp only [SVal.eval]
      congr 1
      apply Memory.readN_congr
      intro j hj
      refine (hf ((a.eval E).toNat + j) (by omega) ?_).symm
      intro d hd hin
      have := List.all_eq_true.1 hcl d hd
      exact disj_sound hpre this _ (by simp only [InReg]; omega) hin
    · cases hv

/-- A store `sstore` allows: the octets are writable, and the new state is described. -/
theorem sstore_sound (hpre : Pre E st) {σ σ' : SState} {ω : Regs} {μ : Memory} (h : Inv E σ ω μ)
    {a : Aff} {A n : Nat} {v : SVal} (hA : A % two32 = (a.eval E).toNat)
    (hs : sstore st σ a n v = some σ') :
    (∀ i ∈ indices A n, μ.writable (i % two32) = true) ∧
      Inv E σ' ω (μ.writeN A (encodeLE n (v.eval E))) := by
  obtain ⟨hl, hr, hc, hf, hp⟩ := h
  unfold sstore at hs
  split at hs
  · rename_i hok
    cases hs
    simp only [Bool.and_eq_true, List.any_eq_true] at hok
    obtain ⟨hval, rg, hrg, hw⟩ := hok
    obtain ⟨ha0, han, hlt'⟩ := valid_sound hpre hval
    have hlt : (a.eval E).toNat < two32 := by omega
    have hwA : μ.writeN A (encodeLE n (v.eval E)) =
        μ.writeN (a.eval E).toNat (encodeLE n (v.eval E)) :=
      Memory.writeN_congr _ _ _ _ (by rw [hA, Nat.mod_eq_of_lt hlt])
    have hlen : (a.eval E).toNat + (encodeLE n (v.eval E)).length ≤ two32 := by
      simp only [Num.length_encodeLE]; omega
    refine ⟨?_, hl, hr, ?_, ?_, ?_⟩
    · intro i hi
      obtain ⟨k, hk, hik⟩ := indices_mod (by omega) i hi
      rw [hik, writable_pages hp]
      exact hpre.2.2.2.1 rg hrg _ (within_sound hpre hw _ (by simp only [InReg]; omega))
    · intro c hcm
      rw [hwA]
      rcases List.mem_cons.1 hcm with rfl | hcm
      · exact ⟨ha0, han, Memory.readN_writeN_same _ _ _ _ (Num.length_encodeLE _ _)
          (by show n ≤ two32; omega)⟩
      · rcases List.mem_append.1 hcm with hcm | hcm
        · rw [List.mem_filter] at hcm
          obtain ⟨hcm, hcd⟩ := hcm
          obtain ⟨h0, h1, h2⟩ := hc c hcm
          refine ⟨h0, h1, ?_⟩
          rw [readN_writeN_apart _ _ _ _ _ ?_ hlen (by omega)]
          · exact h2
          · intro t ht1 ht2
            have := disj_sound hpre hcd t (by simp only [InReg]; omega)
            simp only [InReg, not_and, Num.length_encodeLE] at this ⊢
            omega
        · obtain ⟨c', hc'm, hfm⟩ := List.mem_flatMap.1 hcm
          rw [List.mem_filter] at hc'm
          obtain ⟨⟨h0, h1, h2⟩, hfd⟩ := frags_sound (hc c' hc'm.1) c hfm
          refine ⟨h0, h1, ?_⟩
          rw [readN_writeN_apart _ _ _ _ _ ?_ hlen (by omega)]
          · exact h2
          · intro t ht1 ht2
            have := hfd t (by simp only [InReg]; omega)
            simp only [InReg, not_and, Num.length_encodeLE] at this ⊢
            omega
    · intro t ht hcl
      have hout : ¬ InReg E (a, n) t := by
        split at hcl
        · rename_i hin
          obtain ⟨d, hd, hwd⟩ := List.any_eq_true.1 hin
          exact fun h' => hcl d hd (within_sound hpre hwd t h')
        · exact hcl _ (List.mem_cons_self ..)
      have hold : ∀ d ∈ σ.dirty, ¬ InReg E d t := by
        split at hcl
        · exact hcl
        · exact fun d hd => hcl d (List.mem_cons_of_mem _ hd)
      simp only [InReg, not_and, Int.not_lt] at hout
      rw [hwA, Memory.read_writeN_disjoint _ _ _ _ (by simp only [Num.length_encodeLE]; omega)
        hlen (by omega)]
      exact hf t ht hold
    · simp [hp]
  · cases hs

/-- A load `sload` allows: the octets are readable, and the new state is described. -/
theorem sload_sound (hpre : Pre E st) {σ σ' : SState} {ω : Regs} {μ : Memory} (hinv : Inv E σ ω μ)
    {d : Fin 13} {a : Aff} {A n k : Nat} (hA : A % two32 = (a.eval E).toNat)
    (hl : sload st σ d.val a n k = some σ') :
    memoryException μ (indices A n) [] = none ∧
      Inv E σ' (ω.set d (UInt64.ofNat (if k = 0 then decodeLE (μ.readN A n) else
        u64 (signed k (decodeLE (μ.readN A n)))))) μ := by
  unfold sload at hl
  split at hl
  · rename_i hok
    simp only [Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true] at hok
    obtain ⟨hval, hrw⟩ := hok
    obtain ⟨ha0, han, -⟩ := valid_sound hpre hval
    cases hv : loadVal st σ a n
    · rw [hv] at hl; cases hl
    · rw [hv] at hl; cases hl
      rename_i v
      have hval' := loadVal_sound hpre hinv ha0 han hv
      rw [← hA, ← readN_mod] at hval'
      refine ⟨memEx_none ?_ (by simp), ?_⟩
      · intro i hi
        obtain ⟨j, hj, hij⟩ := indices_mod (by omega) i hi
        rw [hij, readable_pages hinv.2.2.2.2]
        have hin : InReg E (a, n) (A % two32 + j) := by simp only [InReg]; omega
        rcases hrw with ⟨rg, hrg, hw⟩ | ⟨rg, hrg, hw⟩
        · exact hpre.2.2.1 rg hrg _ (within_sound hpre hw _ hin)
        · exact Memory.readable_of_writable (hpre.2.2.2.1 rg hrg _ (within_sound hpre hw _ hin))
      · have := setv_inv hinv d (mkSx st k v)
        rwa [mkSx_eval hpre, hval'] at this
  · cases hl
/-! ## Code -/

theorem NTree.all_find {α : Type} {Q : Nat → α → Prop} :
    ∀ {t : NTree α}, t.All Q → ∀ k v, t.find k = some v → Q k v
  | .leaf, _, _, _, h => by simp [NTree.find] at h
  | .node l k' v' r, ⟨he, hl, hr⟩, k, v, h => by
    simp only [NTree.find] at h
    split at h
    · exact NTree.all_find hl k v h
    · split at h
      · cases h; rename_i hk; subst hk; exact he
      · exact NTree.all_find hr k v h

theorem isBS_sound {P : Program} {bs : NTree Bool} (hb : bs.All (fun n b => P.isBlockStart n = b))
    (n : Nat) (h : isBS bs n = true) : P.isBlockStart n = true := by
  simp only [isBS, beq_iff_eq] at h
  exact NTree.all_find hb n true h

/-! ## Steps -/

/-- How one step ends, given its mutation. -/
theorem finish {p : ByteArray} {P : Program} {pc : Nat} {ins : Instr} {nx : Nat} {ω : Regs}
    {μ : Memory} {σ' : SState}
    (hd : deblob p pc = some P ∧ P.decode pc = some ins ∧ P.next pc = nx ∧
      P.blockCost (P.blockStartOf pc) ≤ stepCostCap)
    (m : Mutation) (hm : P.exec pc ins ω μ = m) (hs : m.status = .cont)
    (hx : memoryException μ m.reads m.writes = none) (hinv : Inv E σ' m.regs m.mem) :
    FreeNext p pc ω μ m.pc m.regs m.mem ∧ CostOk p pc ∧ Inv E σ' m.regs m.mem := by
  refine ⟨⟨P, hd.1, ?_⟩, .of hd.1 hd.2.2.2, hinv⟩
  rw [Program.freeStep_of_decode ω μ hd.2.1]
  simp only [hm, Program.finalState, hx, hs]
  rfl

theorem exec_twoRegImm (P : Program) (i : Nat) (op : TwoRegImmOp) (a b : RegIdx) (x : UInt64)
    (ω : Regs) (μ : Memory) :
    P.exec i (.twoRegImm op a b x) ω μ =
      match tkind op with
      | .alu => { status := .cont, pc := P.next i, mem := μ,
                  regs := ω.set a (UInt64.ofNat
                    ((twoRegImmAlu op (ω.get a).toNat (ω.get b).toNat x.toNat).getD 0)) }
      | .store n => { status := .cont, pc := P.next i, regs := ω,
                      mem := μ.writeN ((ω.get b).toNat + x.toNat)
                        (encodeLE n ((ω.get a).toNat % 2 ^ (8 * n))),
                      writes := indices ((ω.get b).toNat + x.toNat) n }
      | .load n k => { status := .cont, pc := P.next i, mem := μ,
                       regs := ω.set a (UInt64.ofNat (if k = 0 then
                         decodeLE (μ.readN ((ω.get b).toNat + x.toNat) n) else
                         u64 (signed k (decodeLE (μ.readN ((ω.get b).toNat + x.toNat) n))))),
                       reads := indices ((ω.get b).toNat + x.toNat) n } := by
  cases op
  case storeIndU64 =>
    simp only [tkind]
    rw [show (ω.get a).toNat % 2 ^ (8 * 8) = (ω.get a).toNat from
      Nat.mod_eq_of_lt (UInt64.toNat_lt _)]
    rfl
  all_goals rfl

theorem exec_regImm (P : Program) (i : Nat) (op : RegImmOp) (a : RegIdx) (x : UInt64)
    (ω : Regs) (μ : Memory) :
    P.exec i (.regImm op a x) ω μ =
      match rkind op with
      | .store n => { status := .cont, pc := P.next i, regs := ω,
                      mem := μ.writeN x.toNat (encodeLE n ((ω.get a).toNat % 2 ^ (8 * n))),
                      writes := indices x.toNat n }
      | .load n _ => { status := .cont, pc := P.next i, mem := μ,
                       regs := ω.set a (UInt64.ofNat (decodeLE (μ.readN x.toNat n))),
                       reads := indices x.toNat n }
      | .alu => P.exec i (.regImm op a x) ω μ := by
  cases op
  case storeU64 =>
    simp only [rkind]
    rw [show (ω.get a).toNat % 2 ^ (8 * 8) = (ω.get a).toNat from
      Nat.mod_eq_of_lt (UInt64.toNat_lt _)]
    rfl
  all_goals rfl

theorem exec_regImmOffset (P : Program) (i : Nat) (op : RegImmOffsetOp) (a : RegIdx) (x : UInt64)
    (y : Int) (ω : Regs) (μ : Memory) (hop : op ≠ .loadImmJump) :
    P.exec i (.regImmOffset op a x y) ω μ =
      { status := (P.branch i y (regImmBranchCond op (ω.get a).toNat x.toNat)).1,
        pc := (P.branch i y (regImmBranchCond op (ω.get a).toNat x.toNat)).2,
        regs := ω, mem := μ } := by
  cases op <;> first | rfl | exact absurd rfl hop

theorem branch_eq {P : Program} {i : Nat} {y : Int} {c : Bool} (hy : 0 ≤ y)
    (h1 : P.isBlockStart y.toNat = true) (h2 : P.isBlockStart (P.next i) = true) :
    P.branch i y c = (.cont, if c then y.toNat else P.next i) := by
  have : P.isBlockStartInt y = true := by
    simp only [Program.isBlockStartInt, h1]; split <;> simp_all; omega
  unfold Program.branch
  rw [this, h2]
  cases c <;> rfl

theorem sjump_eq {P : Program} {i : Nat} {y : Int} (hy : 0 ≤ y)
    (h1 : P.isBlockStart y.toNat = true) : P.sjump i y = (.cont, y.toNat) := by
  have : P.isBlockStartInt y = true := by
    simp only [Program.isBlockStartInt, h1]; split <;> simp_all; omega
  simp [Program.sjump, this]

theorem sdjump_sound {p : ByteArray} {P : Program} {G : Prog} (hG : ProgHyp p P G) {i a t : Nat}
    (h : sdjump G a = some t) : P.djump i a = (.cont, t) := by
  obtain ⟨_, hbs, hjt, hsz⟩ := hG
  unfold sdjump at h
  split at h
  · cases h
  rename_i hc
  split at h
  · rename_i t' hl
    split at h
    · cases h
      rename_i hb
      have h1 := NTree.all_find hjt _ _ hl
      have h2 := isBS_sound hbs _ hb
      unfold Program.djump
      rw [ite_eq_right (by omega), ite_eq_right (by rw [hsz]; omega)]
      simp [h1, h2]
    · cases h
  · cases h

/-- A store through `mkAddr`: the octets at rb + x are writable, and the new state is described. -/
theorem memStore (hpre : Pre E st) {σ σ' : SState} {ω : Regs} {μ : Memory} (hinv : Inv E σ ω μ)
    {v w : SVal} {x n rb : Nat} (hv : v.eval E = rb)
    (h : ((mkAddr st v x n).bind fun ad => sstore st σ ad n w) = some σ') :
    (∀ i ∈ indices (rb + x) n, μ.writable (i % two32) = true) ∧
      Inv E σ' ω (μ.writeN (rb + x) (encodeLE n (w.eval E))) := by
  cases ha : mkAddr st v x n with
  | none => rw [ha] at h; cases h
  | some ad =>
    rw [ha] at h
    obtain ⟨h1, -, -⟩ := mkAddr_sound hpre ha
    rw [hv] at h1
    exact sstore_sound hpre hinv h1 h

/-- A load through `mkAddr`: the octets at rb + x are readable, and the new state is described. -/
theorem memLoad (hpre : Pre E st) {σ σ' : SState} {ω : Regs} {μ : Memory} (hinv : Inv E σ ω μ)
    {v : SVal} {d : Fin 13} {x n k rb : Nat} (hv : v.eval E = rb)
    (h : ((mkAddr st v x n).bind fun ad => sload st σ d.val ad n k) = some σ') :
    memoryException μ (indices (rb + x) n) [] = none ∧
      Inv E σ' (ω.set d (UInt64.ofNat (if k = 0 then decodeLE (μ.readN (rb + x) n) else
        u64 (signed k (decodeLE (μ.readN (rb + x) n)))))) μ := by
  cases ha : mkAddr st v x n with
  | none => rw [ha] at h; cases h
  | some ad =>
    rw [ha] at h
    obtain ⟨h1, -, -⟩ := mkAddr_sound hpre ha
    rw [hv] at h1
    exact sload_sound hpre hinv h1 h

theorem map_pair {α : Type} {o : Option α} {n : Nat} {pc : Nat} {s : α}
    (h : o.map (fun (x : α) => ((n, x) : Nat × α)) = some (pc, s)) : o = some s ∧ pc = n := by
  cases o with
  | none => cases h
  | some v => simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at h; exact ⟨by rw [h.2], h.1.symm⟩

theorem sstep_sound {p : ByteArray} {P : Program} {G : Prog}
    (hG : ProgHyp p P G) (hpre : Pre E st)
    {pc pc' : Nat} {σ σ' : SState} {ω : Regs} {μ : Memory} (hinv : Inv E σ ω μ)
    (h : sstep st G pc σ = some (pc', σ')) :
    ∃ ω' μ', FreeNext p pc ω μ pc' ω' μ' ∧ CostOk p pc ∧ Inv E σ' ω' μ' := by
  have hrd := rdv_eval (st := st) hpre hinv.2.1
  unfold sstep at h
  split at h
  · cases h
  rename_i e hfe
  have hbs := hG.2.1
  obtain ⟨hd1, hd2, hd3, hd4⟩ := NTree.all_find hG.1 pc e hfe
  -- the step through the mutation `m`, landing at `m.pc`
  have go : ∀ (m : Mutation), P.exec pc e.1 ω μ = m → m.status = .cont →
      memoryException μ m.reads m.writes = none → Inv E σ' m.regs m.mem → m.pc = pc' →
      ∃ ω' μ', FreeNext p pc ω μ pc' ω' μ' ∧ CostOk p pc ∧ Inv E σ' ω' μ' := by
    intro m hm hs hx hi hmpc
    subst hmpc
    exact ⟨_, _, finish ⟨hd1, hd2, hd3, hd4⟩ m hm hs hx hi⟩
  split at h
  · -- unlikely
    rename_i hins; cases h
    exact go { status := .cont, pc := P.next pc, regs := ω, mem := μ } (by rw [hins]; try rfl)
      rfl rfl hinv hd3
  · -- fallthrough
    rename_i hins; split at h
    · cases h
      rename_i hb
      have hj := sjump_eq (P := P) (i := pc) (y := ((P.next pc : Nat) : Int)) (by omega)
        (by rw [Int.toNat_natCast, hd3]; exact isBS_sound hbs _ hb)
      refine go { status := .cont, pc := (P.next pc : Int).toNat, regs := ω, mem := μ }
        ?_ rfl rfl hinv (by simp [hd3])
      rw [hins]; simp only [Program.exec, hj]
    · cases h
  · -- jump
    rename_i x hins; split at h
    · cases h
      rename_i hb
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      have hj := sjump_eq (P := P) (i := pc) hb.1 (isBS_sound hbs _ hb.2)
      refine go { status := .cont, pc := x.toNat, regs := ω, mem := μ } ?_ rfl rfl hinv rfl
      rw [hins]; simp only [Program.exec, hj]
    · cases h
  · -- load_imm
    rename_i a x hins; cases h
    exact go _ (by rw [hins]; try rfl) rfl rfl (setv_inv hinv a (.const x.toNat)) hd3
  · -- jump_ind
    rename_i a x hins
    split at h
    · rename_i v hv
      cases hj : sdjump G ((v + x.toNat) % two32)
      · rw [hj] at h; cases h
      · rw [hj] at h; cases h
        have hav := hrd a
        rw [hv] at hav; simp only [SVal.eval] at hav
        have hd := sdjump_sound (i := pc) hG hj
        rw [hav] at hd
        refine go { status := .cont
                    pc := pc'
                    regs := ω
                    mem := μ } ?_ rfl rfl hinv rfl
        rw [hins]; simp only [Program.exec, hd]
    · cases h
  · -- absolute loads and stores
    rename_i op a x hnl hnj hins
    have hx := exec_regImm P pc op a x ω μ
    rw [← hins] at hx
    split at h
    · rename_i n hk; rw [hk] at hx
      obtain ⟨hs, rfl⟩ := map_pair h
      obtain ⟨hw, hi⟩ := memStore hpre hinv (rb := 0) rfl hs
      rw [mkMod_eval hpre, hrd, Nat.zero_add] at hi
      rw [Nat.zero_add] at hw
      exact go _ hx rfl (memEx_none (by simp) hw) hi hd3
    · rename_i n k hk; rw [hk] at hx
      obtain ⟨hs, rfl⟩ := map_pair h
      obtain ⟨hx2, hi⟩ := memLoad hpre hinv (rb := 0) rfl hs
      simp only [ite_true, Nat.zero_add] at hi hx2
      exact go _ hx rfl hx2 hi hd3
    · cases h
  · -- load_imm_64
    rename_i a x hins; cases h
    exact go _ (by rw [hins]; try rfl) rfl rfl (setv_inv hinv a (.const x.toNat)) hd3
  · -- store of an immediate at an immediate address
    rename_i op x y hins
    obtain ⟨hs, rfl⟩ := map_pair h
    obtain ⟨hw, hi⟩ := memStore hpre hinv (rb := 0) rfl hs
    rw [Nat.zero_add] at hw hi
    refine go { status := .cont
                pc := P.next pc
                regs := ω
                mem := μ.writeN x.toNat
                  (encodeLE op.width (SVal.eval E (.const (y.toNat % 2 ^ (8 * op.width)))))
                writes := indices x.toNat op.width }
      (by rw [hins]; try rfl) rfl ?_ hi hd3
    exact memEx_none (by simp) hw
  · -- two registers
    rename_i op d a hins; cases h
    refine go _ (by rw [hins]; try rfl) rfl rfl ?_ hd3
    have := setv_inv hinv d (mkAlu2 op (rdv st σ a.val))
    rwa [mkAlu2_eval, hrd] at this
  · -- three registers
    rename_i op a b d hins; cases h
    refine go _ (by rw [hins]; try rfl) rfl rfl ?_ hd3
    have := setv_inv hinv d (mkAlu3 st op (rdv st σ a.val) (rdv st σ b.val) (rdv st σ d.val))
    rwa [mkAlu3_eval hpre, hrd, hrd, hrd] at this
  · -- two registers and an immediate
    rename_i op a b x hins
    have hx := exec_twoRegImm P pc op a b x ω μ
    rw [← hins] at hx
    split at h
    · rename_i hk; rw [hk] at hx; cases h
      refine go _ hx rfl rfl ?_ hd3
      have := setv_inv hinv a (mkAlu2i st op (rdv st σ a.val) (rdv st σ b.val) x.toNat)
      rwa [mkAlu2i_eval hpre, hrd, hrd] at this
    · rename_i n hk; rw [hk] at hx
      obtain ⟨hs, rfl⟩ := map_pair h
      obtain ⟨hw, hi⟩ := memStore hpre hinv (hrd b) hs
      rw [mkMod_eval hpre, hrd] at hi
      exact go _ hx rfl (memEx_none (by simp) hw) hi hd3
    · rename_i n k hk; rw [hk] at hx
      obtain ⟨hs, rfl⟩ := map_pair h
      obtain ⟨hx2, hi⟩ := memLoad hpre hinv (hrd b) hs
      exact go _ hx rfl hx2 hi hd3
  · -- store of an immediate
    rename_i op a x y hins
    obtain ⟨hs, rfl⟩ := map_pair h
    obtain ⟨hw, hi⟩ := memStore hpre hinv (hrd a) hs
    refine go { status := .cont
                pc := P.next pc
                regs := ω
                mem := μ.writeN ((ω.get a).toNat + x.toNat)
                  (encodeLE op.width (SVal.eval E (.const (y.toNat % 2 ^ (8 * op.width)))))
                writes := indices ((ω.get a).toNat + x.toNat) op.width }
      (by rw [hins]; try rfl) rfl ?_ hi hd3
    exact memEx_none (by simp) hw
  · -- branches against an immediate, and load_imm_jump
    rename_i op a x y hins
    split at h
    · rename_i hop; subst hop
      split at h
      · cases h
        rename_i hb
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
        have hj := sjump_eq (P := P) (i := pc) hb.1 (isBS_sound hbs _ hb.2)
        refine go _ (by rw [hins]; try rfl) ?_ rfl (setv_inv hinv a (.const x.toNat)) ?_ <;>
          simp [Program.exec, hj]
      · cases h
    · rename_i hop
      split at h
      · rename_i v hv
        split at h
        · cases h
          rename_i hb
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
          have hav := hrd a
          rw [hv] at hav; simp only [SVal.eval] at hav
          have hbr := branch_eq (P := P) (i := pc) (c := regImmBranchCond op v x.toNat) hb.1.1
            (isBS_sound hbs _ hb.1.2) (by rw [hd3]; exact isBS_sound hbs _ hb.2)
          have hx := exec_regImmOffset P pc op a x y ω μ hop
          rw [← hins, ← hav] at hx
          refine go _ hx ?_ rfl hinv ?_ <;> simp [hbr, hd3]
        · cases h
      · cases h
  · -- load_imm_jump_ind
    rename_i a b x y hins
    split at h
    · rename_i v hv
      cases hj : sdjump G ((v + y.toNat) % two32)
      · rw [hj] at h; cases h
      · rw [hj] at h; cases h
        have hbv := hrd b
        rw [hv] at hbv; simp only [SVal.eval] at hbv
        have hd := sdjump_sound (i := pc) hG hj
        rw [hbv] at hd
        refine go { status := .cont
                    pc := pc'
                    regs := ω.set a (UInt64.ofNat (SVal.eval E (.const x.toNat)))
                    mem := μ } ?_ rfl rfl (setv_inv hinv a (.const x.toNat)) rfl
        rw [hins]; simp only [Program.exec, hd]; rfl
    · cases h
  · -- branches on two registers
    rename_i op a b x hins
    split at h
    · rename_i va vb hva hvb
      split at h
      · cases h
        rename_i hb
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
        have hav := hrd a
        rw [hva] at hav; simp only [SVal.eval] at hav
        have hbv := hrd b
        rw [hvb] at hbv; simp only [SVal.eval] at hbv
        have hbr := branch_eq (P := P) (i := pc) (c := twoRegBranchCond op va vb) hb.1.1
          (isBS_sound hbs _ hb.1.2) (by rw [hd3]; exact isBS_sound hbs _ hb.2)
        rw [hav, hbv] at hbr
        refine go { status := (P.branch pc x (twoRegBranchCond op (ω.get a).toNat (ω.get b).toNat)).1
                    pc := (P.branch pc x (twoRegBranchCond op (ω.get a).toNat (ω.get b).toNat)).2
                    regs := ω
                    mem := μ } (by rw [hins]; try rfl) ?_ rfl hinv ?_ <;> simp [hbr, hd3, hav, hbv]
      · cases h
    · cases h
  · cases h

/-- **Soundness of `srun`.** -/
theorem srun_sound {X : Type} {p : ByteArray} {R : HostRel X} {P : Program} {G : Prog}
    (hG : ProgHyp p P G) (hpre : Pre E st) {target : Nat} (x : X) :
    ∀ (k pc : Nat) (σ : SState) (ω : Regs) (μ : Memory) (σ' : SState),
      Inv E σ ω μ → srun st G target k pc σ = some σ' →
      ∃ ω' μ', FreeStepsH p R pc ω μ x target ω' μ' x k ∧ Inv E σ' ω' μ' := by
  intro k
  induction k with
  | zero =>
    intro pc σ ω μ σ' hinv h
    simp only [srun] at h
    split at h
    · cases h; rename_i hpc; subst hpc; exact ⟨ω, μ, .refl, hinv⟩
    · cases h
  | succ k ih =>
    intro pc σ ω μ σ' hinv h
    simp only [srun] at h
    split at h
    · rename_i pc₁ σ₁ hs
      obtain ⟨ω₁, μ₁, hn, hc, hi₁⟩ := sstep_sound hG hpre hinv hs
      obtain ⟨ω', μ', hrun, hi'⟩ := ih pc₁ σ₁ ω₁ μ₁ σ' hi₁ h
      exact ⟨ω', μ', .next hn hc hrun, hi'⟩
    · cases h

end PVM.SymExec
