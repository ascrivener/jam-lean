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

/-! ## Values -/

theorem pow8 (n : Nat) : 2 ^ (8 * n) = 256 ^ n := by
  rw [Nat.pow_mul]

theorem bnd_sound (hB : ∀ k b, st.bounds[k]? = some b → E.ρ k < b) :
    ∀ (v : SVal) b, v.bnd st.bounds = some b → v.eval E < b := by
  intro v b h
  cases v with
  | const n => simp only [SVal.bnd, Option.some.injEq] at h; subst h; simp [SVal.eval]
  | var k => exact hB k b h
  | reg0 r => simp only [SVal.bnd, Option.some.injEq] at h; subst h; exact UInt64.toNat_lt _
  | mem0 a n =>
    simp only [SVal.bnd, Option.some.injEq] at h; subst h
    have := decodeLE_lt (E.μ.readN a n)
    simpa [SVal.eval] using this
  | mod v m =>
    simp only [SVal.bnd] at h
    split at h
    · cases h; exact Nat.mod_lt _ ‹_›
    · cases h
  | _ => simp [SVal.bnd] at h

theorem mkMod_eval (hB : ∀ k b, st.bounds[k]? = some b → E.ρ k < b) (v : SVal) (m : Nat) :
    (mkMod st.bounds v m).eval E = v.eval E % m := by
  unfold mkMod
  split
  · rfl
  · split
    · rename_i b hb
      split
      · exact (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (bnd_sound hB _ _ hb) ‹_›)).symm
      · rfl
    · rfl

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

theorem mkAlu2i_eval (op : TwoRegImmOp) (a b : SVal) (x : Nat) :
    (mkAlu2i op a b x).eval E = (twoRegImmAlu op (a.eval E) (b.eval E) x).getD 0 := by
  have : (twoRegImmAlu op (a.eval E) (b.eval E) x) =
      twoRegImmAlu op ((if usesA op then a else .const 0).eval E) (b.eval E) x := by
    cases hu : usesA op
    · simp only [Bool.false_eq_true, ite_false, SVal.eval]; exact alu2i_noA op hu _ _ _
    · simp
  rw [this, mkAlu2i, foldAlu2i_eval]

theorem mkAlu3_eval (op : ThreeRegOp) (a b d : SVal) :
    (mkAlu3 op a b d).eval E = threeRegAlu op (a.eval E) (b.eval E) (d.eval E) := by
  have : threeRegAlu op (a.eval E) (b.eval E) (d.eval E) =
      threeRegAlu op (a.eval E) (b.eval E) ((if usesD op then d else .const 0).eval E) := by
    cases hu : usesD op
    · simp only [Bool.false_eq_true, ite_false, SVal.eval]; exact alu3_noD op hu _ _ _
    · simp
  rw [this, mkAlu3, foldAlu3_eval]

theorem mkAlu2_eval (op : TwoRegOp) (a : SVal) :
    (mkAlu2 op a).eval E = twoRegAlu op (a.eval E) := by
  unfold mkAlu2; split <;> rfl

theorem u64_signed_small {k x : Nat} (hk : 0 < k) (hk8 : k ≤ 8) (hx : x < 2 ^ (8 * k - 1)) :
    u64 (signed k x) = x := by
  have h1 : 2 ^ (8 * k - 1) ≤ 2 ^ 63 := Nat.pow_le_pow_right (by omega) (by omega)
  simp only [u64, unsigned, signed, ite_eq_left hx]
  have h2 : (x : Int) < 2 ^ (8 * 8) := by
    have : x < 2 ^ 64 := by omega
    exact_mod_cast this
  rw [Int.add_comm, Int.add_emod_right, Int.emod_eq_of_lt (by omega) h2]
  simp

theorem mkSx_eval (hB : ∀ k b, st.bounds[k]? = some b → E.ρ k < b) (k : Nat) (v : SVal) :
    (mkSx st.bounds k v).eval E = if k = 0 then v.eval E else u64 (signed k (v.eval E)) := by
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
            (Nat.lt_of_lt_of_le (bnd_sound hB _ _ hb) hc.1)).symm
        · rfl
      · rfl

/-! ## Registers -/

theorem rdv_eval (hB : ∀ k b, st.bounds[k]? = some b → E.ρ k < b) {σ : SState} {ω : Regs}
    (hr : ∀ r : Fin 13, ω.get r = UInt64.ofNat ((σ.regs.getD r.val (.const 0)).eval E))
    (r : Fin 13) : (rdv st σ r.val).eval E = (ω.get r).toNat := by
  rw [rdv, mkMod_eval hB, hr r]
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

/-! ## Code -/

theorem allCode_mem {p : ByteArray} {P : Program} :
    ∀ {code : List CEntry}, AllCode p P code → ∀ e ∈ code,
      deblob p e.pc = some P ∧ P.decode e.pc = some e.ins ∧ P.next e.pc = e.next ∧
        P.blockCost (P.blockStartOf e.pc) ≤ stepCostCap
  | [], _, e, he => by cases he
  | _ :: _, ⟨h, hs⟩, e, he => by
    rcases List.mem_cons.1 he with rfl | he
    · exact h
    · exact allCode_mem hs e he

theorem allCodeT_find {p : ByteArray} {P : Program} :
    ∀ {t : CTree}, AllCodeT p P t → ∀ pc e, t.find pc = some e →
      e.pc = pc ∧ deblob p e.pc = some P ∧ P.decode e.pc = some e.ins ∧ P.next e.pc = e.next ∧
        P.blockCost (P.blockStartOf e.pc) ≤ stepCostCap
  | .leaf, _, _, _, h => by simp [CTree.find] at h
  | .node l e' r, ⟨he, hl, hr⟩, pc, e, h => by
    simp only [CTree.find] at h
    split at h
    · exact allCodeT_find hl pc e h
    · split at h
      · cases h; rename_i hpc; exact ⟨hpc.symm, he⟩
      · exact allCodeT_find hr pc e h

theorem isBS_sound {P : Program} :
    ∀ {bs : List (Nat × Bool)}, AllBS P bs → ∀ n, isBS bs n = true → P.isBlockStart n = true
  | [], _, n, h => by simp [isBS] at h
  | b :: bs, ⟨hb, hs⟩, n, h => by
    simp only [isBS, List.any_cons, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨rfl, h2⟩ | h
    · rw [hb, h2]
    · exact isBS_sound hs n h

theorem findCode_some {code : List CEntry} {pc : Nat} {e : CEntry} (h : findCode code pc = some e) :
    e ∈ code ∧ e.pc = pc := by
  unfold findCode at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-! ## Memory -/

theorem memEx_nil (μ : Memory) : memoryException μ [] [] = none := rfl

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

theorem inR_sound {L : List (Nat × Nat)} {a n : Nat} (h : inR L a n = true) :
    ∃ r ∈ L, r.1 ≤ a ∧ a + n ≤ r.2 := by
  simp only [inR, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

theorem readN_mod (μ : Memory) (A n : Nat) : μ.readN A n = μ.readN (A % two32) n := by
  by_cases h : two32 ≤ A
  · exact Memory.readN_wrap μ A n h
  · rw [Nat.mod_eq_of_lt (by omega)]

theorem clear_mono {D : List (Nat × Nat)} {a n t : Nat} (h : clear D a n = true) (h1 : a ≤ t)
    (h2 : t < a + n) : clear D t 1 = true := by
  simp only [clear, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  intro d hd
  rcases h d hd with h | h <;> omega

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

theorem assemble_sound {E : Env} {μ : Memory} {cells : List (Nat × Nat × SVal)}
    (hc : ∀ c ∈ cells, μ.readN c.1 c.2.1 = encodeLE c.2.1 (c.2.2.eval E)) :
    ∀ fuel a n w, assemble cells fuel a n = some w → μ.readN a n = encodeLE n w := by
  intro fuel
  induction fuel with
  | zero =>
    intro a n w h
    simp only [assemble] at h
    split at h
    · subst_vars; rfl
    · cases h
  | succ fuel ih =>
    intro a n w h
    simp only [assemble] at h
    split at h
    · subst_vars; rfl
    rename_i hn
    split at h
    · rename_i c m v hf
      cases hr : assemble cells fuel (a + min (c + m - a) n) (n - min (c + m - a) n)
      · rw [hr] at h; cases h
      · rw [hr] at h; cases h
        rename_i r
        have hm := List.mem_of_find?_eq_some hf
        have hp := List.find?_some hf
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
        have hcell := hc _ hm
        simp only [SVal.eval] at hcell
        have hk : 0 < min (c + m - a) n := by omega
        generalize hK : min (c + m - a) n = k at hk hr ⊢
        have hkn : k ≤ n := by omega
        have hkm : a + k ≤ c + m := by omega
        have h1 := readN_inside hcell hp.1.1 hkm
        have h2 := ih _ _ _ hr
        have hlo : v / 256 ^ (a - c) % 256 ^ k < 256 ^ k := Nat.mod_lt _ (Nat.pow_pos (by omega))
        have hpos : 0 < 256 ^ k := Nat.pow_pos (by omega)
        rw [show n = k + (n - k) by omega, Memory.readN_split, h1, h2, Num.encodeLE_split]
        congr 1
        · rw [← encodeLE_mod k (v / 256 ^ (a - c)),
            ← encodeLE_mod k (v / 256 ^ (a - c) % 256 ^ k + 256 ^ k * r),
            Nat.add_mul_mod_self_left, Nat.mod_mod]
        · rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hlo, Nat.zero_add]
    · cases h

/-- What `loadVal` returns is what the octets at `[a, a + n)` decode to. -/
theorem loadVal_sound (hB : ∀ k b, st.bounds[k]? = some b → E.ρ k < b) {σ : SState} {ω : Regs}
    {μ : Memory} (h : Inv E σ ω μ) {a n : Nat} (han : a + n ≤ two32) {v : SVal}
    (hv : loadVal st σ a n = some v) : v.eval E = decodeLE (μ.readN a n) := by
  obtain ⟨_, _, hc, hf, _⟩ := h
  unfold loadVal at hv
  split at hv
  · rename_i c hfc
    cases hv
    have hm := List.mem_of_find?_eq_some hfc
    have hp := List.find?_some hfc
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨h1, h2⟩ := hp
    rw [mkMod_eval hB, ← h1, ← h2, (hc c hm).2, decodeLE_encodeLE]
  · split at hv
    · rename_i w hw
      cases hv
      rw [assemble_sound (fun c hc' => (hc c hc').2) _ _ _ _ hw, decodeLE_encodeLE, pow8]
      rfl
    split at hv
    · cases hv
      rename_i hcl
      simp only [SVal.eval]
      congr 1
      apply Memory.readN_congr
      intro j hj
      exact (hf (a + j) (by omega) (clear_mono hcl (by omega) (by omega))).symm
    · cases hv

theorem frags_sound {E : Env} {μ : Memory} {a n : Nat} {c : Nat × Nat × SVal}
    (hc : μ.readN c.1 c.2.1 = encodeLE c.2.1 (c.2.2.eval E)) :
    ∀ f ∈ frags a n c, f.1 + f.2.1 ≤ two32 ∧ (f.1 + f.2.1 ≤ a ∨ a + n ≤ f.1) ∧
      μ.readN f.1 f.2.1 = encodeLE f.2.1 (f.2.2.eval E) := by
  intro f hf
  obtain ⟨c, m, v⟩ := c
  cases v with
  | const v =>
    simp only [frags] at hf
    simp only [SVal.eval] at hc
    split at hf
    · rename_i hok
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.or_eq_false_iff,
        decide_eq_false_iff_not, Nat.not_le] at hok
      rcases List.mem_append.1 hf with hf | hf
      · split at hf
        · simp only [List.mem_singleton] at hf; subst hf
          refine ⟨show c + (a - c) ≤ two32 by omega, Or.inl (show c + (a - c) ≤ a by omega), ?_⟩
          have := readN_inside hc (Nat.le_refl c) (show c + (a - c) ≤ c + m by omega)
          simp only [Nat.sub_self, Nat.pow_zero, Nat.div_one] at this
          exact this
        · cases hf
      · split at hf
        · simp only [List.mem_singleton] at hf; subst hf
          refine ⟨show a + n + (c + m - (a + n)) ≤ two32 by omega,
            Or.inr (show a + n ≤ a + n by omega), ?_⟩
          exact readN_inside (a := a + n) (n := c + m - (a + n)) hc (by omega) (by omega)
        · cases hf
    · cases hf
  | _ => simp [frags] at hf

/-- A store `sstore` allows: the octets are writable, and the new state is described. -/
theorem sstore_sound (hpre : Pre E st) {σ σ' : SState} {ω : Regs} {μ : Memory} (h : Inv E σ ω μ)
    {A n : Nat} {v : SVal} (hs : sstore st σ A n v = some σ') :
    (∀ i ∈ indices A n, μ.writable (i % two32) = true) ∧
      Inv E σ' ω (μ.writeN A (encodeLE n (v.eval E))) := by
  obtain ⟨hl, hr, hc, hf, hp⟩ := h
  unfold sstore at hs
  dsimp only at hs
  split at hs
  · rename_i hok
    cases hs
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨han, hw⟩ := hok
    obtain ⟨rg, hrg, h1, h2⟩ := inR_sound hw
    have hwA : μ.writeN A (encodeLE n (v.eval E)) = μ.writeN (A % two32) (encodeLE n (v.eval E)) :=
      Memory.writeN_congr _ _ _ _ (by rw [Nat.mod_mod])
    refine ⟨?_, hl, hr, ?_, ?_, ?_⟩
    · intro i hi
      obtain ⟨k, hk, hik⟩ := indices_mod han i hi
      rw [hik, writable_pages hp]
      exact hpre.2.2 rg hrg _ (by omega) (by omega)
    · intro c hcm
      rw [hwA]
      rcases List.mem_cons.1 hcm with rfl | hcm
      · exact ⟨han, Memory.readN_writeN_same _ _ _ _ (Num.length_encodeLE _ _) (by dsimp only; omega)⟩
      · rcases List.mem_append.1 hcm with hcm | hcm
        · rw [List.mem_filter] at hcm
          obtain ⟨hcm, hcd⟩ := hcm
          simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hcd
          refine ⟨hcd.1, ?_⟩
          rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp only [Num.length_encodeLE]; omega)
            (by simp only [Num.length_encodeLE]; omega) hcd.1]
          exact (hc c hcm).2
        · obtain ⟨c', hc'm, hfm⟩ := List.mem_flatMap.1 hcm
          obtain ⟨hf1, hf2, hf3⟩ := frags_sound (hc c' hc'm).2 c hfm
          refine ⟨hf1, ?_⟩
          rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp only [Num.length_encodeLE]; omega)
            (by simp only [Num.length_encodeLE]; omega) hf1]
          exact hf3
    · intro t ht hcl
      have key : (t + 1 ≤ A % two32 ∨ A % two32 + n ≤ t) ∧ clear σ.dirty t 1 = true := by
        split at hcl
        · rename_i hin
          obtain ⟨d, hd, h1, h2⟩ := inR_sound hin
          refine ⟨?_, hcl⟩
          simp only [clear, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hcl
          have := hcl d hd; omega
        · simp only [clear, List.all_cons, Bool.and_eq_true] at hcl
          refine ⟨?_, hcl.2⟩
          have := hcl.1
          simp only [Bool.or_eq_true, decide_eq_true_eq] at this
          exact this
      rw [hwA, Memory.read_writeN_disjoint _ _ _ _ (by simp only [Num.length_encodeLE]; omega)
        (by simp only [Num.length_encodeLE]; omega) (by omega)]
      exact hf t ht key.2
    · simp [hp]
  · cases hs

/-- A load `sload` allows: the octets are readable, and the new state is described. -/
theorem sload_sound (hpre : Pre E st) {σ σ' : SState} {ω : Regs} {μ : Memory} (hinv : Inv E σ ω μ)
    {d : Fin 13} {A n k : Nat} (hl : sload st σ d.val A n k = some σ') :
    memoryException μ (indices A n) [] = none ∧
      Inv E σ' (ω.set d (UInt64.ofNat (if k = 0 then decodeLE (μ.readN A n) else
        u64 (signed k (decodeLE (μ.readN A n)))))) μ := by
  have hB := hpre.1
  unfold sload at hl
  dsimp only at hl
  split at hl
  · rename_i hok
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
    obtain ⟨han, hrw⟩ := hok
    cases hv : loadVal st σ (A % two32) n
    · rw [hv] at hl; cases hl
    · rw [hv] at hl; cases hl
      rename_i v
      have hval := loadVal_sound hB hinv han hv
      rw [← readN_mod] at hval
      refine ⟨memEx_none ?_ (by simp), ?_⟩
      · intro i hi
        obtain ⟨j, hj, hij⟩ := indices_mod han i hi
        rw [hij, readable_pages hinv.2.2.2.2]
        rcases hrw with hr | hw
        · obtain ⟨rg, hrg, h1, h2⟩ := inR_sound hr
          exact hpre.2.1 rg hrg _ (by omega) (by omega)
        · obtain ⟨rg, hrg, h1, h2⟩ := inR_sound hw
          exact Memory.readable_of_writable (hpre.2.2 rg hrg _ (by omega) (by omega))
      · have := setv_inv hinv d (mkSx st.bounds k v)
        rwa [mkSx_eval hB, hval] at this
  · cases hl

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

theorem allJT_lookup {P : Program} : ∀ {jt : List (Nat × Nat)}, AllJT P jt → ∀ k t,
    jt.lookup k = some t → P.jumpTable.getD k 0 = t
  | [], _, _, _, h => by simp at h
  | (a, b) :: js, ⟨hj, hs⟩, k, t, h => by
    simp only [List.lookup_cons] at h
    by_cases hk : k = a
    · subst hk; simp at h; subst h; exact hj
    · rw [show (k == a) = false by simpa using hk] at h
      exact allJT_lookup hs k t h

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
      have h1 := allJT_lookup hjt _ _ hl
      have h2 := isBS_sound hbs _ hb
      unfold Program.djump
      rw [ite_eq_right (by omega), ite_eq_right (by rw [hsz]; omega)]
      simp [h1, h2]
    · cases h
  · cases h

theorem sstep_sound {p : ByteArray} {P : Program} {G : Prog}
    (hG : ProgHyp p P G) (hpre : Pre E st)
    {pc pc' : Nat} {σ σ' : SState} {ω : Regs} {μ : Memory} (hinv : Inv E σ ω μ)
    (h : sstep st G pc σ = some (pc', σ')) :
    ∃ ω' μ', FreeNext p pc ω μ pc' ω' μ' ∧ CostOk p pc ∧ Inv E σ' ω' μ' := by
  have hB := hpre.1
  have hrd := rdv_eval (st := st) hB hinv.2.1
  unfold sstep at h
  split at h
  · cases h
  rename_i e hfe
  have hbs := hG.2.1
  obtain ⟨hpc, hd⟩ := allCodeT_find hG.1 pc e hfe
  rw [hpc] at hd
  obtain ⟨hd1, hd2, hd3, hd4⟩ := hd
  -- the step through the mutation `m`, landing at `m.pc`
  have go : ∀ (m : Mutation), P.exec pc e.ins ω μ = m → m.status = .cont →
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
      cases hs : sstore st σ x.toNat n (mkMod st.bounds (rdv st σ a.val) (2 ^ (8 * n)))
      · rw [hs] at h; cases h
      · rw [hs] at h; cases h
        obtain ⟨hw, hi⟩ := sstore_sound hpre hinv hs
        rw [mkMod_eval hB, hrd] at hi
        exact go _ hx rfl (memEx_none (by simp) hw) hi hd3
    · rename_i n k hk; rw [hk] at hx
      cases hl : sload st σ a.val x.toNat n 0
      · rw [hl] at h; cases h
      · rw [hl] at h; cases h
        obtain ⟨hx2, hi⟩ := sload_sound hpre hinv hl
        simp only [ite_true] at hi
        exact go _ hx rfl hx2 hi hd3
    · cases h
  · -- load_imm_64
    rename_i a x hins; cases h
    exact go _ (by rw [hins]; try rfl) rfl rfl (setv_inv hinv a (.const x.toNat)) hd3
  · -- two registers
    rename_i op d a hins; cases h
    refine go _ (by rw [hins]; try rfl) rfl rfl ?_ hd3
    have := setv_inv hinv d (mkAlu2 op (rdv st σ a.val))
    rwa [mkAlu2_eval, hrd] at this
  · -- three registers
    rename_i op a b d hins; cases h
    refine go _ (by rw [hins]; try rfl) rfl rfl ?_ hd3
    have := setv_inv hinv d (mkAlu3 op (rdv st σ a.val) (rdv st σ b.val) (rdv st σ d.val))
    rwa [mkAlu3_eval, hrd, hrd, hrd] at this
  · -- two registers and an immediate
    rename_i op a b x hins
    have hx := exec_twoRegImm P pc op a b x ω μ
    rw [← hins] at hx
    split at h
    · rename_i hk; rw [hk] at hx; cases h
      refine go _ hx rfl rfl ?_ hd3
      have := setv_inv hinv a (mkAlu2i op (rdv st σ a.val) (rdv st σ b.val) x.toNat)
      rwa [mkAlu2i_eval, hrd, hrd] at this
    · rename_i n hk; rw [hk] at hx
      split at h
      · rename_i base hbase
        cases hs : sstore st σ (base + x.toNat) n (mkMod st.bounds (rdv st σ a.val) (2 ^ (8 * n)))
        · rw [hs] at h; cases h
        · rw [hs] at h; cases h
          rename_i σ''
          have hbv := hrd b
          rw [hbase] at hbv; simp only [SVal.eval] at hbv
          obtain ⟨hw, hi⟩ := sstore_sound hpre hinv hs
          rw [mkMod_eval hB, hrd] at hi
          rw [← hbv] at hx
          exact go _ hx rfl (memEx_none (by simp) hw) hi hd3
      · cases h
    · rename_i n k hk; rw [hk] at hx
      split at h
      · rename_i base hbase
        have hbv := hrd b
        rw [hbase] at hbv; simp only [SVal.eval] at hbv
        rw [← hbv] at hx
        cases hl : sload st σ a.val (base + x.toNat) n k
        · rw [hl] at h; cases h
        · rw [hl] at h; cases h
          unfold sload at hl
          dsimp only at hl
          split at hl
          · rename_i hok
            simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
            obtain ⟨han, hrw⟩ := hok
            cases hv : loadVal st σ ((base + x.toNat) % two32) n
            · rw [hv] at hl; cases hl
            · rw [hv] at hl; cases hl
              rename_i v
              have hval := loadVal_sound hB hinv han hv
              rw [← readN_mod] at hval
              refine go _ hx rfl (memEx_none ?_ (by simp)) ?_ hd3
              · intro i hi
                obtain ⟨j, hj, hij⟩ := indices_mod han i hi
                rw [hij, readable_pages hinv.2.2.2.2]
                rcases hrw with hr | hw
                · obtain ⟨rg, hrg, h1, h2⟩ := inR_sound hr
                  exact hpre.2.1 rg hrg _ (by omega) (by omega)
                · obtain ⟨rg, hrg, h1, h2⟩ := inR_sound hw
                  exact Memory.readable_of_writable (hpre.2.2 rg hrg _ (by omega) (by omega))
              · have := setv_inv hinv a (mkSx st.bounds k v)
                rwa [mkSx_eval hB, hval] at this
          · cases hl
      · cases h
  · -- store of an immediate
    rename_i op a x y hins
    split at h
    · rename_i base hbase
      cases hs : sstore st σ (base + x.toNat) op.width (.const (y.toNat % 2 ^ (8 * op.width)))
      · rw [hs] at h; cases h
      · rw [hs] at h; cases h
        have hbv := hrd a
        rw [hbase] at hbv; simp only [SVal.eval] at hbv
        obtain ⟨hw, hi⟩ := sstore_sound hpre hinv hs
        rw [hbv] at hw hi
        refine go { status := .cont
                    pc := P.next pc
                    regs := ω
                    mem := μ.writeN ((ω.get a).toNat + x.toNat)
                      (encodeLE op.width (SVal.eval E (.const (y.toNat % 2 ^ (8 * op.width)))))
                    writes := indices ((ω.get a).toNat + x.toNat) op.width }
          (by rw [hins]; try rfl) rfl ?_ hi hd3
        exact memEx_none (by simp) hw
    · cases h
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
