import Services.Bootstrap.Encode.Dispatch

/-!
# `Instruction::encode_to`: the writer's state between calls, and the variants of fixed width

Inside `Instruction::encode_to` (frame at F − 56) each variant's arm appends its encoding in pieces:
it puts a piece in the scratch word at F − 32 (or points into the value at S) and calls
`Vec<u8>::extend_from_slice` (58508), which returns to the arm through the jump table. `St pre` is the
state between pieces: the frame's saved words, the octets `pre` appended so far with the writer's
length `len + |pre|`, and memory otherwise as at entry (`μ0`) outside the stack below F. `ext_step`
is one call (`Writer.extend_ok`); `tailAt` is the function's end, from any of the shared tails.
-/

namespace Services.Bootstrap.Encode.Enc

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.Encode.Writer

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **The state between pieces**: ω₁ = F − 56, ω₀, ω₅, ω₆ of the caller saved at F − 8, F − 16, F − 24,
    the octets `pre` appended at `ptr + len` and the writer's length `len + |pre|`, and every other
    octet outside the stack below F as in μ0, with the same access. -/
structure St (F v ptr len ret r5 r6 : Nat) (μ0 : Memory) (pre : List UInt8) (ω : Regs) (μ : Memory) :
    Prop where
  h1 : ω[1] = UInt64.ofNat (F - 56)
  s0 : μ.readN (F - 8) 8 = Num.encodeLE 8 ret
  s5 : μ.readN (F - 16) 8 = Num.encodeLE 8 r5
  s6 : μ.readN (F - 24) 8 = Num.encodeLE 8 r6
  vl : μ.readN (v + 16) 8 = Num.encodeLE 8 (len + pre.length)
  out : μ.readN (ptr + len) pre.length = pre
  keep : ∀ a, a < 4294967296 → (a < F - 136 ∨ F ≤ a) → (a < ptr + len ∨ ptr + len + pre.length ≤ a) →
    (a < v + 16 ∨ v + 24 ≤ a) → μ.read a = μ0.read a
  rd : ∀ a, μ.readable a = μ0.readable a
  wr : ∀ a, μ.writable a = μ0.writable a

theorem readN_add' (μ : Memory) (a n m : Nat) : μ.readN a (n + m) = μ.readN a n ++ μ.readN (a + n) m := by
  simp only [Memory.readN, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  simp [Function.comp, Nat.add_assoc]

/-- The value's octets are as at entry. -/
theorem St.slot {F S v cap ptr len N ret t r5 r6 : Nat} {μ0 : Memory} {pre : List UInt8} {ω : Regs}
    {μ : Memory} {P : Program} (L : Lay P F S v cap ptr len N ret t μ0) (st : St F v ptr len ret r5 r6 μ0 pre ω μ)
    (hpre : pre.length ≤ N) (i m : Nat) (him : i + m ≤ 232) : μ.readN (S + i) m = μ0.readN (S + i) m :=
  Memory.readN_congr (fun j hj => st.keep _ (by have := L.hS'; omega) (by have := L.hSF; omega)
    (by have := L.hdS; omega) (by have := L.hvS; omega))

/-- **One piece** (`Vec<u8>::extend_from_slice`, 58508, returning to e): the n octets at `src`, from the
    scratch word at F − 32 or from the value at S, are appended: `St pre` becomes
    `St (pre ++ μ.readN src n)`. The frame at F − 56 is kept, and ω₅, ω₆. -/
theorem ext_step {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ μ0 : Memory)
    {F S v cap ptr len N ret t r5 r6 : Nat} {pre : List UInt8} (L : Lay P F S v cap ptr len N ret t μ0)
    (st : St F v ptr len ret r5 r6 μ0 pre ω μ) (src n r e : Nat)
    (h0 : ω[0] = UInt64.ofNat r) (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat src)
    (h9 : ω[9] = UInt64.ofNat n) (hr : 0 < r ∧ r ≤ 2806 ∧ r % 2 = 0) (hje : P.jumpTable.getD (r / 2 - 1) 0 = e)
    (hbe : P.isBlockStart e = true) (hn : pre.length + n ≤ N)
    (hsrc : (src = F - 32 ∧ n ≤ 8) ∨ (S ≤ src ∧ src + n ≤ S + 232)) :
    ∃ ω' μ', FreeStepsH p R 58508 ω μ x e ω' μ' x (7 * n + 360) ∧
      St F v ptr len ret r5 r6 μ0 (pre ++ μ.readN src n) ω' μ' ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      (∀ a, F - 56 ≤ a → a < F → μ'.read a = μ.read a) := by
  have hF := L.hF; have hF' := L.hF'; have hF8 := L.hF8; have hS := L.hS; have hS' := L.hS'
  have hSF := L.hSF; have hroom := L.hroom; have hv := L.hv; have hvF := L.hvF; have hvS := L.hvS
  have hd := L.hd; have hd' := L.hd'; have hdF := L.hdF; have hdS := L.hdS; have hdv := L.hdv
  have kv : ∀ a, v ≤ a → a < v + 16 → μ.read a = μ0.read a := fun a h1 h2 =>
    st.keep a (by omega) (by omega) (by omega) (by omega)
  obtain ⟨ω', μ', run, c0, c1, c5, c6, cd, cl, cfr, crd, cwr⟩ := extend_ok (p := p) (P := P) (R := R) x ω μ
    (F - 56) v src n cap ptr (len + pre.length) r e ⟨by omega, by omega, by omega⟩ h0 st.h1 h7 h8 h9
    (by omega) L.hcap
    (by rw [Memory.readN_congr (fun j hj => kv _ (by omega) (by omega))]; exact L.vc)
    (by rw [Memory.readN_congr (fun j hj => kv _ (by omega) (by omega))]; exact L.vp)
    st.vl hv (by omega) ⟨by omega, by omega⟩
    (by rcases hsrc with ⟨rfl, _⟩ | _ <;> constructor <;> omega)
    (by rcases hsrc with ⟨rfl, _⟩ | _ <;> omega)
    (by omega) (by rcases hsrc with ⟨rfl, _⟩ | _ <;> omega) (by omega) hr hje hbe
    (fun a h1 h2 => by rw [st.rd]; exact L.hrv a h1 h2)
    (fun a h1 h2 => by rw [st.wr]; exact L.hwv a h1 h2)
    (fun a h1 h2 => by
      rw [st.rd]
      rcases hsrc with ⟨rfl, _⟩ | _
      · exact Memory.readable_of_writable (L.hwF a (by omega) (by omega))
      · exact L.hrS a (by omega) (by omega))
    (fun a h1 h2 => by rw [st.wr]; exact L.hwd a (by omega) (by omega))
    (fun a h1 h2 => by rw [st.wr]; exact L.hwF a (by omega) (by omega))
  have kF : ∀ a, F - 56 ≤ a → a < F → μ'.read a = μ.read a := fun a h1 h2 =>
    cfr a (by omega) (by omega) (by omega) (by omega)
  have hlen : (μ.readN src n).length = n := by simp [Memory.readN]
  refine ⟨ω', μ', run, ⟨by rw [c1], ?_, ?_, ?_, ?_, ?_, ?_, fun a => by rw [crd, st.rd],
    fun a => by rw [cwr, st.wr]⟩, c5, c6, kF⟩
  · rw [Memory.readN_congr (fun j hj => kF _ (by omega) (by omega))]; exact st.s0
  · rw [Memory.readN_congr (fun j hj => kF _ (by omega) (by omega))]; exact st.s5
  · rw [Memory.readN_congr (fun j hj => kF _ (by omega) (by omega))]; exact st.s6
  · rw [List.length_append, hlen, ← Nat.add_assoc]; exact cl
  · rw [List.length_append, hlen, readN_add', show ptr + len + pre.length = ptr + (len + pre.length) by omega, cd,
      Memory.readN_congr (fun j hj => cfr _ (by omega) (by omega) (by omega) (by omega)), st.out]
  · intro a h0 h1 h2 h3
    rw [List.length_append, hlen] at h2
    rw [cfr a h0 (by omega) (by omega) h3, st.keep a h0 h1 (by omega) h3]

/-- The function's end, from any of the shared tails (20155, 20204, 20329, 20383): ω₀, ω₅, ω₆ from the
    frame at sp, the frame closed, and the return. -/
theorem tailAt {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (e sp ret t r5 r6 : Nat) (he : e = 20155 ∨ e = 20204 ∨ e = 20329 ∨ e = 20383)
    (hsp : sp + 56 < 4294967296) (h1 : ω[1] = UInt64.ofNat sp)
    (s0 : μ.readN (sp + 48) 8 = Num.encodeLE 8 ret)
    (s5 : μ.readN (sp + 40) 8 = Num.encodeLE 8 r5) (s6 : μ.readN (sp + 32) 8 = Num.encodeLE 8 r6)
    (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hr : ∀ a, sp + 32 ≤ a → a < sp + 56 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R e ω μ x t ω' μ x 6 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (sp + 56) ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 := by
  have r0 := rd8 (by omega) s0
  have r5' := rd8 hr5 s5
  have r6' := rd8 hr6 s6
  rw [show ω = regsNF ω [] from rfl]
  rcases he with rfl | rfl | rfl | rfl <;>
  · refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, hsp, hr, r0, r5', r6', hret, hjt, hbt, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_⟩
      all_goals simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, PVM.getD_some', h1]
      all_goals try (congr 1; omega)

/-- From `St enc` at one of the shared tails: the function returns as `EncOk` says. -/
theorem finish {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ μ0 : Memory)
    {F S v cap ptr len ret t r5 r6 : Nat} {enc : List UInt8} (L : Lay P F S v cap ptr len enc.length ret t μ0)
    (st : St F v ptr len ret r5 r6 μ0 enc ω μ) (e : Nat) (he : e = 20155 ∨ e = 20204 ∨ e = 20329 ∨ e = 20383)
    (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616) :
    ∃ ω', FreeStepsH p R e ω μ x t ω' μ x 6 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat F ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 ∧
      μ.readN (ptr + len) enc.length = enc ∧ μ.readN (v + 16) 8 = Num.encodeLE 8 (len + enc.length) ∧
      (∀ a, a < 4294967296 → (a < F - 136 ∨ F ≤ a) → (a < ptr + len ∨ ptr + len + enc.length ≤ a) →
        (a < v + 16 ∨ v + 24 ≤ a) → μ.read a = μ0.read a) ∧
      (∀ a, μ.readable a = μ0.readable a) ∧ (∀ a, μ.writable a = μ0.writable a) := by
  have hF := L.hF; have hF' := L.hF'
  obtain ⟨ω', run, e0, e1, e5, e6⟩ := tailAt (p := p) (P := P) (R := R) x ω μ e (F - 56) ret t r5 r6 he (by omega)
    st.h1 (by rw [show F - 56 + 48 = F - 8 by omega]; exact st.s0)
    (by rw [show F - 56 + 40 = F - 16 by omega]; exact st.s5)
    (by rw [show F - 56 + 32 = F - 24 by omega]; exact st.s6) hr5 hr6 L.hret L.hjt L.hbt
    (fun a h1 h2 => by rw [st.rd]; exact Memory.readable_of_writable (L.hwF a (by omega) (by omega)))
  exact ⟨ω', run, e0, by rw [e1]; congr 1; omega, e5, e6, st.out, st.vl, st.keep, st.rd, st.wr⟩

/-- Writes to the scratch word [F − 32, F − 24) (with ω₁ kept) keep `St`. -/
theorem St.scratch {F S v cap ptr len N ret t r5 r6 : Nat} {μ0 : Memory} {pre : List UInt8} {ω ω' : Regs}
    {μ μ' : Memory} {P : Program} (L : Lay P F S v cap ptr len N ret t μ0) (st : St F v ptr len ret r5 r6 μ0 pre ω μ)
    (hpre : pre.length ≤ N) (h1 : ω'[1] = UInt64.ofNat (F - 56))
    (hk : ∀ a, a < 4294967296 → (a < F - 32 ∨ F - 24 ≤ a) → μ'.read a = μ.read a)
    (hrd : ∀ a, μ'.readable a = μ.readable a) (hwr : ∀ a, μ'.writable a = μ.writable a) :
    St F v ptr len ret r5 r6 μ0 pre ω' μ' := by
  have hF := L.hF; have hF' := L.hF'; have hvF := L.hvF; have hdF := L.hdF; have hv := L.hv
  have hd' := L.hd'
  refine ⟨h1, ?_, ?_, ?_, ?_, ?_, fun a h0 h1 h2 h3 => ?_, fun a => by rw [hrd, st.rd],
    fun a => by rw [hwr, st.wr]⟩
  · rw [Memory.readN_congr (fun j hj => hk _ (by omega) (by omega))]; exact st.s0
  · rw [Memory.readN_congr (fun j hj => hk _ (by omega) (by omega))]; exact st.s5
  · rw [Memory.readN_congr (fun j hj => hk _ (by omega) (by omega))]; exact st.s6
  · rw [Memory.readN_congr (fun j hj => hk _ (by omega) (by omega))]; exact st.vl
  · rw [Memory.readN_congr (fun j hj => hk _ (by omega) (by omega))]; exact st.out
  · rw [hk a h0 (by omega)]; exact st.keep a h0 h1 h2 h3

/-- A variant's first piece, its tag octet: from the arm e the octet goes to sp + 24 and the arm calls
    `Vec<u8>::extend_from_slice` for it with return address r, the writer v (ω₁₀) in ω₇ and ω₅ and the
    value S (ω₁₁) in ω₆. -/
theorem tagArm {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (e tag r sp v S : Nat) (he : (e = 18890 ∧ tag = 3 ∧ r = 792) ∨ (e = 19088 ∧ tag = 20 ∧ r = 816))
    (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616) (hS : S < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h10 : ω[10] = UInt64.ofNat v) (h11 : ω[11] = UInt64.ofNat S)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 25 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R e ω μ x 58508 ω' μ' x 8 ∧
      ω'[0] = UInt64.ofNat r ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v ∧ ω'[6] = UInt64.ofNat S ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (sp + 24) 1 = [UInt8.ofNat tag] ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 25 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  rcases he with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  · refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h10, h11, hsp, hw]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h10, h11, Nat.mod_eq_of_lt hv,
        Nat.mod_eq_of_lt hS]
      post_simp
      all_goals try assumption

/-- A field of 4 octets (`Zombify`'s `ejector`, at S + 8): from 18913 the arm loads it from the value
    (ω₆ = S), and the shared tail at 20292 puts it at sp + 24 and calls `Vec<u8>::extend_from_slice` for
    the 4 octets, returning to 916 (→ 20329), with the writer from ω₅. -/
theorem fieldU32 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hS : S + 12 ≤ 4294967296)
    (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v) (h6 : ω[6] = UInt64.ofNat S)
    (hr : ∀ a, S + 8 ≤ a → a < S + 12 → μ.readable a = true)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 28 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 18913 ω μ x 58508 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 916 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 4 ∧
      μ'.readN (sp + 24) 4 = μ.readN (S + 8) 4 ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 28 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hsx : Num.encodeLE 4 (sxw 4 (rdN μ (S + 8) 4)) = μ.readN (S + 8) 4 := by
    rw [encodeLE_sxw 4 _ (Or.inr rfl) (rdN_lt μ _ 4), encodeLE_rdN]
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hsp, hS, hr, hw, ↓rdN_fold, ↓loadI_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, h6, Nat.mod_eq_of_lt hv]
    post_simp
    all_goals try assumption
    all_goals try (rw [← hsx, show ∀ w : Nat, w % 18446744073709551616 % 4294967296 = w % 256 ^ 4 from
      fun w => by omega, encodeLE_mod])

/-- A field of 8 octets (`Exported`'s segment index, at S + 8): from 19111 the arm loads it from the
    value (ω₆ = S), and the shared tail at 19519 puts it at sp + 24 and calls
    `Vec<u8>::extend_from_slice` for the 8 octets, returning to 916 (→ 20329). -/
theorem fieldU64 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hS : S + 16 ≤ 4294967296)
    (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v) (h6 : ω[6] = UInt64.ofNat S)
    (hr : ∀ a, S + 8 ≤ a → a < S + 16 → μ.readable a = true)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 19111 ω μ x 58508 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 916 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 8 ∧
      μ'.readN (sp + 24) 8 = μ.readN (S + 8) 8 ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 32 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hsp, hS, hr, hw, ↓rdN_fold, rdN_mod64]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, h6, Nat.mod_eq_of_lt hv]
    post_simp
    all_goals try assumption
    all_goals try exact encodeLE_rdN μ _ 8

/-- From 30145 to the arm of the variant with discriminant word 2^63 + t − 1, in `St []`, with the writer
    in ω₁₀ and the value in ω₁₁. -/
theorem start {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    {F S v cap ptr len N ret t' : Nat} (L : Lay P F S v cap ptr len N ret t' μ) (t : Nat) (ht : 1 ≤ t ∧ t < 25)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat F) (h7 : ω[7] = UInt64.ofNat S)
    (h8 : ω[8] = UInt64.ofNat v) (hD : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + t))
    (tab : μ.readN 67376 100 = table) (hrt : ∀ a, 67376 ≤ a → a < 67476 → μ.readable a = true) :
    ∃ ω1 μ1, FreeStepsH p R 30145 ω μ x (arm t) ω1 μ1 x 24 ∧
      St F v ptr len ret ω[5].toNat ω[6].toNat μ [] ω1 μ1 ∧ ω1[10] = UInt64.ofNat v ∧
      ω1[11] = UInt64.ofNat S := by
  have hF := L.hF; have hF' := L.hF'; have hS := L.hS; have hS' := L.hS'; have hSF := L.hSF
  have hv := L.hv; have hvF := L.hvF
  have h5 : ω[5] = UInt64.ofNat ω[5].toNat := UInt64.ofNat_toNat.symm
  have h6 : ω[6] = UInt64.ofNat ω[6].toNat := UInt64.ofNat_toNat.symm
  have hret := L.hret
  obtain ⟨ω1, μ1, run1, a1, a10, a11, a0', a5', a6', _, afr, ard, awr⟩ := dispatch (p := p) (P := P) (R := R)
    x ω μ F S v ret ω[5].toNat ω[6].toNat t ht ⟨by omega, hF'⟩ h0 h1 h5 h6 h7 h8 (by omega)
    (UInt64.toNat_lt _) (UInt64.toNat_lt _) (by omega) (by omega) (by omega) hD tab hrt
    (fun a h1 h2 => L.hrS a h1 (by omega)) (fun a h1 h2 => L.hwF a (by omega) h2)
  refine ⟨ω1, μ1, run1, ⟨a1, a0', a5', a6', ?_, by simp [Memory.readN], fun a h0 h1 _ _ => afr a h0 (by omega),
    ard, awr⟩, a10, a11⟩
  rw [Memory.readN_congr (fun j hj => afr _ (by omega) (by omega))]; simpa using L.vl

/-- The value's first word, and a later stretch of it, from `Rep`'s form. -/
theorem slot_take (μ : Memory) (S i m : Nat) (him : i + m ≤ 232) :
    ((μ.readN S 232).drop i).take m = μ.readN (S + i) m := by
  rw [show 232 = i + (m + (232 - i - m)) by omega, readN_add', readN_add', List.drop_left' (by simp [Memory.readN]),
    List.take_left' (by simp [Memory.readN])]

/-- **`Zombify`** (tag 3): a value holding the discriminant 2^63 + 2 and then e, the 4 octets of
    `ejector`, encodes to 3 :: e. -/
theorem zombify {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (e : List UInt8) (he : e.length = 4) :
    EncOk p P (3 :: e) (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775810 ∧ (bs.drop 8).take 4 = e) := by
  intro X R x ω μ F S v cap ptr len ret t' h0 h1 h7 h8 rep L tab hrt
  have hN : (3 :: e).length = 5 := by simp [he]
  have hv := L.hv; have hF := L.hF; have hF' := L.hF'; have hS := L.hS; have hS' := L.hS'; have hSF := L.hSF
  have hD : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 3) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact rep.1
  have hE : μ.readN (S + 8) 4 = e := by rw [← slot_take μ S 8 4 (by decide)]; exact rep.2
  obtain ⟨ω1, μ1, run1, st1, a10, a11⟩ := start (p := p) (P := P) (R := R) x ω μ L 3 (by decide) h0 h1 h7 h8 hD
    tab hrt
  rw [show arm 3 = 18890 from rfl] at run1
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bt, bfr, brd, bwr⟩ := tagArm (p := p) (P := P) (R := R) x ω1 μ1
    18890 3 792 (F - 56) v S (Or.inl ⟨rfl, rfl, rfl⟩) (by omega) (by omega) (by omega) st1.h1 a10 a11
    (fun a h1 h2 => by rw [st1.wr]; exact L.hwF a (by omega) (by omega))
  have st2 := st1.scratch L (by simp) b1 (fun a h0 h1 => bfr a h0 (by omega)) brd bwr
  obtain ⟨ω3, μ3, run3, st3, c5, c6, _⟩ := ext_step (p := p) (P := P) (R := R) x ω2 μ2 μ L st2 (F - 32) 1 792 18913
    b0 b7 (by rw [b8]; congr 1; omega) b9 ⟨by decide, by decide, by decide⟩ jte_395 bs_18913
    (by rw [hN]; decide) (Or.inl ⟨rfl, by decide⟩)
  rw [show F - 32 = F - 56 + 24 by omega, bt] at st3
  obtain ⟨ω4, μ4, run4, d0, d1, d5, d6, d7, d8, d9, dt, dfr, drd, dwr⟩ := fieldU32 (p := p) (P := P) (R := R) x ω3
    μ3 (F - 56) v S (by omega) (by omega) (by omega) st3.h1 (c5.trans b5) (c6.trans b6)
    (fun a h1 h2 => by rw [st3.rd]; exact L.hrS a (by omega) (by omega))
    (fun a h1 h2 => by rw [st3.wr]; exact L.hwF a (by omega) (by omega))
  have st4 := st3.scratch L (by simp [hN]) d1 (fun a h0 h1 => dfr a h0 (by omega)) drd dwr
  obtain ⟨ω5, μ5, run5, st5, _, _, _⟩ := ext_step (p := p) (P := P) (R := R) x ω4 μ4 μ L st4 (F - 32) 4 916 20329
    d0 d7 (by rw [d8]; congr 1; omega) d9 ⟨by decide, by decide, by decide⟩ jte_457 bs_20329
    (by simp [hN]) (Or.inl ⟨rfl, by decide⟩)
  have hpre : [] ++ [UInt8.ofNat 3] ++ μ4.readN (F - 32) 4 = 3 :: e := by
    rw [show F - 32 = F - 56 + 24 by omega, dt, st3.slot L (by simp [hN]) 8 4 (by decide), hE]; rfl
  rw [hpre] at st5
  obtain ⟨ω6, run6, e0, e1, e5, e6, eo, el, efr, erd, ewr⟩ := finish (p := p) (P := P) (R := R) x ω5 μ5 μ L st5
    20329 (by decide) (UInt64.toNat_lt _) (UInt64.toNat_lt _)
  refine ⟨ω6, μ5, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))).mono (by simp [hN]),
    e0, e1, by rw [e5]; exact UInt64.ofNat_toNat, by rw [e6]; exact UInt64.ofNat_toNat, eo, el, efr, erd, ewr⟩

/-- **`Exported`** (tag 20): a value holding the discriminant 2^63 + 19 and then e, the 8 octets of
    the segment index, encodes to 20 :: e. -/
theorem exported {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (e : List UInt8) (he : e.length = 8) :
    EncOk p P (20 :: e) (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775827 ∧ (bs.drop 8).take 8 = e) := by
  intro X R x ω μ F S v cap ptr len ret t' h0 h1 h7 h8 rep L tab hrt
  have hN : (20 :: e).length = 9 := by simp [he]
  have hv := L.hv; have hF := L.hF; have hF' := L.hF'; have hS := L.hS; have hS' := L.hS'; have hSF := L.hSF
  have hD : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 20) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact rep.1
  have hE : μ.readN (S + 8) 8 = e := by rw [← slot_take μ S 8 8 (by decide)]; exact rep.2
  obtain ⟨ω1, μ1, run1, st1, a10, a11⟩ := start (p := p) (P := P) (R := R) x ω μ L 20 (by decide) h0 h1 h7 h8 hD
    tab hrt
  rw [show arm 20 = 19088 from rfl] at run1
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bt, bfr, brd, bwr⟩ := tagArm (p := p) (P := P) (R := R) x ω1 μ1
    19088 20 816 (F - 56) v S (Or.inr ⟨rfl, rfl, rfl⟩) (by omega) (by omega) (by omega) st1.h1 a10 a11
    (fun a h1 h2 => by rw [st1.wr]; exact L.hwF a (by omega) (by omega))
  have st2 := st1.scratch L (by simp) b1 (fun a h0 h1 => bfr a h0 (by omega)) brd bwr
  obtain ⟨ω3, μ3, run3, st3, c5, c6, _⟩ := ext_step (p := p) (P := P) (R := R) x ω2 μ2 μ L st2 (F - 32) 1 816 19111
    b0 b7 (by rw [b8]; congr 1; omega) b9 ⟨by decide, by decide, by decide⟩ jte_407 bs_19111
    (by rw [hN]; decide) (Or.inl ⟨rfl, by decide⟩)
  rw [show F - 32 = F - 56 + 24 by omega, bt] at st3
  obtain ⟨ω4, μ4, run4, d0, d1, d5, d6, d7, d8, d9, dt, dfr, drd, dwr⟩ := fieldU64 (p := p) (P := P) (R := R) x ω3
    μ3 (F - 56) v S (by omega) (by omega) (by omega) st3.h1 (c5.trans b5) (c6.trans b6)
    (fun a h1 h2 => by rw [st3.rd]; exact L.hrS a (by omega) (by omega))
    (fun a h1 h2 => by rw [st3.wr]; exact L.hwF a (by omega) (by omega))
  have st4 := st3.scratch L (by simp [hN]) d1 (fun a h0 h1 => dfr a h0 (by omega)) drd dwr
  obtain ⟨ω5, μ5, run5, st5, _, _, _⟩ := ext_step (p := p) (P := P) (R := R) x ω4 μ4 μ L st4 (F - 32) 8 916 20329
    d0 d7 (by rw [d8]; congr 1; omega) d9 ⟨by decide, by decide, by decide⟩ jte_457 bs_20329
    (by simp [hN]) (Or.inl ⟨rfl, by decide⟩)
  have hpre : [] ++ [UInt8.ofNat 20] ++ μ4.readN (F - 32) 8 = 20 :: e := by
    rw [show F - 32 = F - 56 + 24 by omega, dt, st3.slot L (by simp [hN]) 8 8 (by decide), hE]; rfl
  rw [hpre] at st5
  obtain ⟨ω6, run6, e0, e1, e5, e6, eo, el, efr, erd, ewr⟩ := finish (p := p) (P := P) (R := R) x ω5 μ5 μ L st5
    20329 (by decide) (UInt64.toNat_lt _) (UInt64.toNat_lt _)
  refine ⟨ω6, μ5, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))).mono (by simp [hN]),
    e0, e1, by rw [e5]; exact UInt64.ofNat_toNat, by rw [e6]; exact UInt64.ofNat_toNat, eo, el, efr, erd, ewr⟩

end Services.Bootstrap.Encode.Enc
