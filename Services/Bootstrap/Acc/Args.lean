import Services.Bootstrap.DecodeU32
import Services.Bootstrap.CodeAAll
import PVM.Logic.Go

/-!
# Bootstrap's accumulate: the decodes of its arguments

Ψ_A passes ℰ(t, s, |**i**|) (GP v0.8.0 eq. `accinvocation`). At 6429 the accumulate entry calls the
`u32` decoder (`decodeU32`, at 31894) three times, on a reader over the arguments at 4278058720,
and keeps t in ω₅ and s in ω₆; it then stores t and s as `u32`s at sp + 256 and sp + 260 and calls
49454 at 6501. No host call is made, so this holds under any host relation.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 6435 … 6451 / 6457 … 6473: after a successful decode (ω₇ = 0), move the value to `dst`, point
    ω₇ at the reader and call the decoder again, with return address `ret`. -/
theorem gap1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory) (v : Nat)
    (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat 4278057152) (h7 : ω[7] = UInt64.ofNat 0) (h8 : ω[8] = UInt64.ofNat v) :
    ∃ ω', FreeStepsH p R 6435 ω μ x 31894 ω' μ x 5 ∧
      ω'[0] = UInt64.ofNat 216 ∧ ω'[1] = UInt64.ofNat 4278057152 ∧ ω'[5] = UInt64.ofNat v ∧
      ω'[7] = UInt64.ofNat 4278058720 ∧ ω'[8] = UInt64.ofNat v ∧
      ω'[2] = ω[2] ∧ ω'[3] = ω[3] ∧ ω'[4] = ω[4] ∧ ω'[6] = ω[6] ∧ ω'[9] = ω[9] ∧
      ω'[10] = ω[10] ∧ ω'[11] = ω[11] ∧ ω'[12] = ω[12] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, h7, h8]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h8]
    all_goals try rfl

/-- 6457 … 6473: after the second decode, move s to ω₆, point ω₇ at the reader and call the decoder
    again (return address 218). -/
theorem gap2 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory) (v : Nat)
    (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat 4278057152) (h7 : ω[7] = UInt64.ofNat 0) (h8 : ω[8] = UInt64.ofNat v) :
    ∃ ω', FreeStepsH p R 6457 ω μ x 31894 ω' μ x 5 ∧
      ω'[0] = UInt64.ofNat 218 ∧ ω'[1] = UInt64.ofNat 4278057152 ∧ ω'[6] = UInt64.ofNat v ∧
      ω'[7] = UInt64.ofNat 4278058720 ∧ ω'[8] = UInt64.ofNat v ∧
      ω'[2] = ω[2] ∧ ω'[3] = ω[3] ∧ ω'[4] = ω[4] ∧ ω'[5] = ω[5] ∧ ω'[9] = ω[9] ∧
      ω'[10] = ω[10] ∧ ω'[11] = ω[11] ∧ ω'[12] = ω[12] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, h7, h8]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h8, Nat.mod_eq_of_lt hv]
    all_goals try rfl

/-- 6479 … 6497: after the third decode, store t (ω₅) and s (ω₆) as `u32`s at sp + 256 and
    sp + 260 and point ω₇ at the reader, reaching the call at 6501. -/
theorem gap3 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (T S : Nat)
    (h1 : ω[1] = UInt64.ofNat 4278057152) (h5 : ω[5] = UInt64.ofNat T) (h6 : ω[6] = UInt64.ofNat S)
    (h7 : ω[7] = UInt64.ofNat 0)
    (hw : ∀ a, 4278057408 ≤ a → a < 4278057416 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 6479 ω μ x 6501 ω' μ' x 5 ∧
      ω'[1] = UInt64.ofNat 4278057152 ∧ ω'[5] = UInt64.ofNat T ∧ ω'[6] = UInt64.ofNat S ∧
      ω'[7] = UInt64.ofNat 4278058720 ∧
      ω'[0] = ω[0] ∧ ω'[2] = ω[2] ∧ ω'[3] = ω[3] ∧ ω'[4] = ω[4] ∧ ω'[8] = ω[8] ∧ ω'[9] = ω[9] ∧
      ω'[10] = ω[10] ∧ ω'[11] = ω[11] ∧ ω'[12] = ω[12] ∧
      μ' = (μ.writeN 4278057408 (Num.encodeLE 4 (T % 4294967296))).writeN 4278057412
        (Num.encodeLE 4 (S % 4294967296)) := by
  have hr : ∀ a, 4278057408 ≤ a → a < 4278057416 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, h6, h7, hw, hr]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h5, h6]
    all_goals try rfl
    all_goals simp only [Nat.mod_mod_of_dvd _ (by decide : 4294967296 ∣ 18446744073709551616)]

/-- 6429: the first call of the decoder (return address 214). -/
theorem call1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory) :
    ∃ ω', FreeStepsH p R 6429 ω μ x 31894 ω' μ x 1 ∧ ω'[0] = UInt64.ofNat 214 ∧
      ∀ j : Fin 13, j.val ≠ 0 → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go []
  case post =>
    refine ⟨?_, ?_⟩
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, ↓reduceIte, PVM.getD_some']
    · intro j hj
      simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, hj]

/-- **The three decodes of Ψ_A's arguments ℰ(t, s, n)**, from the call at 6429 to the call at 6501:
    with the reader at 4278058720 over the LA octets at 4278124544, which hold ℰ(T) ⌢ ℰ(S) ⌢ ℰ(N),
    the run leaves T in ω₅, S in ω₆ and N in ω₈, stores T and S as `u32`s at sp + 256 and sp + 260,
    advances the reader to the end of the arguments, and changes nothing else but the decoder's stack
    frame below sp. -/
theorem args_run {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (T S N LA : Nat) (hT : T < 4294967296) (hS : S < 4294967296) (hN : N < 4294967296)
    (hLA : (Blob.encodeNat T).length + (Blob.encodeNat S).length + (Blob.encodeNat N).length = LA)
    (h1 : ω[1] = UInt64.ofNat 4278057152) (h7 : ω[7] = UInt64.ofNat 4278058720)
    (hR0 : μ.readN 4278058720 8 = Num.encodeLE 8 4278124544) (hR8 : μ.readN 4278058728 8 = Num.encodeLE 8 LA)
    (hmem : μ.readN 4278124544 LA = Blob.encodeNat T ++ Blob.encodeNat S ++ Blob.encodeNat N)
    (hrd : ∀ a, 4278124544 ≤ a → a < 4278124544 + LA → μ.readable a = true)
    (hwf : ∀ a, 4278057024 ≤ a → a < 4278057152 → μ.writable a = true)
    (hwr : ∀ a, 4278058720 ≤ a → a < 4278058736 → μ.writable a = true)
    (hws : ∀ a, 4278057408 ≤ a → a < 4278057416 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 6429 ω μ x 6501 ω' μ' x 1516 ∧
      ω'[1] = UInt64.ofNat 4278057152 ∧ ω'[5] = UInt64.ofNat T ∧ ω'[6] = UInt64.ofNat S ∧
      ω'[7] = UInt64.ofNat 4278058720 ∧ ω'[8] = UInt64.ofNat N ∧
      ω'[2] = ω[2] ∧ ω'[3] = ω[3] ∧ ω'[4] = ω[4] ∧ ω'[12] = ω[12] ∧
      μ'.readN 4278058720 8 = Num.encodeLE 8 (4278124544 + LA) ∧ μ'.readN 4278058728 8 = Num.encodeLE 8 0 ∧
      μ'.readN 4278057408 4 = Num.encodeLE 4 T ∧ μ'.readN 4278057412 4 = Num.encodeLE 4 S ∧
      (∀ a, a < 4294967296 → (a < 4278057024 ∨ 4278057152 ≤ a) → (a < 4278058720 ∨ 4278058736 ≤ a) →
        (a < 4278057408 ∨ 4278057416 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨lT1, lT⟩ := encodeNat_len_le5 T hT
  obtain ⟨lS1, lS⟩ := encodeNat_len_le5 S hS
  obtain ⟨lN1, lN⟩ := encodeNat_len_le5 N hN
  have hm3 : μ.readN 4278124544 (Blob.encodeNat T ++ Blob.encodeNat S ++ Blob.encodeNat N).length =
      Blob.encodeNat T ++ Blob.encodeNat S ++ Blob.encodeNat N := by
    rw [show (Blob.encodeNat T ++ Blob.encodeNat S ++ Blob.encodeNat N).length = LA by simp; omega]
    exact hmem
  have sT : μ.readN 4278124544 (Blob.encodeNat T).length = Blob.encodeNat T := by
    have := Memory.readN_mid μ 4278124544 [] (Blob.encodeNat T) (Blob.encodeNat S ++ Blob.encodeNat N)
      (by simpa only [List.nil_append, List.append_assoc] using hm3)
    simpa using this
  have sS : μ.readN (4278124544 + (Blob.encodeNat T).length) (Blob.encodeNat S).length = Blob.encodeNat S :=
    Memory.readN_mid μ 4278124544 (Blob.encodeNat T) (Blob.encodeNat S) (Blob.encodeNat N) hm3
  have sN : μ.readN (4278124544 + (Blob.encodeNat T).length + (Blob.encodeNat S).length)
      (Blob.encodeNat N).length = Blob.encodeNat N := by
    have := Memory.readN_mid μ 4278124544 (Blob.encodeNat T ++ Blob.encodeNat S) (Blob.encodeNat N) []
      (by simpa only [List.append_nil] using hm3)
    simpa [Nat.add_assoc] using this
  -- the call at 6429
  obtain ⟨ω1, run1, e1_0, e1fr⟩ := call1 (p := p) (P := P) (R := R) x ω μ
  have e1_1 : ω1[1] = UInt64.ofNat 4278057152 := by have := e1fr 1 (by decide); simp_all
  have e1_7 : ω1[7] = UInt64.ofNat 4278058720 := by have := e1fr 7 (by decide); simp_all
  have e1_2 : ω1[2] = ω[2] := by have := e1fr 2 (by decide); simp_all
  have e1_3 : ω1[3] = ω[3] := by have := e1fr 3 (by decide); simp_all
  have e1_4 : ω1[4] = ω[4] := by have := e1fr 4 (by decide); simp_all
  have e1_12 : ω1[12] = ω[12] := by have := e1fr 12 (by decide); simp_all
  -- t
  obtain ⟨ω2, μ2, run2, d2_0, d2_1, d2_2, d2_3, d2_4, d2_5, d2_6, d2_12, d2_7, d2_8, d2_r0, d2_r8, d2_fr, d2_rd, d2_wr⟩ :=
    decodeU32 (p := p) (P := P) (R := R) x ω1 μ 214 6435 4278057152 4278058720 4278124544 LA e1_0 e1_1 e1_7
      (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_106]) bs_6435 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (fun a h1 h2 => hwf a (by omega) h2) hwr hR0 hR8 T hT ⟨by omega, by omega⟩
      (fun a h1 h2 => hrd a h1 (by omega)) sT
  have arg2 : ∀ a, 4278124544 ≤ a → a < 4278124544 + LA → μ2.read a = μ.read a := fun a h1 h2 =>
    d2_fr a (by omega) (by omega) (by omega)
  obtain ⟨ω3, run3, g1_0, g1_1, g1_5, g1_7, g1_8, g1_2, g1_3, g1_4, g1_6, g1_9, g1_10, g1_11, g1_12⟩ :=
    gap1 (p := p) (P := P) (R := R) x ω2 μ2 T (by omega) (d2_1.trans e1_1) d2_7 d2_8
  -- s
  obtain ⟨ω4, μ4, run4, d4_0, d4_1, d4_2, d4_3, d4_4, d4_5, d4_6, d4_12, d4_7, d4_8, d4_r0, d4_r8, d4_fr, d4_rd, d4_wr⟩ :=
    decodeU32 (p := p) (P := P) (R := R) x ω3 μ2 216 6457 4278057152 4278058720
      (4278124544 + (Blob.encodeNat T).length) (LA - (Blob.encodeNat T).length) g1_0 g1_1 g1_7
      (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_107]) bs_6457 (by decide) (by decide)
      (by omega) (by decide) (by omega) (by omega)
      (fun a h1 h2 => by rw [d2_wr]; exact hwf a (by omega) h2) (fun a h1 h2 => by rw [d2_wr]; exact hwr a h1 h2)
      d2_r0 d2_r8 S hS ⟨by omega, by omega⟩
      (fun a h1 h2 => by rw [d2_rd]; exact hrd a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => arg2 _ (by omega) (by omega))]; exact sS)
  have arg4 : ∀ a, 4278124544 ≤ a → a < 4278124544 + LA → μ4.read a = μ.read a := fun a h1 h2 =>
    (d4_fr a (by omega) (by omega) (by omega)).trans (arg2 a h1 h2)
  obtain ⟨ω5, run5, g2_0, g2_1, g2_6, g2_7, g2_8, g2_2, g2_3, g2_4, g2_5, g2_9, g2_10, g2_11, g2_12⟩ :=
    gap2 (p := p) (P := P) (R := R) x ω4 μ4 S (by omega) (d4_1.trans g1_1) d4_7 d4_8
  -- n
  obtain ⟨ω6, μ6, run6, d6_0, d6_1, d6_2, d6_3, d6_4, d6_5, d6_6, d6_12, d6_7, d6_8, d6_r0, d6_r8, d6_fr, d6_rd, d6_wr⟩ :=
    decodeU32 (p := p) (P := P) (R := R) x ω5 μ4 218 6479 4278057152 4278058720
      (4278124544 + (Blob.encodeNat T).length + (Blob.encodeNat S).length)
      (LA - (Blob.encodeNat T).length - (Blob.encodeNat S).length) g2_0 g2_1 g2_7
      (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_108]) bs_6479 (by decide) (by decide)
      (by omega) (by decide) (by omega) (by omega)
      (fun a h1 h2 => by rw [d4_wr, d2_wr]; exact hwf a (by omega) h2)
      (fun a h1 h2 => by rw [d4_wr, d2_wr]; exact hwr a h1 h2)
      d4_r0 (by rw [d4_r8, Nat.sub_sub]) N hN ⟨by omega, by omega⟩
      (fun a h1 h2 => by rw [d4_rd, d2_rd]; exact hrd a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => arg4 _ (by omega) (by omega))]; exact sN)
  -- store t and s, reach 6501
  obtain ⟨ω7, μ7, run7, f_1, f_5, f_6, f_7, f_0, f_2, f_3, f_4, f_8, f_9, f_10, f_11, f_12, f_mem⟩ :=
    gap3 (p := p) (P := P) (R := R) x ω6 μ6 T S (d6_1.trans g2_1) (d6_5.trans (g2_5.trans (d4_5.trans g1_5)))
      (d6_6.trans g2_6) d6_7 (fun a h1 h2 => by rw [d6_wr, d4_wr, d2_wr]; exact hws a h1 h2)
  subst f_mem
  refine ⟨ω7, _, ((run1.trans run2).trans ((run3.trans run4).trans ((run5.trans run6).trans run7))).mono
    (by decide), f_1, f_5, f_6, f_7, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f_8, d6_8]
  · rw [f_2, d6_2, g2_2, d4_2, g1_2, d2_2, e1_2]
  · rw [f_3, d6_3, g2_3, d4_3, g1_3, d2_3, e1_3]
  · rw [f_4, d6_4, g2_4, d4_4, g1_4, d2_4, e1_4]
  · rw [f_12, d6_12, g2_12, d4_12, g1_12, d2_12, e1_12]
  · rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp) (by simp [two32]) (by simp [two32]),
      Memory.readN_writeN_disjoint _ _ _ _ _ (by simp) (by simp [two32]) (by simp [two32]), d6_r0]
    congr 1; omega
  · rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp) (by simp [two32]) (by simp [two32]),
      Memory.readN_writeN_disjoint _ _ _ _ _ (by simp) (by simp [two32]) (by simp [two32]), d6_r8]
    congr 1; omega
  · rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp) (by simp [two32]) (by simp [two32]),
      Memory.readN_writeN_same _ _ _ _ (by simp) (by simp [two32]), Nat.mod_eq_of_lt hT]
  · rw [Memory.readN_writeN_same _ _ _ _ (by simp) (by simp [two32]), Nat.mod_eq_of_lt hS]
  · intro a ha h1 h2 h3
    rw [Memory.read_writeN_disjoint _ _ _ _ (by simp; omega) (by simp [two32]) (by simp [two32]; omega),
      Memory.read_writeN_disjoint _ _ _ _ (by simp; omega) (by simp [two32]) (by simp [two32]; omega),
      d6_fr a ha (by omega) h2, d4_fr a ha (by omega) h2, d2_fr a ha (by omega) h2]
  · intro a; simp only [Memory.readable_writeN, d6_rd, d4_rd, d2_rd]
  · intro a; simp only [Memory.writable_writeN, d6_wr, d4_wr, d2_wr]

/-- 6508 … 6576: after `info`, the arguments of the first log line's `format!`: the fmt::Arguments
    pairs (value address, formatter) at sp + 1144 … sp + 1191 for s (sp + 260, 2616), t (sp + 256,
    2800) and the info record (sp + 1600, 2804), spills at sp + 80, sp + 136 and sp + 208; then ω₇ =
    sp + 744 (the `String`), ω₈ = 66464 (the pieces) and ω₉ = sp + 1144 for the call at 6580. -/
theorem fmt_setup {p : ByteArray} {P : Program} [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (h1 : ω[1] = UInt64.ofNat 4278057152)
    (hw1 : ∀ a, 4278057232 ≤ a → a < 4278057240 → μ.writable a = true)
    (hw2 : ∀ a, 4278057288 ≤ a → a < 4278057296 → μ.writable a = true)
    (hw3 : ∀ a, 4278057360 ≤ a → a < 4278057368 → μ.writable a = true)
    (hw4 : ∀ a, 4278058296 ≤ a → a < 4278058344 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 6508 ω μ x 6580 ω' μ' x 18 ∧
      ω'[1] = UInt64.ofNat 4278057152 ∧ ω'[7] = UInt64.ofNat 4278057896 ∧ ω'[8] = UInt64.ofNat 66464 ∧
      ω'[9] = UInt64.ofNat 4278058296 ∧
      ω'[0] = ω[0] ∧ ω'[2] = ω[2] ∧ ω'[3] = ω[3] ∧ ω'[4] = ω[4] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      μ'.readN 4278058296 8 = Num.encodeLE 8 4278057412 ∧ μ'.readN 4278058304 8 = Num.encodeLE 8 2616 ∧
      μ'.readN 4278058312 8 = Num.encodeLE 8 4278057408 ∧ μ'.readN 4278058320 8 = Num.encodeLE 8 2800 ∧
      μ'.readN 4278058328 8 = Num.encodeLE 8 4278058752 ∧ μ'.readN 4278058336 8 = Num.encodeLE 8 2804 ∧
      (∀ a, a < 4294967296 → (a < 4278057232 ∨ 4278057240 ≤ a) → (a < 4278057288 ∨ 4278057296 ≤ a) →
        (a < 4278057360 ∨ 4278057368 ≤ a) → (a < 4278058296 ∨ 4278058344 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr1 := fun a h1 h2 => Memory.readable_of_writable (hw1 a h1 h2)
  have hr2 := fun a h1 h2 => Memory.readable_of_writable (hw2 a h1 h2)
  have hr3 := fun a h1 h2 => Memory.readable_of_writable (hw3 a h1 h2)
  have hr4 := fun a h1 h2 => Memory.readable_of_writable (hw4 a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, hw1, hw2, hw3, hw4, hr1, hr2, hr3, hr4]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1]
    all_goals try rfl
    all_goals try (simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_same, PVM.Memory.readN_writeN_disjoint,
      PVM.Num.length_encodeLE, List.length_cons, List.length_nil, PVM.two32]; done)
    all_goals try (intro a; simp only [PVM.Memory.readable_writeN, PVM.Memory.writable_writeN]; done)
    all_goals try (intro a ha h1 h2 h3 h4
                   simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint, PVM.Num.length_encodeLE,
                     List.length_cons, List.length_nil, PVM.two32])

end Services.Bootstrap.Acc
