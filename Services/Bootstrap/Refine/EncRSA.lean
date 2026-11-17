import Services.Bootstrap.Encode.ArmsHVecAssign
import Services.Bootstrap.Decode.RandomStorageOk

/-!
# `RandomStorageAccumulate` (22) in refine's output encoder, with growth (`EncOkMH`)

The arm at 19870 (dispatch index 22, `Instruction::encode_to`): the tag octet 22, then by the word at S + 8 (compared
with ω₅ = 2^64 − 1, which the dispatch leaves): `Err` (2^64 − 1) the octet 1 (20363, to the end 20383); `Ok(v)` the octet
0, the length prefix ℰ(n) of the `Vec<[u8; 32]>` (n at S + 24, a 32-bit word: n ≥ 2^32 traps at 20397), and the n
hashes' 32 octets each, from q (S + 16) on the heap (the loop 19955 … 19976, to the end 20118). GP v0.8.0 Appendix C
(the encoding of a `Result` and of a sequence), B.7 (refine's output).
-/

namespace Services.Bootstrap.Refine.EncRSA

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX
  Services.Bootstrap.CodeA Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Encode.WriterGrow Services.Bootstrap.Encode.Enc
  Services.Bootstrap.Encode.EncMD Services.Bootstrap.Encode.GrowH

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

section
variable {X : Type} {R : HostRel X}

/-- `Enc.dispatchV` for `RandomStorageAccumulate` (22): the dispatch, with ω₅ = 2^64 − 1. -/
theorem dispatch22 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (F S v ret r5 r6 t : Nat) (ht : t = 22) (hF : 67476 + 56 ≤ F ∧ F < 4294967296)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat F) (h5 : ω[5] = UInt64.ofNat r5)
    (h6 : ω[6] = UInt64.ofNat r6) (h7 : ω[7] = UInt64.ofNat S) (h8 : ω[8] = UInt64.ofNat v)
    (hret : ret < 18446744073709551616) (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hv : v < 18446744073709551616)
    (hS : S + 8 ≤ 4294967296) (hSF : S + 8 ≤ F - 56 ∨ F ≤ S)
    (hD : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + t))
    (tab : μ.readN 67376 100 = table) (hrt : ∀ a, 67376 ≤ a → a < 67476 → μ.readable a = true)
    (hrS : ∀ a, S ≤ a → a < S + 8 → μ.readable a = true)
    (hw : ∀ a, F - 56 ≤ a → a < F → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 30145 ω μ x (arm t) ω' μ' x 24 ∧
      ω'[1] = UInt64.ofNat (F - 56) ∧ ω'[5] = UInt64.ofNat 18446744073709551615 ∧
      ω'[10] = UInt64.ofNat v ∧ ω'[11] = UInt64.ofNat S ∧
      μ'.readN (F - 8) 8 = Num.encodeLE 8 ret ∧ μ'.readN (F - 16) 8 = Num.encodeLE 8 r5 ∧
      μ'.readN (F - 24) 8 = Num.encodeLE 8 r6 ∧ μ'.readN (F - 40) 8 = Num.encodeLE 8 v ∧
      (∀ a, a < 4294967296 → (a < F - 56 ∨ F ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rD := rd8 (by omega) hD
  have hrt' : ∀ a, 67376 + 4 * t ≤ a → a < 67376 + 4 * t + 4 → μ.readable a = true :=
    fun a h1 h2 => hrt a (by omega) (by omega)
  have rt : rdN μ (67376 + 4 * t) 4 = ents.getD t 0 := by
    show Num.decodeLE (μ.readN _ 4) = _
    rw [table_entry tab t (by omega)]
    exact table_val t (by omega)
  have hsx := sxw_table t (by omega)
  have hr : ∀ a, F - 56 ≤ a → a < F → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  subst ht
  · simp only [ents, List.getD_cons_succ, List.getD_cons_zero, Nat.reduceMul, Nat.reduceAdd] at rt hrt' hsx
    simp only [arm, List.getD_cons_succ, List.getD_cons_zero]
    refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · pvm_go [h0, h1, h5, h6, h7, h8, hF, hS, hSF, hw, hr, hrS, rD, rt, hrt', hsx, rdN_writeN_disjoint,
        ↓rdN_fold, ↓loadI_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
      all_goals try simp only [show F - 56 + 48 = F - 8 by omega, show F - 56 + 40 = F - 16 by omega,
        show F - 56 + 32 = F - 24 by omega, show F - 56 + 16 = F - 40 by omega]
      post_simp
      all_goals try assumption

/-- `Enc.startV` for index 22. -/
theorem startV22 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    {D F S v cap ptr len N ret t' : Nat} (L : LayD P D F S v cap ptr len N ret t' μ) (hD : 136 ≤ D)
    (t : Nat) (ht : t = 22)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat F) (h7 : ω[7] = UInt64.ofNat S)
    (h8 : ω[8] = UInt64.ofNat v) (hD8 : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + t))
    (tab : μ.readN 67376 100 = table) (hrt : ∀ a, 67376 ≤ a → a < 67476 → μ.readable a = true) :
    ∃ ω1 μ1, FreeStepsH p R 30145 ω μ x (arm t) ω1 μ1 x 24 ∧
      StD D F v ptr len ret ω[5].toNat ω[6].toNat μ [] ω1 μ1 ∧ ω1[5] = UInt64.ofNat 18446744073709551615 ∧
      ω1[10] = UInt64.ofNat v ∧ ω1[11] = UInt64.ofNat S := by
  have hF := L.hF; have hF' := L.hF'; have hS := L.hS; have hS' := L.hS'; have hSF := L.hSF
  have hv := L.hv; have hvF := L.hvF
  have h5 : ω[5] = UInt64.ofNat ω[5].toNat := UInt64.ofNat_toNat.symm
  have h6 : ω[6] = UInt64.ofNat ω[6].toNat := UInt64.ofNat_toNat.symm
  have hret := L.hret
  obtain ⟨ω1, μ1, run1, a1, a5, a10, a11, a0', a5', a6', av, afr, ard, awr⟩ := dispatch22 (p := p) (P := P)
    (R := R) x ω μ F S v ret ω[5].toNat ω[6].toNat t ht ⟨by omega, hF'⟩ h0 h1 h5 h6 h7 h8 (by omega)
    (UInt64.toNat_lt _) (UInt64.toNat_lt _) (by omega) (by omega) (by omega) hD8 tab hrt
    (fun a h1 h2 => L.hrS a h1 (by omega)) (fun a h1 h2 => L.hwF a (by omega) h2)
  refine ⟨ω1, μ1, run1, ⟨a1, a0', a5', a6', av, ?_, by simp [Memory.readN],
    fun a h0 h1 _ _ => afr a h0 (by omega), ard, awr⟩, a5, a10, a11⟩
  rw [Memory.readN_congr (fun j hj => afr _ (by omega) (by omega))]; simpa using L.vl

/-- `GrowH.startVH` for index 22. -/
theorem startVH22 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (K : Nat) (x : RefineCtx)
    (ω : Regs) (μ : Memory) {env : RefineHost.Env} {pb S0 S1 D F S v cap ptr len ret t' : Nat} {s : State}
    (L : LayDH env pb S0 S1 P D F S v cap ptr len ret t' s μ) (hD : 136 ≤ D) (t : Nat) (ht : t = 22)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat F) (h7 : ω[7] = UInt64.ofNat S)
    (h8 : ω[8] = UInt64.ofNat v) (hD8 : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + t))
    (tab : μ.readN 67376 100 = table) (hrt : ∀ a, 67376 ≤ a → a < 67476 → μ.readable a = true) :
    ∃ ω1 μ1, FreeStepsH p (refineContractK K env) 30145 ω μ x (arm t) ω1 μ1 x 24 ∧
      StDH env pb S0 S1 F v len ptr ret ω[5].toNat ω[6].toNat s μ [] ω1 μ1 ∧
      ω1[5] = UInt64.ofNat 18446744073709551615 ∧ ω1[10] = UInt64.ofNat v ∧ ω1[11] = UInt64.ofNat S := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := L.nums
  obtain ⟨ω1, μ1, run1, st1, a5, a10, a11⟩ := startV22 (p := p) (P := P) (R := refineContractK K env) x ω μ
    L.toLayD0 hD t ht h0 h1 h7 h8 hD8 tab hrt
  have hk := keep_vl (Q := fun a => a < 4294967296 ∧ (a < F - D ∨ F ≤ a)) (by simpa using st1.vl) L.vl
    (fun a ha h => st1.keep a ha.1 ha.2 (by simp; omega) h)
  exact ⟨ω1, μ1, run1, ⟨⟨st1.h1, st1.s0, st1.s5, st1.s6, ⟨cap, ptr, s,
    L.init.frame (F - D) F (by omega) (Nat.le_refl _) (Or.inl n5) (fun a h0 h1 => hk a ⟨h0, h1⟩) st1.rd st1.wr⟩⟩,
    st1.sv⟩, a5, a10, a11⟩

/-- 19870 … 19884 (`RandomStorageAccumulate`, tag 22): the octet 22 at sp + 24 and the call for it (return 884 →
    19891), with S (ω₁₁) in ω₆ and ω₅ kept. -/
theorem seg_19870 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616) (hS : S < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h10 : ω[10] = UInt64.ofNat v) (h11 : ω[11] = UInt64.ofNat S)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 25 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 19870 ω μ x 58508 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 884 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = UInt64.ofNat S ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (sp + 24) 1 = [UInt8.ofNat 22] ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 25 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h10, h11, hsp, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h10, h11, Nat.mod_eq_of_lt hv,
      Nat.mod_eq_of_lt hS]
    post_simp
    all_goals try assumption

/-- 19891 … 20376 (`Err`): the word at S + 8 is 2^64 − 1 (= ω₅): the octet 1 at sp + 24 and the call for it (return
    918 → 20383), the writer from sp + 16. -/
theorem seg_19891_err {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616) (hS : S + 16 ≤ 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat 18446744073709551615) (h6 : ω[6] = UInt64.ofNat S)
    (s8 : μ.readN (S + 8) 8 = Num.encodeLE 8 18446744073709551615)
    (v16 : μ.readN (sp + 16) 8 = Num.encodeLE 8 v)
    (hrS : ∀ a, S + 8 ≤ a → a < S + 16 → μ.readable a = true)
    (hw : ∀ a, sp + 16 ≤ a → a < sp + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 19891 ω μ x 58508 ω' μ' x 7 ∧
      ω'[0] = UInt64.ofNat 918 ∧ ω'[1] = UInt64.ofNat sp ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (sp + 24) 1 = [UInt8.ofNat 1] ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 25 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r8 := rd8 (by decide) s8
  have rv := rd8 hv v16
  have hr : ∀ a, sp + 16 ≤ a → a < sp + 32 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hsp, hS, hw, hr, hrS, r8, rv, ↓rdN_fold, rdN_writeN_disjoint]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, Nat.mod_eq_of_lt hv]
    post_simp
    all_goals try assumption

/-- 19891 … 19910 (`Ok`): the word c at S + 8 is not 2^64 − 1 (= ω₅): the octet 0 at sp + 24 and the call for it
    (return 886 → 19917), the writer from sp + 16, ω₆ = S kept. -/
theorem seg_19891_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S c : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616) (hS : S + 16 ≤ 4294967296)
    (hc : c < 18446744073709551615)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat 18446744073709551615) (h6 : ω[6] = UInt64.ofNat S)
    (s8 : μ.readN (S + 8) 8 = Num.encodeLE 8 c)
    (v16 : μ.readN (sp + 16) 8 = Num.encodeLE 8 v)
    (hrS : ∀ a, S + 8 ≤ a → a < S + 16 → μ.readable a = true)
    (hw : ∀ a, sp + 16 ≤ a → a < sp + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 19891 ω μ x 58508 ω' μ' x 7 ∧
      ω'[0] = UInt64.ofNat 886 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[6] = UInt64.ofNat S ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (sp + 24) 1 = [UInt8.ofNat 0] ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 25 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r8 := rd8 (by omega) s8
  have rv := rd8 hv v16
  have hne : ¬ c = 18446744073709551615 := by omega
  have hr : ∀ a, sp + 16 ≤ a → a < sp + 32 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hsp, hS, hw, hr, hrS, r8, rv, hne, hc, ↓rdN_fold, rdN_writeN_disjoint]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h6, Nat.mod_eq_of_lt hv]
    post_simp
    all_goals try assumption

/-- 19917 … 19939 (`Ok`): the length n < 2^32 (S + 24, ω₆ = S) as a 32-bit word to sp + 24 and the pointer q
    (S + 16) in ω₆; the call of the length prefix with ω₇ = sp + 24, the writer (from sp + 16) in ω₈ and n in ω₅
    (return 888 → 19945). -/
theorem seg_19917 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (sp v S q n : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616)
    (hS : S + 32 ≤ 4294967296) (hq : q < 18446744073709551616) (hn : n < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h6 : ω[6] = UInt64.ofNat S)
    (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 q) (s24 : μ.readN (S + 24) 8 = Num.encodeLE 8 n)
    (v16 : μ.readN (sp + 16) 8 = Num.encodeLE 8 v)
    (hrS : ∀ a, S + 16 ≤ a → a < S + 32 → μ.readable a = true)
    (hw : ∀ a, sp + 16 ≤ a → a < sp + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 19917 ω μ x 30977 ω' μ' x 8 ∧
      ω'[0] = UInt64.ofNat 888 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat n ∧ ω'[6] = UInt64.ofNat q ∧
      ω'[7] = UInt64.ofNat (sp + 24) ∧ ω'[8] = UInt64.ofNat v ∧ rdN μ' (sp + 24) 4 = n ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 28 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r16 := rd8 hq s16
  have r24 := rd8 (by omega) s24
  have rv := rd8 hv v16
  have hsh : n >>> 32 = 0 := by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt hn
  have hr : ∀ a, sp + 16 ≤ a → a < sp + 32 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, hsp, hS, hw, hr, hrS, r16, r24, rv, hsh, ↓rdN_fold, rdN_writeN_disjoint]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h6, Nat.mod_eq_of_lt hv,
      Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt (show n < 18446744073709551616 by omega)]
    post_simp
    all_goals try assumption
    all_goals try (show Num.decodeLE _ = _; rw [Memory.readN_writeN_same _ _ _ _ (by simp) (by simp [two32] <;> omega),
      Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt (by omega))

/-- 19945 (no hashes): n = 0, on to the end at 20118. -/
theorem seg_19945_zero {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (h5 : ω[5] = UInt64.ofNat 0) :
    ∃ ω', FreeStepsH p R 19945 ω μ x 20118 ω' μ x 1 ∧ ω' = ω := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h5]
  · rfl

/-- 19945 … 19954 (n > 0 hashes): ω₈ = q (from ω₆), ω₅ = 32 n; on to the loop at 19955. -/
theorem seg_19945_pos {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (q n : Nat) (hq : q < 18446744073709551616) (hn : 0 < n ∧ 32 * n < 18446744073709551616)
    (h5 : ω[5] = UInt64.ofNat n) (h6 : ω[6] = UInt64.ofNat q) :
    ∃ ω', FreeStepsH p R 19945 ω μ x 19955 ω' μ x 4 ∧
      ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat (32 * n) ∧ ω'[8] = UInt64.ofNat q := by
  have hn0 : ¬ n = 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h5, h6, hn0, hn.2]
  · refine ⟨?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h5, h6, Nat.mod_eq_of_lt hq]
    all_goals try (congr 1; omega)

/-- 19955 … 19964 (the loop's head, hash at a): ω₆ = a + 32, ω₉ = 32, the writer (from sp + 16) in ω₇ and the call
    appending the hash (return 890 → 19971). -/
theorem seg_19955 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v a : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616)
    (ha : a + 32 < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat a)
    (v16 : μ.readN (sp + 16) 8 = Num.encodeLE 8 v)
    (hr : ∀ b, sp + 16 ≤ b → b < sp + 24 → μ.readable b = true) :
    ∃ ω', FreeStepsH p R 19955 ω μ x 58508 ω' μ x 4 ∧
      ω'[0] = UInt64.ofNat 890 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = UInt64.ofNat (a + 32) ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat a ∧ ω'[9] = UInt64.ofNat 32 := by
  have rv := rd8 hv v16
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h8, hsp, hr, rv, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h8, Nat.mod_eq_of_lt hv]
    all_goals try (congr 1; omega)

/-- 19971 … 19976 (after a hash, more left): ω₅ = 32 i less 32 is not 0; ω₈ = ω₆; back to 19955. -/
theorem seg_19971_more {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (i b : Nat) (hi : 2 ≤ i ∧ 32 * i < 18446744073709551616) (hb : b < 18446744073709551616)
    (h5 : ω[5] = UInt64.ofNat (32 * i)) (h6 : ω[6] = UInt64.ofNat b) :
    ∃ ω', FreeStepsH p R 19971 ω μ x 19955 ω' μ x 3 ∧
      ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat (32 * (i - 1)) ∧ ω'[8] = UInt64.ofNat b := by
  have hne : ¬ (32 * i + 18446744073709551584) % 18446744073709551616 = 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h5, h6, hne]
  · refine ⟨?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h5, h6, Nat.mod_eq_of_lt hb]
    all_goals try (congr 1; omega)

/-- 19971 … 19980 (after the last hash): ω₅ = 32 less 32 is 0; on to the end at 20118. -/
theorem seg_19971_last {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (h5 : ω[5] = UInt64.ofNat 32) :
    ∃ ω', FreeStepsH p R 19971 ω μ x 20118 ω' μ x 5 ∧ ω'[1] = ω[1] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h5]
  · simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some']

end

section
variable {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
  {env : RefineHost.Env} {pb S0 S1 D F v len ptr0 ret r5 r6 : Nat} {s0 : State} {μ0 : Memory}

/-- **The hash loop, with growth** (`GrowH.assign_loopH` for 19955 … 19976): from the loop's head for hash k
    (ω₈ = q + 32 k, ω₅ = 32 i, i = n − k > 0) in `StDH (pre0 ++ hb.take (32 k))`, the hashes' octets (the kept
    stretch (q, 32 n)) appended, at the end 20118 in `StDH (pre0 ++ hb)`, the frame [F − 56, F) kept; or a failed
    `realloc`. -/
theorem rsa_loopH (K : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (x : RefineCtx)
    (Fr : FrH S0 S1 D F v) (hD : 136 ≤ D) (q n : Nat) (pre0 hb : List UInt8) (hhb : hb.length = 32 * n)
    (hsrc : SafeR s0 ptr0 F S1 v q (32 * n))
    (arr : ∀ k, k < n → μ0.readN (q + 32 * k) 32 = (hb.drop (32 * k)).take 32)
    (hlen : 2 * (len + pre0.length + 32 * n) ≤ capBound) :
    ∀ i k (ω : Regs) (μ1 : Memory), k + i = n → 0 < i →
      StDH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 (pre0 ++ hb.take (32 * k)) ω μ1 →
      ω[5] = UInt64.ofNat (32 * i) → ω[8] = UInt64.ofNat (q + 32 * k) →
      (∃ ω' μ', FreeStepsH p (refineContractK K env) 19955 ω μ1 x 20118 ω' μ' x ((2000 + growGas) * (32 * i)) ∧
        StDH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 (pre0 ++ hb) ω' μ' ∧
        (∀ a, F - 56 ≤ a → a < F → μ'.read a = μ1.read a)) ∨
      ExhaustsW env K pb p P 19955 ω μ1 x ((2000 + growGas) * (32 * i)) := by
  have := Fr.hF2; have := Fr.hFv; have := Fr.hvS1; have := Fr.hS1; have := Fr.hFS0
  intro i
  induction i with
  | zero => intro k ω μ1 _ h; omega
  | succ i ih =>
    intro k ω μ1 hki _ st h5 h8
    have hk : k < n := by omega
    obtain ⟨cap1, ptr1, s1, W1⟩ := st.buf
    obtain ⟨bq1, bq2, bq3⟩ := SafeR.bounds W1.H Fr (W1.safe hsrc)
    have hlenk : (hb.take (32 * k)).length = 32 * k := by simp [hhb]; omega
    obtain ⟨ω2, run2, b0, b1, b5, b6, b7, b8, b9⟩ := seg_19955 (p := p) (P := P) (R := refineContractK K env)
      x ω μ1 (F - 56) v (q + 32 * k) (by omega) (by omega) (by omega) st.h1 h8
      (by rw [show F - 56 + 16 = F - 40 by omega]; exact st.sv)
      (fun b h1 h2 => Memory.readable_of_writable (W1.H.st b (by omega) (by omega)))
    rcases heapDH (p := p) (P := P) env K hK1 hK x ω2 μ1 Fr hD ⟨⟨b1.trans st.h1, st.w0, st.w5, st.w6, st.buf⟩, st.sv⟩
        (q + 32 * k) 32 890 19971 (by simp [hhb]; omega) (arr k hk) b0 b7 b8 b9
        ⟨by decide, by decide, by decide⟩ jte_444 bs_19971 (by simp [hlenk]; omega)
        (Or.inr (hsrc.sub (by omega) (by omega))) with
      ⟨ω3, μ3, run3, st3, c5, c6, cF⟩ | hx
    rotate_left
    · exact Or.inr ((ExhaustsW.pre run2 hx).mono (by unfold stepGas growGas; omega))
    have st3' := st3.cast (show pre0 ++ hb.take (32 * k) ++ (hb.drop (32 * k)).take 32 =
      pre0 ++ hb.take (32 * (k + 1)) by rw [show 32 * (k + 1) = 32 * k + 32 by omega, List.take_add]; simp)
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · obtain ⟨ω4, run4, d1⟩ := seg_19971_last (p := p) (P := P) (R := refineContractK K env) x ω3 μ3
        (by rw [c5, b5, h5])
      have hkn : 32 * (k + 1) = hb.length := by omega
      exact Or.inl ⟨ω4, μ3, (run2.trans (run3.trans run4)).mono (by unfold stepGas growGas; omega),
        StDH.cast ⟨⟨d1.trans st3'.h1, st3'.w0, st3'.w5, st3'.w6, st3'.buf⟩, st3'.sv⟩
          (by rw [hkn, List.take_length]), cF⟩
    · obtain ⟨ω4, run4, d1, d5, d8⟩ := seg_19971_more (p := p) (P := P) (R := refineContractK K env) x ω3 μ3
        (i + 1) (q + 32 * k + 32) ⟨by omega, by omega⟩ (by omega) (by rw [c5, b5, h5]) (by rw [c6, b6])
      rcases ih (k + 1) ω4 μ3 (by omega) hi0 ⟨⟨d1.trans st3'.h1, st3'.w0, st3'.w5, st3'.w6, st3'.buf⟩, st3'.sv⟩
          (by rw [d5]; congr 1) (by rw [d8]; congr 1) with
        ⟨ω5, μ5, run5, st5, kF5⟩ | hx
      · exact Or.inl ⟨ω5, μ5, (run2.trans (run3.trans (run4.trans run5))).mono (by unfold stepGas growGas; omega),
          st5, fun a h1 h2 => by rw [kF5 a h1 h2, cF a h1 h2]⟩
      · exact Or.inr ((ExhaustsW.pre (run2.trans (run3.trans run4)) hx).mono (by unfold stepGas growGas; omega))

end

/-- `RandomStorageAccumulate(Ok(v))`'s slot, the hashes at q: tag word 2^63 + 21, capacity and length n, the n
    hashes' 32 octets each at q (`Decode.RandomStorageOkRep` with its q given). -/
def RSAOkRepAt (q n : Nat) (hs : List UInt8) (bs : List UInt8) (μ : Memory) : Prop :=
  bs.take 8 = Num.encodeLE 8 9223372036854775829 ∧
  (bs.drop 8).take 8 = Num.encodeLE 8 n ∧ (bs.drop 16).take 8 = Num.encodeLE 8 q ∧
    (bs.drop 24).take 8 = Num.encodeLE 8 n ∧ μ.readN q (32 * n) = hs

/-- `RandomStorageAccumulate(Err)`'s slot: tag word 2^63 + 21, then 2^64 − 1. -/
def RSAErrRep (bs : List UInt8) (_μ : Memory) : Prop :=
  bs.take 8 = Num.encodeLE 8 9223372036854775829 ∧ (bs.drop 8).take 8 = Num.encodeLE 8 18446744073709551615

/-- The decode side's `RandomStorageOkRep` is `RSAOkRepAt` for some q. -/
theorem rsaOkRep_iff (n : Nat) (hs bs : List UInt8) (μ : Memory) :
    Decode.RandomStorage.RandomStorageOkRep n hs bs μ ↔ ∃ q, RSAOkRepAt q n hs bs μ := by
  constructor
  · rintro ⟨h0, q, h1, h2, h3, h4⟩; exact ⟨q, h0, h1, h2, h3, h4⟩
  · rintro ⟨q, h0, h1, h2, h3, h4⟩; exact ⟨h0, q, h1, h2, h3, h4⟩

/-- A stretch inside a read stretch. -/
theorem readN_slice (μ : Memory) (q a l m : Nat) (h : a + l ≤ m) :
    μ.readN (q + a) l = ((μ.readN q m).drop a).take l := by
  apply List.ext_getElem
  · simp [Memory.readN]; omega
  · intro j h1 h2
    simp only [Memory.readN, List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
    congr 1; omega

/-- **`RandomStorageAccumulate(Ok(v))` (index 22), with growth**: `RSAOkRepAt q n hs` encodes to
    22 :: 0 :: ℰ(n) ++ hs (n < 2^32), the heap octets the hashes' stretch (q, 32 n) when n > 0. -/
theorem rsa_okH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (q n : Nat) (hs : List UInt8) (hhs : hs.length = 32 * n) (hn : n < 4294967296)
    (hq64 : q < 18446744073709551616) :
    EncOkMH env K pb p P 192 (22 :: 0 :: (Blob.encodeNat n ++ hs)) (RSAOkRepAt q n hs) (SrcAtP q (32 * n)) := by
  intro x ω μ s S0 S1 F S v cap ptr len ret t h0 h1 h7 h8 rep L hlen tab hrt hsrc
  obtain ⟨r0, r8, r16, r24, rhs⟩ := rep
  have hD8 : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 22) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact r0
  have c8 : μ.readN (S + 8) 8 = Num.encodeLE 8 n := by rw [← slot_take μ S 8 8 (by decide)]; exact r8
  have c16 : μ.readN (S + 16) 8 = Num.encodeLE 8 q := by rw [← slot_take μ S 16 8 (by decide)]; exact r16
  have c24 : μ.readN (S + 24) 8 = Num.encodeLE 8 n := by rw [← slot_take μ S 24 8 (by decide)]; exact r24
  have Fr := L.fr
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := L.nums
  have hS := L.hS; have hS' := L.hS'
  have hE := encodeNat_pos n
  have hN : (22 :: 0 :: (Blob.encodeNat n ++ hs) : List UInt8).length = 2 + (Blob.encodeNat n).length + 32 * n := by
    simp [hhs]; omega
  rw [hN] at hlen
  obtain ⟨ω1, μ1, run1, st1, a5, a10, a11⟩ := startVH22 (p := p) (P := P) K x ω μ L (by decide) 22 rfl
    h0 h1 h7 h8 hD8 tab hrt
  rw [show arm 22 = 19870 from rfl] at run1
  obtain ⟨cap1, ptr1, s1, W1⟩ := st1.buf
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bt, bfr, brd, bwr⟩ := seg_19870 (p := p) (P := P)
    (R := refineContractK K env) x ω1 μ1 (F - 56) v S (by omega) (by omega) (by omega) st1.h1 a10 a11
    (fun a h1 h2 => W1.H.st a (by omega) (by omega))
  have st2 := st1.scratch Fr b1 (fun a h0 h1 => bfr a h0 (by omega)) brd bwr
  rcases scratchDH (p := p) (P := P) env K hK1 hK x ω2 μ2 Fr (by decide) st2 [UInt8.ofNat 22] 1 884 19891 rfl
      (by decide) b0 b7 b8 b9 ⟨by decide, by decide, by decide⟩ jte_441 bs_19891 (by simp; omega) bt with
    ⟨ω3, μ3, run3, st3, c5, c6, -⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans run2) hx).mono (by unfold encGas stepGas growGas; rw [hN]; omega))
  -- `Ok`: the octet 0
  obtain ⟨cap3, ptr3, s3, W3⟩ := st3.buf
  obtain ⟨ω4, μ4, run4, d0, d1, d6, d7, d8, d9, dt, dfr, drd, dwr⟩ := seg_19891_ok (p := p) (P := P)
    (R := refineContractK K env) x ω3 μ3 (F - 56) v S n (by omega) (by omega) (by omega) (by omega) st3.h1
    (by rw [c5, b5, a5]) (by rw [c6, b6])
    (by rw [st3.slot L.slot (by decide)]; exact c8)
    (by rw [show F - 56 + 16 = F - 40 by omega]; exact st3.sv)
    (fun a h1 h2 => W3.safe_readable (by omega) (W3.safe L.slot) a (by omega) (by omega))
    (fun a h1 h2 => W3.H.st a (by omega) (by omega))
  have st4 := st3.scratch Fr d1 (fun a h0 h1 => dfr a h0 (by omega)) drd dwr
  rcases scratchDH (p := p) (P := P) env K hK1 hK x ω4 μ4 Fr (by decide) st4 [UInt8.ofNat 0] 1 886 19917 rfl
      (by decide) d0 d7 d8 d9 ⟨by decide, by decide, by decide⟩ jte_442 bs_19917 (by simp; omega) dt with
    ⟨ω5, μ5, run5, st5, e5, e6, -⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans run4))) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  -- the length prefix
  obtain ⟨cap5, ptr5, s5, W5⟩ := st5.buf
  obtain ⟨ω6, μ6, run6, f0, f1, f5, f6, f7, f8, fn, ffr, frd, fwr⟩ := seg_19917 (p := p) (P := P)
    (R := refineContractK K env) x ω5 μ5 (F - 56) v S q n (by omega) (by omega) (by omega) hq64 hn st5.h1
    (by rw [e6, d6])
    (by rw [st5.slot L.slot (by decide)]; exact c16)
    (by rw [st5.slot L.slot (by decide)]; exact c24)
    (by rw [show F - 56 + 16 = F - 40 by omega]; exact st5.sv)
    (fun a h1 h2 => W5.safe_readable (by omega) (W5.safe L.slot) a (by omega) (by omega))
    (fun a h1 h2 => W5.H.st a (by omega) (by omega))
  have st6 := st5.scratch Fr f1 (fun a h0 h1 => ffr a h0 (by omega)) frd fwr
  rcases prefixDH (p := p) (P := P) env K hK1 hK x ω6 μ6 Fr (by decide) st6 n 888 19945 f0
      (by rw [f7]; congr 1; omega) f8 (by rw [show F - 32 = F - 56 + 24 by omega]; exact fn)
      ⟨by decide, by decide, by decide⟩ jte_443 bs_19945 (by simp; omega) with
    ⟨ω7, μ7, run7, st7, g5, g6, -⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))) hx).mono
      (by unfold encGas stepGas prefixGas growGas; rw [hN]; omega))
  have hpre : ([] ++ [UInt8.ofNat 22] ++ [UInt8.ofNat 0] ++ Blob.encodeNat n : List UInt8).length =
      2 + (Blob.encodeNat n).length := by simp; omega
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · -- no hashes
    subst hn0
    have hk0 : hs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hk0
    obtain ⟨ω8, run8, rfl⟩ := seg_19945_zero (p := p) (P := P) (R := refineContractK K env) x ω7 μ7
      (by rw [g5, f5])
    exact Or.inl (closeH L 20118 _ (by decide) (by unfold encGas stepGas prefixGas growGas; rw [hN]; omega)
      (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans run8)))))))
      (st7.toStH.cast (by simp)))
  · have hsq := hsrc q (32 * n) ⟨by omega, rfl, rfl⟩
    obtain ⟨ω8, run8, k1, k5, k8⟩ := seg_19945_pos (p := p) (P := P) (R := refineContractK K env) x ω7 μ7
      q n hq64 ⟨hn0, by omega⟩ (by rw [g5, f5]) (by rw [g6, f6])
    have henc : (22 :: 0 :: (Blob.encodeNat n ++ hs) : List UInt8) =
        ([] ++ [UInt8.ofNat 22] ++ [UInt8.ofNat 0] ++ Blob.encodeNat n) ++ hs := by
      simp only [List.nil_append, List.cons_append] <;> rfl
    have arr : ∀ k, k < n → μ.readN (q + 32 * k) 32 = (hs.drop (32 * k)).take 32 := fun k hk => by
      rw [readN_slice μ q (32 * k) 32 (32 * n) (by omega), rhs]
    rcases rsa_loopH (p := p) (P := P) K hK1 hK x Fr (by decide) q n
        ([] ++ [UInt8.ofNat 22] ++ [UInt8.ofNat 0] ++ Blob.encodeNat n) hs hhs hsq arr (by rw [hpre]; omega)
        n 0 ω8 μ7 (by omega) hn0
        (StDH.cast ⟨⟨k1.trans st7.h1, st7.w0, st7.w5, st7.w6, st7.buf⟩, st7.sv⟩ (by simp)) k5
        (by rw [k8]; congr 1) with
      ⟨ω9, μ9, run9, st9, -⟩ | hx
    · exact Or.inl (closeH L 20118 _ (by decide) (by unfold encGas stepGas prefixGas growGas; rw [hN]; omega)
        (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans (run8.trans
          run9))))))))
        (st9.toStH.cast henc.symm))
    · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans
        (run7.trans run8))))))) hx).mono (by unfold encGas stepGas prefixGas growGas; rw [hN]; omega))

/-- **`RandomStorageAccumulate(Err)` (index 22), with growth**: `RSAErrRep` encodes to [22, 1]; no heap octets. -/
theorem rsa_errH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) :
    EncOkMH env K pb p P 136 [22, 1] RSAErrRep (fun _ _ => False) := by
  intro x ω μ s S0 S1 F S v cap ptr len ret t h0 h1 h7 h8 rep L hlen tab hrt hsrc
  obtain ⟨r0, r8⟩ := rep
  have hD8 : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 22) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact r0
  have c8 : μ.readN (S + 8) 8 = Num.encodeLE 8 18446744073709551615 := by
    rw [← slot_take μ S 8 8 (by decide)]; exact r8
  have Fr := L.fr
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := L.nums
  have hS := L.hS; have hS' := L.hS'
  have hN : ([22, 1] : List UInt8).length = 2 := rfl
  rw [hN] at hlen
  obtain ⟨ω1, μ1, run1, st1, a5, a10, a11⟩ := startVH22 (p := p) (P := P) K x ω μ L (by decide) 22 rfl
    h0 h1 h7 h8 hD8 tab hrt
  rw [show arm 22 = 19870 from rfl] at run1
  obtain ⟨cap1, ptr1, s1, W1⟩ := st1.buf
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bt, bfr, brd, bwr⟩ := seg_19870 (p := p) (P := P)
    (R := refineContractK K env) x ω1 μ1 (F - 56) v S (by omega) (by omega) (by omega) st1.h1 a10 a11
    (fun a h1 h2 => W1.H.st a (by omega) (by omega))
  have st2 := st1.scratch Fr b1 (fun a h0 h1 => bfr a h0 (by omega)) brd bwr
  rcases scratchDH (p := p) (P := P) env K hK1 hK x ω2 μ2 Fr (by decide) st2 [UInt8.ofNat 22] 1 884 19891 rfl
      (by decide) b0 b7 b8 b9 ⟨by decide, by decide, by decide⟩ jte_441 bs_19891 (by simp; omega) bt with
    ⟨ω3, μ3, run3, st3, c5, c6, -⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans run2) hx).mono (by unfold encGas stepGas growGas; rw [hN]; omega))
  obtain ⟨cap3, ptr3, s3, W3⟩ := st3.buf
  obtain ⟨ω4, μ4, run4, d0, d1, d7, d8, d9, dt, dfr, drd, dwr⟩ := seg_19891_err (p := p) (P := P)
    (R := refineContractK K env) x ω3 μ3 (F - 56) v S (by omega) (by omega) (by omega) st3.h1
    (by rw [c5, b5, a5]) (by rw [c6, b6])
    (by rw [st3.slot L.slot (by decide)]; exact c8)
    (by rw [show F - 56 + 16 = F - 40 by omega]; exact st3.sv)
    (fun a h1 h2 => W3.safe_readable (by omega) (W3.safe L.slot) a (by omega) (by omega))
    (fun a h1 h2 => W3.H.st a (by omega) (by omega))
  have st4 := st3.scratch Fr d1 (fun a h0 h1 => dfr a h0 (by omega)) drd dwr
  rcases scratchDH (p := p) (P := P) env K hK1 hK x ω4 μ4 Fr (by decide) st4 [UInt8.ofNat 1] 1 918 20383 rfl
      (by decide) d0 d7 d8 d9 ⟨by decide, by decide, by decide⟩ jte_458 bs_20383 (by simp; omega) dt with
    ⟨ω5, μ5, run5, st5, -, -, -⟩ | hx
  · exact Or.inl (closeH L 20383 _ (by decide) (by unfold encGas stepGas growGas; rw [hN]; omega)
      (run1.trans (run2.trans (run3.trans (run4.trans run5)))) (st5.toStH.cast (by simp)))
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans run4))) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))

/-- `rsa_okH` at the depth 232. -/
theorem rsa_okH_232 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (q n : Nat) (hs : List UInt8) (hhs : hs.length = 32 * n) (hn : n < 4294967296)
    (hq64 : q < 18446744073709551616) :
    EncOkMH env K pb p P 232 (22 :: 0 :: (Blob.encodeNat n ++ hs)) (RSAOkRepAt q n hs) (SrcAtP q (32 * n)) :=
  (rsa_okH env K pb hK1 hK q n hs hhs hn hq64).mono (by decide)

/-- `rsa_errH` at the depth 232. -/
theorem rsa_errH_232 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) :
    EncOkMH env K pb p P 232 [22, 1] RSAErrRep (fun _ _ => False) :=
  (rsa_errH env K pb hK1 hK).mono (by decide)

end Services.Bootstrap.Refine.EncRSA
