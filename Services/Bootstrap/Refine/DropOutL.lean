import Services.Bootstrap.Refine.DropOutH

/-!
# Refine's exit: the drop arm of `LookedUp`

`drop_in_place::<[Instruction]>` dispatches a `LookedUp` element (index 18) through the table at 67760 (jump entry 682)
to its arm at 29376. The element's words 1 … 3 hold its `Option<Vec<u8>>` `{cap, ptr, len}`, `None` being cap = 2^64 − 1
(`LookupRun.ResAt`). The arm frees the buffer (`dealloc(ptr, cap, 1)`, return address 1356 → 29181) unless cap is 2^64 − 1
or 0, and goes on to the next element (29181). The code facts are tier T1B. GP v0.8.0 Appendix B.4 (Ψ_R running
bootstrap's code).
-/

namespace Services.Bootstrap.Refine.DropOutL

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeR
  Services.Bootstrap.CodeT1B
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Refine.DropOut Services.Bootstrap.Refine.DropOutH
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA Picoalloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 29188 … 29376: element k at E + 232 k (kept at F + 48) of index 18 dispatches through the table at 67760 (entry 682)
    to its arm. -/
theorem ddL {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P] (x : X)
    (ω : Regs) (μ : Memory) (F E k : Nat)
    (hF : 67856 ≤ F ∧ F + 80 ≤ 4294967296 ∧ F % 8 = 0)
    (hEk : E + 232 * k + 8 ≤ 4294967296) (hEF : E + 232 * k + 8 ≤ F ∨ F + 80 ≤ E + 232 * k)
    (h1 : ω[1] = UInt64.ofNat F) (h6 : ω[6] = UInt64.ofNat k)
    (s40 : μ.readN (F + 40) 8 = Num.encodeLE 8 E) (s32 : μ.readN (F + 32) 8 = Num.encodeLE 8 9223372036854775807)
    (s24 : μ.readN (F + 24) 8 = Num.encodeLE 8 9223372036854775832) (s16 : μ.readN (F + 16) 8 = Num.encodeLE 8 67760)
    (hD : μ.readN (E + 232 * k) 8 = Num.encodeLE 8 (9223372036854775807 + 18))
    (tab : μ.readN 67760 96 = dtable) (hrt : ∀ a, 67760 ≤ a → a < 67856 → μ.readable a = true)
    (hrE : ∀ a, E + 232 * k ≤ a → a < E + 232 * k + 8 → μ.readable a = true)
    (hw : ∀ a, F ≤ a → a < F + 80 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 29188 ω μ x 29376 ω' μ' x 20 ∧
      ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ μ'.readN (F + 48) 8 = Num.encodeLE 8 (E + 232 * k) ∧
      (∀ a, a < 4294967296 → (a < F + 48 ∨ F + 56 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hF0, hF1, hF8⟩ := hF
  have hk : k < 18446744073709551616 := by omega
  have rE := rd8 (by omega) s40
  have r32 := rd8 (by decide) s32
  have r24 := rd8 (by decide) s24
  have r16 := rd8 (by decide) s16
  have hrE' : ∀ a, k * 232 + E ≤ a → a < k * 232 + E + 8 → μ.readable a = true :=
    fun a h1 h2 => hrE a (by omega) (by omega)
  have hr : ∀ a, F ≤ a → a < F + 80 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have e1 : (E + 232 * k) % 18446744073709551616 = E + 232 * k := Nat.mod_eq_of_lt (by omega)
  rw [show ω = regsNF ω [] from rfl]
  have rD0 := rd8 (by decide) hD
  have rD : rdN μ (k * 232 + E) 8 = 9223372036854775807 + 18 := by
    rw [show k * 232 + E = E + 232 * k by omega]; exact rD0
  have rt : rdN μ 67832 4 = 4294900902 := by
    show Num.decodeLE (μ.readN _ 4) = _
    rw [show (67832 : Nat) = 67760 + 4 * 18 from rfl, dtable_entry tab 18 (by decide)]; rfl
  have hrt' : ∀ a, 67832 ≤ a → a < 67836 → μ.readable a = true := fun a h1 h2 => hrt a (by omega) (by omega)
  have sx : sxw 4 4294900902 = 18446744069414584320 + 4294900902 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, hF0, hF1, hF8, hEk, hEF, hw, hr, hrE, hrE', rE, r32, r24, r16, rD, rt, hrt', sx, e1,
      rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  · refine ⟨?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h6, Nat.mul_comm k 232]
    post_simp

/-- 29376 … 29181: the capacity (word 1 of `el`) is 2^64 − 1 (`None`) or 0: nothing to free. -/
theorem lo0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P] (x : X)
    (ω : Regs) (μ : Memory) (F el v : Nat) (hF : F + 80 ≤ 4294967296) (hel : el + 16 ≤ 4294967296)
    (hv : v = 18446744073709551615 ∨ v = 0)
    (h1 : ω[1] = UInt64.ofNat F) (s48 : μ.readN (F + 48) 8 = Num.encodeLE 8 el)
    (s8 : μ.readN (el + 8) 8 = Num.encodeLE 8 v)
    (hr : ∀ a, el + 8 ≤ a → a < el + 16 → μ.readable a = true)
    (hr2 : ∀ a, F + 48 ≤ a → a < F + 56 → μ.readable a = true) :
    ∃ ω' N, FreeStepsH p R 29376 ω μ x 29181 ω' μ x N ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have re := rd8 (by omega) s48
  rw [show ω = regsNF ω [] from rfl]
  rcases hv with rfl | rfl
  · have rc := rd8 (by decide) s8
    refine ⟨?_, 4, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, hF, hel, hr, hr2, re, rc, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]
  · have rc := rd8 (by decide) s8
    refine ⟨?_, 5, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, hF, hel, hr, hr2, re, rc, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]

/-- 29376 … 40613: the capacity c is neither 2^64 − 1 nor 0: `dealloc(ptr, c, 1)` (ptr word 2; return address
    1356 → 29181). -/
theorem lo1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P] (x : X)
    (ω : Regs) (μ : Memory) (F el c ptr : Nat) (hF : F + 80 ≤ 4294967296) (hel : el + 24 ≤ 4294967296)
    (hc : c ≠ 0) (hc1 : c < 18446744073709551615) (hptr : ptr < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat F) (s48 : μ.readN (F + 48) 8 = Num.encodeLE 8 el)
    (s8 : μ.readN (el + 8) 8 = Num.encodeLE 8 c) (s16 : μ.readN (el + 16) 8 = Num.encodeLE 8 ptr)
    (hr : ∀ a, el + 8 ≤ a → a < el + 24 → μ.readable a = true)
    (hr2 : ∀ a, F + 48 ≤ a → a < F + 56 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 29376 ω μ x 40613 ω' μ x 11 ∧ ω'[0] = UInt64.ofNat 1356 ∧ ω'[1] = ω[1] ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat ptr := by
  have re := rd8 (by omega) s48
  have rc := rd8 (by omega) s8
  have rp := rd8 hptr s16
  have hc0 : ¬ c = 0 := hc
  have hcm : ¬ c = 18446744073709551615 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hF, hel, hc0, hcm, hc1, hr, hr2, re, rc, rp, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]

/-- **One `LookedUp` element dropped** (29188 … 29181): element k at el = E + 232 k of index 18, its `Option<Vec<u8>>`
    capacity c at el + 8 and buffer ptr at el + 16: when c is neither 2^64 − 1 (`None`) nor 0, the buffer, the allocated
    chunk `ch`, is freed. The element lies in the data of an allocated chunk `cb` other than `ch`. The heap context holds
    after; every other allocated chunk stays with its data; the frame from F up is kept but for F + 48 … F + 56; the
    pages and the read-only bytes are kept. -/
theorem drop_lu {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P]
    (env : RefineHost.Env) (pb S0 S1 : Nat) (x : X) (ω : Regs) (μ : Memory) (s : State)
    (F E k c ptr : Nat) (ch cb : Chunk)
    (hF : 2147483716 ≤ F ∧ S0 + 40 ≤ F ∧ F + 80 ≤ S1 ∧ F % 8 = 0)
    (hel : E + 232 * k + 32 ≤ 2147483648) (hptr : ptr < 18446744073709551616)
    (hc : c = 18446744073709551615 ∨ c = 0 ∨
      (c < 18446744073709551615 ∧ ch ∈ chunks s ∧ ch.used = true ∧ ch.addr + 32 = ptr))
    (hcbD : ∀ a, E + 232 * k ≤ a → a < E + 232 * k + 32 → InData cb a)
    (hcbch : c ≠ 0 → c ≠ 18446744073709551615 → cb ≠ ch)
    (h1 : ω[1] = UInt64.ofNat F) (h6 : ω[6] = UInt64.ofNat k) (H : HeapCtx env pb S0 S1 μ s)
    (cbm : cb ∈ chunks s) (cbu : cb.used = true)
    (s40 : μ.readN (F + 40) 8 = Num.encodeLE 8 E) (s32 : μ.readN (F + 32) 8 = Num.encodeLE 8 9223372036854775807)
    (s24 : μ.readN (F + 24) 8 = Num.encodeLE 8 9223372036854775832) (s16 : μ.readN (F + 16) 8 = Num.encodeLE 8 67760)
    (hD : μ.readN (E + 232 * k) 8 = Num.encodeLE 8 (9223372036854775807 + 18))
    (e8 : μ.readN (E + 232 * k + 8) 8 = Num.encodeLE 8 c)
    (e16 : μ.readN (E + 232 * k + 16) 8 = Num.encodeLE 8 ptr)
    (tab : μ.readN 67760 96 = dtable) (hrt : ∀ a, 67760 ≤ a → a < 67856 → μ.readable a = true) :
    ∃ ω' μ' s' N, FreeStepsH p R 29188 ω μ x 29181 ω' μ' x N ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧
      ω'[6] = ω[6] ∧ HeapCtx env pb S0 S1 μ' s' ∧
      (∀ a, a < 4294967296 → F ≤ a → (a < F + 8 ∨ F + 16 ≤ a) → (a < F + 48 ∨ F + 56 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ d ∈ chunks s, d.used = true → (c ≠ 0 → c ≠ 18446744073709551615 → d ≠ ch) →
        d ∈ chunks s' ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      (∀ b, b < two32 → μ.writable b = false → μ'.read b = μ.read b) := by
  obtain ⟨hF0, hF1, hF2, hF8⟩ := hF
  have hS := H.hS1
  have hwF : ∀ a, F ≤ a → a < F + 80 → μ.writable a = true := fun a h1 h2 => H.st a (by omega) (by omega)
  have rdcb : ∀ a, E + 232 * k ≤ a → a < E + 232 * k + 32 → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (Decode.VecU8.heap_writable H cbm cbu (hcbD a h1 h2))
  obtain ⟨ω1, μ1, run1, a1, a5, a6, a48, afr, ard, awr⟩ := ddL (p := p) (P := P) (R := R) x ω μ F E k
    ⟨by omega, by omega, hF8⟩ (by omega) (Or.inl (by omega)) h1 h6 s40 s32 s24 s16 hD tab hrt
    (fun a h1 h2 => rdcb a h1 (by omega)) hwF
  have H1 : HeapCtx env pb S0 S1 μ1 s := Decode.GrowOne.ctx_high H (fun a ha => afr a (by omega) (Or.inl (by omega))) awr
  have k1 : ∀ a l, a + l ≤ 2147483648 → μ1.readN a l = μ.readN a l :=
    fun a l h => Memory.readN_congr (fun j hj => afr _ (by omega) (Or.inl (by omega)))
  have ro1 : ∀ b, b < two32 → μ.writable b = false → μ1.read b = μ.read b := fun b hb hwb => by
    refine afr b (by unfold two32 at hb; omega) ?_
    by_cases h : F + 48 ≤ b ∧ b < F + 56
    · have := hwF b (by omega) (by omega); rw [hwb] at this; exact absurd this (by decide)
    · omega
  have fr1 : ∀ a, a < 4294967296 → F ≤ a → (a < F + 8 ∨ F + 16 ≤ a) → (a < F + 48 ∨ F + 56 ≤ a) →
      μ1.read a = μ.read a := fun a h0 _ _ h => afr a h0 h
  have rd48 : ∀ a, F + 48 ≤ a → a < F + 56 → μ1.readable a = true := fun a h1 h2 => by
    rw [ard]; exact Memory.readable_of_writable (hwF a (by omega) (by omega))
  have rde : ∀ a, E + 232 * k + 8 ≤ a → a < E + 232 * k + 24 → μ1.readable a = true := fun a h1 h2 => by
    rw [ard]; exact rdcb a (by omega) (by omega)
  by_cases hfree : c ≠ 0 ∧ c ≠ 18446744073709551615
  · obtain ⟨hc0, hcm⟩ := hfree
    obtain ⟨hc1, hchm, hchu, hcha⟩ : c < 18446744073709551615 ∧ ch ∈ chunks s ∧ ch.used = true ∧ ch.addr + 32 = ptr := by
      rcases hc with h | h | h
      · exact absurd h hcm
      · exact absurd h hc0
      · exact h
    obtain ⟨ω2, run2, b0, b1, b5, b6, b7⟩ := lo1 (p := p) (P := P) (R := R) x ω1 μ1 F (E + 232 * k) c ptr (by omega)
      (by omega) hc0 hc1 hptr (a1.trans h1) a48 (by rw [k1 _ _ (by omega)]; exact e8)
      (by rw [k1 _ _ (by omega)]; exact e16) rde rd48
    obtain ⟨ω3, μ3, run3, H3, -, pg3, ro3, stk3, -, keep3, d0, d1, d5, d6⟩ :=
      Decode.DeallocCall.dealloc_call (R := R) (p := p) (P := P) env pb S0 S1 x ω2 μ1 s F ptr 1356 29181 ch H1 hchm
        hchu hcha b0 (by rw [b1, a1]; exact h1) b7 (by decide)
        (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_677]) bs_29181 hF0 ⟨hF1, by omega⟩
    refine ⟨ω3, μ3, free s ptr, 20 + 11 + 249, (run1.trans run2).trans run3, by rw [d1, b1, a1], by rw [d5, b5, a5],
      by rw [d6, b6, a6], H3, fun a h0 hF h2 h3 => by rw [stk3 a h0 hF, fr1 a h0 hF h2 h3],
      fun d hd hu hne => ?_,
      fun a => by unfold Memory.readable; rw [pg3]; exact ard a,
      fun a => by unfold Memory.writable; rw [pg3]; exact awr a,
      fun b hb hwb => by rw [ro3 b hb (by rw [awr]; exact hwb), ro1 b hb hwb]⟩
    obtain ⟨hd3, kd3⟩ := keep3 d hd hu (hne hc0 hcm)
    exact ⟨hd3, fun a ha => by rw [kd3 a ha, afr a (by have := data_lo H hd hu ha; omega)
      (Or.inl (by have := data_lo H hd hu ha; omega))]⟩
  · have hv : c = 18446744073709551615 ∨ c = 0 := by omega
    obtain ⟨ω2, N2, run2, b1, b5, b6⟩ := lo0 (p := p) (P := P) (R := R) x ω1 μ1 F (E + 232 * k) c (by omega)
      (by omega) hv (a1.trans h1) a48 (by rw [k1 _ _ (by omega)]; exact e8)
      (fun a h1 h2 => rde a h1 (by omega)) rd48
    exact ⟨ω2, μ1, s, 20 + N2, run1.trans run2, by rw [b1, a1], by rw [b5, a5], by rw [b6, a6], H1, fr1,
      fun d hd hu _ => ⟨hd, fun a ha => afr a (by have := data_lo H hd hu ha; omega)
        (Or.inl (by have := data_lo H hd hu ha; omega))⟩, ard, awr, ro1⟩

end Services.Bootstrap.Refine.DropOutL
