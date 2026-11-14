import Services.Bootstrap.Encode.Writer
import Services.Bootstrap.Refine.Exit

/-!
# Refine's exit: the output `Vec<Instruction>` dropped

After the output is encoded (6295), refine drops its output `Vec<Instruction>` at M + 168:
`drop_in_place::<[Instruction]>` (29087) walks the n elements, 232 octets each from E, and for each runs
the variant's drop through the table at 67760 (read-only data). For the variants that own nothing on the
heap (`NoDrop`: dispatch indices 1, 2, 3, 4, 6, 7, 8, 14, 15, 16, 20, 21, 23, exactly the fixed-width
variants the encoder covers) the arm is 29181, which goes on to the next element. The function returns to
6305 (return address 206). This is the end of `Service::refine`'s body, GP v0.8.0 Appendix B.4 (Ψ_R
running bootstrap's code).
-/

namespace Services.Bootstrap.Refine.DropOut

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Encode.Writer

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- The variants whose drop does nothing: their dispatch indices. -/
def NoDrop (t : Nat) : Prop :=
  t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 14 ∨ t = 15 ∨ t = 16 ∨ t = 20 ∨ t = 21 ∨ t = 23

/-- The drop's table at 67760 (read-only data): one 32-bit offset per index 0 … 23, relative to 67760,
    to the jump-table address of the variant's drop. -/
def dtable : List UInt8 :=
  [176, 252, 254, 255, 156, 252, 254, 255, 156, 252, 254, 255, 156, 252, 254, 255, 156, 252, 254, 255,
   160, 252, 254, 255, 156, 252, 254, 255, 156, 252, 254, 255, 156, 252, 254, 255, 158, 252, 254, 255,
   168, 252, 254, 255, 158, 252, 254, 255, 154, 252, 254, 255, 178, 252, 254, 255, 156, 252, 254, 255,
   156, 252, 254, 255, 156, 252, 254, 255, 164, 252, 254, 255, 166, 252, 254, 255, 172, 252, 254, 255,
   156, 252, 254, 255, 156, 252, 254, 255, 180, 252, 254, 255, 156, 252, 254, 255]

theorem dtable_entry {μ : Memory} (tab : μ.readN 67760 96 = dtable) (t : Nat) (ht : t < 24) :
    μ.readN (67760 + 4 * t) 4 = (dtable.drop (4 * t)).take 4 := by
  rw [← tab]
  apply List.ext_getElem
  · simp [Memory.readN]; omega
  · intro j h1 h2
    simp only [Memory.readN, List.getElem_map, List.getElem_range, List.getElem_take,
      List.getElem_drop]
    congr 1; omega

/-- A no-op variant's entry is 4294900892: 67760 plus it (sign-extended) is the jump-table address
    1356, whose entry is 29181. -/
theorem dtable_val : ∀ t, t < 24 → NoDrop t → Num.decodeLE ((dtable.drop (4 * t)).take 4) = 4294900892 := by
  intro t ht hn
  unfold NoDrop at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem sxw_noop : sxw 4 4294900892 = 18446744069414584320 + 4294900892 := by decide

/-- 29087 … 29151: the drop opens its frame at sp − 80 (ω₀, ω₅, ω₆ at sp − 8, sp − 16, sp − 24), keeps
    n (from V + 16, nonzero) at sp − 80, E (from V + 8) at sp − 40, 2^63 − 1, 2^63 + 24 and 67760 at
    sp − 48, sp − 56, sp − 64, and goes to the element loop at 29188 with ω₅ = n, ω₆ = 0. -/
theorem dh {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp V E n : Nat) (hsp : 65536 + 80 ≤ sp ∧ sp < 4294967296 ∧ sp % 8 = 0) (hV : V + 24 ≤ 4294967296)
    (hVs : V + 24 ≤ sp - 80 ∨ sp ≤ V)
    (hE : E < 18446744073709551616) (hn : n ≠ 0) (hn' : n < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat V)
    (sV8 : μ.readN (V + 8) 8 = Num.encodeLE 8 E) (sV16 : μ.readN (V + 16) 8 = Num.encodeLE 8 n)
    (hr : ∀ a, V + 8 ≤ a → a < V + 24 → μ.readable a = true)
    (hw : ∀ a, sp - 80 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 29087 ω μ x 29188 ω' μ' x 20 ∧
      ω'[1] = UInt64.ofNat (sp - 80) ∧ ω'[5] = UInt64.ofNat n ∧ ω'[6] = UInt64.ofNat 0 ∧
      μ'.readN (sp - 80 + 72) 8 = Num.encodeLE 8 ω[0].toNat ∧
      μ'.readN (sp - 80 + 64) 8 = Num.encodeLE 8 ω[5].toNat ∧
      μ'.readN (sp - 80 + 56) 8 = Num.encodeLE 8 ω[6].toNat ∧
      μ'.readN (sp - 80 + 40) 8 = Num.encodeLE 8 E ∧
      μ'.readN (sp - 80 + 32) 8 = Num.encodeLE 8 9223372036854775807 ∧
      μ'.readN (sp - 80 + 24) 8 = Num.encodeLE 8 9223372036854775832 ∧
      μ'.readN (sp - 80 + 16) 8 = Num.encodeLE 8 67760 ∧
      (∀ a, a < 4294967296 → (a < sp - 80 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hsp0, hsp1, hsp8⟩ := hsp
  have rE := rd8 hE sV8
  have rn := rd8 hn' sV16
  have hn0 : ¬ n = 0 := hn
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hsp0, hsp1, hsp8, hV, hVs, hn0, hr, hw, rE, rn, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, Nat.mod_eq_of_lt hn']
    post_simp

/-- 29188 … 29239 → 29181: element k at E + 232 k (kept at F + 48), of a variant whose drop does nothing
    (its first word 2^63 − 1 + t, `NoDrop t`), dispatches through the table at 67760 to 29181. -/
theorem dd {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (F E k t : Nat)
    (hF : 67856 ≤ F ∧ F + 80 ≤ 4294967296 ∧ F % 8 = 0) (ht : NoDrop t)
    (hEk : E + 232 * k + 8 ≤ 4294967296) (hEF : E + 232 * k + 8 ≤ F ∨ F + 80 ≤ E + 232 * k)
    (h1 : ω[1] = UInt64.ofNat F) (h6 : ω[6] = UInt64.ofNat k)
    (s40 : μ.readN (F + 40) 8 = Num.encodeLE 8 E) (s32 : μ.readN (F + 32) 8 = Num.encodeLE 8 9223372036854775807)
    (s24 : μ.readN (F + 24) 8 = Num.encodeLE 8 9223372036854775832) (s16 : μ.readN (F + 16) 8 = Num.encodeLE 8 67760)
    (hD : μ.readN (E + 232 * k) 8 = Num.encodeLE 8 (9223372036854775807 + t))
    (tab : μ.readN 67760 96 = dtable) (hrt : ∀ a, 67760 ≤ a → a < 67856 → μ.readable a = true)
    (hrE : ∀ a, E + 232 * k ≤ a → a < E + 232 * k + 8 → μ.readable a = true)
    (hw : ∀ a, F ≤ a → a < F + 80 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 29188 ω μ x 29181 ω' μ' x 20 ∧
      ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      (∀ a, a < 4294967296 → (a < F + 48 ∨ F + 56 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hF0, hF1, hF8⟩ := hF
  have hk : k < 18446744073709551616 := by omega
  have ht' : t < 24 := by unfold NoDrop at ht; omega
  have rE := rd8 (by omega) s40
  have r32 := rd8 (by decide) s32
  have r24 := rd8 (by decide) s24
  have r16 := rd8 (by decide) s16
  have rD0 := rd8 (by omega) hD
  have rD : rdN μ (k * 232 + E) 8 = 9223372036854775807 + t := by
    rw [show k * 232 + E = E + 232 * k by omega]; exact rD0
  have hrE' : ∀ a, k * 232 + E ≤ a → a < k * 232 + E + 8 → μ.readable a = true :=
    fun a h1 h2 => hrE a (by omega) (by omega)
  have hrt' : ∀ a, 67760 + 4 * t ≤ a → a < 67760 + 4 * t + 4 → μ.readable a = true :=
    fun a h1 h2 => hrt a (by omega) (by omega)
  have rt : rdN μ (67760 + 4 * t) 4 = 4294900892 := by
    show Num.decodeLE (μ.readN _ 4) = _
    rw [dtable_entry tab t ht']
    exact dtable_val t ht' ht
  have hr : ∀ a, F ≤ a → a < F + 80 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have e1 : (E + 232 * k) % 18446744073709551616 = E + 232 * k := Nat.mod_eq_of_lt (by omega)
  rw [show ω = regsNF ω [] from rfl]
  unfold NoDrop at ht
  rcases ht with h | h | h | h | h | h | h | h | h | h | h | h | h <;>
  subst h <;>
  · simp only [Nat.reduceMul, Nat.reduceAdd] at rt hrt' rD
    refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h6, hF0, hF1, hF8, hEk, hEF, hw, hr, hrE, hrE', rE, r32, r24, r16, rD, rt, hrt', sxw_noop, e1,
        rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
    · refine ⟨?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h6]
      post_simp

/-- 29181 … 29184: the next element: ω₆ := k + 1, and back to 29188 while k + 1 ≠ n. -/
theorem dn {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (k n : Nat)
    (hk : k + 1 < n) (hn : n < 18446744073709551616) (h5 : ω[5] = UInt64.ofNat n) (h6 : ω[6] = UInt64.ofNat k) :
    ∃ ω', FreeStepsH p R 29181 ω μ x 29188 ω' μ x 2 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧
      ω'[6] = UInt64.ofNat (k + 1) := by
  have hne : ¬ (k + 1) = n := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h5, h6, hk, hn, hne]
  · refine ⟨?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h5, h6]

/-- 29181 … 29673, after the last element (k + 1 = n): the frame at F is closed (ω₀, ω₅, ω₆ from F + 72,
    F + 64, F + 56) and the drop returns to the caller's return address `ret` (→ t). -/
theorem dl {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (F k n ret r5 r6 t : Nat)
    (hF : F + 80 < 4294967296) (hk : k + 1 = n) (hn : n < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat F) (h5 : ω[5] = UInt64.ofNat n) (h6 : ω[6] = UInt64.ofNat k)
    (s72 : μ.readN (F + 72) 8 = Num.encodeLE 8 ret) (s64 : μ.readN (F + 64) 8 = Num.encodeLE 8 r5)
    (s56 : μ.readN (F + 56) 8 = Num.encodeLE 8 r6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hr5 : r5 < 18446744073709551616)
    (hr6 : r6 < 18446744073709551616) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) (hr : ∀ a, F + 56 ≤ a → a < F + 80 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 29181 ω μ x t ω' μ x 10 ∧ ω'[0] = UInt64.ofNat ret ∧
      ω'[1] = UInt64.ofNat (F + 80) ∧ ω'[5] = UInt64.ofNat r5 ∧ ω'[6] = UInt64.ofNat r6 := by
  have rr := rd8 (by omega) s72
  have r5' := rd8 hr5 s64
  have r6' := rd8 hr6 s56
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, h6, hk, hn, hF, hr, rr, r5', r6', hret, hjt, hbt, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]

/-- **The output `Vec<Instruction>` dropped** (29087 … t): the slice of n ≥ 1 elements at E (from V + 8,
    V + 16), each of a variant whose drop does nothing, is walked and nothing is freed; the function returns
    to `ret` (→ t) with ω₁, ω₅, ω₆ as they were. Memory changes only in its frame [sp − 80, sp). -/
theorem drop_vec {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp V E n ret t : Nat) (hsp : 67856 + 80 ≤ sp ∧ sp < 4294967296 ∧ sp % 8 = 0) (hV : V + 24 ≤ 4294967296)
    (hVs : V + 24 ≤ sp - 80 ∨ sp ≤ V) (hn : 0 < n) (hEn : E + 232 * n ≤ 4294967296)
    (hEs : E + 232 * n ≤ sp - 80 ∨ sp ≤ E)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat V)
    (sV8 : μ.readN (V + 8) 8 = Num.encodeLE 8 E) (sV16 : μ.readN (V + 16) 8 = Num.encodeLE 8 n)
    (kinds : ∀ j, j < n → ∃ t, NoDrop t ∧ μ.readN (E + 232 * j) 8 = Num.encodeLE 8 (9223372036854775807 + t))
    (tab : μ.readN 67760 96 = dtable) (hrt : ∀ a, 67760 ≤ a → a < 67856 → μ.readable a = true)
    (hrV : ∀ a, V + 8 ≤ a → a < V + 24 → μ.readable a = true)
    (hrE : ∀ a, E ≤ a → a < E + 232 * n → μ.readable a = true)
    (hw : ∀ a, sp - 80 ≤ a → a < sp → μ.writable a = true)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) :
    ∃ ω' μ', FreeStepsH p R 29087 ω μ x t ω' μ' x (32 * n + 40) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      (∀ a, a < 4294967296 → (a < sp - 80 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hsp0, hsp1, hsp8⟩ := hsp
  have hE64 : E < 18446744073709551616 := by omega
  have hr0 : ω[0].toNat = ret := by rw [h0]; simp; omega
  obtain ⟨ω1, μ1, run1, a1, a5, a6, a72, a64, a56, a40, a32, a24, a16, afr, ard, awr⟩ := dh (p := p) (P := P)
    (R := R) x ω μ sp V E n ⟨by omega, hsp1, hsp8⟩ hV hVs hE64 (by omega) (by omega) h1 h7 sV8 sV16 hrV hw
  -- the element loop, from element k with the frame's words in place
  have loop : ∀ m k (ω2 : Regs) (μ2 : Memory), k + m = n → k < n → ω2[1] = UInt64.ofNat (sp - 80) →
      ω2[5] = UInt64.ofNat n → ω2[6] = UInt64.ofNat k →
      (∀ a, a < 4294967296 → (a < sp - 80 + 48 ∨ sp - 80 + 56 ≤ a) → μ2.read a = μ1.read a) →
      (∀ a, μ2.readable a = μ1.readable a) → (∀ a, μ2.writable a = μ1.writable a) →
      ∃ ω' μ', FreeStepsH p R 29188 ω2 μ2 x t ω' μ' x (32 * m + 10) ∧
        ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
        (∀ a, a < 4294967296 → (a < sp - 80 + 48 ∨ sp - 80 + 56 ≤ a) → μ'.read a = μ1.read a) ∧
        (∀ a, μ'.readable a = μ1.readable a) ∧ (∀ a, μ'.writable a = μ1.writable a) := by
    intro m
    induction m with
    | zero => intro k _ _ _ hkm hk; omega
    | succ m ih =>
      intro k ω2 μ2 hkm hk b1 b5 b6 bfr brd bwr
      have kr : ∀ a l, (a + l ≤ sp - 80 + 48 ∨ sp - 80 + 56 ≤ a) → a + l ≤ 4294967296 →
          μ2.readN a l = μ1.readN a l := fun a l h h' => Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))
      have k0 : ∀ a l, (a + l ≤ sp - 80 ∨ sp ≤ a) → a + l ≤ 4294967296 → μ1.readN a l = μ.readN a l :=
        fun a l h h' => Memory.readN_congr (fun j hj => afr _ (by omega) (by omega))
      obtain ⟨tk, htk, sD⟩ := kinds k hk
      obtain ⟨ω3, μ3, run3, c1, c5, c6, cfr, crd, cwr⟩ := dd (p := p) (P := P) (R := R) x ω2 μ2 (sp - 80) E k tk
        ⟨by omega, by omega, by omega⟩ htk (by omega) (by omega) b1 b6
        (by rw [kr _ _ (by omega) (by omega)]; exact a40) (by rw [kr _ _ (by omega) (by omega)]; exact a32)
        (by rw [kr _ _ (by omega) (by omega)]; exact a24) (by rw [kr _ _ (by omega) (by omega)]; exact a16)
        (by rw [kr _ _ (by omega) (by omega), k0 _ _ (by omega) (by omega)]; exact sD)
        (by rw [kr _ _ (by omega) (by omega), k0 _ _ (by omega) (by omega)]; exact tab)
        (fun a h1 h2 => by rw [brd, ard]; exact hrt a h1 h2)
        (fun a h1 h2 => by rw [brd, ard]; exact hrE a (by omega) (by omega))
        (fun a h1 h2 => by rw [bwr, awr]; exact hw a (by omega) (by omega))
      have e3 : ∀ a, a < 4294967296 → (a < sp - 80 + 48 ∨ sp - 80 + 56 ≤ a) → μ3.read a = μ1.read a :=
        fun a h0 h => by rw [cfr a h0 h, bfr a h0 h]
      by_cases hlast : k + 1 = n
      · obtain ⟨ω4, run4, d0, d1, d5, d6⟩ := dl (p := p) (P := P) (R := R) x ω3 μ3 (sp - 80) k n ret
          ω[5].toNat ω[6].toNat t (by omega) hlast (by omega) (c1.trans b1) (c5.trans b5) (c6.trans b6)
          (by rw [Memory.readN_congr (fun j hj => e3 _ (by omega) (by omega)), a72, hr0])
          (by rw [Memory.readN_congr (fun j hj => e3 _ (by omega) (by omega))]; exact a64)
          (by rw [Memory.readN_congr (fun j hj => e3 _ (by omega) (by omega))]; exact a56)
          hret (UInt64.toNat_lt _) (UInt64.toNat_lt _) hjt hbt
          (fun a h1 h2 => by rw [crd, brd, ard]; exact Memory.readable_of_writable (hw a (by omega) (by omega)))
        refine ⟨ω4, μ3, (run3.trans run4).mono (by omega), d0, by rw [d1]; congr 1; omega,
          by rw [d5]; simp, by rw [d6]; simp, e3, fun a => by rw [crd, brd], fun a => by rw [cwr, bwr]⟩
      · obtain ⟨ω4, run4, d1, d5, d6⟩ := dn (p := p) (P := P) (R := R) x ω3 μ3 k n (by omega) (by omega)
          (c5.trans b5) (c6.trans b6)
        obtain ⟨ω', μ', run', r0, r1, r5, r6, rfr, rrd, rwr⟩ := ih (k + 1) ω4 μ3 (by omega) (by omega)
          (by rw [d1, c1, b1]) (by rw [d5, c5, b5]) d6 e3 (fun a => by rw [crd, brd]) (fun a => by rw [cwr, bwr])
        exact ⟨ω', μ', ((run3.trans run4).trans run').mono (by omega), r0, r1, r5, r6, rfr, rrd, rwr⟩
  obtain ⟨ω', μ', run', r0, r1, r5, r6, rfr, rrd, rwr⟩ := loop n 0 ω1 μ1 (by omega) hn a1 a5 a6
    (fun a _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
  refine ⟨ω', μ', (run1.trans run').mono (by omega), r0, r1, r5, r6, fun a h0 h => ?_,
    fun a => by rw [rrd, ard], fun a => by rw [rwr, awr]⟩
  rw [rfr a h0 (by omega), afr a h0 h]

end Services.Bootstrap.Refine.DropOut
