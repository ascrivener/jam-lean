import Services.Bootstrap.Acc.Handlers.RecentSlotWriteImpl

/-!
# `add_recent_work_item`'s counter read: the straight-line segments (8013 … 8056)

Spec `addRecent`'s `(← load .counter (Dec.fixedN 4)).getD 0` (GP v0.8.0 Appendix B, Ω_R; quirk Q12):
1. 8013 … 8046: the key value `RecentWorkItemCounter` (the `u16` 0) at sp + 1568, a callee frame at
   T = sp − 80 (ω₀ = 278, ω₅, ω₆ saved), and the key encoder (33843) with out T + 32 (return address
   1610 → 34637);
2. 34637 … 34648: `get` (47857) of the key, out T + 8 (return address 1612 → 34654);
3. 34654 … 34665: `dealloc` of the key's buffer (1614 → 34671);
4. 34671: `None` → ω₇ := 0 and the return (34755 … 34770); `Some(Vec { cap, ptr, len })` → the slice
   reader {ptr, len} at T + 32 and `read_exact` (58434) of 4 octets into T + 8 (1616 → 34711);
5. 34711 … 34753: ω₈ := the `i32` at T + 8, ω₆ := 1 if the read succeeded; `dealloc` of the value's
   buffer if cap ≠ 0 (1618 → 34735); the return (ω₀ = 278 → 8049) with ω₇ = ω₆;
6. 8049 … 8054: ω₅ := ω₈, or 0 if ω₇'s low bit is 0.
-/

namespace Services.Bootstrap.Acc.Handlers.RecentCounterGet

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.Alloc Services.Bootstrap.Acc Services.Bootstrap.Spec
  Services.Bootstrap.Acc.Handlers.KeyEnc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **8013 … 8046**: the `u16` 0 at sp + 1568; the frame at sp − 80 (ω₀ = 278 at sp − 8, ω₅ and ω₆ at
    sp − 16 and sp − 24); the key encoder (33843) with out ω₇ = sp − 48, the key value ω₈ = sp + 1568 and
    return address 1610. -/
theorem cg_pre {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : 68712 + 80 ≤ sp ∧ sp + 1604 < 4294967296)
    (hw1 : ∀ a, sp - 80 ≤ a → a < sp → μ.writable a = true)
    (hw2 : ∀ a, sp + 1568 ≤ a → a < sp + 1570 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 8013 ω μ x 33843 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 1610 ∧ ω'[1] = UInt64.ofNat (sp - 80) ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (sp - 48) ∧ ω'[8] = UInt64.ofNat (sp + 1568) ∧
      μ'.readN (sp + 1568) 2 = Num.encodeLE 2 0 ∧ μ'.readN (sp - 8) 8 = Num.encodeLE 8 278 ∧
      μ'.readN (sp - 16) 8 = Num.encodeLE 8 ω[5].toNat ∧ μ'.readN (sp - 24) 8 = Num.encodeLE 8 ω[6].toNat ∧
      (∀ a, a < 4294967296 → (a < sp - 80 ∨ sp ≤ a) → (a < sp + 1568 ∨ sp + 1570 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 80 ≤ a → a < sp → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw1 a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hsp, hw1, hw2, hr, bs_33843, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨by reg_val, ?_, by reg_val, by reg_val, by reg_val, by reg_val, ?_, ?_, ?_, ?_,
      fun a ha h1' h2' => ?_, fun a => ?_, fun a => ?_⟩
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some', h1,
        List.lookup_nil, Option.getD_none]
    all_goals try rw [show sp - 80 + 72 = sp - 8 by omega, show sp - 80 + 64 = sp - 16 by omega,
      show sp - 80 + 56 = sp - 24 by omega]
    all_goals try simp only [PVM.getElem_regsNF, List.lookup_nil, Option.getD_none]
    all_goals try rd_simp []
    all_goals try rfl
    all_goals try (congr 1; omega)

/-- **34637 … 34648**: the key's `Vec { kc, kp, len }` at T + 32: kp in ω₅, the call of `get` (47857)
    with out ω₇ = T + 8, the key ω₈ = kp (ω₉ = len octets) and return address 1612. Memory is kept. -/
theorem cg_g {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (T kp len : Nat) (h1 : ω[1] = UInt64.ofNat T) (hT : T + 80 < 4294967296)
    (hkp : kp < 2 ^ 64) (hlen : len < 2 ^ 64)
    (mp : μ.readN (T + 40) 8 = Num.encodeLE 8 kp) (ml : μ.readN (T + 48) 8 = Num.encodeLE 8 len)
    (hr : ∀ a, T + 40 ≤ a → a < T + 56 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 34637 ω μ x 47857 ω' μ x 5 ∧
      ω'[0] = UInt64.ofNat 1612 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[5] = UInt64.ofNat kp ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (T + 8) ∧ ω'[8] = UInt64.ofNat kp ∧ ω'[9] = UInt64.ofNat len := by
  have rp := Handlers.DesignateAlloc.rd8 hkp mp
  have rl := Handlers.DesignateAlloc.rd8 hlen ml
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hT, rp, rl, hr, bs_47857, ↓rdN_fold]
  · refine ⟨by reg_val, ?_, by reg_val, by reg_val, by reg_val, by reg_val, by reg_val⟩
    simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some', h1,
      List.lookup_nil, Option.getD_none]

/-- **`get`'s returns** (the `jumpInd` at 47927, 47957 or 48102) with ω₀ = 1612: on to 34654. -/
theorem cg_gret {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (e : Nat) (he : e = 47927 ∨ e = 47957 ∨ e = 48102) (h0 : ω[0] = UInt64.ofNat 1612) :
    FreeStepsH p R e ω μ x 34654 ω μ x 1 := by
  rcases he with rfl | rfl | rfl
  all_goals
    rw [show ω = regsNF ω [] from rfl]
    pvm_go [h0]

/-- **34654 … 34665**, the key's capacity kc ≠ 0 (at T + 32): the call of `dealloc` (40613) with
    ω₇ = ω₅ (the key's buffer) and return address 1614. Memory is kept. -/
theorem cg_dk {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (T kc : Nat) (h1 : ω[1] = UInt64.ofNat T) (hT : T + 80 < 4294967296)
    (hkc : kc < 2 ^ 64) (hk0 : kc ≠ 0) (mk : μ.readN (T + 32) 8 = Num.encodeLE 8 kc)
    (hr : ∀ a, T + 32 ≤ a → a < T + 40 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 34654 ω μ x 40613 ω' μ x 5 ∧
      ω'[0] = UInt64.ofNat 1614 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = ω[5] := by
  have rk := Handlers.DesignateAlloc.rd8 hkc mk
  have hk0' : kc % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt hkc]; exact hk0
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hT, rk, hk0', hr, ↓rdN_fold]
  · refine ⟨by reg_val, ?_, by reg_val, by reg_val, ?_⟩
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some', h1,
        List.lookup_nil, Option.getD_none]
    · simp [PVM.getElem_regsNF, PVM.lookup_cons_nat]

/-- **34671 … 34770 and 8049 … 8054, `None`** (the word −1 at T + 8): ω₇ := 0, ω₀, ω₅, ω₆ restored from
    T + 72, T + 64, T + 56, the frame popped, the return (278 → 8049), and ω₅ := 0. -/
theorem cg_none {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (T v6 : Nat) (h1 : ω[1] = UInt64.ofNat T) (hT : T + 80 < 4294967296) (hv6 : v6 < 2 ^ 64)
    (m8 : μ.readN (T + 8) 8 = Num.encodeLE 8 18446744073709551615)
    (m0 : μ.readN (T + 72) 8 = Num.encodeLE 8 278) (m6 : μ.readN (T + 56) 8 = Num.encodeLE 8 v6)
    (hr : ∀ a, T ≤ a → a < T + 80 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 34671 ω μ x 8056 ω' μ x 12 ∧
      ω'[1] = UInt64.ofNat (T + 80) ∧ ω'[5] = UInt64.ofNat 0 ∧ ω'[6] = UInt64.ofNat v6 := by
  have r8 := Handlers.DesignateAlloc.rd8 (by decide) m8
  have r0 := Handlers.DesignateAlloc.rd8 (by decide) m0
  have r6 := Handlers.DesignateAlloc.rd8 hv6 m6
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hT, r8, r0, r6, hr, ↓rdN_fold]
  · refine ⟨?_, by reg_val, by reg_val⟩
    all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1]
    all_goals try (congr 1; omega)

/-- **34671 … 34705, `Some(Vec { cap, ptr, len })`** (at T + 8, cap ≠ −1): cap in ω₅, ptr at T, the slice
    reader {ptr, len} at T + 32, the `u32` 0 at T + 8, and the call of `read_exact` (58434) with
    ω₇ = T + 32, ω₈ = T + 8, ω₉ = 4 and return address 1616. -/
theorem cg_some {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (T cap ptr len : Nat) (h1 : ω[1] = UInt64.ofNat T) (hT : T + 80 < 4294967296)
    (hcap : cap < 2 ^ 64) (hc1 : cap ≠ 18446744073709551615) (hptr : ptr < 2 ^ 64) (hlen : len < 2 ^ 64)
    (mc : μ.readN (T + 8) 8 = Num.encodeLE 8 cap) (mp : μ.readN (T + 16) 8 = Num.encodeLE 8 ptr)
    (ml : μ.readN (T + 24) 8 = Num.encodeLE 8 len)
    (hw : ∀ a, T ≤ a → a < T + 48 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 34671 ω μ x 58434 ω' μ' x 13 ∧
      ω'[0] = UInt64.ofNat 1616 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[5] = UInt64.ofNat cap ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (T + 32) ∧ ω'[8] = UInt64.ofNat (T + 8) ∧ ω'[9] = UInt64.ofNat 4 ∧
      μ'.readN T 8 = Num.encodeLE 8 ptr ∧ μ'.readN (T + 32) 8 = Num.encodeLE 8 ptr ∧
      μ'.readN (T + 40) 8 = Num.encodeLE 8 len ∧
      (∀ a, a < 4294967296 → (a < T ∨ T + 48 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, T ≤ a → a < T + 48 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have qc := Handlers.DesignateAlloc.rd8 hcap mc
  have qp := Handlers.DesignateAlloc.rd8 hptr mp
  have ql := Handlers.DesignateAlloc.rd8 hlen ml
  have hc1' : cap % 18446744073709551616 ≠ 18446744073709551615 := by rw [Nat.mod_eq_of_lt hcap]; exact hc1
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hT, qc, qp, ql, hc1', hr, hw, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [h1, Nat.mod_eq_of_lt hptr, Nat.mod_eq_of_lt hlen, Nat.mod_eq_of_lt hcap]

/-- **34711 … 34770 and 8049 … 8054, cap = 0** (no buffer to free): ω₈ := the `i32` at T + 8 (sign-extended
    from v), ω₆ := ω₇ xor 1, the return (278 → 8049) with ω₇ = ω₆, and ω₅ := ω₈ if ω₇'s low bit is 1,
    else 0. -/
theorem cg_fin0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (T v ok v6 : Nat) (h1 : ω[1] = UInt64.ofNat T) (h5 : ω[5] = UInt64.ofNat 0)
    (h7 : ω[7] = UInt64.ofNat ok) (hok : ok = 0 ∨ ok = 1) (hT : T + 80 < 4294967296) (hv6 : v6 < 2 ^ 64)
    (mv : μ.readN (T + 8) 4 = Num.encodeLE 4 v) (hv : v < 2 ^ 32)
    (m0 : μ.readN (T + 72) 8 = Num.encodeLE 8 278) (m6 : μ.readN (T + 56) 8 = Num.encodeLE 8 v6)
    (hr : ∀ a, T ≤ a → a < T + 80 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 34711 ω μ x 8056 ω' μ x 13 ∧ ω'[1] = UInt64.ofNat (T + 80) ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[5].toNat % 4294967296 = (if ok = 0 then v else 0) := by
  have rv : rdN μ (T + 8) 4 = v := by
    show Num.decodeLE _ = _; rw [mv, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hv]
  have r0 := Handlers.DesignateAlloc.rd8 (by decide) m0
  have r6 := Handlers.DesignateAlloc.rd8 hv6 m6
  rw [show ω = regsNF ω [] from rfl]
  rcases hok with rfl | rfl
  all_goals
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h5, h7, hT, rv, r0, r6, hr, ↓rdN_fold]
    · refine ⟨?_, by reg_val, ?_⟩
      all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1, Num.sext]
      all_goals try (congr 1; omega)
      all_goals try omega

/-- **34711 … 34729, cap ≠ 0** (ω₅): ω₈ := the `i32` at T + 8 (from v, sign-extended to sv), ω₆ := 1 if the
    read succeeded (ω₇ = ok = 0), else 0; sv saved at T and the call of `dealloc` (40613) with ω₇ = the
    value's buffer (the word ptr at T) and return address 1618. -/
theorem cg_finD {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (T v ok cap ptr : Nat) (h1 : ω[1] = UInt64.ofNat T) (h5 : ω[5] = UInt64.ofNat cap)
    (h7 : ω[7] = UInt64.ofNat ok) (hok : ok = 0 ∨ ok = 1) (hT : T + 80 < 4294967296)
    (hcap : cap < 2 ^ 64) (hc0 : cap ≠ 0) (hptr : ptr < 2 ^ 64)
    (mv : μ.readN (T + 8) 4 = Num.encodeLE 4 v) (hv : v < 2 ^ 32) (mp : μ.readN T 8 = Num.encodeLE 8 ptr)
    (hw : ∀ a, T ≤ a → a < T + 16 → μ.writable a = true) :
    ∃ ω' μ' sv, FreeStepsH p R 34711 ω μ x 40613 ω' μ' x 8 ∧
      ω'[0] = UInt64.ofNat 1618 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[5] = ω[5] ∧
      ω'[6] = UInt64.ofNat (if ok = 0 then 1 else 0) ∧ ω'[7] = UInt64.ofNat ptr ∧
      sv < 2 ^ 64 ∧ sv % 4294967296 = v ∧ μ'.readN T 8 = Num.encodeLE 8 sv ∧
      (∀ a, a < 4294967296 → (a < T ∨ T + 8 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, T ≤ a → a < T + 16 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have rv : rdN μ (T + 8) 4 = v := by
    show Num.decodeLE _ = _; rw [mv, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hv]
  have rp := Handlers.DesignateAlloc.rd8 hptr mp
  have hc0' : cap % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt hcap]; exact hc0
  rw [show ω = regsNF ω [] from rfl]
  rcases hok with rfl | rfl
  all_goals
    refine ⟨?_, ?_, ((if v < 2147483648 then (v : Int) else (v : Int) - 4294967296) % 18446744073709551616).toNat,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h5, h7, hT, rv, rp, hc0', hr, hw, rdN_writeN_disjoint, ↓rdN_fold]
    all_goals try (simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1, h5]; done)
    all_goals try (split <;> omega)
    all_goals try (intro a ha h1'; rd_simp [])
    all_goals try (intro a; simp)
    all_goals try (rd_simp []; done)
    all_goals try rfl

/-- **34735 … 34770 and 8049 … 8054**, after the value's buffer is freed: ω₈ := sv (the word at T), the return
    (278 → 8049) with ω₇ = ω₆ = b, and ω₅ := sv if b's low bit is 1, else 0. -/
theorem cg_finR {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (T sv b v6 : Nat) (h1 : ω[1] = UInt64.ofNat T) (h6 : ω[6] = UInt64.ofNat b)
    (hb : b = 0 ∨ b = 1) (hT : T + 80 < 4294967296) (hsv : sv < 2 ^ 64) (hv6 : v6 < 2 ^ 64)
    (ms : μ.readN T 8 = Num.encodeLE 8 sv)
    (m0 : μ.readN (T + 72) 8 = Num.encodeLE 8 278) (m6 : μ.readN (T + 56) 8 = Num.encodeLE 8 v6)
    (hr : ∀ a, T ≤ a → a < T + 80 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 34735 ω μ x 8056 ω' μ x 12 ∧ ω'[1] = UInt64.ofNat (T + 80) ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[5] = UInt64.ofNat (if b = 1 then sv else 0) := by
  have rs := Handlers.DesignateAlloc.rd8 hsv ms
  have r0 := Handlers.DesignateAlloc.rd8 (by decide) m0
  have r6 := Handlers.DesignateAlloc.rd8 hv6 m6
  rw [show ω = regsNF ω [] from rfl]
  rcases hb with rfl | rfl
  all_goals
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h6, hT, rs, r0, r6, hr, ↓rdN_fold]
    all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1, Nat.mod_eq_of_lt hsv]
    all_goals try (congr 1; omega)

end Services.Bootstrap.Acc.Handlers.RecentCounterGet
