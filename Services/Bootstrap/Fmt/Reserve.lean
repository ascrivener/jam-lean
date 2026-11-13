import Services.Bootstrap.Fmt.Tac

/-!
# The `String`'s growth: `RawVec::reserve` for octets

When `write_str` (59959) finds too little room, it goes to 60030. That calls
`do_reserve_and_handle` (58615) with the `String` W, its length and n more octets.
`do_reserve_and_handle` asks `finish_grow` (58717) for a new capacity:

  newcap = max(len + n, 8, 2 · cap)

`finish_grow` gets it through picoalloc's `alloc` wrapper (40494) when the capacity is 0, else
through its `realloc` wrapper (40701). On success, the new capacity and buffer go into W and the
run is back at 59989 (`write_str`'s copy). These are the steps between the calls:
- `rs1`: 60030 … 58615;
- `rs2`: 58615 … 58717;
- `rs3a`, `rs3r`: finish_grow to the alloc or realloc wrapper;
- `ret_alloc`, `ret_realloc`: the wrappers' returns;
- `rt_a`, `rt_r`, `rt`: finish_grow's success path and the way back.
-/

namespace Services.Bootstrap.Fmt

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}


/-- 60030 … 60044: src (ω₈) saved at S, then `do_reserve_and_handle` (58615) called with the
    `String` W, len and n, alignment and size 1, returning to 60050 (2600). -/
theorem rs1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (S W n len src : Nat) (hS : 65536 ≤ S ∧ S + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat n) (h6 : ω[6] = UInt64.ofNat W)
    (h8 : ω[8] = UInt64.ofNat src) (h9 : ω[9] = UInt64.ofNat len)
    (hb : W < 4294967296 ∧ n < 4294967296 ∧ len < 4294967296 ∧ src < 4294967296)
    (hw : ∀ a, S ≤ a → a < S + 8 → μ.writable a = true) :
    ∃ ω', FreeStepsH p R 60030 ω μ x 58615 ω' (μ.writeN S (Num.encodeLE 8 src)) x 7 ∧
      ω'[0] = UInt64.ofNat 2600 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat W ∧ ω'[8] = UInt64.ofNat len ∧ ω'[9] = UInt64.ofNat n ∧
      ω'[10] = UInt64.ofNat 1 ∧ ω'[11] = UInt64.ofNat 1 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, h6, h8, h9, hS, hw, hb]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp

/-- 58615 … 58664: `do_reserve_and_handle` opens a 56-octet frame at D = ω₁ − 56 (ω₀, ω₅, ω₆ at
    D + 48, D + 40, D + 32, W at D), computes len + n in ω₁₀ and reads cap (ω₈) and ptr (ω₉) from W;
    ω₆ = 8, the least nonzero capacity. -/
theorem rs2a {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (D W n len cap ptr r0 v5 v6 : Nat) (hD : 65536 ≤ D ∧ D + 56 < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat (D + 56)) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat W) (h8 : ω[8] = UInt64.ofNat len)
    (h9 : ω[9] = UInt64.ofNat n) (h10 : ω[10] = UInt64.ofNat 1) (h11 : ω[11] = UInt64.ofNat 1)
    (hb : W + 24 < 4294967296 ∧ len + n < 4294967296 ∧ cap < 4294967296 ∧ ptr < 18446744073709551616)
    (hb' : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616)
    (hWf : W + 24 ≤ D ∨ D + 56 ≤ W)
    (rc : rdN μ W 8 = cap) (rp : rdN μ (W + 8) 8 = ptr)
    (hWr : ∀ a, W ≤ a → a < W + 16 → μ.readable a = true)
    (hw : ∀ a, D ≤ a → a < D + 56 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 58615 ω μ x 58667 ω' μ' x 20 ∧
      ω'[1] = UInt64.ofNat D ∧ ω'[6] = UInt64.ofNat 8 ∧ ω'[8] = UInt64.ofNat cap ∧
      ω'[9] = UInt64.ofNat ptr ∧ ω'[10] = UInt64.ofNat (len + n) ∧ ω'[11] = UInt64.ofNat 1 ∧
      ω'[12] = UInt64.ofNat 1 ∧
      μ'.readN (D + 48) 8 = Num.encodeLE 8 r0 ∧ μ'.readN (D + 40) 8 = Num.encodeLE 8 v5 ∧
      μ'.readN (D + 32) 8 = Num.encodeLE 8 v6 ∧ μ'.readN D 8 = Num.encodeLE 8 W ∧
      (∀ a, a < 4294967296 → (a < D ∨ D + 56 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, D ≤ a → a < D + 56 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, h9, h10, h11, hD, hw, hr, hWr, hb, hb', hWf, rc, rp,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_,
      fun a => ?_⟩
    all_goals post_simp

/-- The new capacity `do_reserve_and_handle` asks for: max(len + n, 8, 2 · cap). Irreducible, so
    the stepping keeps it whole. -/
@[irreducible] def newcap (a c : Nat) : Nat := max (max a 8) (2 * c)

theorem newcap_ite (a c : Nat) :
    (if (if a ≤ 8 then 8 else a) ≤ 2 * c then 2 * c else if a ≤ 8 then 8 else a) = newcap a c := by
  unfold newcap; simp only [Nat.max_def] <;> (repeat' split) <;> omega

theorem newcap_ite' (a c : Nat) (ha : a < 4294967296) :
    (if (if a ≤ 8 then 8 else a) % 18446744073709551616 ≤ c * 2 then c * 2
      else (if a ≤ 8 then 8 else a) % 18446744073709551616) = newcap a c := by
  unfold newcap; simp only [Nat.max_def] <;> (repeat' split) <;> omega

theorem newcap_lt (a c : Nat) (ha : a < 4294967296) (hc : c < 4294967296) : newcap a c < 8589934592 := by
  unfold newcap; simp only [Nat.max_def] <;> (repeat' split) <;> omega

theorem newcap_ge (a c : Nat) : a ≤ newcap a c ∧ 8 ≤ newcap a c ∧ 2 * c ≤ newcap a c := by
  unfold newcap; simp only [Nat.max_def] <;> (repeat' split) <;> omega

/-- 58667 … 58756: newcap = max(len + n, 8, 2 · cap) into ω₅ and ω₁₀, then `finish_grow` (58717)
    called with its result slot D + 8 (return address 2558); it opens a 40-octet frame at F = D − 40
    (ω₀ = 2558, ω₅ = newcap, ω₆ = 8 at F + 32, F + 24, F + 16), keeps D + 8 in ω₆ and checks newcap
    against the layout limits, reaching 58759. -/
theorem rs2b {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (F len n cap : Nat) (hF : 65536 ≤ F ∧ F + 96 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat (F + 40)) (h6 : ω[6] = UInt64.ofNat 8) (h8 : ω[8] = UInt64.ofNat cap)
    (h10 : ω[10] = UInt64.ofNat (len + n)) (h12 : ω[12] = UInt64.ofNat 1)
    (hb : len + n < 4294967296 ∧ cap < 4294967296)
    (hw : ∀ a, F ≤ a → a < F + 40 → μ.writable a = true) :
    ∃ ω', FreeStepsH p R 58667 ω μ x 58759 ω'
      (((μ.writeN (F + 32) (Num.encodeLE 8 2558)).writeN (F + 24)
        (Num.encodeLE 8 (newcap (len + n) cap))).writeN (F + 16) (Num.encodeLE 8 8)) x 20 ∧
      ω'[1] = UInt64.ofNat F ∧ ω'[6] = UInt64.ofNat (F + 48) ∧ ω'[8] = ω[8] ∧ ω'[9] = ω[9] ∧
      ω'[10] = UInt64.ofNat (newcap (len + n) cap) ∧ ω'[11] = ω[11] ∧ ω'[12] = ω[12] := by
  have hr : ∀ a, F ≤ a → a < F + 40 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hm := newcap_ite (len + n) cap
  have hm' := newcap_ite' (len + n) cap hb.1
  have hm1 := newcap_lt (len + n) cap hb.1 hb.2
  have hm2 : newcap (len + n) cap / 18446744073709551616 = 0 := Nat.div_eq_of_lt (by omega)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h6, h8, h10, h12, hF, hw, hr, hb, hm, hm', hm1, hm2]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp

/-- 58759 … 58811, the old capacity 0: `finish_grow` saves the alignment 1 at F and newcap at
    F + 8 and calls the `alloc` wrapper (40494) for newcap octets at alignment 1, returning to 58817
    (2562). -/
theorem rs3a {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (F m : Nat) (hF : 65536 ≤ F ∧ F + 96 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat F) (h8 : ω[8] = UInt64.ofNat 0) (h10 : ω[10] = UInt64.ofNat m)
    (hm : 0 < m ∧ m < 4294967296)
    (hw : ∀ a, F ≤ a → a < F + 16 → μ.writable a = true) :
    ∃ ω', FreeStepsH p R 58759 ω μ x 40494 ω'
      ((μ.writeN F (Num.encodeLE 8 1)).writeN (F + 8) (Num.encodeLE 8 m)) x 10 ∧
      ω'[0] = UInt64.ofNat 2562 ∧ ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat m ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat m ∧ ω'[8] = UInt64.ofNat 1 := by
  have hr : ∀ a, F ≤ a → a < F + 16 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h8, h10, hF, hw, hr, hm, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try rw [rdN_one _ F (by omega)]
    all_goals post_simp [h1, h8, h10, hm]

/-- 58759 … 58775, an old capacity cap ≠ 0: `finish_grow` saves the alignment 1 at F and newcap at
    F + 8 and calls the `realloc` wrapper (40701) with the buffer ptr (ω₉ before), its size cap,
    alignment 1 and newcap, returning to 58781 (2560). -/
theorem rs3r {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (F cap ptr m : Nat) (hF : 65536 ≤ F ∧ F + 96 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat F) (h8 : ω[8] = UInt64.ofNat cap) (h9 : ω[9] = UInt64.ofNat ptr)
    (h10 : ω[10] = UInt64.ofNat m) (h11 : ω[11] = UInt64.ofNat 1)
    (hc : 0 < cap ∧ cap < 4294967296) (hp : ptr < 4294967296) (hm : m < 4294967296)
    (hw : ∀ a, F ≤ a → a < F + 16 → μ.writable a = true) :
    ∃ ω', FreeStepsH p R 58759 ω μ x 40701 ω'
      ((μ.writeN F (Num.encodeLE 8 1)).writeN (F + 8) (Num.encodeLE 8 m)) x 10 ∧
      ω'[0] = UInt64.ofNat 2560 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat ptr ∧ ω'[8] = UInt64.ofNat cap ∧ ω'[9] = UInt64.ofNat 1 ∧
      ω'[10] = UInt64.ofNat m := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h8, h9, h10, h11, hF, hw, hc, hp, hm]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, h8, h9, h10, h11, hc, hp, hm]

/-- The `alloc` wrapper's return (40611) to `finish_grow` (58817, 2562). -/
theorem ret_alloc {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (h0 : ω[0] = UInt64.ofNat 2562) : FreeStepsH p R 40611 ω μ x 58817 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0]

/-- The `realloc` wrapper's return (40821) to `finish_grow` (58781, 2560). -/
theorem ret_realloc {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (h0 : ω[0] = UInt64.ofNat 2560) : FreeStepsH p R 40821 ω μ x 58781 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0]

/-- 58817 … 58823: the `alloc` wrapper returned q ≠ 0; newcap reloaded from F + 8 into ω₁₀; on to
    58848. -/
theorem rt_a {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (F q m : Nat) (hF : 65536 ≤ F ∧ F + 96 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat F) (h7 : ω[7] = UInt64.ofNat q) (hq : 0 < q ∧ q < 4294967296)
    (rm : rdN μ (F + 8) 8 = m) (hr : ∀ a, F + 8 ≤ a → a < F + 16 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 58817 ω μ x 58848 ω' μ x 4 ∧
      ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = ω[7] ∧ ω'[10] = UInt64.ofNat m := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h7, hF, hq, rm, hr, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp

/-- 58781 … 58787: the `realloc` wrapper returned q ≠ 0; newcap reloaded from F + 8 into ω₁₀; on
    to 58848. -/
theorem rt_r {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (F q m : Nat) (hF : 65536 ≤ F ∧ F + 96 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat F) (h7 : ω[7] = UInt64.ofNat q) (hq : 0 < q ∧ q < 4294967296)
    (rm : rdN μ (F + 8) 8 = m) (hr : ∀ a, F + 8 ≤ a → a < F + 16 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 58781 ω μ x 58848 ω' μ x 4 ∧
      ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = ω[7] ∧ ω'[10] = UInt64.ofNat m := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h7, hF, hq, rm, hr, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp

/-- 58848 … 58876: `finish_grow` succeeded with q: `Ok` (0) at its result slot D + 8 (ω₆), q at
    D + 16 and newcap m at D + 24; ω₀, ω₅, ω₆ restored from F + 32, F + 24, F + 16, the frame closed,
    and the return to 58686 (2558). -/
theorem rt {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (F q m : Nat) (hF : 65536 ≤ F ∧ F + 96 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat F) (h6 : ω[6] = UInt64.ofNat (F + 48)) (h7 : ω[7] = UInt64.ofNat q)
    (h10 : ω[10] = UInt64.ofNat m) (hq : q < 4294967296) (hm : m < 4294967296)
    (r0 : rdN μ (F + 32) 8 = 2558) (r5 : rdN μ (F + 24) 8 = m) (r6 : rdN μ (F + 16) 8 = 8)
    (hw : ∀ a, F ≤ a → a < F + 72 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 58848 ω μ x 58686 ω' μ' x 12 ∧
      ω'[1] = UInt64.ofNat (F + 40) ∧ ω'[5] = UInt64.ofNat m ∧ ω'[6] = UInt64.ofNat 8 ∧
      rdN μ' (F + 48) 8 = 0 ∧ rdN μ' (F + 56) 8 = q ∧
      (∀ a, a < 4294967296 → (a < F + 48 ∨ F + 72 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, F ≤ a → a < F + 72 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, h7, h10, hF, hw, hr, hq, hm, r0, r5, r6, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try rw [rdN_zero _ (F + 48) (by omega)]
    all_goals post_simp [h1, rdN_writeN_disjoint, rdN_writeN_same8, Nat.mod_eq_of_lt (show q < 18446744073709551616 by omega)]

/-- 58686 … 58715, then 60050 … 60055: `do_reserve_and_handle` finds `Ok` at D + 8, stores newcap m
    (ω₅) and the buffer q (from D + 16) in the `String` W (from D), restores ω₀, ω₅, ω₆ from D + 48,
    D + 40, D + 32, closes its frame and returns to `write_str` (60050), which reloads src from
    S = D + 56 and the length from W + 16 and goes to its copy (59989). -/
theorem rt2 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (D W q m n src len : Nat) (hD : 65536 ≤ D ∧ D + 96 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat D) (h5 : ω[5] = UInt64.ofNat m) (hq : q < 4294967296)
    (hm : m < 4294967296) (hn : n < 4294967296) (hsrc : src < 4294967296)
    (hW : W + 24 < 4294967296) (hWf : W + 24 ≤ D ∨ D + 64 ≤ W)
    (r8 : rdN μ (D + 8) 8 = 0) (r16 : rdN μ (D + 16) 8 = q) (rW : rdN μ D 8 = W)
    (r0 : rdN μ (D + 48) 8 = 2600) (r5 : rdN μ (D + 40) 8 = n) (r6 : rdN μ (D + 32) 8 = W)
    (rs : rdN μ (D + 56) 8 = src) (rl : rdN μ (W + 16) 8 = len)
    (hr : ∀ a, D ≤ a → a < D + 64 → μ.readable a = true)
    (hWw : ∀ a, W ≤ a → a < W + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 58686 ω μ x 59989 ω' μ' x 20 ∧
      rdN μ' W 8 = m ∧ rdN μ' (W + 8) 8 = q ∧ rdN μ' (W + 16) 8 = len ∧
      (∀ a, a < 4294967296 → (a < W ∨ W + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      ω'[0] = UInt64.ofNat 2600 ∧ ω'[1] = UInt64.ofNat (D + 56) ∧ ω'[5] = UInt64.ofNat n ∧
      ω'[6] = UInt64.ofNat W ∧ ω'[8] = UInt64.ofNat src ∧ ω'[9] = UInt64.ofNat len := by
  have hWr : ∀ a, W ≤ a → a < W + 24 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hWw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hD, hr, hq, hm, hn, hsrc, hW, hWf, r8, r16, rW, r0, r5, r6, rs, rl, hWw, hWr,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, rdN_writeN_disjoint, rdN_writeN_same8, rl]

end Services.Bootstrap.Fmt
