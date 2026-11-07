import Services.Bootstrap.Alloc.ReallocEntry

/-!
# The binary's `grow_inplace`: the checks

`realloc_impl`'s inlined `grow_inplace` (43169 …), for a request `req` above the usable size
(n = req + 1 > cur units): the old next chunk nc = X + 32·cur must be below the heap's end, free,
and with `sz` units enough (`cur + sz ≥ n`); otherwise the fallback (43259: `alloc_impl`, copy,
free). Then the allocation's new end against the allocated space, and the bin of nc.

The frame (sp = the caller's sp − 152): X at sp + 120 and sp + 88, n at sp + 112, the heap's end at
sp + 96, nc at sp + 80 and sp + 56, sz at sp + 40, nc's size word at sp + 48, `cur + sz` at sp + 72,
X + 32·n at sp + 64.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

theorem bitwise_xor_lxor (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    Exec.bitwise (· ^^ ·) a b = a ^^^ b := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Exec.bitwise, Num.testBit_ofBits, Num.bit_eq_testBit, Nat.testBit_xor]
  by_cases hi : i < 64
  · simp [hi]
  · have h1 : a.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))
    have h2 : b.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [hi, h1, h2]

/-- The tail test: `(a xor b) > 0` is `a ≠ b`. -/
theorem xor_pos (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (if Exec.bitwise (· ^^ ·) a b % 18446744073709551616 > 0 then 1 else 0) = (if a - b = 0 ∧ b - a = 0 then 0 else 1) := by
  rw [bitwise_xor_lxor a b ha hb, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow ha hb)]
  by_cases h : a = b
  · subst h; simp
  · have : a ^^^ b ≠ 0 := fun h0 => h (by have := congrArg (· ^^^ b) h0; simpa [Nat.xor_assoc] using this)
    rw [if_pos (by omega), if_neg (by omega)]

/-- **43169 … 43224**: the chunk X = ptr − 32 of `cur` units (size word 2·cur + 1) and n > cur:
    ω₀ = X + 32·cur (the old next chunk), ω₄ = the heap's end, ω₂ = the base, ω₁₂ = cur, ω₅ = X;
    X saved at sp + 120 and sp + 88, n at sp + 112, the end at sp + 96. -/
theorem rg_pre {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp ptr req cur base : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr)
    (h10 : ω[10] = UInt64.ofNat req) (h5 : ω[5] = UInt64.ofNat (req + 1)) (h3 : ω[3] = UInt64.ofNat 204984)
    (hp : 206896 ≤ ptr) (hw : rdN μ (ptr - 32 + 4) 4 = 2 * cur + 1) (hn : cur < req + 1) (hr : req < 2147483647)
    (hb : rdN μ 206520 8 = base) (hbT : base + 1073741824 < 2147483648) (hpc : ptr - 32 + 32 * cur < 2147483648)
    (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296) (hwr : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 43169 ω μ x 43224 ω' μ' x 18 ∧
      ω'[0] = UInt64.ofNat (ptr - 32 + 32 * cur) ∧ ω'[4] = UInt64.ofNat (base + 1073741824) ∧
      ω'[2] = UInt64.ofNat base ∧ ω'[12] = UInt64.ofNat cur ∧ ω'[5] = UInt64.ofNat (ptr - 32) ∧
      rdN μ' (sp + 120) 8 = ptr - 32 ∧ rdN μ' (sp + 88) 8 = ptr - 32 ∧ rdN μ' (sp + 112) 8 = req + 1 ∧
      rdN μ' (sp + 96) 8 = base + 1073741824 ∧
      (∀ a, a < 4294967296 → (a < sp + 88 ∨ sp + 128 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) ∧
      ∀ j : Fin 13, j.val ∉ [0, 2, 4, 5, 11, 12] → ω'[j] = ω[j] := by
  have hr' : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hwr a)
  have hb64 : base < 18446744073709551616 := by omega
  have ha : (ptr + 18446744073709551584) % 18446744073709551616 = ptr - 32 := by omega
  have hne : req ≠ 18446744073709551615 := by omega
  have hc : ¬ req + 1 ≤ cur := by omega
  have hb' : rdN μ (204984 + 1536) 8 = base := hb
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h8, h10, h5, h3, ha, hne, hw, hb', hc, hwr, hr', rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, by reg_val, by reg_val, ?_, by reg_val, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, by reg_frame⟩
    · reg_get; rw [show (2 * cur + 1) / 2 * 32 + (ptr - 32) = ptr - 32 + 32 * cur by omega]
    · reg_get; rw [show (2 * cur + 1) / 2 = cur by omega]
    · rd_simp []; simp only [Nat.reducePow, Nat.reduceMul]; omega
    · rd_simp []; simp only [Nat.reducePow, Nat.reduceMul]; omega
    · rd_simp []; simp only [Nat.reducePow, Nat.reduceMul]; omega
    · rd_simp []; simp only [Nat.reducePow, Nat.reduceMul]; omega
    · rd_simp []
    · rd_simp [hwr]

/-- 43224: the old next chunk at or past the heap's end, to the fallback (43259). -/
theorem rg_br_end {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (a b : Nat) (h0 : ω[0] = UInt64.ofNat a) (h4 : ω[4] = UInt64.ofNat b) (hab : b ≤ a)
    (ha : a < 2147483648) (hb : b < 2147483648) :
    FreeStepsH p R 43224 ω μ x 43259 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0, h4, hab]

/-- 43224: below the heap's end, to 43227. -/
theorem rg_br_in {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (a b : Nat) (h0 : ω[0] = UInt64.ofNat a) (h4 : ω[4] = UInt64.ofNat b) (hab : a < b)
    (ha : a < 2147483648) (hb : b < 2147483648) :
    FreeStepsH p R 43224 ω μ x 43227 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0, h4, hab]

/-- **43227 … 43243**: the old next chunk nc's size word w: ω₅ = w, ω₁₁ = its used bit; nc saved
    at sp + 80. -/
theorem rg_nhdr {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp nc w : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h0 : ω[0] = UInt64.ofNat nc) (hnc : nc < 2147483648)
    (hw : rdN μ (nc + 4) 4 = w)
    (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296) (hwr : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 43227 ω μ x 43243 ω' μ' x 6 ∧ ω'[5] = UInt64.ofNat w ∧
      ω'[11] = UInt64.ofNat (w % 2) ∧ rdN μ' (sp + 80) 8 = nc ∧
      (∀ a, a < 4294967296 → (a < sp + 80 ∨ sp + 88 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) ∧ ∀ j : Fin 13, j.val ∉ [5, 11] → ω'[j] = ω[j] := by
  have hr : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hwr a)
  have hw32 : w < 4294967296 := by rw [← hw]; exact rdN_lt μ _ 4
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h0, hw, hwr, hr, rdN_writeN_disjoint, ↓rdN_fold]
  case post =>
    refine ⟨by reg_val, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, by reg_frame⟩
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some',
        PVM.bitwise_and_m1]
    · rd_simp []; simp only [Nat.reducePow, Nat.reduceMul]; omega
    · rd_simp []
    · rd_simp [hwr]

/-- 43243, the old next chunk allocated: to the fallback (43259). -/
theorem rg_br_used {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (c : Nat) (h11 : ω[11] = UInt64.ofNat c) (hc : c ≠ 0) (hc2 : c < 2) :
    FreeStepsH p R 43243 ω μ x 43259 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h11, hc]

/-- 43243, the old next chunk free: to 43246. -/
theorem rg_br_free {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (h11 : ω[11] = UInt64.ofNat 0) :
    FreeStepsH p R 43243 ω μ x 43246 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h11]

/-- **43246 … 43375**, the old next chunk free with sz units (size word 2·sz in ω₅) and
    cur + sz ≥ n (n at sp + 112): ω₄ = sz, ω₁₂ = cur + sz, ω₁₁ = n; to the growth. -/
theorem rg_avail_ok {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp cur sz n : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat (2 * sz))
    (h12 : ω[12] = UInt64.ofNat cur) (h112 : rdN μ (sp + 112) 8 = n) (hge : n ≤ cur + sz)
    (hcs : cur + sz < 2147483648) (hsz : sz < 2147483648) (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296)
    (hr : ∀ a, μ.readable a = true) :
    ∃ ω', FreeStepsH p R 43246 ω μ x 43375 ω' μ x 5 ∧ ω'[4] = UInt64.ofNat sz ∧
      ω'[12] = UInt64.ofNat (cur + sz) ∧ ω'[11] = UInt64.ofNat n ∧
      ∀ j : Fin 13, j.val ∉ [4, 11, 12] → ω'[j] = ω[j] := by
  have hn : n < 18446744073709551616 := by rw [← h112]; exact rdN_lt64 μ _
  have hsh : 2 * sz / 2 = sz := by omega
  have hadd : (sz + cur) % 4294967296 = cur + sz := by omega
  have hge' : n ≤ cur + sz := hge
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, h5, h12, h112, hsh, hadd, hge', hr, ↓rdN_fold]
  case post => refine ⟨by reg_val, by reg_val, by reg_val, by reg_frame⟩

/-- **43246 … 43259**, the old next chunk free but too small (cur + sz < n): to the fallback. -/
theorem rg_avail_lt {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp cur sz n : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat (2 * sz))
    (h12 : ω[12] = UInt64.ofNat cur) (h112 : rdN μ (sp + 112) 8 = n) (hlt : cur + sz < n)
    (hn : n < 2147483648) (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296)
    (hr : ∀ a, μ.readable a = true) :
    ∃ ω', FreeStepsH p R 43246 ω μ x 43259 ω' μ x 5 ∧ ∀ j : Fin 13, j.val ∉ [4, 11, 12] → ω'[j] = ω[j] := by
  have hsh : 2 * sz / 2 = sz := by omega
  have hadd : (sz + cur) % 4294967296 = cur + sz := by omega
  have hlt' : ¬ n ≤ cur + sz := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, h5, h12, h112, hsh, hadd, hlt', hr, ↓rdN_fold]
  case post => exact by reg_frame

/-- **43375 … 43421**: the allocation's new end, in units past the base:
    E = (X + 32·n − base)/32 + (1 if a tail remains); ω₅ = the allocated space; the frame
    (sz, nc's size word, nc, cur + sz, X + 32·n) saved. -/
theorem rg_end {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp ptr n cur sz nc w base al : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr)
    (h4 : ω[4] = UInt64.ofNat sz) (h5 : ω[5] = UInt64.ofNat w) (h0 : ω[0] = UInt64.ofNat nc)
    (h12 : ω[12] = UInt64.ofNat (cur + sz)) (h112 : rdN μ (sp + 112) 8 = n) (h2 : ω[2] = UInt64.ofNat base)
    (h3 : ω[3] = UInt64.ofNat 204984) (hal : rdN μ 206840 4 = al) (hal1 : al < 2147483648)
    (hp : 32 + base ≤ ptr) (hX : ptr - 32 + 32 * n < 2147483648) (hn : n ≤ cur + sz)
    (hcs : cur + sz < 2147483648) (hw : w < 4294967296) (hnc : nc < 2147483648)
    (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296) (hwr : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 43375 ω μ x 43421 ω' μ' x 18 ∧
      ω'[11] = UInt64.ofNat ((ptr - 32 + 32 * n - base) / 32 + (if cur + sz - n = 0 then 0 else 1)) ∧
      ω'[5] = UInt64.ofNat al ∧
      rdN μ' (sp + 40) 8 = sz ∧ rdN μ' (sp + 48) 8 = w ∧ rdN μ' (sp + 56) 8 = nc ∧
      rdN μ' (sp + 72) 8 = cur + sz ∧ rdN μ' (sp + 64) 8 = ptr - 32 + 32 * n ∧
      (∀ a, a < 4294967296 → (a < sp + 40 ∨ sp + 80 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) ∧ ∀ j : Fin 13, j.val ∉ [4, 5, 11, 12] → ω'[j] = ω[j] := by
  have hr : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hwr a)
  have hsx : sxw 4 al = al := sxw4_small hal1
  have hal' : rdN μ (204984 + 1856) 4 = al := hal
  have ha : (ptr + 18446744073709551584) % 18446744073709551616 = ptr - 32 := by omega
  have hif : (if Exec.bitwise (· ^^ ·) (cur + sz) n % 18446744073709551616 > 0 then 1 else 0) =
      (if cur + sz - n = 0 then 0 else 1) := by
    rw [xor_pos (cur + sz) n (by omega) (by omega)]; split <;> split <;> omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h8, h4, h5, h0, h12, h112, h2, h3, hal', hsx, ha, hwr, hr, rdN_writeN_disjoint,
    ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, by reg_val, ?_, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, by reg_frame⟩
    · reg_get
      rw [hif, show ((ptr - 32 + n * 32 - base) / 32 + (if cur + sz - n = 0 then 0 else 1) % 18446744073709551616) %
          18446744073709551616 = (ptr - 32 + 32 * n - base) / 32 + (if cur + sz - n = 0 then 0 else 1) by
        split <;> omega]
    all_goals try (rd_simp []; simp only [Nat.reducePow, Nat.reduceMul]; omega)
    · rd_simp []
    · rd_simp [hwr]

/-- 43421: the allocated space covers the new end E, to 43504 (no growth). -/
theorem rg_nogrow {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (al E : Nat) (h5 : ω[5] = UInt64.ofNat al) (h11 : ω[11] = UInt64.ofNat E) (hle : E ≤ al)
    (hal : al < 2147483648) (hE : E < 2147483648) :
    FreeStepsH p R 43421 ω μ x 43504 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h5, h11, hle]

/-- **43504 … 43910**, the old next chunk of 1 … 127 units (size word 2·sz at sp + 48, sz at
    sp + 40): ω₁₀ = its bin sz − 1, ω₅ = n (sp + 112), ω₂ = X + 32·n (sp + 64). -/
theorem rg_bin_small {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp sz n N : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h40 : rdN μ (sp + 40) 8 = sz)
    (h48 : rdN μ (sp + 48) 8 = 2 * sz) (h112 : rdN μ (sp + 112) 8 = n) (h64 : rdN μ (sp + 64) 8 = N)
    (hs1 : 1 ≤ sz) (hs2 : sz < 128) (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296)
    (hr : ∀ a, μ.readable a = true) :
    ∃ ω', FreeStepsH p R 43504 ω μ x 43910 ω' μ x 10 ∧ ω'[10] = UInt64.ofNat (sz - 1) ∧
      ω'[5] = UInt64.ofNat n ∧ ω'[2] = UInt64.ofNat N ∧
      ∀ j : Fin 13, j.val ∉ [2, 5, 9, 10, 11] → ω'[j] = ω[j] := by
  have hc1 : ¬ 67108864 < 2 * sz := by omega
  have hc2 : 2 * sz ≠ 0 := by omega
  have hc3 : ¬ 256 ≤ 2 * sz := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, h40, h48, h112, h64, hc1, hc2, hc3, hr, ↓rdN_fold]
  case post => refine ⟨by reg_val, by reg_val, by reg_val, by reg_frame⟩

/-- **43504 … 43910**, the old next chunk of 128 … 2²⁵ units: ω₁₀ = its bin, ω₅ = n, ω₂ = X + 32·n. -/
theorem rg_bin_big {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp sz n N : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h40 : rdN μ (sp + 40) 8 = sz)
    (h48 : rdN μ (sp + 48) 8 = 2 * sz) (h112 : rdN μ (sp + 112) 8 = n) (h64 : rdN μ (sp + 64) 8 = N)
    (hs1 : 128 ≤ sz) (hs2 : sz ≤ 33554432) (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296)
    (hr : ∀ a, μ.readable a = true) :
    ∃ ω', FreeStepsH p R 43504 ω μ x 43910 ω' μ x 18 ∧ ω'[10] = UInt64.ofNat (binDown sz) ∧
      ω'[5] = UInt64.ofNat n ∧ ω'[2] = UInt64.ofNat N ∧
      ∀ j : Fin 13, j.val ∉ [2, 5, 9, 10, 11] → ω'[j] = ω[j] := by
  have hc1 : ¬ 67108864 < 2 * sz := by omega
  have hc2 : 2 * sz ≠ 0 := by omega
  have hc3 : 256 ≤ 2 * sz := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, h40, h48, h112, h64, hc1, hc2, hc3, hr, ↓rdN_fold]
  case post =>
    refine ⟨?_, by reg_val, by reg_val, by reg_frame⟩
    simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some',
      Option.getD_some]
    congr 1
    rw [binDown_big hs1, show min sz 33554432 = sz by omega]
    have hy0 : sz ≠ 0 := by omega
    rw [clz32 hy0 (by omega)]
    have hL1 : 7 ≤ Nat.log2 sz := (Nat.le_log2 hy0).mpr (by simpa using hs1)
    have hL2 : Nat.log2 sz < 26 := (Nat.log2_lt hy0).mpr (by simpa using Nat.lt_of_le_of_lt hs2 (by decide))
    have hv : sz / 2 ^ (Nat.log2 sz - 7) < 256 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
      have := Nat.lt_log2_self (n := sz)
      calc sz < 2 ^ (Nat.log2 sz + 1) := this
        _ = 256 * 2 ^ (Nat.log2 sz - 7) := by
          rw [show Nat.log2 sz + 1 = 8 + (Nat.log2 sz - 7) by omega, Nat.pow_add]
    rw [show (18446744073709551640 - (31 - Nat.log2 sz) % 18446744073709551616) % 18446744073709551616 % 32 =
      Nat.log2 sz - 7 by omega]
    generalize sz / 2 ^ (Nat.log2 sz - 7) = v at *
    simp only [show v % 4294967296 = v by omega, show v / 2147483648 = 0 by omega, Nat.zero_mul, Nat.add_zero,
      bitwise_and_m127]
    omega

/-- **43910 … 43930**: ω₁₁ = the head slot of bin ω₁₀, ω₁₂ = the bin's head `hd`, ω₆ = the tail's
    size `avail − n` (avail at sp + 72, n in ω₅), ω₉ = nc (sp + 56). -/
theorem rg_head {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp bin hd avail n nc : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h10 : ω[10] = UInt64.ofNat bin)
    (h7 : ω[7] = UInt64.ofNat 196792) (h5 : ω[5] = UInt64.ofNat n) (hb : bin < 2432)
    (hhd : rdN μ (196792 + bin * 4) 4 = hd) (hhd1 : hd < 2147483648)
    (h72 : rdN μ (sp + 72) 8 = avail) (h56 : rdN μ (sp + 56) 8 = nc) (hn : n ≤ avail)
    (hav : avail < 2147483648) (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296)
    (hr : ∀ a, μ.readable a = true) :
    ∃ ω', FreeStepsH p R 43910 ω μ x 43930 ω' μ x 7 ∧ ω'[11] = UInt64.ofNat (196792 + bin * 4) ∧
      ω'[12] = UInt64.ofNat hd ∧ ω'[6] = UInt64.ofNat (avail - n) ∧ ω'[9] = UInt64.ofNat nc ∧
      ∀ j : Fin 13, j.val ∉ [6, 9, 11, 12] → ω'[j] = ω[j] := by
  have hsx : sxw 4 hd = hd := sxw4_small hhd1
  have hq : bin * 4294967296 % 18446744073709551616 / 1073741824 = bin * 4 := by omega
  have hsub : (avail + 4294967296 - n) % 4294967296 = avail - n := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, h10, h7, h5, hhd, hsx, hq, h72, h56, hsub, hr, ↓rdN_fold, ↓loadI_fold]
  case post => refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, by reg_frame⟩

/-- 43930: nc is its bin's head, to 43933. -/
theorem rg_br_head {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (a : Nat) (h12 : ω[12] = UInt64.ofNat a) (h9 : ω[9] = UInt64.ofNat a) :
    FreeStepsH p R 43930 ω μ x 43933 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h12, h9]

/-- 43930: nc is not its bin's head, to 43950. -/
theorem rg_br_mid {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (a b : Nat) (h12 : ω[12] = UInt64.ofNat b) (h9 : ω[9] = UInt64.ofNat a) (hab : b ≠ a)
    (ha : a < 2147483648) (hb : b < 2147483648) :
    FreeStepsH p R 43930 ω μ x 43950 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h12, h9, hab]

end Services.Bootstrap.Alloc
