import Services.Bootstrap.Alloc.AllocWrap
import Services.Bootstrap.Alloc.Writable

/-!
# The binary's `realloc_impl`: entry

`realloc_impl` (42980 … 44239, called by `realloc` at 40799 with ω₀ = 1988): ω₇ the allocator,
ω₈ the data address, ω₉ the alignment and ω₁₀ the new request, both in units. The prologue saves
the frame and reads the chunk's size `cur` from its header; then

* the request equal to the usable size `cur − 1`: the address back (43148);
* a request of 0 (43139): the chunk is freed (the free path, returning to 43145) and null comes back;
* a request below `cur − 1` (43027): `shrink_inplace`;
* a request above it (43169): `grow_inplace`, else `alloc_impl` (43259) + `memcpy` + free.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- A register's value after `pvm_go`, as an expression (no closing). -/
macro "reg_get" : tactic => `(tactic|
  simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some',
    Option.getD_some])

/-- Reads see addresses modulo 2³²: a load at a − 28 through a 64-bit negative offset. -/
theorem rdN_wrap (μ : Memory) {a b : Nat} (n : Nat) (h : a % 4294967296 = b % 4294967296) :
    rdN μ a n = rdN μ b n := by
  unfold rdN; congr 1
  exact readN_congr2 fun j _ => by
    simp only [Memory.read, show two32 = 4294967296 from rfl]; congr 1; omega

/-- **42980 … 43005**: the frame, and the chunk's size `cur` (its size word w at ptr − 28):
    ω₁₁ = cur, ω₆ = cur − 1. -/
theorem rl_pro {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp ptr w : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr)
    (hp : 32 ≤ ptr) (hp1 : ptr < 2147483648) (hw : rdN μ (ptr - 28) 4 = w) (hw1 : 2 ≤ w)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296) {HT S0 S1 : Nat}
    (hXH : 196608 ≤ ptr - 32 ∧ ptr - 32 + 8 ≤ HT) (hS : S0 + 152 ≤ sp ∧ sp ≤ S1) (hwr : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 42980 ω μ x 43005 ω' μ' x 7 ∧
      ω'[1] = UInt64.ofNat (sp - 152) ∧ ω'[11] = UInt64.ofNat (w / 2) ∧ ω'[6] = UInt64.ofNat (w / 2 - 1) ∧
      μ'.readN (sp - 8) 8 = Num.encodeLE 8 ω[0].toNat ∧ μ'.readN (sp - 16) 8 = Num.encodeLE 8 ω[5].toNat ∧
      μ'.readN (sp - 24) 8 = Num.encodeLE 8 ω[6].toNat ∧
      (∀ a, a < 4294967296 → (a < sp - 24 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧
      ∀ j : Fin 13, j.val ∉ [1, 6, 11] → ω'[j] = ω[j] := by
  have hr := hwr.rd
  have hw32 : w < 4294967296 := by rw [← hw]; exact rdN_lt μ _ 4
  have ha : ∀ μ' : Memory, rdN μ' (ptr + 18446744073709551588) 4 = rdN μ' (ptr - 28) 4 :=
    fun μ' => rdN_wrap μ' 4 (by omega)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h8, ha, hw, hwr, hr, rdN_writeN_disjoint, ↓rdN_fold]
  case post =>
    refine ⟨by reg_val, by reg_val, by reg_val, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, by reg_frame⟩
    · rw [show sp - 8 = sp - 152 + 144 by omega]; rd_simp []; rfl
    · rw [show sp - 16 = sp - 152 + 136 by omega]; rd_simp []; rfl
    · rw [show sp - 24 = sp - 152 + 128 by omega]; rd_simp []; rfl
    · rd_simp []
    · rd_simp [hwr]

/-- 43005: the request equals the usable size, to 43148. -/
theorem rl_br_same {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (a : Nat) (h10 : ω[10] = UInt64.ofNat a) (h6 : ω[6] = UInt64.ofNat a) :
    FreeStepsH p R 43005 ω μ x 43148 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h10, h6]

/-- **43005 … 43027**, a request `req` of 1 … `cur − 2` units: ω₃ = 204984 (the allocator + 8192),
    ω₅ = req + 1; to the shrink. -/
theorem rl_go_shrink {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (req u : Nat) (h10 : ω[10] = UInt64.ofNat req) (h6 : ω[6] = UInt64.ofNat u)
    (h7 : ω[7] = UInt64.ofNat 196792) (h0 : req ≠ 0) (hlt : req < u) (hu : u < 2147483648) :
    ∃ ω', FreeStepsH p R 43005 ω μ x 43027 ω' μ x 6 ∧ ω'[3] = UInt64.ofNat 204984 ∧
      ω'[5] = UInt64.ofNat (req + 1) ∧ ∀ j : Fin 13, j.val ∉ [3, 5, 11] → ω'[j] = ω[j] := by
  have hne : req ≠ u := by omega
  have hge : ¬ u ≤ req := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h10, h6, h7, h0, hne, hge]
  case post => refine ⟨by reg_val, by reg_val, by reg_frame⟩

/-- **43005 … 43169**, a request `req` above `cur − 1` units (below 2³¹): ω₃ = 204984,
    ω₅ = req + 1; to the growth. -/
theorem rl_go_grow {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (req u : Nat) (h10 : ω[10] = UInt64.ofNat req) (h6 : ω[6] = UInt64.ofNat u)
    (h7 : ω[7] = UInt64.ofNat 196792) (hlt : u < req) (hr : req < 2147483647) :
    ∃ ω', FreeStepsH p R 43005 ω μ x 43169 ω' μ x 6 ∧ ω'[3] = UInt64.ofNat 204984 ∧
      ω'[5] = UInt64.ofNat (req + 1) ∧ ∀ j : Fin 13, j.val ∉ [3, 5, 11] → ω'[j] = ω[j] := by
  have hne : req ≠ u := by omega
  have h0 : req ≠ 0 := by omega
  have hge : u ≤ req := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h10, h6, h7, h0, hne, hge]
  case post => refine ⟨by reg_val, by reg_val, by reg_frame⟩

/-- **43005 … the free path (42327)**, a request of 0 with a usable size `u` ≠ 0: ω₀ = 2000 (the
    return to 43145). -/
theorem rl_go_zero {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (u : Nat) (h10 : ω[10] = UInt64.ofNat 0) (h6 : ω[6] = UInt64.ofNat u) (hu : u ≠ 0)
    (hu1 : u < 18446744073709551616) :
    ∃ ω', FreeStepsH p R 43005 ω μ x 42327 ω' μ x 3 ∧ ω'[0] = UInt64.ofNat 2000 ∧
      ∀ j : Fin 13, j.val ∉ [0] → ω'[j] = ω[j] := by
  have hne : (0 : Nat) ≠ u % 18446744073709551616 := by rw [Nat.mod_eq_of_lt hu1]; omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h10, h6, hne]
  case post => refine ⟨by reg_val, by reg_frame⟩

/-- **43145 … 43167 … 40805**: null in ω₇, the frame popped, and the return (ω₀ = 1988 from the frame)
    to `realloc` at 40805. -/
theorem rl_ret_null {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v5 v6 : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296)
    (s0 : rdN μ (sp + 144) 8 = 1988) (s5 : rdN μ (sp + 136) 8 = v5) (s6 : rdN μ (sp + 128) 8 = v6)
    {HT S0 S1 : Nat} (hS : S0 ≤ sp ∧ sp + 152 ≤ S1) (hr : RdAt μ HT S0 S1) :
    ∃ ω', FreeStepsH p R 43145 ω μ x 40805 ω' μ x 9 ∧ ω'[7] = UInt64.ofNat 0 ∧ ω'[8] = UInt64.ofNat 0 ∧
      ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat (sp + 152) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ∀ j : Fin 13, j.val ∉ [0, 1, 5, 6, 7, 8] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, s0, s5, s6, hr, ↓rdN_fold]
  case post => refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, by reg_val, by reg_val, by reg_frame⟩

/-- **43148 … 43167 … 40805**: ω₇ = ω₈ (the address), the frame popped, and the return to 40805. -/
theorem rl_ret {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp ptr v5 v6 : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr)
    (hp : ptr < 18446744073709551616) (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296)
    (s0 : rdN μ (sp + 144) 8 = 1988) (s5 : rdN μ (sp + 136) 8 = v5) (s6 : rdN μ (sp + 128) 8 = v6)
    {HT S0 S1 : Nat} (hS : S0 ≤ sp ∧ sp + 152 ≤ S1) (hr : RdAt μ HT S0 S1) :
    ∃ ω', FreeStepsH p R 43148 ω μ x 40805 ω' μ x 7 ∧ ω'[7] = UInt64.ofNat ptr ∧
      ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat (sp + 152) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ∀ j : Fin 13, j.val ∉ [0, 1, 5, 6, 7] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, h8, s0, s5, s6, hr, ↓rdN_fold]
  case post => refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, by reg_val, by reg_frame⟩

/-- **43027 … 43080**, the shrink: the chunk X = ptr − 32 of `cur` units (size word read again)
    keeps `n` = req + 1 < cur units, its size word becomes 2·n + 1; ω₀ = X, ω₄ = the heap's end,
    ω₁₂ = X + 32·cur (the old next chunk), ω₂ = cur − n; the allocator + 8192 saved at sp + 120. -/
theorem rs_hdr {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp ptr n cur base : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr)
    (h5 : ω[5] = UInt64.ofNat n) (h3 : ω[3] = UInt64.ofNat 204984)
    (hp : 206896 ≤ ptr) (hw : rdN μ (ptr - 32 + 4) 4 = 2 * cur + 1) (hn : n < cur)
    (hb : rdN μ 206520 8 = base) (hbT : base + 1073741824 < 2147483648) (hpc : ptr - 32 + 32 * cur < 2147483648)
    (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296) {HT S0 S1 : Nat} (hH : 206864 ≤ HT)
    (hXH : 196608 ≤ ptr - 32 ∧ ptr - 32 + 8 ≤ HT) (hS : S0 ≤ sp ∧ sp + 152 ≤ S1) (hwr : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 43027 ω μ x 43080 ω' μ' x 18 ∧
      ω'[0] = UInt64.ofNat (ptr - 32) ∧ ω'[4] = UInt64.ofNat (base + 1073741824) ∧
      ω'[12] = UInt64.ofNat (ptr - 32 + 32 * cur) ∧ ω'[2] = UInt64.ofNat (cur - n) ∧
      rdN μ' (ptr - 32 + 4) 4 = 2 * n + 1 ∧ rdN μ' (sp + 120) 8 = 204984 ∧
      (∀ a, a < 4294967296 → (a < ptr - 32 + 4 ∨ ptr - 32 + 8 ≤ a) → (a < sp + 120 ∨ sp + 128 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧
      ∀ j : Fin 13, j.val ∉ [0, 2, 4, 9, 10, 11, 12] → ω'[j] = ω[j] := by
  have hr := hwr.rd
  have hb' : rdN μ 206520 4 = base := by
    have := rdN_lo μ 206520; rw [hb] at this; rw [this]; omega
  have hsx : sxw 4 base = base := sxw4_small (by omega)
  have ha : (ptr + 18446744073709551584) % 18446744073709551616 = ptr - 32 := by omega
  have hc : ¬ cur ≤ n := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h8, h5, h3, ha, hw, hb', hsx, hc, hwr, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, by reg_val, ?_, ?_, ?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_, by reg_frame⟩
    · reg_get; rw [show (2 * cur + 1) / 2 * 32 + (ptr - 32) = ptr - 32 + 32 * cur by omega]
    · reg_get; rw [show ((2 * cur + 1) / 2 + 4294967296 - n) % 4294967296 = cur - n by omega]
    · rd_simp []; simp only [Nat.reducePow, Nat.reduceMul]; omega
    · rd_simp []; simp [Num.decodeLE]
    · rd_simp []
    · rd_simp [hwr]

/-- 43080: the old next chunk at or past the heap's end, to the registration (43677). -/
theorem rs_br_end {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (a b : Nat) (h12 : ω[12] = UInt64.ofNat a) (h4 : ω[4] = UInt64.ofNat b) (hab : b ≤ a)
    (ha : a < 2147483648) (hb : b < 2147483648) :
    FreeStepsH p R 43080 ω μ x 43677 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h12, h4, hab]

/-- 43080: below the heap's end, to 43084. -/
theorem rs_br_in {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (a b : Nat) (h12 : ω[12] = UInt64.ofNat a) (h4 : ω[4] = UInt64.ofNat b) (hab : a < b)
    (ha : a < 2147483648) (hb : b < 2147483648) :
    FreeStepsH p R 43080 ω μ x 43084 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h12, h4, hab]

/-- **43084 … 43097**: the old next chunk nc's size word w: ω₆ = nc, ω₁₁ = w, ω₉ = its used bit. -/
theorem rs_nhdr {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (nc w : Nat) (h12 : ω[12] = UInt64.ofNat nc) (hnc : nc < 2147483648)
    (hw : rdN μ (nc + 4) 4 = w) {HT S0 S1 : Nat} (hncH : 196608 ≤ nc ∧ nc + 8 ≤ HT) (hr : RdAt μ HT S0 S1) :
    ∃ ω', FreeStepsH p R 43084 ω μ x 43097 ω' μ x 5 ∧ ω'[6] = UInt64.ofNat nc ∧
      ω'[11] = UInt64.ofNat w ∧ ω'[9] = UInt64.ofNat (w % 2) ∧
      ∀ j : Fin 13, j.val ∉ [6, 9, 11] → ω'[j] = ω[j] := by
  have hw32 : w < 4294967296 := by rw [← hw]; exact rdN_lt μ _ 4
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h12, hw, hr, ↓rdN_fold]
  case post =>
    refine ⟨by reg_val, by reg_val, ?_, by reg_frame⟩
    simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some',
      PVM.bitwise_and_m1]

/-- 43097, the old next chunk allocated: to the registration (43677). -/
theorem rs_br_used {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (c : Nat) (h9 : ω[9] = UInt64.ofNat c) (hc : c ≠ 0) (hc2 : c < 2) :
    FreeStepsH p R 43097 ω μ x 43677 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h9, hc]

/-- 43097, the old next chunk free: to 43101. -/
theorem rs_br_free {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (h9 : ω[9] = UInt64.ofNat 0) :
    FreeStepsH p R 43097 ω μ x 43101 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h9]

end Services.Bootstrap.Alloc
