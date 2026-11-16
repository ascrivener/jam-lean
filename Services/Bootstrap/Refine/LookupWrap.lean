import Services.Bootstrap.Refine.Lookup
import Services.Bootstrap.Alloc.AllocWrap

/-!
# `foreign_historical_lookup` (49015), the straight-line pieces

Refine's eager `Lookup` handler makes Ω_H (host 7, GP v0.8.0 Appendix B.4) with an empty buffer (5366) and jumps
to the SDK's wrapper at 49015 with Ω_H's ω₇ = r and its frame G = M − 48 (the service id at G, the hash's address
at G + 8, the output address `out` at G + 16, ω₆, ω₅ and the return address 170 at G + 24 … G + 48). On r:
* r = NONE (2^64 − 1): the niche word 2^64 − 1 (`None`) at `out` (`wn`);
* 2^64 − 9 ≤ r < 2^64 − 1, or 2^63 ≤ r: a trap (49052, 49024);
* r = 0: buffer 1 (dangling), Ω_H again (`wz`);
* 2^37 − 32 < r < 2^63: the size check traps at 49074 (`wbig`; `Bridge.sizeTrap`);
* otherwise: the allocator's lock is taken (196608, 206848) and `alloc_impl` (41177) is called for ⌈r/32⌉ units,
  zeroed, align 1 (`wl`); on return the lock is cleared and a null block traps at 49074 (`wu`), else Ω_H again
  into the block (49174);
after the second Ω_H, `out` := `Some(Vec)` {r, buf, r} and the wrapper returns to 5372 (`wr`).
-/

namespace Services.Bootstrap.Refine.LookupWrap

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeR
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 5368 … 5372, r = NONE: the niche word 2^64 − 1 at `out` (from G + 16), the frame popped (ω₀, ω₅, ω₆ from
    G + 40, G + 32, G + 24, ω₁ = G + 48), back to 5372. Memory changes only at `out` … `out` + 8. -/
theorem wn {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (G out r5 r6 : Nat) (hG : 65536 ≤ G ∧ G + 48 ≤ 4294967296)
    (hout : out + 8 ≤ 4294967296) (hoG : out + 8 ≤ G ∨ G + 48 ≤ out)
    (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat G) (h7 : ω[7] = UInt64.ofNat 18446744073709551615)
    (s16 : μ.readN (G + 16) 8 = Num.encodeLE 8 out) (s24 : μ.readN (G + 24) 8 = Num.encodeLE 8 r6)
    (s32 : μ.readN (G + 32) 8 = Num.encodeLE 8 r5) (s40 : μ.readN (G + 40) 8 = Num.encodeLE 8 170)
    (hr : ∀ a, G + 16 ≤ a → a < G + 48 → μ.readable a = true)
    (hw : ∀ a, out ≤ a → a < out + 8 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 5368 ω μ x 5372 ω' μ' x 14 ∧ ω'[1] = UInt64.ofNat (G + 48) ∧
      ω'[5] = UInt64.ofNat r5 ∧ ω'[6] = UInt64.ofNat r6 ∧
      μ'.readN out 8 = Num.encodeLE 8 18446744073709551615 ∧
      (∀ a, a < 4294967296 → (a < out ∨ out + 8 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hG0, hG1⟩ := hG
  have ro := rd8 (by omega) s16
  have r6' := rd8 hr6 s24
  have r5' := rd8 hr5 s32
  have r0 := rd8 (by decide) s40
  have hr2 : ∀ a, out ≤ a → a < out + 8 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hG0, hG1, hout, hoG, hr, hr2, hw, ro, r6', r5', r0, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]
    post_simp

/-- 5368 … 49174, r = 0: Ω_H again with the dangling buffer 1, offset 0, length 0 (ω₇ = the service id from G,
    ω₈ = the hash's address from G + 8, ω₉ = 1, ω₁₀ = 0, ω₁₁ = 0), with ω₅ = 0 and ω₆ = 1. -/
theorem wz {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (G svc hp : Nat) (hG : G + 48 ≤ 4294967296) (hsvc : svc < 18446744073709551616)
    (hhp : hp < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat G) (h7 : ω[7] = UInt64.ofNat 0)
    (s0 : μ.readN G 8 = Num.encodeLE 8 svc) (s8 : μ.readN (G + 8) 8 = Num.encodeLE 8 hp)
    (hr : ∀ a, G ≤ a → a < G + 16 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 5368 ω μ x 49174 ω' μ x 13 ∧ ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat 0 ∧
      ω'[6] = UInt64.ofNat 1 ∧ ω'[7] = UInt64.ofNat svc ∧ ω'[8] = UInt64.ofNat hp ∧ ω'[9] = UInt64.ofNat 1 ∧
      ω'[10] = UInt64.ofNat 0 ∧ ω'[11] = UInt64.ofNat 0 := by
  have rs := rd8 hsvc s0
  have rh := rd8 hhp s8
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h7, hG, hr, rs, rh, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]

/-- 5368 … 49074, 2^37 − 32 < r < 2^63: the size check traps (`Bridge.sizeTrap`). -/
theorem wbig {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (r : Nat) (hr1 : 137438953440 < r) (hr2 : r < 9223372036854775808)
    (h7 : ω[7] = UInt64.ofNat r) :
    ∃ ω', FreeStepsH p R 5368 ω μ x 49074 ω' μ x 8 := by
  have hr0 : ¬ r = 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_⟩
  rotate_left
  pvm_go [h7, hr1, hr2, hr0]

/-- 5368 … 41177, 1 ≤ r ≤ 2^37 − 32 with ⌈r/32⌉ < 2^31 units: the allocator's lock is taken (ω₄ parked at 196608,
    the lock word at 206848 or-ed with 1) and `alloc_impl` is called for ⌈r/32⌉ units, align 1, zeroed (ω₁₀ = 1),
    return address 2184, with ω₅ = r and ω₆ = 196792. Memory changes only at 196608 … 196616 and 206848 … 206852. -/
theorem wl {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (r : Nat) (hr0 : r ≠ 0) (hr1 : r ≤ 137438953440) (hu : (r + 31) / 32 < 2147483648)
    (h7 : ω[7] = UInt64.ofNat r) (hl : rdN μ 206848 1 = 0) {HT S0 S1 : Nat} (hH : 206864 ≤ HT)
    (hwr : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 5368 ω μ x 41177 ω' μ' x 30 ∧ ω'[1] = ω[1] ∧
      ω'[0] = UInt64.ofNat 2184 ∧ ω'[5] = UInt64.ofNat r ∧ ω'[6] = UInt64.ofNat 196792 ∧
      ω'[7] = UInt64.ofNat 196792 ∧ ω'[8] = UInt64.ofNat 1 ∧ ω'[9] = UInt64.ofNat ((r + 31) / 32) ∧
      ω'[10] = UInt64.ofNat 1 ∧
      (∀ a, a < 4294967296 → (a < 196608 ∨ 196616 ≤ a) → (a < 206848 ∨ 206852 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) := by
  have hr := hwr.rd
  have hand := Alloc.lock_test (w := rdN μ 206848 4) (by rw [Alloc.rdN4_mod]; exact hl)
  have hr0' : ¬ r = 0 := hr0
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h7, hr0', hr1, hu, hand, hwr, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, by reg_val, by reg_val, ?_, by reg_val,
      fun a ha h1 h2 => ?_, fun a => ?_⟩
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some',
        List.lookup_nil, Option.getD_none]
      try rd_simp []
      try simp
    · rd_simp []
    · rd_simp [hwr]

/-- 49149 … 49174, back from `alloc_impl` with a block buf ≠ 0 (ω₇): the lock octet 206848 cleared, then Ω_H again
    into the block: ω₇ = the service id (G), ω₈ = the hash's address (G + 8), ω₉ = buf, ω₁₀ = 0, ω₁₁ = r (ω₅), with
    ω₆ = buf. Memory changes only at 206848. -/
theorem wu {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (G svc hp buf r : Nat) (hG : 206856 ≤ G ∧ G + 48 ≤ 4294967296) (hsvc : svc < 18446744073709551616)
    (hhp : hp < 18446744073709551616) (hbuf : buf ≠ 0) (hbuf1 : buf < 18446744073709551616) (hrr : r < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat G) (h5 : ω[5] = UInt64.ofNat r) (h6 : ω[6] = UInt64.ofNat 196792)
    (h7 : ω[7] = UInt64.ofNat buf)
    (s0 : μ.readN G 8 = Num.encodeLE 8 svc) (s8 : μ.readN (G + 8) 8 = Num.encodeLE 8 hp)
    (hr : ∀ a, G ≤ a → a < G + 16 → μ.readable a = true) (hw : μ.writable 206848 = true) :
    ∃ ω' μ', FreeStepsH p R 49149 ω μ x 49174 ω' μ' x 10 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧
      ω'[6] = UInt64.ofNat buf ∧ ω'[7] = UInt64.ofNat svc ∧ ω'[8] = UInt64.ofNat hp ∧
      ω'[9] = UInt64.ofNat buf ∧ ω'[10] = UInt64.ofNat 0 ∧ ω'[11] = UInt64.ofNat r ∧ rdN μ' 206848 1 = 0 ∧
      (∀ a, a < 4294967296 → a ≠ 206848 → μ'.read a = μ.read a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rs := rd8 hsvc s0
  have rh := rd8 hhp s8
  have hb0 : ¬ buf = 0 := hbuf
  have hw' : ∀ a, 206848 ≤ a → a < 206849 → μ.writable a = true := fun a h1 h2 => by
    rw [show a = 206848 by omega]; exact hw
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, h7, hG.2, hb0, hbuf1, hr, hw', rs, rh, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, rdN_writeN_disjoint, rs, rh, Nat.mod_eq_of_lt hrr]
    post_simp
    all_goals try (unfold rdN; rw [Memory.readN_writeN_same _ _ _ _ (by simp) (by simp only [two32]; omega)]; rfl)

/-- 49176 … 5372, after the second Ω_H: `Some(Vec)` {r, buf, r} at `out` (from G + 16), the frame popped (ω₀, ω₅,
    ω₆ from G + 40, G + 32, G + 24, ω₁ = G + 48), back to 5372. Memory changes only at `out` … `out` + 24. -/
theorem wr {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (G out r5 r6 r buf : Nat) (hG : 65536 ≤ G ∧ G + 48 ≤ 4294967296)
    (hout : out + 24 ≤ 4294967296) (hoG : out + 24 ≤ G ∨ G + 48 ≤ out)
    (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616) (hr : r < 18446744073709551616)
    (hbuf : buf < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat G) (h5 : ω[5] = UInt64.ofNat r) (h6 : ω[6] = UInt64.ofNat buf)
    (s16 : μ.readN (G + 16) 8 = Num.encodeLE 8 out) (s24 : μ.readN (G + 24) 8 = Num.encodeLE 8 r6)
    (s32 : μ.readN (G + 32) 8 = Num.encodeLE 8 r5) (s40 : μ.readN (G + 40) 8 = Num.encodeLE 8 170)
    (hrd : ∀ a, G + 16 ≤ a → a < G + 48 → μ.readable a = true)
    (hw : ∀ a, out ≤ a → a < out + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 49176 ω μ x 5372 ω' μ' x 12 ∧ ω'[1] = UInt64.ofNat (G + 48) ∧
      ω'[5] = UInt64.ofNat r5 ∧ ω'[6] = UInt64.ofNat r6 ∧
      μ'.readN out 8 = Num.encodeLE 8 r ∧ μ'.readN (out + 8) 8 = Num.encodeLE 8 buf ∧
      μ'.readN (out + 16) 8 = Num.encodeLE 8 r ∧
      (∀ a, a < 4294967296 → (a < out ∨ out + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hG0, hG1⟩ := hG
  have ro := rd8 (by omega) s16
  have r6' := rd8 hr6 s24
  have r5' := rd8 hr5 s32
  have r0 := rd8 (by decide) s40
  have hr2 : ∀ a, out ≤ a → a < out + 24 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hG0, hG1, hout, hoG, hr, hbuf, hrd, hr2, hw, ro, r6', r5', r0, rdN_writeN_disjoint,
      ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]
    post_simp

end Services.Bootstrap.Refine.LookupWrap
