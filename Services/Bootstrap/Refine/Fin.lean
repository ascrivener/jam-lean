import Services.Bootstrap.Refine.DropOut
import Services.Bootstrap.Refine.Exit

/-!
# Refine's exit: the epilogue

After the output is encoded (6295), refine drops its output `Vec<Instruction>` at M + 168 (29087, return
address 206 → 6305), frees its buffer (`dealloc`, 232·cap octets, align 8; return address 208 → 6330) when
its capacity is nonzero, frees the `Vec<u8>` whose capacity is at M + 88 and data at M + 112 (return
address 210 → 6349) when that capacity is nonzero, and returns the encoded output: ω₇ = the buffer (from
M + 280), ω₈ = its length (from M + 288), restoring ω₀, ω₅, ω₆ from M + 624, M + 616, M + 608 and closing
its 632-octet frame. GP v0.8.0 Appendix B.4 (Ψ_R running bootstrap's code).
-/

namespace Services.Bootstrap.Refine.Fin

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Encode.Writer

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 6295 … 6299: the call of the drop on the output `Vec` at M + 168 (return address 206). -/
theorem f1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (M : Nat)
    (hM : M + 168 < 4294967296) (h1 : ω[1] = UInt64.ofNat M) :
    ∃ ω', FreeStepsH p R 6295 ω μ x 29087 ω' μ x 2 ∧ ω'[0] = UInt64.ofNat 206 ∧ ω'[1] = ω[1] ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat (M + 168) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hM]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]

/-- 6305 … 6323, the output buffer's capacity c (at M + 168) nonzero: `dealloc(ptr, 232 c, 8)` with ptr from
    M + 176 (return address 208 → 6330). -/
theorem f2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (M c ptr : Nat)
    (hM : M + 184 ≤ 4294967296) (hc : c ≠ 0) (hc' : 232 * c < 18446744073709551616)
    (hptr : ptr < 18446744073709551616) (h1 : ω[1] = UInt64.ofNat M)
    (s168 : μ.readN (M + 168) 8 = Num.encodeLE 8 c) (s176 : μ.readN (M + 176) 8 = Num.encodeLE 8 ptr)
    (hr : ∀ a, M + 168 ≤ a → a < M + 184 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 6305 ω μ x 40613 ω' μ x 6 ∧ ω'[0] = UInt64.ofNat 208 ∧ ω'[1] = ω[1] ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat ptr := by
  have rc := rd8 (by omega) s168
  have rp := rd8 hptr s176
  have hc0 : ¬ c = 0 := hc
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hM, hc0, hr, rc, rp, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]

/-- 6305 … 6309, capacity 0: on to 6330. -/
theorem f2z {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (M : Nat)
    (hM : M + 176 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat M)
    (s168 : μ.readN (M + 168) 8 = Num.encodeLE 8 0) (hr : ∀ a, M + 168 ≤ a → a < M + 176 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 6305 ω μ x 6330 ω' μ x 2 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have rc := rd8 (by decide) s168
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hM, hr, rc, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]

/-- 6330 … 6342, the capacity c at M + 88 nonzero: `dealloc(ptr, c, 1)` with ptr from M + 112 (return
    address 210 → 6349). -/
theorem f3 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (M c ptr : Nat)
    (hM : M + 120 ≤ 4294967296) (hc : c ≠ 0) (hc' : c < 18446744073709551616)
    (hptr : ptr < 18446744073709551616) (h1 : ω[1] = UInt64.ofNat M)
    (s88 : μ.readN (M + 88) 8 = Num.encodeLE 8 c) (s112 : μ.readN (M + 112) 8 = Num.encodeLE 8 ptr)
    (hr : ∀ a, M + 88 ≤ a → a < M + 120 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 6330 ω μ x 40613 ω' μ x 6 ∧ ω'[0] = UInt64.ofNat 210 ∧ ω'[1] = ω[1] ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat ptr := by
  have rc := rd8 hc' s88
  have rp := rd8 hptr s112
  have hc0 : ¬ c = 0 := hc
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hM, hc0, hr, rc, rp, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]

/-- 6330 … 6333, the capacity at M + 88 zero: on to 6349. -/
theorem f3z {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (M : Nat)
    (hM : M + 96 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat M)
    (s88 : μ.readN (M + 88) 8 = Num.encodeLE 8 0) (hr : ∀ a, M + 88 ≤ a → a < M + 96 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 6330 ω μ x 6349 ω' μ x 2 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have rc := rd8 (by decide) s88
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hM, hr, rc, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]

/-- 6349 … 6373: refine returns ω₇ = buf (M + 280) and ω₈ = len (M + 288) to `ret` (from M + 624; → t),
    with ω₅, ω₆ from M + 616, M + 608 and ω₁ = M + 632. -/
theorem f4 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (M buf len ret r5 r6 t : Nat)
    (hM : M + 632 < 4294967296) (hbuf : buf < 18446744073709551616) (hlen : len < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat M)
    (s280 : μ.readN (M + 280) 8 = Num.encodeLE 8 buf) (s288 : μ.readN (M + 288) 8 = Num.encodeLE 8 len)
    (s624 : μ.readN (M + 624) 8 = Num.encodeLE 8 ret) (s616 : μ.readN (M + 616) 8 = Num.encodeLE 8 r5)
    (s608 : μ.readN (M + 608) 8 = Num.encodeLE 8 r6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hr5 : r5 < 18446744073709551616)
    (hr6 : r6 < 18446744073709551616) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hr : ∀ a, M + 280 ≤ a → a < M + 296 → μ.readable a = true)
    (hr2 : ∀ a, M + 608 ≤ a → a < M + 632 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 6349 ω μ x t ω' μ x 8 ∧ ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (M + 632) ∧
      ω'[5] = UInt64.ofNat r5 ∧ ω'[6] = UInt64.ofNat r6 ∧ ω'[7] = UInt64.ofNat buf ∧ ω'[8] = UInt64.ofNat len := by
  have rb := rd8 hbuf s280
  have rl := rd8 hlen s288
  have rr := rd8 (by omega) s624
  have r5' := rd8 hr5 s616
  have r6' := rd8 hr6 s608
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hM, hr, hr2, rb, rl, rr, r5', r6', hret, hjt, hbt, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]

end Services.Bootstrap.Refine.Fin
