import Services.Bootstrap.Refine.DropOut
import Services.Bootstrap.Refine.Exit
import Services.Bootstrap.Decode.DeallocCall
import Services.Bootstrap.Decode.GrowOne

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

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Encode.Writer
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

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
theorem f4j {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (M buf len ret r5 r6 t : Nat)
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

/-- Where refine's return lands: a return address of the jump table (→ t), or the halt address 2³² − 2¹⁶, the
    run then stopping at the `jump_ind` 6373 that halts (GP v0.8.0 §A.5.1). -/
def RetTo (P : Program) (ret t : Nat) : Prop :=
  (0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0 ∧ P.jumpTable.getD (ret / 2 - 1) 0 = t ∧ P.isBlockStart t = true) ∨
  (ret = 4294901760 ∧ t = 6373)

theorem RetTo.lt {P : Program} {ret t : Nat} (h : RetTo P ret t) : ret < 18446744073709551616 := by
  rcases h with ⟨-, h, -⟩ | ⟨h, -⟩ <;> omega

/-- 6349 … 6373 without the jump: ω₇ = buf, ω₈ = len, ω₀ = ret, ω₅, ω₆ restored, ω₁ = M + 632, at the
    `jump_ind` 6373. -/
theorem f4h {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (M buf len ret r5 r6 : Nat)
    (hM : M + 632 < 4294967296) (hbuf : buf < 18446744073709551616) (hlen : len < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat M)
    (s280 : μ.readN (M + 280) 8 = Num.encodeLE 8 buf) (s288 : μ.readN (M + 288) 8 = Num.encodeLE 8 len)
    (s624 : μ.readN (M + 624) 8 = Num.encodeLE 8 ret) (s616 : μ.readN (M + 616) 8 = Num.encodeLE 8 r5)
    (s608 : μ.readN (M + 608) 8 = Num.encodeLE 8 r6)
    (hret : ret < 18446744073709551616) (hr5 : r5 < 18446744073709551616)
    (hr6 : r6 < 18446744073709551616)
    (hr : ∀ a, M + 280 ≤ a → a < M + 296 → μ.readable a = true)
    (hr2 : ∀ a, M + 608 ≤ a → a < M + 632 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 6349 ω μ x 6373 ω' μ x 8 ∧ ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (M + 632) ∧
      ω'[5] = UInt64.ofNat r5 ∧ ω'[6] = UInt64.ofNat r6 ∧ ω'[7] = UInt64.ofNat buf ∧ ω'[8] = UInt64.ofNat len := by
  have rb := rd8 hbuf s280
  have rl := rd8 hlen s288
  have rr := rd8 hret s624
  have r5' := rd8 hr5 s616
  have r6' := rd8 hr6 s608
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hM, hr, hr2, rb, rl, rr, r5', r6', ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]

/-- 6349 … t: refine returns ω₇ = buf (M + 280) and ω₈ = len (M + 288) to `ret` (from M + 624; `RetTo`),
    with ω₅, ω₆ from M + 616, M + 608 and ω₁ = M + 632. -/
theorem f4 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (M buf len ret r5 r6 t : Nat)
    (hM : M + 632 < 4294967296) (hbuf : buf < 18446744073709551616) (hlen : len < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat M)
    (s280 : μ.readN (M + 280) 8 = Num.encodeLE 8 buf) (s288 : μ.readN (M + 288) 8 = Num.encodeLE 8 len)
    (s624 : μ.readN (M + 624) 8 = Num.encodeLE 8 ret) (s616 : μ.readN (M + 616) 8 = Num.encodeLE 8 r5)
    (s608 : μ.readN (M + 608) 8 = Num.encodeLE 8 r6)
    (hret : RetTo P ret t) (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hr : ∀ a, M + 280 ≤ a → a < M + 296 → μ.readable a = true)
    (hr2 : ∀ a, M + 608 ≤ a → a < M + 632 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 6349 ω μ x t ω' μ x 8 ∧ ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (M + 632) ∧
      ω'[5] = UInt64.ofNat r5 ∧ ω'[6] = UInt64.ofNat r6 ∧ ω'[7] = UInt64.ofNat buf ∧ ω'[8] = UInt64.ofNat len := by
  rcases hret with ⟨h0, h2, h3, hjt, hbt⟩ | ⟨hr0, rfl⟩
  · exact f4j (p := p) (P := P) (R := R) x ω μ M buf len ret r5 r6 t hM hbuf hlen h1 s280 s288 s624 s616 s608 ⟨h0, h2, h3⟩ hr5 hr6 hjt hbt hr hr2
  · exact f4h (p := p) (P := P) (R := R) x ω μ M buf len ret r5 r6 hM hbuf hlen h1 s280 s288 s624 s616 s608 (by omega) hr5 hr6 hr hr2

/-- One `dealloc` (40613) of an allocated chunk, or none: a free that may or may not happen. -/
theorem free_opt {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) {pb S0 S1 : Nat} (x : X)
    (ω : Regs) (μ : Memory) (s : State) (M ret t : Nat) (c : Chunk) (H : HeapCtx env pb S0 S1 μ s)
    (hc : c ∈ chunks s) (hcu : c.used = true) (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat M)
    (h7 : ω[7] = UInt64.ofNat (c.addr + 32))
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) (hM : 2147483716 ≤ M ∧ S0 + 40 ≤ M ∧ M ≤ S1) :
    ∃ ω' μ', FreeStepsH p R 40613 ω μ x t ω' μ' x 249 ∧ HeapCtx env pb S0 S1 μ' (free s (c.addr + 32)) ∧
      (∀ a, a < 4294967296 → M ≤ a → μ'.read a = μ.read a) ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ c → d ∈ chunks (free s (c.addr + 32)) ∧
        ∀ a, InData d a → μ'.read a = μ.read a) ∧
      ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  obtain ⟨ω', μ', run, H', -, -, -, stk, -, keep, -, e1, e5, e6⟩ := Decode.DeallocCall.dealloc_call (R := R)
    (p := p) (P := P) env pb S0 S1 x ω μ s M (c.addr + 32) ret t c H hc hcu rfl h0 h1 h7 hret hjt hbt hM.1
    ⟨hM.2.1, hM.2.2⟩
  exact ⟨ω', μ', run, H', stk, keep, e1, e5, e6⟩

/-- **Refine's epilogue** (6295 … t): the output `Vec<Instruction>` at M + 168 (`{c, E, n}`, 1 ≤ n ≤ c,
    every element of a variant whose drop does nothing, its buffer the chunk co) is dropped and its buffer
    freed, the `Vec<u8>` at M + 88 / M + 112 (its buffer the chunk cq when its capacity c' ≠ 0) is freed,
    and refine returns ω₇ = buf, ω₈ = len (from M + 280, M + 288) to the return address at M + 624 (→ t).
    The allocator's context holds for the heap after the frees, every other allocated chunk keeps its data,
    and the stack from M up is kept. -/
theorem fin_run {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) {pb S0 S1 : Nat} (x : X)
    (ω : Regs) (μ : Memory) (s : State) (H : HeapCtx env pb S0 S1 μ s) (M c E n c' q buf len ret r5 r6 t : Nat)
    (co cq : Chunk)
    (hM : S0 + 456 ≤ M ∧ M + 632 ≤ S1 ∧ 2147484104 ≤ M ∧ M % 8 = 0) (hn : 0 < n) (hnc : n ≤ c)
    (hc : co ∈ chunks s ∧ co.used = true ∧ co.addr + 32 = E ∧ E + 232 * n ≤ co.addr + 32 * co.size)
    (hc'' : 232 * c < 18446744073709551616)
    (hq : c' ≠ 0 → cq ∈ chunks s ∧ cq.used = true ∧ cq.addr + 32 = q ∧ cq ≠ co) (hq' : c' < 18446744073709551616)
    (hbuf : buf < 18446744073709551616) (hlen : len < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat M)
    (s168 : μ.readN (M + 168) 8 = Num.encodeLE 8 c) (s176 : μ.readN (M + 176) 8 = Num.encodeLE 8 E)
    (s184 : μ.readN (M + 184) 8 = Num.encodeLE 8 n)
    (s88 : μ.readN (M + 88) 8 = Num.encodeLE 8 c') (s112 : μ.readN (M + 112) 8 = Num.encodeLE 8 q)
    (s280 : μ.readN (M + 280) 8 = Num.encodeLE 8 buf) (s288 : μ.readN (M + 288) 8 = Num.encodeLE 8 len)
    (s624 : μ.readN (M + 624) 8 = Num.encodeLE 8 ret) (s616 : μ.readN (M + 616) 8 = Num.encodeLE 8 r5)
    (s608 : μ.readN (M + 608) 8 = Num.encodeLE 8 r6)
    (hret : RetTo P ret t) (hr5 : r5 < 18446744073709551616)
    (hr6 : r6 < 18446744073709551616)
    (kinds : ∀ j, j < n → ∃ t, DropOut.NoDrop t ∧ μ.readN (E + 232 * j) 8 = Num.encodeLE 8 (9223372036854775807 + t))
    (tab : μ.readN 67760 96 = DropOut.dtable) (hrt : ∀ a, 67760 ≤ a → a < 67856 → μ.readable a = true) :
    ∃ ω' μ' s', FreeStepsH p R 6295 ω μ x t ω' μ' x (32 * n + 600) ∧ HeapCtx env pb S0 S1 μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (M + 632) ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 ∧ ω'[7] = UInt64.ofNat buf ∧ ω'[8] = UInt64.ofNat len ∧
      (∀ a, a < 4294967296 → M ≤ a → μ'.read a = μ.read a) ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ co → (c' ≠ 0 → d ≠ cq) → d ∈ chunks s' ∧
        ∀ a, InData d a → μ'.read a = μ.read a) := by
  obtain ⟨hS0M, hMS1, hM2, hM8⟩ := hM
  have hS1 := H.hS1
  have hbT := H.hbT
  have hb0 := H.hb0
  obtain ⟨hco, hcou, hcoa, hcoE⟩ := hc
  obtain ⟨hco0, -, hcoT⟩ := Decode.VecU8.chunk_in H.wf hco hcou
  have rM : ∀ a, S0 ≤ a → a < S1 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (H.st a h1 h2)
  -- the drop
  obtain ⟨ω1, run1, a0, a1, a5, a6, a7⟩ := f1 (p := p) (P := P) (R := R) x ω μ M (by omega) h1
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, bfr, brd, bwr⟩ := DropOut.drop_vec (p := p) (P := P) (R := R) x ω1 μ M
    (M + 168) E n 206 6305 ⟨by omega, by omega, hM8⟩ (by omega) (Or.inr (by omega)) hn (by omega)
    (Or.inl (by omega)) a0 (a1.trans h1) a7 s176 s184 kinds tab hrt (fun a h1 h2 => rM a (by omega) (by omega))
    (fun a h1 h2 => Memory.readable_of_writable (Decode.VecU8.heap_writable H hco hcou ⟨by omega, by omega⟩))
    (fun a h1 h2 => H.st a (by omega) (by omega)) ⟨by decide, by decide, by decide⟩ jte_102 bs_6305
  have H2 : HeapCtx env pb S0 S1 μ2 s := Decode.GrowOne.ctx_high H (fun a ha => bfr a (by omega) (by omega)) bwr
  have k2 : ∀ a, a < 4294967296 → M ≤ a → μ2.read a = μ.read a := fun a h0 h => bfr a h0 (by omega)
  have r2 : ∀ a l, M ≤ a → a + l ≤ 4294967296 → μ2.readN a l = μ.readN a l :=
    fun a l h h' => Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega))
  -- the output buffer's free
  obtain ⟨ω3, run3, c0, c1, c5, c6, c7⟩ := f2 (p := p) (P := P) (R := R) x ω2 μ2 M c E (by omega) (by omega) hc''
    (by omega) b1 (by rw [r2 _ _ (by omega) (by omega)]; exact s168)
    (by rw [r2 _ _ (by omega) (by omega)]; exact s176) (fun a h1 h2 => by rw [brd]; exact rM a (by omega) (by omega))
  obtain ⟨ω4, μ4, run4, H4, k4, keep4, d1, d5, d6⟩ := free_opt (p := p) (P := P) (R := R) env x ω3 μ2 s M 208 6330
    co H2 hco hcou c0 (c1.trans b1) (by rw [c7, hcoa]) ⟨by decide, by decide, by decide⟩
    jte_103 bs_6330 ⟨by omega, by omega, by omega⟩
  have r4 : ∀ a l, M ≤ a → a + l ≤ 4294967296 → μ4.readN a l = μ.readN a l :=
    fun a l h h' => Memory.readN_congr (fun j hj => by rw [k4 _ (by omega) (by omega), k2 _ (by omega) (by omega)])
  have h1' : ω4[1] = UInt64.ofNat M := by rw [d1, c1, b1]
  -- the `Vec<u8>`'s free, then the return
  have fin : ∀ (ω5 : Regs) (μ5 : Memory) (s5 : State) (n5 : Nat), HeapCtx env pb S0 S1 μ5 s5 →
      FreeStepsH p R 6295 ω μ x 6349 ω5 μ5 x n5 → ω5[1] = UInt64.ofNat M →
      (∀ a, a < 4294967296 → M ≤ a → μ5.read a = μ.read a) → n5 ≤ 32 * n + 590 →
      ∃ ω' μ', FreeStepsH p R 6295 ω μ x t ω' μ' x (32 * n + 600) ∧
        ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (M + 632) ∧ ω'[5] = UInt64.ofNat r5 ∧
        ω'[6] = UInt64.ofNat r6 ∧ ω'[7] = UInt64.ofNat buf ∧ ω'[8] = UInt64.ofNat len ∧ μ' = μ5 := by
    intro ω5 μ5 s5 n5 H5 run5 e1 k5 hn5
    have r5' : ∀ a l, M ≤ a → a + l ≤ 4294967296 → μ5.readN a l = μ.readN a l :=
      fun a l h h' => Memory.readN_congr (fun j hj => k5 _ (by omega) (by omega))
    obtain ⟨ω6, run6, g0, g1, g5, g6, g7, g8⟩ := f4 (p := p) (P := P) (R := R) x ω5 μ5 M buf len ret r5 r6 t
      (by omega) hbuf hlen e1 (by rw [r5' _ _ (by omega) (by omega)]; exact s280)
      (by rw [r5' _ _ (by omega) (by omega)]; exact s288) (by rw [r5' _ _ (by omega) (by omega)]; exact s624)
      (by rw [r5' _ _ (by omega) (by omega)]; exact s616) (by rw [r5' _ _ (by omega) (by omega)]; exact s608)
      hret hr5 hr6 (fun a h1 h2 => Memory.readable_of_writable (H5.st a (by omega) (by omega)))
      (fun a h1 h2 => Memory.readable_of_writable (H5.st a (by omega) (by omega)))
    exact ⟨ω6, μ5, (run5.trans run6).mono (by omega), g0, g1, g5, g6, g7, g8, rfl⟩
  have pre := run1.trans (run2.trans (run3.trans run4))
  by_cases hq0 : c' = 0
  · subst hq0
    obtain ⟨ω5, run5, e1, -, -⟩ := f3z (p := p) (P := P) (R := R) x ω4 μ4 M (by omega) h1'
      (by rw [r4 _ _ (by omega) (by omega)]; exact s88)
      (fun a h1 h2 => Memory.readable_of_writable (H4.st a (by omega) (by omega)))
    obtain ⟨ω', μ', run', g0, g1, g5, g6, g7, g8, e⟩ := fin ω5 μ4 _ _ H4 (pre.trans run5)
      (e1.trans h1') (fun a h0 h => by rw [k4 a h0 h, k2 a h0 h]) (by omega)
    subst e
    refine ⟨ω', μ', _, run', H4, g0, g1, g5, g6, g7, g8, fun a h0 h => by rw [k4 a h0 h, k2 a h0 h],
      fun d hd hu hne _ => ?_⟩
    · obtain ⟨hd', hk⟩ := keep4 d hd hu hne
      refine ⟨hd', fun a ha => ?_⟩
      obtain ⟨-, -, hdT⟩ := Decode.VecU8.chunk_in H.wf hd hu
      unfold InData at ha
      rw [hk a ⟨ha.1, ha.2⟩, bfr a (by omega) (by omega)]
  · obtain ⟨hcq, hcqu, hcqa, hcqo⟩ := hq hq0
    obtain ⟨-, -, hcqT⟩ := Decode.VecU8.chunk_in H.wf hcq hcqu
    obtain ⟨ω5, run5, e0, e1, e5, e6, e7⟩ := f3 (p := p) (P := P) (R := R) x ω4 μ4 M c' q (by omega) hq0 hq'
      (by omega) h1' (by rw [r4 _ _ (by omega) (by omega)]; exact s88)
      (by rw [r4 _ _ (by omega) (by omega)]; exact s112)
      (fun a h1 h2 => Memory.readable_of_writable (H4.st a (by omega) (by omega)))
    obtain ⟨hcq4, -⟩ := keep4 cq hcq hcqu hcqo
    obtain ⟨ω6, μ6, run6, H6, k6, keep6, f1', -, -⟩ := free_opt (p := p) (P := P) (R := R) env x ω5 μ4
      (free s (co.addr + 32)) M 210 6349 cq H4 hcq4 hcqu e0 (e1.trans h1') (by rw [e7, hcqa])
      ⟨by decide, by decide, by decide⟩ jte_104 bs_6349 ⟨by omega, by omega, by omega⟩
    obtain ⟨ω', μ', run', g0, g1, g5, g6, g7, g8, e⟩ := fin ω6 μ6 _ _ H6 ((pre.trans run5).trans run6)
      (f1'.trans (e1.trans h1')) (fun a h0 h => by rw [k6 a h0 h, k4 a h0 h, k2 a h0 h]) (by omega)
    subst e
    refine ⟨ω', μ', _, run', H6, g0, g1, g5, g6, g7, g8, fun a h0 h => by rw [k6 a h0 h, k4 a h0 h, k2 a h0 h],
      fun d hd hu hne hne' => ?_⟩
    obtain ⟨hd4, hk4⟩ := keep4 d hd hu hne
    obtain ⟨hd6, hk6⟩ := keep6 d hd4 hu (hne' hq0)
    refine ⟨hd6, fun a ha => ?_⟩
    obtain ⟨-, -, hdT⟩ := Decode.VecU8.chunk_in H.wf hd hu
    rw [hk6 a ha, hk4 a ha]
    unfold InData at ha
    exact bfr a (by omega) (by omega)

end Services.Bootstrap.Refine.Fin
