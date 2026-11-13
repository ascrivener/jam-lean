import Services.Bootstrap.Decode.VecPairsBig

/-!
# `RawVec::grow_one` for refine's output `Vec<Instruction>` (32785)

`grow_one` (32785 … 32858) grows a `RawVec` of 232-octet elements at alignment 8 (refine's output
`Vec<Instruction>`, each `Instruction` 232 octets in memory) by at least one element. With ω₇ = V the
`RawVec`'s address (capacity at V, pointer at V + 8), it opens a 48-octet frame at S = sp − 48 (ω₀,
ω₅, ω₆ at S + 40, S + 32, S + 24), computes the new capacity max(2·cap, 4), and calls `finish_grow`
(32989; result slot S, return address 1516, the jump-table entry 757 = 32830) for that capacity of
232-octet elements at alignment 8, with the old buffer (cap, ptr). On `Ok` it stores the new
capacity at V and the new block at V + 8, restores ω₀, ω₅, ω₆ and returns; on `Err` it traps
(32858, the `handle_error` path, not taken here).

`finish_grow` calls `alloc` (40494) when there is no old buffer (cap = 0) and `realloc` (40701)
otherwise. `grow_one_first` is the first case (refine's first push), with the globals below the
allocator (`Glob`) kept; `grow_one_call` is both cases. Either `grow_one` returns, or the run reaches
a failed allocator call (`LoopA.Exhausts`).

GP v0.8.0: the octets are read from and written to the service's memory by the PVM (Appendix A); the
`Vec<Instruction>` is the bootstrap service's own result of refinement (§B.7, the bootstrap
service's refine argument).
-/

namespace Services.Bootstrap.Decode.GrowOne

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.Decode.VecU8

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {X : Type} {R : HostRel X}

/-- 32785 … 32824: `grow_one` opens its 48-octet frame at S (ω₀, ω₅, ω₆ at S + 40, S + 32, S + 24),
    reads the capacity oc (V) and pointer op (V + 8) of the `RawVec` at V (ω₇), and calls
    `finish_grow` for the capacity max(2·oc, 4) (ω₆ = ω₁₀) of 232-octet elements at alignment 8,
    with the old buffer (ω₈ = oc, ω₉ = op), result slot S (ω₇), return address 1516. -/
theorem q1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S V oc op r0 v5 v6 : Nat) (hS : 65536 ≤ S ∧ S + 48 < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat (S + 48)) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat V)
    (hr0 : r0 < 18446744073709551616) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hV : S + 48 ≤ V ∧ V + 16 ≤ 4294967296) (hoc : oc < 4294967296) (hop : op < 18446744073709551616)
    (sV0 : μ.readN V 8 = Num.encodeLE 8 oc) (sV8 : μ.readN (V + 8) 8 = Num.encodeLE 8 op)
    (hw : ∀ a, S ≤ a → a < S + 48 → μ.writable a = true)
    (hrV : ∀ a, V ≤ a → a < V + 16 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 32785 ω μ x 32989 ω' μ' x 16 ∧
      ω'[0] = UInt64.ofNat 1516 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat V ∧
      ω'[6] = UInt64.ofNat (max (2 * oc) 4) ∧ ω'[7] = UInt64.ofNat S ∧ ω'[8] = UInt64.ofNat oc ∧
      ω'[9] = UInt64.ofNat op ∧ ω'[10] = UInt64.ofNat (max (2 * oc) 4) ∧ ω'[11] = UInt64.ofNat 8 ∧
      ω'[12] = UInt64.ofNat 232 ∧
      μ'.readN (S + 40) 8 = Num.encodeLE 8 r0 ∧ μ'.readN (S + 32) 8 = Num.encodeLE 8 v5 ∧
      μ'.readN (S + 24) 8 = Num.encodeLE 8 v6 ∧
      (∀ a, a < 4294967296 → (a < S + 24 ∨ S + 48 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S ≤ a → a < S + 48 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have r0' := rd8'' (by omega) sV0
  have r8' := rd8'' hop sV8
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, hS, hV, hw, hr, hrV, r0', r8', hoc, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals (congr 1; rw [Nat.max_def]; split <;> split <;> omega)

/-- 32989 … 33084, `finish_grow` with no old buffer (ω₈ = 0) for 1 ≤ n ≤ 2²² elements of 232 octets at
    alignment 8: as `VecPairs.g1e` (which bounds the element size by 64), it calls `alloc` (40494) for
    232·n octets at alignment 8 (return address 1526). -/
theorem g1i {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (F res n r0 v5 v6 : Nat) (hF : 65536 ≤ F ∧ F + 40 < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat (F + 40)) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat res) (h8 : ω[8] = UInt64.ofNat 0)
    (h10 : ω[10] = UInt64.ofNat n) (h11 : ω[11] = UInt64.ofNat 8) (h12 : ω[12] = UInt64.ofNat 232)
    (hr0 : r0 < 18446744073709551616) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hres : res < 18446744073709551616) (hn : 1 ≤ n ∧ n ≤ 4194304)
    (hw : ∀ a, F ≤ a → a < F + 40 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 32989 ω μ x 40494 ω' μ' x 25 ∧
      ω'[0] = UInt64.ofNat 1526 ∧ ω'[1] = UInt64.ofNat F ∧ ω'[6] = UInt64.ofNat res ∧
      ω'[7] = UInt64.ofNat (232 * n) ∧ ω'[8] = UInt64.ofNat 8 ∧
      μ'.readN (F + 32) 8 = Num.encodeLE 8 r0 ∧ μ'.readN (F + 24) 8 = Num.encodeLE 8 v5 ∧
      μ'.readN (F + 16) 8 = Num.encodeLE 8 v6 ∧ μ'.readN (F + 8) 8 = Num.encodeLE 8 (232 * n) ∧
      (∀ a, a < 4294967296 → (a < F ∨ F + 40 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, F ≤ a → a < F + 40 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hEn : 232 * n < 274877906944 := by omega
  have hEn0 : ¬ 232 * n = 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, h10, h11, h12, hF, hw, hr, hn, hEn, hEn0, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, PVM.Memory.readN_writeN_same,
      PVM.Memory.readN_writeN_disjoint, PVM.Memory.read_writeN_disjoint, PVM.Memory.readable_writeN,
      PVM.Memory.writable_writeN, PVM.Num.length_encodeLE, List.length_cons, List.length_nil, PVM.two32]
    all_goals first
      | (rw [VecU8.rdN_writeN_same8 _ _ _ (by omega), Nat.mod_eq_of_lt (by omega)])
      | (rw [VecU8.rdN_writeN_lit _ _ _ (by rfl) (by omega)]; rfl)

/-- 32989 … 33049: `finish_grow` with an old buffer q of capacity L ≥ 1 (ω₈ = L, ω₉ = q), the new
    capacity 1 ≤ N ≤ 2²² (ω₁₀), alignment 8 and element size 232: as `VecPairs.g3e` (which bounds the
    element size by 64), it calls `realloc` (40701) for q to 232·N octets at alignment 8 (ω₇ = q,
    ω₉ = 8, ω₁₀ = 232·N, return address 1524), 232·N also at F + 8. -/
theorem g3i {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (F res L q N r0 v5 v6 : Nat) (hF : 65536 ≤ F ∧ F + 40 < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat (F + 40)) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat res) (h8 : ω[8] = UInt64.ofNat L)
    (h9 : ω[9] = UInt64.ofNat q) (h10 : ω[10] = UInt64.ofNat N) (h11 : ω[11] = UInt64.ofNat 8)
    (h12 : ω[12] = UInt64.ofNat 232)
    (hr0 : r0 < 18446744073709551616) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hres : res < 18446744073709551616) (hL : 1 ≤ L ∧ L < 4294967296) (hN : 1 ≤ N ∧ N ≤ 4194304)
    (hq : q < 18446744073709551616)
    (hw : ∀ a, F ≤ a → a < F + 40 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 32989 ω μ x 40701 ω' μ' x 25 ∧
      ω'[0] = UInt64.ofNat 1524 ∧ ω'[1] = UInt64.ofNat F ∧ ω'[6] = UInt64.ofNat res ∧
      ω'[7] = UInt64.ofNat q ∧ ω'[9] = UInt64.ofNat 8 ∧ ω'[10] = UInt64.ofNat (232 * N) ∧
      μ'.readN (F + 32) 8 = Num.encodeLE 8 r0 ∧ μ'.readN (F + 24) 8 = Num.encodeLE 8 v5 ∧
      μ'.readN (F + 16) 8 = Num.encodeLE 8 v6 ∧ μ'.readN (F + 8) 8 = Num.encodeLE 8 (232 * N) ∧
      (∀ a, a < 4294967296 → (a < F ∨ F + 40 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, F ≤ a → a < F + 40 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hEn : 232 * N < 274877906944 := by omega
  have hEn0 : ¬ 232 * N = 0 := by omega
  have hL0 : ¬ L = 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, h9, h10, h11, h12, hF, hw, hr, hL, hL0, hN, hEn, hEn0,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals (try simp only [show F + 40 - 40 = F by omega]); post_simp
    all_goals try (congr 1; omega)

/-- 32830 … 32856: `finish_grow` returned `Ok` (0 at S) with the block q at S + 8: `grow_one` stores
    the new capacity N (ω₆) at V (ω₅) and q at V + 8, restores ω₀, ω₅, ω₆ from its frame and returns
    to the address saved at S + 40. -/
theorem q2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S V N q ret t v5 v6 : Nat) (hS : 65536 ≤ S ∧ S + 48 < 4294967296)
    (hV : S + 48 ≤ V ∧ V + 16 ≤ 4294967296)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat V) (h6 : ω[6] = UInt64.ofNat N)
    (hN : N < 18446744073709551616) (hq : q < 18446744073709551616)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (s0 : μ.readN S 8 = Num.encodeLE 8 0) (s8 : μ.readN (S + 8) 8 = Num.encodeLE 8 q)
    (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 ret) (s32 : μ.readN (S + 32) 8 = Num.encodeLE 8 v5)
    (s24 : μ.readN (S + 24) 8 = Num.encodeLE 8 v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hr : ∀ a, S ≤ a → a < S + 48 → μ.readable a = true)
    (hwV : ∀ a, V ≤ a → a < V + 16 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 32830 ω μ x t ω' μ' x 16 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (S + 48) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN V 8 = Num.encodeLE 8 N ∧ μ'.readN (V + 8) 8 = Num.encodeLE 8 q ∧
      (∀ a, a < 4294967296 → (a < V ∨ V + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r0 := rd8'' (by decide) s0
  have r8 := rd8'' hq s8
  have r40 := rd8'' (by omega) s40
  have r32 := rd8'' hv5 s32
  have r24 := rd8'' hv6 s24
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hS, hV, hr, hwV, r0, r8, r40, r32, r24, hret, hjt, hbt,
      rdN_writeN_disjoint, rdN_writeN_same8, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try decide

open Picoalloc JAM Services.Bootstrap.Decode.HeapCtx in
/-- **Writes above 2³¹ keep the allocator's context** (`VecU8.ctx_congr_data` for no chunk: a
    well-formed heap has one). -/
theorem ctx_high {env : RefineHost.Env} {pb S0 S1 : Nat} {μ μ' : Memory} {s : State}
    (H : HeapCtx env pb S0 S1 μ s) (wf : ∀ a, a < 2147483648 → μ'.read a = μ.read a)
    (ww : ∀ a, μ'.writable a = μ.writable a) : HeapCtx env pb S0 S1 μ' s := by
  have ht := H.wf.2.2.2.1
  unfold TilesOk at ht
  cases hcs : chunks s with
  | nil =>
    rw [hcs] at ht
    have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
    have e : s.base = s.top := ht
    omega
  | cons c cs =>
    exact ctx_congr_data H (c := c) (by rw [hcs]; exact List.mem_cons_self) (fun a h _ => wf a h) ww

open Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.AllocOk Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA in
/-- **`grow_one` on an empty `RawVec<Instruction>`** (32785; refine's first push): with ω₇ = V, the
    `RawVec` at V holding capacity 0 (and any dangling pointer op at V + 8), the allocator's context
    `HeapCtx` under `refineContractK cap` (cap ≥ 2²⁷), either the model's `alloc` of ⌈232·4/32⌉ = 29
    units gives `(q, s')` and `grow_one` returns to t with the capacity 4 at V and q at V + 8, q the data
    of a new allocated chunk of 30 units (no allocated chunk of `s` is it, nor has its data at q), the
    context kept for `s'`, every allocated chunk of `s` kept with its data, the stack from sp up kept
    except V … V + 16, and the globals below the allocator (`Glob`) kept; or the run reaches a failed
    `alloc` (`Exhausts`). -/
theorem grow_one_first {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs) (μ : Memory)
    {hb : Nat} (s : State) (sp V op ret t v5 v6 pb S0 S1 : Nat)
    (H : HeapCtx env pb S0 S1 μ s)
    (hS : S0 + 256 ≤ sp ∧ sp ≤ S1) (hsp : 2147483904 ≤ sp) (hV : sp ≤ V ∧ V + 16 ≤ S1)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat V)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616) (hop : op < 18446744073709551616)
    (sV0 : μ.readN V 8 = Num.encodeLE 8 0) (sV8 : μ.readN (V + 8) 8 = Num.encodeLE 8 op) :
    (∃ q s' ω' μ', alloc (growTo pb) hb 1 ((232 * 4 + 31) / 32) s = some (q, s') ∧
      FreeStepsH p (refineContractK cap env) 32785 ω μ x t ω' μ' x 700 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN V 8 = Num.encodeLE 8 4 ∧ μ'.readN (V + 8) 8 = Num.encodeLE 8 q ∧
      HeapCtx env pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (⟨q - 32, (232 * 4 + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ ⟨q - 32, (232 * 4 + 31) / 32 + 1, true⟩) ∧
      (∀ d ∈ chunks s, d.used = true → d.addr + 32 ≠ q) ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InData c a → μ'.read a = μ.read a) ∧
      PagesOut 48 pb μ μ' ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < V ∨ V + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) ∧ (∀ a, S0 ≤ a → μ'.writable a = μ.writable a)) ∨
    Exhausts env cap pb p P 32785 ω μ x 700 := by
  have hb0 := H.hb0
  have hbT := H.hbT
  have hS1 := H.hS1
  have hst := H.st
  -- the frame S = sp − 48 and the call of finish_grow
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, a10, a11, a12, m40, m32, m24, fr1, rd1, wr1⟩ :=
    q1 (p := p) (P := P) (R := refineContractK cap env) x ω μ (sp - 48) V 0 op ret v5 v6 ⟨by omega, by omega⟩
      h0 (by rw [h1]; congr 1; omega) h5 h6 h7 (by omega) hv5 hv6 ⟨by omega, by omega⟩ (by decide) hop sV0 sV8
      (fun a h1 h2 => hst a (by omega) (by omega))
      (fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)))
  have hmax : max (2 * 0) 4 = 4 := rfl
  rw [hmax] at a6 a10
  obtain ⟨ω2, μ2, run2, b0, b1, b6, b7, b8, n32, n24, n16, n8, fr2, rd2, wr2⟩ :=
    g1i (p := p) (P := P) (R := refineContractK cap env) x ω1 μ1 (sp - 88) (sp - 48) 4 1516 V 4
      ⟨by omega, by omega⟩ a0 (by rw [a1]; congr 1; omega) a5 a6 a7 a8 a10 a11 a12 (by decide) (by omega)
      (by decide) (by omega) (by decide) (fun a h1 h2 => by rw [wr1]; exact hst a (by omega) (by omega))
  have hlow : ∀ a, a < 4294967296 → (a < sp - 88 ∨ sp ≤ a) → μ2.read a = μ.read a := fun a h0 h1 =>
    (fr2 a h0 (by omega)).trans (fr1 a h0 (by omega))
  have wr12 : ∀ a, μ2.writable a = μ.writable a := fun a => by rw [wr2, wr1]
  have H2 : HeapCtx env pb S0 S1 μ2 s := ctx_high H (fun a h => hlow a (by omega) (Or.inl (by omega))) wr12
  -- alloc
  rcases alloc_call (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω2 μ2 s (sp - 88) (232 * 4) 8 pb S0 S1 H2
      b1 b7 b8 (by decide) (by decide) (by decide) (by omega) ⟨by omega, by omega⟩ with
    ⟨q, s', ω3, μ3, ha, run3, H3, keep, hnew, hfresh, hk, e7, stk3, e0, e1, e5, e6⟩ |
    ⟨hna, ω3, μ3, run3, e7, -, -, -, -, -⟩
  rotate_left
  · exact Or.inr (Exhausts.of_alloc ((run1.trans (run2.trans run3)).mono (by omega)) e7 hna)
  obtain ⟨hqb, hqT, hqT'⟩ := chunk_in H3.wf hnew rfl
  simp only at hqb hqT hqT'
  have hbase' : s'.base = s.base := alloc_base H.wf ha
  rw [hbase'] at hqb hqT hqT'
  have kd : ∀ d ∈ chunks s, d.used = true → ∀ a, InData d a → μ3.read a = μ2.read a := fun d hd hu a ha =>
    hk.hkeep a (off_hdr_data H3.wf H3.hb0 H3.hbT (keep d hd hu) ha.1 ha.2)
  have run4 := alloc_ret (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (by rw [e0, b0])
  have hF : ∀ a, sp - 88 ≤ a → a < 4294967296 → μ3.read a = μ2.read a := fun a h1 h2 => stk3 a h2 h1
  obtain ⟨ω5, μ5, run5, c0, c1, c5, c6, cres, cres8, cres16, fr5, rd5, wr5⟩ :=
    g2 (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (sp - 88) (sp - 48) (232 * 4) q 1516 32830 V 4
      ⟨by omega, by omega⟩ (by omega) (Or.inr (by omega)) (by rw [e1, b1]) (by rw [e6, b6]) e7
      ⟨by omega, by omega⟩ (by decide) (by omega) (by decide)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n32)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n24)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n16)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n8)
      (by decide) jte_757 bs_32830
      (fun a h1 h2 => Memory.readable_of_writable (H3.st a (by omega) (by omega)))
      (fun a h1 h2 => H3.st a (by omega) (by omega))
  have h51 : ∀ a, sp - 48 + 24 ≤ a → a < 4294967296 → μ5.read a = μ1.read a := fun a h1 h2 =>
    (fr5 a h2 (Or.inr (by omega))).trans ((hF a (by omega) h2).trans (fr2 a h2 (Or.inr (by omega))))
  obtain ⟨ω6, μ6, run6, d0, d1, d5, d6, dV, dV8, fr6, rd6, wr6⟩ :=
    q2 (p := p) (P := P) (R := refineContractK cap env) x ω5 μ5 (sp - 48) V 4 q ret t v5 v6 ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ (by rw [c1]; congr 1; omega) c5 c6 (by decide) (by omega) hv5 hv6 cres cres8
      (by rw [Memory.readN_congr (fun j hj => h51 _ (by omega) (by omega))]; exact m40)
      (by rw [Memory.readN_congr (fun j hj => h51 _ (by omega) (by omega))]; exact m32)
      (by rw [Memory.readN_congr (fun j hj => h51 _ (by omega) (by omega))]; exact m24)
      hret hjt hbt
      (fun a h1 h2 => by rw [rd5]; exact Memory.readable_of_writable (H3.st a (by omega) (by omega)))
      (fun a h1 h2 => by rw [wr5]; exact H3.st a (by omega) (by omega))
  have hlate : ∀ a, a < 2147483648 → μ6.read a = μ3.read a := fun a h =>
    (fr6 a (by omega) (Or.inl (by omega))).trans (fr5 a (by omega) (Or.inl (by omega)))
  have wr63 : ∀ a, μ6.writable a = μ3.writable a := fun a => by rw [wr6, wr5]
  have run16 := run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))
  refine Or.inl ⟨q, s', ω6, μ6, ha, run16.mono (by omega), d0, by rw [d1]; congr 1; omega, d5, d6, dV, dV8,
    ctx_high H3 hlate wr63, keep, hnew, hfresh, ?_, ?_, FreeStepsH.pagesOut H.bd run16, ?_, ?_, ?_, ?_⟩
  · intro d hd hu e
    have ht := H3.wf.2.2.2.1
    unfold TilesOk at ht
    have := Tiles.addr_inj ht d (keep d hd hu) _ hnew (by simp only; omega)
    exact hfresh d hd hu this
  · intro d hd hu a ha
    have hca := ha
    unfold InData at hca
    have := (chunk_in H.wf hd hu).2.2
    rw [hlate a (by omega), kd d hd hu a ha]
    exact hlow a (by omega) (Or.inl (by omega))
  · intro a h0 h1 h2
    rw [fr6 a h0 h2, fr5 a h0 (Or.inr (by omega)), hF a (by omega) h0]
    exact hlow a h0 (Or.inr h1)
  · intro a ha'
    obtain ⟨kp, kr⟩ := FreeStepsH.keepRO H.bd run16
    refine ⟨kr a (by unfold two32; omega) (Or.inl (by unfold pageSize; omega)) (H.ro a ha'), ?_⟩
    unfold Memory.readable
    rw [kp _ (Or.inl (by unfold pageSize; omega))]
  · intro a ha'
    have hg := ha'
    unfold Glob at hg
    have ht3 := H3.wf.2.2.2.1
    unfold TilesOk at ht3
    have hb3 := H3.hb0
    rw [hlate a (by omega),
      hk.glob (fun b ⟨c, hc, e⟩ => Or.inr (by have := (ht3.mem_lt c hc).1; omega)) a ha']
    exact hlow a (by omega) (Or.inl (by omega))
  · intro a ha'
    obtain ⟨kp, -⟩ := FreeStepsH.keepRO H.bd run16
    have := H.hSb
    unfold Memory.writable
    rw [kp _ (Or.inr (by unfold pageSize; omega))]

open Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.AllocOk Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Decode.ReallocCall Services.Bootstrap.Decode.ReallocKeepAll in
/-- **`grow_one` on a `RawVec<Instruction>`** (32785; GP v0.8.0 §B.7, refine's output): with ω₇ = V, the
    `RawVec` at V holding capacity oc ≤ 2²¹ and pointer op (at V + 8), op the data address of an
    allocated chunk of ⌈232·oc/32⌉ + 1 units when oc ≥ 1, and the allocator's context `HeapCtx` under
    `refineContractK cap` (cap ≥ 2²⁷): either `grow_one` returns to t with the new capacity
    max(2·oc, 4) at V and the new block q at V + 8, q the data of an allocated chunk of
    ⌈232·max(2·oc, 4)/32⌉ + 1 units holding the old buffer's 232·oc octets, the context kept for the
    new state `s'`, every other allocated chunk of `s` kept with its data, no such chunk with its data
    at q, the stack from sp up kept except V … V + 16, the globals below the allocator (`Glob`) kept;
    or the run reaches a failed allocator call
    (`Exhausts`: `alloc` for oc = 0, `realloc` otherwise). -/
theorem grow_one_call {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs)
    (μ : Memory) {hb : Nat} (s : State) (sp V oc op ret t v5 v6 pb S0 S1 : Nat)
    (H : HeapCtx env pb S0 S1 μ s)
    (hold : oc = 0 ∨ ∃ c ∈ chunks s, c.addr + 32 = op ∧ c.used = true ∧ c.size = (232 * oc + 31) / 32 + 1)
    (hoc : oc ≤ 2097152)
    (hS : S0 + 408 ≤ sp ∧ sp ≤ S1) (hsp : 2147484056 ≤ sp ∧ sp % 8 = 0) (hV : sp ≤ V ∧ V + 16 ≤ S1)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat V)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616) (hop : op < 18446744073709551616)
    (sV0 : μ.readN V 8 = Num.encodeLE 8 oc) (sV8 : μ.readN (V + 8) 8 = Num.encodeLE 8 op) :
    (∃ q s' ω' μ', FreeStepsH p (refineContractK cap env) 32785 ω μ x t ω' μ' x
        (64 * ((232 * oc + 31) / 32) + 1500) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN V 8 = Num.encodeLE 8 (max (2 * oc) 4) ∧ μ'.readN (V + 8) 8 = Num.encodeLE 8 q ∧
      (⟨q - 32, (232 * max (2 * oc) 4 + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      μ'.readN q (232 * oc) = μ.readN op (232 * oc) ∧
      HeapCtx env pb S0 S1 μ' s' ∧
      (∀ c ∈ chunks s, c.used = true → c.addr + 32 ≠ op →
        c ∈ chunks s' ∧ ∀ a, InData c a → μ'.read a = μ.read a) ∧
      (∀ d ∈ chunks s, d.used = true → d.addr + 32 ≠ op → d.addr + 32 ≠ q) ∧
      PagesOut 48 pb μ μ' ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < V ∨ V + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) ∧ (∀ a, S0 ≤ a → μ'.writable a = μ.writable a)) ∨
    Exhausts env cap pb p P 32785 ω μ x (64 * ((232 * oc + 31) / 32) + 1500) := by
  by_cases hz : oc = 0
  · subst hz
    rcases grow_one_first (hb := hb) env cap hcap1 hcap x ω μ s sp V op ret t v5 v6 pb S0 S1 H
        ⟨by omega, hS.2⟩ (by omega) hV h0 h1 h5 h6 h7 hret hjt hbt hv5 hv6 hop sV0 sV8 with
      ⟨q, s', ω', μ', -, run, e0, e1, e5, e6, eV, eV8, H', keep, hnew, -, hfr, kd, po, stk, low, gl, wr⟩ | hx
    · exact Or.inl ⟨q, s', ω', μ', run.mono (by omega), e0, e1, e5, e6, eV, eV8, hnew, rfl, H',
        fun c hc hu _ => ⟨keep c hc hu, kd c hc hu⟩, fun d hd hu _ => hfr d hd hu, po, stk, low, gl, wr⟩
    · exact Or.inr (hx.mono (by omega))
  obtain ⟨cq, hcqm, hcqa, hcqu, hcqs⟩ := hold.resolve_left hz
  have hu : usable s op = (232 * oc + 31) / 32 := by rw [← hcqa, usable_of_chunk hcqm, hcqs]; rfl
  obtain ⟨hq0, -, hqT⟩ := chunk_in H.wf hcqm hcqu
  have hb0 := H.hb0
  have hbT := H.hbT
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst := H.st
  have hba : s.base % 8 = 0 := by have := H.wf.2.1; omega
  generalize hnc : max (2 * oc) 4 = nc
  have hnc1 : 2 * oc ≤ nc ∧ 4 ≤ nc ∧ nc ≤ 4194304 := by omega
  -- the frame S = sp − 48 and the call of finish_grow
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, a10, a11, a12, m40, m32, m24, fr1, rd1, wr1⟩ :=
    q1 (p := p) (P := P) (R := refineContractK cap env) x ω μ (sp - 48) V oc op ret v5 v6 ⟨by omega, by omega⟩
      h0 (by rw [h1]; congr 1; omega) h5 h6 h7 (by omega) hv5 hv6 ⟨by omega, by omega⟩ (by omega) hop sV0 sV8
      (fun a h1 h2 => hst a (by omega) (by omega))
      (fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)))
  rw [hnc] at a6 a10
  obtain ⟨ω2, μ2, run2, b0, b1, b6, b7, b9, b10, n32, n24, n16, n8, fr2, rd2, wr2⟩ :=
    g3i (p := p) (P := P) (R := refineContractK cap env) x ω1 μ1 (sp - 88) (sp - 48) oc op nc 1516 V nc
      ⟨by omega, by omega⟩ a0 (by rw [a1]; congr 1; omega) a5 a6 a7 a8 a9 a10 a11 a12 (by decide) (by omega)
      (by omega) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hop
      (fun a h1 h2 => by rw [wr1]; exact hst a (by omega) (by omega))
  have hlow : ∀ a, a < 4294967296 → (a < sp - 88 ∨ sp ≤ a) → μ2.read a = μ.read a := fun a h0 h1 =>
    (fr2 a h0 (by omega)).trans (fr1 a h0 (by omega))
  have wr12 : ∀ a, μ2.writable a = μ.writable a := fun a => by rw [wr2, wr1]
  have H2 : HeapCtx env pb S0 S1 μ2 s := ctx_high H (fun a h => hlow a (by omega) (Or.inl (by omega))) wr12
  -- realloc
  rcases realloc_call (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω2 μ2 s (sp - 88) op 8 (232 * nc) pb
      S0 S1 H2 ⟨cq, hcqm, hcqa, hcqu⟩ (by omega) (by omega) hba b1 b7 b9 b10 (by decide) (by decide)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ with
    ⟨r, s', b, ω3, μ3, hR, run3, e7, H3, dat3, keep3, ⟨cr, hcrm, hcra, hcru, hcrs⟩, kp3, stk3, -, -, e0, e1,
      e5, e6, gl3, -, -⟩ |
    ⟨hR, ω3, μ3, run3, e7, -, -, e0, -, -, -, -⟩
  rotate_left
  · rw [hu] at run3
    have run4 := realloc_ret (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (by rw [e0, b0])
    exact Or.inr (Exhausts.of_realloc ((run1.trans (run2.trans (run3.trans run4))).mono (by omega)) e7 hR)
  have hR1 : realloc (growTo pb) hb s op 1 ((232 * nc + 31) / 32) = some (r, s', b) := hR
  have hfr := realloc_fresh H.wf ⟨cq, hcqm, hcqa, hcqu⟩ (by omega) hR1
  rw [hu, Nat.min_eq_left (by omega)] at dat3
  rw [hu] at run3
  obtain ⟨hr0, -, hrT⟩ := chunk_in H3.wf hcrm hcru
  rw [hcrs] at hrT
  have hb3 := H3.hb0
  have hbT3 := H3.hbT
  have run4 := realloc_ret (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (by rw [e0, b0])
  have hF : ∀ a, sp - 88 ≤ a → a < 4294967296 → μ3.read a = μ2.read a := fun a h1 h2 => stk3 a h2 h1
  -- back in finish_grow
  obtain ⟨ω5, μ5, run5, c0, c1, c5, c6, cres, cres8, cres16, fr5, rd5, wr5⟩ :=
    g2r (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (sp - 88) (sp - 48) (232 * nc) r 1516 32830 V nc
      ⟨by omega, by omega⟩ (by omega) (Or.inr (by omega)) (by rw [e1, b1]) (by rw [e6, b6]) e7
      ⟨by omega, by omega⟩ (by omega) (by omega) (by omega)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n32)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n24)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n16)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n8)
      (by decide) jte_757 bs_32830
      (fun a h1 h2 => Memory.readable_of_writable (H3.st a (by omega) (by omega)))
      (fun a h1 h2 => H3.st a (by omega) (by omega))
  have h51 : ∀ a, sp - 48 + 24 ≤ a → a < 4294967296 → μ5.read a = μ1.read a := fun a h1 h2 =>
    (fr5 a h2 (Or.inr (by omega))).trans ((hF a (by omega) h2).trans (fr2 a h2 (Or.inr (by omega))))
  obtain ⟨ω6, μ6, run6, d0, d1, d5, d6, dV, dV8, fr6, rd6, wr6⟩ :=
    q2 (p := p) (P := P) (R := refineContractK cap env) x ω5 μ5 (sp - 48) V nc r ret t v5 v6 ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ (by rw [c1]; congr 1; omega) c5 c6 (by omega) (by omega) hv5 hv6 cres cres8
      (by rw [Memory.readN_congr (fun j hj => h51 _ (by omega) (by omega))]; exact m40)
      (by rw [Memory.readN_congr (fun j hj => h51 _ (by omega) (by omega))]; exact m32)
      (by rw [Memory.readN_congr (fun j hj => h51 _ (by omega) (by omega))]; exact m24)
      hret hjt hbt
      (fun a h1 h2 => by rw [rd5]; exact Memory.readable_of_writable (H3.st a (by omega) (by omega)))
      (fun a h1 h2 => by rw [wr5]; exact H3.st a (by omega) (by omega))
  have hlate : ∀ a, a < 2147483648 → μ6.read a = μ3.read a := fun a h =>
    (fr6 a (by omega) (Or.inl (by omega))).trans (fr5 a (by omega) (Or.inl (by omega)))
  have wr63 : ∀ a, μ6.writable a = μ3.writable a := fun a => by rw [wr6, wr5]
  have run16 := run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))
  refine Or.inl ⟨r, s', ω6, μ6, run16.mono (by omega), d0, by rw [d1]; congr 1; omega, d5, d6, dV, dV8, ?_, ?_,
    ctx_high H3 hlate wr63, ?_, hfr, FreeStepsH.pagesOut H.bd run16, ?_, ?_, ?_, ?_⟩
  · rcases cr with ⟨ca, csz, cu⟩
    simp only at hcra hcru hcrs
    subst hcru hcrs
    rw [show r - 32 = ca by omega]
    exact hcrm
  · rw [Memory.readN_congr (fun j hj => hlate _ (by omega)),
      readN_prefix (show 232 * oc ≤ 32 * ((232 * oc + 31) / 32) by omega) dat3]
    exact Memory.readN_congr (fun j hj => hlow _ (by omega) (Or.inl (by omega)))
  · intro c hc hu hne
    refine ⟨keep3 c hc hu hne, fun a ha => ?_⟩
    have hca := ha
    unfold InData at hca
    have := (chunk_in H.wf hc hu).2.2
    rw [hlate a (by omega), kp3 a ⟨c, hc, hu, hne, ha⟩]
    exact hlow a (by omega) (Or.inl (by omega))
  · intro a h0 h1 h2
    rw [fr6 a h0 h2, fr5 a h0 (Or.inr (by omega)), hF a (by omega) h0]
    exact hlow a h0 (Or.inr h1)
  · intro a ha'
    obtain ⟨kp, kr⟩ := FreeStepsH.keepRO H.bd run16
    refine ⟨kr a (by unfold two32; omega) (Or.inl (by unfold pageSize; omega)) (H.ro a ha'), ?_⟩
    unfold Memory.readable
    rw [kp _ (Or.inl (by unfold pageSize; omega))]
  · intro a ha'
    have hg := ha'
    unfold Glob at hg
    rw [hlate a (by omega), gl3 a ha']
    exact hlow a (by omega) (Or.inl (by omega))
  · intro a ha'
    obtain ⟨kp, -⟩ := FreeStepsH.keepRO H.bd run16
    unfold Memory.writable
    rw [kp _ (Or.inr (by unfold pageSize; omega))]

end Services.Bootstrap.Decode.GrowOne
