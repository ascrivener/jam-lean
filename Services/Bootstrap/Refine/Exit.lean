import Services.Bootstrap.Encode.Writer
import Services.Bootstrap.Decode.DeallocCall
import Services.Bootstrap.Decode.HeapCtx

/-!
# Refine's transform loop: the exit and the `IntoIter` drop

When the transform loop's cursor reaches its end (5042 → 6120), refine drops the input instructions'
`vec::IntoIter` at M + 272: `{buf, ptr, cap, end}`. Here the iterator is empty (`ptr = end`), so its
drop (33214) frees only the buffer: it tail-calls `dealloc` (40613) on `buf` when `cap ≠ 0`, and
returns to 6130 (return address 198). This is `Service::refine`'s `for` ending, GP v0.8.0 Appendix B.4
(Ψ_R running bootstrap's code).
-/

namespace Services.Bootstrap.Refine.Exit

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Encode.Writer
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- A word stored and loaded back. -/
theorem rdN_writeN_enc8 (μ : Memory) (a v : Nat) :
    rdN (μ.writeN a (Num.encodeLE 8 v)) a 8 = v % 18446744073709551616 := by
  show Num.decodeLE _ = _
  rw [Memory.readN_writeN_same μ a 8 _ (Num.length_encodeLE 8 v) (by decide), Num.decodeLE_encodeLE]

/-- The return address 198, stored and loaded back. -/
theorem rdN_writeN_198 (μ : Memory) (a : Nat) :
    rdN (μ.writeN a [UInt8.ofNat 198, UInt8.ofNat 0, UInt8.ofNat 0, UInt8.ofNat 0, UInt8.ofNat 0, UInt8.ofNat 0,
      UInt8.ofNat 0, UInt8.ofNat 0]) a 8 = 198 :=
  rdN_writeN_enc8 μ a 198

/-- 6120 … 33825, with the iterator at M + 272 empty (`ptr = end`) and `cap ≠ 0`: `IntoIter::drop`
    opens an 88-octet frame at M − 88 and leaves it again, then jumps to `dealloc` (40613) with ω₇ = buf,
    ω₈ = 232·cap, ω₉ = 8, ω₀ = 198 (→ 6130), ω₁ = M, and ω₅, ω₆ as they were. Memory changes only in
    [M − 88, M). -/
theorem dr1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (M buf cur cap : Nat) (hM : 65536 + 88 ≤ M ∧ M + 304 ≤ 4294967296 ∧ M % 8 = 0)
    (hbuf : buf < 18446744073709551616) (hcur : cur < 18446744073709551616)
    (hcap : cap ≠ 0) (hcap' : 232 * cap < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat M)
    (s272 : μ.readN (M + 272) 8 = Num.encodeLE 8 buf) (s280 : μ.readN (M + 280) 8 = Num.encodeLE 8 cur)
    (s288 : μ.readN (M + 288) 8 = Num.encodeLE 8 cap) (s296 : μ.readN (M + 296) 8 = Num.encodeLE 8 cur)
    (hr : ∀ a, M + 272 ≤ a → a < M + 304 → μ.readable a = true)
    (hw : ∀ a, M - 88 ≤ a → a < M → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 6120 ω μ x 40613 ω' μ' x 40 ∧
      ω'[0] = UInt64.ofNat 198 ∧ ω'[1] = UInt64.ofNat M ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat buf ∧ ω'[8] = UInt64.ofNat (232 * cap) ∧ ω'[9] = UInt64.ofNat 8 ∧
      (∀ a, a < 4294967296 → (a < M - 88 ∨ M ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hM0, hM1, hM8⟩ := hM
  have rb := rd8 hbuf s272
  have rc := rd8 hcur s280
  have rk := rd8 (by omega) s288
  have re := rd8 hcur s296
  have hcap0 : ¬ cap = 0 := hcap
  have hr2 : ∀ a, M - 88 ≤ a → a < M → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hM0, hM1, hM8, hcap0, hr, hw, hr2, rb, rc, rk, re, rdN_writeN_enc8, rdN_writeN_198, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]
    post_simp
    all_goals try assumption
    all_goals try (congr 1; omega)

/-- 6120 … 6130, with the iterator at M + 272 empty and `cap = 0`: `IntoIter::drop` frees nothing and
    returns to 6130. Memory changes only in [M − 88, M). -/
theorem dr0 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (M buf cur : Nat) (hM : 65536 + 88 ≤ M ∧ M + 304 ≤ 4294967296 ∧ M % 8 = 0)
    (hbuf : buf < 18446744073709551616) (hcur : cur < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat M)
    (s272 : μ.readN (M + 272) 8 = Num.encodeLE 8 buf) (s280 : μ.readN (M + 280) 8 = Num.encodeLE 8 cur)
    (s288 : μ.readN (M + 288) 8 = Num.encodeLE 8 0) (s296 : μ.readN (M + 296) 8 = Num.encodeLE 8 cur)
    (hr : ∀ a, M + 272 ≤ a → a < M + 304 → μ.readable a = true)
    (hw : ∀ a, M - 88 ≤ a → a < M → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 6120 ω μ x 6130 ω' μ' x 40 ∧
      ω'[1] = UInt64.ofNat M ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      (∀ a, a < 4294967296 → (a < M - 88 ∨ M ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hM0, hM1, hM8⟩ := hM
  have rb := rd8 hbuf s272
  have rc := rd8 hcur s280
  have rk := rd8 (by decide) s288
  have re := rd8 hcur s296
  have hr2 : ∀ a, M - 88 ≤ a → a < M → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hM0, hM1, hM8, hr, hw, hr2, rb, rc, rk, re, rdN_writeN_enc8, rdN_writeN_198, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]
    post_simp
    all_goals try assumption
    all_goals try (congr 1; omega)

/-- 5042 … 6120: at the loop head with the cursor at its end (M + 144 = M + 120), the loop ends. -/
theorem ex0 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (M en : Nat)
    (hM : M + 152 ≤ 4294967296) (hen : en < 18446744073709551616) (h1 : ω[1] = UInt64.ofNat M)
    (s144 : μ.readN (M + 144) 8 = Num.encodeLE 8 en) (s120 : μ.readN (M + 120) 8 = Num.encodeLE 8 en)
    (hr : ∀ a, M + 120 ≤ a → a < M + 152 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 5042 ω μ x 6120 ω' μ x 4 ∧ ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat en ∧
      ω'[6] = ω[6] := by
  have rc := rd8 hen s144
  have re := rd8 hen s120
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hM, hr, rc, re, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]

/-- 6130 … 6159: the `Debug` line's setup. The arguments at M + 272 are `(&out, 1382)` (the output
    `Vec<Instruction>` at M + 248 and its `Debug` function), the template is at 66099, the `String` goes
    to M + 168, and `alloc::fmt::format` (59375) is called with return address 200 (→ 6166). Memory
    changes only at M + 272 … M + 288. -/
theorem ex1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (M : Nat)
    (hM : 65536 ≤ M ∧ M + 304 ≤ 4294967296 ∧ M % 8 = 0) (h1 : ω[1] = UInt64.ofNat M)
    (hw : ∀ a, M + 272 ≤ a → a < M + 288 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 6130 ω μ x 59375 ω' μ' x 10 ∧
      ω'[0] = UInt64.ofNat 200 ∧ ω'[1] = UInt64.ofNat M ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (M + 168) ∧ ω'[8] = UInt64.ofNat 66099 ∧ ω'[9] = UInt64.ofNat (M + 272) ∧
      μ'.readN (M + 272) 8 = Num.encodeLE 8 (M + 248) ∧ μ'.readN (M + 280) 8 = Num.encodeLE 8 1382 ∧
      (∀ a, a < 4294967296 → (a < M + 272 ∨ M + 288 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hM0, hM1, hM8⟩ := hM
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hM0, hM1, hM8, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]
    post_simp
    all_goals try assumption
    all_goals try (congr 1; omega)

end Services.Bootstrap.Refine.Exit
