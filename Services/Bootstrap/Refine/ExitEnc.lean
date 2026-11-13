import Services.Bootstrap.Refine.Exit
import Services.Bootstrap.Encode.Loop

/-!
# Refine's exit: the output handed to the encoder

After the `Debug` line (6159 … 6209), refine moves its output `Vec<Instruction>` `{cap, ptr, n}` from M + 248
to M + 168, puts the work item's index (the low 16 bits of the word at M + 80) after it at M + 192, opens the
encoder's frame at M − 80 (`BootstrapWorkOutput::encode`, inlined: the output `Vec<u8>` goes to M + 272, the
value at M + 168, the return address 204) and calls `alloc(232 n + 6, 1)` (40494), which returns into the
encoder at 30073 (return address 1414). This is the `encode()` of `Service::refine`'s result, GP v0.8.0
Appendix B.4 (Ψ_R running bootstrap's code).
-/

namespace Services.Bootstrap.Refine.ExitEnc

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Encode.Writer
  Services.Bootstrap.Decode.HeapCtx

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 6209 … 6291: the output moved to M + 168, the work item's index to M + 192, the encoder's frame at
    M − 80 (M + 272, M + 168 and n at M − 80, M − 72, M − 64; return address 204 and ω₅, ω₆ at M − 8,
    M − 16, M − 24), and the call `alloc(232 n + 6, 1)` with return address 1414. Memory changes only in
    [M − 80, M) and [M + 168, M + 194). -/
theorem en1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (M cap ptr n w : Nat)
    (hM : 65536 + 80 ≤ M ∧ M + 304 ≤ 4294967296 ∧ M % 8 = 0) (hcap : cap < 18446744073709551616)
    (hptr : ptr < 18446744073709551616) (hn : 232 * n + 6 < 18446744073709551616)
    (hw64 : w < 18446744073709551616) (h1 : ω[1] = UInt64.ofNat M)
    (s248 : μ.readN (M + 248) 8 = Num.encodeLE 8 cap) (s256 : μ.readN (M + 256) 8 = Num.encodeLE 8 ptr)
    (s264 : μ.readN (M + 264) 8 = Num.encodeLE 8 n) (s80 : μ.readN (M + 80) 8 = Num.encodeLE 8 w)
    (hr : ∀ a, M + 80 ≤ a → a < M + 88 → μ.readable a = true)
    (hr2 : ∀ a, M + 248 ≤ a → a < M + 272 → μ.readable a = true)
    (hw : ∀ a, M - 80 ≤ a → a < M → μ.writable a = true)
    (hw2 : ∀ a, M + 168 ≤ a → a < M + 194 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 6209 ω μ x 40494 ω' μ' x 40 ∧
      ω'[0] = UInt64.ofNat 1414 ∧ ω'[1] = UInt64.ofNat (M - 80) ∧ ω'[5] = UInt64.ofNat (232 * n + 6) ∧
      ω'[6] = UInt64.ofNat (232 * n) ∧ ω'[7] = UInt64.ofNat (232 * n + 6) ∧ ω'[8] = UInt64.ofNat 1 ∧
      μ'.readN (M + 168) 8 = Num.encodeLE 8 cap ∧ μ'.readN (M + 176) 8 = Num.encodeLE 8 ptr ∧
      μ'.readN (M + 184) 8 = Num.encodeLE 8 n ∧ μ'.readN (M + 192) 2 = Num.encodeLE 2 (w % 65536) ∧
      μ'.readN (M - 80) 8 = Num.encodeLE 8 (M + 272) ∧ μ'.readN (M - 80 + 8) 8 = Num.encodeLE 8 (M + 168) ∧
      μ'.readN (M - 80 + 16) 8 = Num.encodeLE 8 n ∧ μ'.readN (M - 80 + 72) 8 = Num.encodeLE 8 204 ∧
      μ'.readN (M - 80 + 64) 8 = Num.encodeLE 8 ω[5].toNat ∧ μ'.readN (M - 80 + 56) 8 = Num.encodeLE 8 ω[6].toNat ∧
      (∀ a, a < 4294967296 → (a < M - 80 ∨ M ≤ a) → (a < M + 168 ∨ M + 194 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hM0, hM1, hM8⟩ := hM
  have rc := rd8 hcap s248
  have rp := rd8 hptr s256
  have rn := rd8 (by omega) s264
  have rw := rd8 hw64 s80
  have hr3 : ∀ a, M - 80 ≤ a → a < M → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hr4 : ∀ a, M + 168 ≤ a → a < M + 194 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw2 a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hM0, hM1, hM8, hr, hr2, hr3, hr4, hw, hw2, rc, rp, rn, rw, Exit.rdN_writeN_enc8,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_,
      fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]
    post_simp

/-- 40611: `alloc`'s return into the encoder (return address 1414, the jump-table entry 30073). -/
theorem alloc_ret {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (h0 : ω[0] = UInt64.ofNat 1414) : FreeStepsH p R 40611 ω μ x 30073 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0]

end Services.Bootstrap.Refine.ExitEnc
