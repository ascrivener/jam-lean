import Services.Bootstrap.Refine.LoopAll

/-!
# Refine's prologue into the transform loop

After `Instructions::decode` returns (4842) with the `Vec<Instruction>` `{cap, ptr, len}` at M + 168, refine
builds the output `Vec::new()` at M + 248, the input's `vec::IntoIter` at M + 272 and the loop's constants, and
enters the loop past its end test (5054) with ω₅ = ptr. `entry` gives `PInv` at 5054 for k = 0, with μ0 the
memory there. GP v0.8.0 Appendix B.4 (Ψ_R running bootstrap's code); `Spec.refine`'s `is.mapM`.
-/

namespace Services.Bootstrap.Refine.Entry

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeR
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Refine.PassLoop

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 4842 … 4899, the decode's result `{cap, ptr, len}` at M + 168 (cap not the error word 2^64 − 1, len ≠ 0):
    the output `{0, 8, 0}` at M + 248, the `IntoIter` `{ptr, ptr, cap, ptr + 232 len}` at M + 272 and its end
    at M + 120; on to 4903 with ω₁₀ = ptr. Memory changes only at M + 120 … M + 128 and M + 248 … M + 304. -/
theorem e1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (M cap ptr len : Nat) (hM : 65536 ≤ M ∧ M + 632 ≤ 4294967296 ∧ M % 8 = 0)
    (hcap : cap < 18446744073709551616) (hce : cap ≠ 18446744073709551615)
    (hptr : ptr + 232 * len < 18446744073709551616) (hl : len ≠ 0) (h1 : ω[1] = UInt64.ofNat M)
    (s168 : μ.readN (M + 168) 8 = Num.encodeLE 8 cap) (s176 : μ.readN (M + 176) 8 = Num.encodeLE 8 ptr)
    (s184 : μ.readN (M + 184) 8 = Num.encodeLE 8 len)
    (hr : ∀ a, M + 168 ≤ a → a < M + 192 → μ.readable a = true)
    (hw : ∀ a, M + 120 ≤ a → a < M + 304 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 4842 ω μ x 4903 ω' μ' x 20 ∧ ω'[1] = ω[1] ∧ ω'[10] = UInt64.ofNat ptr ∧
      μ'.readN (M + 248) 8 = Num.encodeLE 8 0 ∧ μ'.readN (M + 256) 8 = Num.encodeLE 8 8 ∧
      μ'.readN (M + 264) 8 = Num.encodeLE 8 0 ∧ μ'.readN (M + 272) 8 = Num.encodeLE 8 ptr ∧
      μ'.readN (M + 280) 8 = Num.encodeLE 8 ptr ∧ μ'.readN (M + 288) 8 = Num.encodeLE 8 cap ∧
      μ'.readN (M + 296) 8 = Num.encodeLE 8 (ptr + 232 * len) ∧
      μ'.readN (M + 120) 8 = Num.encodeLE 8 (ptr + 232 * len) ∧
      (∀ a, a < 4294967296 → (a < M + 120 ∨ (M + 128 ≤ a ∧ a < M + 248) ∨ M + 304 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hM0, hM1, hM8⟩ := hM
  have rc := rd8 hcap s168
  have rp := rd8 (by omega) s176
  have rl := rd8 (by omega) s184
  have hce' : ¬ cap = 18446744073709551615 := hce
  have hl' : ¬ len = 0 := hl
  have e : (len * 232 + ptr) % 18446744073709551616 = ptr + 232 * len := by
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have e' : (len * 232) % 18446744073709551616 = len * 232 := Nat.mod_eq_of_lt (by omega)
  have hr2 : ∀ a, M + 120 ≤ a → a < M + 304 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hM0, hM1, hM8, hce', hl', hr, hr2, hw, rc, rp, rl, e, e', rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]
    all_goals try simp only [show ptr + len * 232 = ptr + 232 * len by omega]
    post_simp

/-- 4903 … 5006: the loop's constants (M + 0 … M + 56, M + 128, M + 136), ω₅ = ptr (from ω₁₀), then into the
    loop at 5054. Memory changes only at M … M + 56 and M + 128 … M + 144. -/
theorem e2 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (M ptr : Nat) (hM : 65536 ≤ M ∧ M + 632 ≤ 4294967296 ∧ M % 8 = 0)
    (h1 : ω[1] = UInt64.ofNat M) (h10 : ω[10] = UInt64.ofNat ptr) (hp : ptr < 18446744073709551616)
    (hw : ∀ a, M ≤ a → a < M + 144 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 4903 ω μ x 5054 ω' μ' x 30 ∧ ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat ptr ∧
      μ'.readN (M + 16) 8 = Num.encodeLE 8 66793 ∧ μ'.readN (M + 24) 8 = Num.encodeLE 8 66506 ∧
      μ'.readN (M + 32) 8 = Num.encodeLE 8 668 ∧ μ'.readN (M + 40) 8 = Num.encodeLE 8 2098688 ∧
      μ'.readN (M + 48) 8 = Num.encodeLE 8 384307168202282325 ∧
      μ'.readN (M + 128) 8 = Num.encodeLE 8 9223372036854775832 ∧
      μ'.readN (M + 136) 8 = Num.encodeLE 8 9223372036854775809 ∧
      (∀ a, a < 4294967296 → (a < M ∨ (M + 56 ≤ a ∧ a < M + 128) ∨ M + 144 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hM0, hM1, hM8⟩ := hM
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h10, hM0, hM1, hM8, hw, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, Nat.mod_eq_of_lt hp]
    post_simp

/-- **Into the transform loop** (4842 … 5054): from the decode's `Vec<Instruction>` `{cap, E, n}` at M + 168
    (1 ≤ n < 128, its buffer the allocated chunk ce from E = ce.addr + 32), refine enters the loop at 5054
    with `PInv` for k = 0, μ0 being the memory there; any chunks to keep `Kp` must be allocated. Memory changes
    only in refine's frame (M … M + 56, M + 120 … M + 144, M + 248 … M + 304). -/
theorem entry {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (env : RefineHost.Env)
    (x : X) (ω : Regs) (μ : Memory) (s : State) {pb S0 S1 : Nat} (M cap n : Nat) (ce : Chunk)
    (Kp : Chunk → Prop) (O : Nat → List UInt8 → Prop) (H : HeapCtx env pb S0 S1 μ s)
    (hM : S0 + 456 ≤ M ∧ M + 648 ≤ S1 ∧ 2147484104 ≤ M ∧ M % 8 = 0) (hn : 0 < n) (hn128 : n < 128)
    (hcap : cap < 18446744073709551616) (hce : cap ≠ 18446744073709551615)
    (hceC : ce ∈ chunks s ∧ ce.used = true) (hE : ce.addr + 32 + 232 * n ≤ ce.addr + 32 * ce.size)
    (hEtop : ce.addr + 32 + 232 * n + 24 < 2147483648)
    (hkp : ∀ d, Kp d → d ∈ chunks s ∧ d.used = true) (h1 : ω[1] = UInt64.ofNat M)
    (s168 : μ.readN (M + 168) 8 = Num.encodeLE 8 cap) (s176 : μ.readN (M + 176) 8 = Num.encodeLE 8 (ce.addr + 32))
    (s184 : μ.readN (M + 184) 8 = Num.encodeLE 8 n) :
    ∃ ω' μ', FreeStepsH p R 4842 ω μ x 5054 ω' μ' x 50 ∧ LayP S0 S1 M (ce.addr + 32) n ce ∧
      PInv env pb S0 S1 M (ce.addr + 32) n ce cap μ' Kp O 5054 0 ω' μ' s ∧
      (∀ a, a < 4294967296 → (a < M ∨ (M + 56 ≤ a ∧ a < M + 120) ∨ (M + 144 ≤ a ∧ a < M + 248) ∨ M + 304 ≤ a) →
        μ'.read a = μ.read a) := by
  obtain ⟨hS0M, hMS1, hM2, hM8⟩ := hM
  have hS1 := H.hS1
  have wM : ∀ a, M ≤ a → a < M + 304 → μ.writable a = true := fun a h1 h2 => H.st a (by omega) (by omega)
  obtain ⟨ω1, μ1, run1, a1, a10, a248, a256, a264, a272, a280, a288, a296, a120, afr, ard, awr⟩ := e1 (p := p)
    (P := P) (R := R) x ω μ M cap (ce.addr + 32) n ⟨by omega, by omega, hM8⟩ hcap hce (by omega) (by omega) h1
    s168 s176 s184 (fun a h1 h2 => Memory.readable_of_writable (wM a (by omega) (by omega)))
    (fun a h1 h2 => wM a (by omega) (by omega))
  obtain ⟨ω2, μ2, run2, b1, b5, b16, b24, b32, b40, b48, b128, b136, bfr, brd, bwr⟩ := e2 (p := p) (P := P)
    (R := R) x ω1 μ1 M (ce.addr + 32) ⟨by omega, by omega, hM8⟩ (a1.trans h1) a10 (by omega)
    (fun a h1 h2 => by rw [awr]; exact wM a h1 (by omega))
  have k2 : ∀ a l, M + 144 ≤ a → a + l ≤ 4294967296 → μ2.readN a l = μ1.readN a l :=
    fun a l h0 h => Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))
  have H2 : HeapCtx env pb S0 S1 μ2 s := Decode.GrowOne.ctx_high (Decode.GrowOne.ctx_high H
    (fun a ha => afr a (by omega) (Or.inl (by omega))) awr) (fun a ha => bfr a (by omega) (Or.inl (by omega))) bwr
  refine ⟨ω2, μ2, (run1.trans run2).mono (by omega), ⟨⟨hS0M, hMS1, hM2, hM8⟩, hn128, ⟨by omega, hE⟩, hEtop⟩,
    ⟨by rw [b1, a1, h1], Or.inr ⟨rfl, by rw [b5]⟩,
      by rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))]; exact a120,
      b128, b136, b48, b40, b16, b24, b32, by rw [k2 _ _ (by omega) (by omega)]; exact a272,
      by rw [k2 _ _ (by omega) (by omega)]; simpa using a280, by rw [k2 _ _ (by omega) (by omega)]; exact a288,
      by rw [k2 _ _ (by omega) (by omega)]; exact a296,
      ⟨0, 8, by rw [k2 _ _ (by omega) (by omega)]; exact a248, by rw [k2 _ _ (by omega) (by omega)]; exact a256,
        by rw [k2 _ _ (by omega) (by omega)]; exact a264, Nat.le_refl _, by omega, by omega, Or.inl ⟨rfl, rfl⟩,
        fun j hj => absurd hj (Nat.not_lt_zero _)⟩,
      H2, hceC, fun _ _ => rfl, fun d hd => ⟨(hkp d hd).1, (hkp d hd).2, fun _ _ => rfl⟩, fun _ _ => rfl⟩,
    fun a h0 h => by rw [bfr a h0 (by omega), afr a h0 (by omega)]⟩

end Services.Bootstrap.Refine.Entry
