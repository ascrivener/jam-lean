import Services.Bootstrap.Acc.Handlers.InstrLoopSeg
import Services.Bootstrap.Acc.ContractC
import Services.Bootstrap.Acc.Impl.ContractS

/-!
# R5, the instruction loop: the result's tail (14376 … 14546)

After the handler (14278) and the result's log line (`format!`, a G4 hypothesis), the tail:
- `log` (host call 100) of the line, which only sets ω₇ (`FreeStepsH.logS`, under the stream contract);
- the line's `String` deallocated if its cap is not 0;
- the result pushed onto the results `Vec` at sp + 448 (growth through `finish_grow` 32989 when
  len = cap: an R8 hypothesis), its 144 octets copied from sp + 1000;
- the instruction's `String` at sp + 976 deallocated if its cap is not 0, and back to the head 8540.

Spec `onWorkItem`'s `results := results ++ [r]` (GP v0.8.0 Appendix B, Ω_W; bootstrap's own loop).
Logging is frame-only (Adam's standing decision): the text of the lines is never specified.
-/

namespace Services.Bootstrap.Acc.Handlers.InstrLoop

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.Alloc Services.Bootstrap.Acc Services.Bootstrap.Spec

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **A `log` (100) step under the stream contract**: ω₇ := WHAT, memory, context and stream kept. -/
theorem FreeStepsH.logS (env : AccEnv) (f : Stream)
    {p : ByteArray} {P : Program} {i n : Nat} {ω : Regs} {μ : Memory} {x : AccCtx}
    {i'' : Nat} {ω'' : Regs} {μ'' : Memory} {x'' : AccCtx × Stream} {k : Nat}
    (hd : deblob p i = some P ∧ P.decode i = some (.oneImm .ecalli 100) ∧ P.next i = n ∧
      P.blockCost (P.blockStartOf i) ≤ stepCostCap)
    (rest : FreeStepsH p (KeepCtx (accContractS env)) n (setR7 ω Result.WHAT) μ (x, f) i'' ω'' μ'' x'' k) :
    FreeStepsH p (KeepCtx (accContractS env)) i ω μ (x, f) i'' ω'' μ'' x'' (k + 1) := by
  refine FreeStepsH.host_decode hd ⟨.inl ⟨by unfold AccGasFreeId; decide, by simp [accHostFn, AccHost.dispatch],
    rfl, UInt64.ofNat 1000000, ?_⟩, rfl⟩ rest
  simp [accHostFn, AccHost.dispatch, UInt64.toNat_ofNat, Constants.Cgasunknown]

variable {X : Type} {R : HostRel X}

/-- **14376 … 14399**: `log`'s arguments: level 3 (ω₇), the target at 66793 (ω₈, 4 octets, ω₉), the
    line's buffer q (ω₁₀ = ω₆, from sp + 1152) and length l (ω₁₁, from sp + 1160); its cap c in ω₅. -/
theorem il_tail_a {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp c q l : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : 65536 ≤ sp ∧ sp + 1632 < 4294967296)
    (hc : c < 2 ^ 64) (hq : q < 2 ^ 64) (hl : l < 2 ^ 64)
    (mc : μ.readN (sp + 1144) 8 = Num.encodeLE 8 c) (mq : μ.readN (sp + 1152) 8 = Num.encodeLE 8 q)
    (ml : μ.readN (sp + 1160) 8 = Num.encodeLE 8 l)
    (hr : ∀ a, sp + 1144 ≤ a → a < sp + 1168 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 14376 ω μ x 14401 ω' μ x 8 ∧ ω'[1] = ω[1] ∧
      ω'[5] = UInt64.ofNat c ∧ ω'[6] = UInt64.ofNat q := by
  have rc := Handlers.DesignateAlloc.rd8 hc mc
  have rq := Handlers.DesignateAlloc.rd8 hq mq
  have rl := Handlers.DesignateAlloc.rd8 hl ml
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hsp, rc, rq, rl, hr, ↓rdN_fold]
  · refine ⟨by reg_val, ?_, ?_⟩
    all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hq]

/-- **14403 … 14404, cap 0**: no buffer to free; on to the push at 14420. -/
theorem il_tail_b0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (h5 : ω[5] = UInt64.ofNat 0) :
    ∃ ω', FreeStepsH p R 14403 ω μ x 14420 ω' μ x 2 ∧ ω'[1] = ω[1] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h5]
  · exact by reg_val

/-- **14403 … 14414, cap c ≠ 0**: the call of `dealloc` (40613, return 536) of the line's buffer q
    (ω₇ = q, ω₈ = c, ω₉ = 1). -/
theorem il_tail_b1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (c q : Nat) (h5 : ω[5] = UInt64.ofNat c) (h6 : ω[6] = UInt64.ofNat q) (hc : c < 2 ^ 64) (hc0 : c ≠ 0)
    (hq : q < 2 ^ 64) :
    ∃ ω', FreeStepsH p R 14403 ω μ x 40613 ω' μ x 6 ∧ ω'[0] = UInt64.ofNat 536 ∧ ω'[1] = ω[1] ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat q ∧ ω'[8] = UInt64.ofNat c ∧
      ω'[9] = UInt64.ofNat 1 := by
  have hc' : c % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt hc]; exact hc0
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h5, h6, hc', hc0]
  · refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, ?_, ?_, by reg_val⟩
    all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h5, h6, Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hc]

/-- **14420 … 14509, room** (len n ≠ cap at sp + 464 / sp + 448): the call of memcpy (68729, return
    540) of the 144 octets of the result at sp + 1000 to rp + 144·n (rp at sp + 456); ω₅ = n. -/
theorem il_push {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp cp rp n : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : 65536 ≤ sp ∧ sp + 1632 < 4294967296)
    (hcp : cp < 2 ^ 64) (hn : n < 2 ^ 64) (hrp : rp + 144 * n < 2 ^ 64) (hne : n ≠ cp)
    (mcp : μ.readN (sp + 448) 8 = Num.encodeLE 8 cp) (mrp : μ.readN (sp + 456) 8 = Num.encodeLE 8 rp)
    (mn : μ.readN (sp + 464) 8 = Num.encodeLE 8 n)
    (hr : ∀ a, sp + 448 ≤ a → a < sp + 472 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 14420 ω μ x 68729 ω' μ x 13 ∧ ω'[0] = UInt64.ofNat 540 ∧ ω'[1] = ω[1] ∧
      ω'[5] = UInt64.ofNat n ∧ ω'[7] = UInt64.ofNat (rp + 144 * n) ∧ ω'[8] = UInt64.ofNat (sp + 1000) ∧
      ω'[9] = UInt64.ofNat 144 := by
  have rcp := Handlers.DesignateAlloc.rd8 hcp mcp
  have rrp := Handlers.DesignateAlloc.rd8 (by omega) mrp
  have rn := Handlers.DesignateAlloc.rd8 hn mn
  have hne' : n ≠ cp := hne
  have e144 : (rp + ((n * 16 % 18446744073709551616) + (n * 128 % 18446744073709551616)) %
      18446744073709551616) % 18446744073709551616 = rp + 144 * n := by
    rw [Nat.mod_eq_of_lt (a := n * 16) (by omega), Nat.mod_eq_of_lt (a := n * 128) (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hsp, rcp, rrp, rn, hr, hne', ↓rdN_fold]
  · refine ⟨by reg_val, by reg_val, ?_, ?_, ?_, by reg_val⟩
    all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1, Nat.mod_eq_of_lt hn]
    all_goals try (congr 1; omega)
    all_goals try (apply UInt64.toNat_inj.1; simp [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat]; omega)

/-- **14516 … 14530, no instruction `String` to free** (cap 0 at sp + 976): len := n + 1 at sp + 464
    (n in ω₅), and back to the head 8540. -/
theorem il_post0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp n : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat n)
    (hsp : 65536 ≤ sp ∧ sp + 1632 < 4294967296) (hn : n + 1 < 2 ^ 64)
    (mc : μ.readN (sp + 976) 8 = Num.encodeLE 8 0)
    (hr : ∀ a, sp + 976 ≤ a → a < sp + 984 → μ.readable a = true)
    (hw : ∀ a, sp + 464 ≤ a → a < sp + 472 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 14516 ω μ x 8540 ω' μ' x 5 ∧ ω'[1] = ω[1] ∧
      μ'.readN (sp + 464) 8 = Num.encodeLE 8 (n + 1) ∧
      (∀ a, a < 4294967296 → (a < sp + 464 ∨ sp + 472 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rc := Handlers.DesignateAlloc.rd8 (by decide) mc
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hsp, rc, hr, hw, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨by reg_val, ?_, fun a ha h1' => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
      PVM.getD_some', List.lookup_nil, Option.getD_none]
    all_goals try rd_simp []
    all_goals try rfl
    all_goals try (congr 1; omega)
    all_goals try simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1, h5, Nat.mod_eq_of_lt hn,
      Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega)]
    all_goals try (congr 1; omega)

/-- **14516 … 14540, an instruction `String` to free** (cap c ≠ 0 at sp + 976, buffer q at sp + 984):
    len := n + 1 at sp + 464, and the call of `dealloc` (40613, return 542) of q (ω₇ = q, ω₈ = c,
    ω₉ = 1). -/
theorem il_post1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp n c q : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat n)
    (hsp : 65536 ≤ sp ∧ sp + 1632 < 4294967296) (hn : n + 1 < 2 ^ 64) (hc : c < 2 ^ 64) (hc0 : c ≠ 0)
    (hq : q < 2 ^ 64)
    (mc : μ.readN (sp + 976) 8 = Num.encodeLE 8 c) (mq : μ.readN (sp + 984) 8 = Num.encodeLE 8 q)
    (hr : ∀ a, sp + 976 ≤ a → a < sp + 992 → μ.readable a = true)
    (hw : ∀ a, sp + 464 ≤ a → a < sp + 472 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 14516 ω μ x 40613 ω' μ' x 7 ∧ ω'[0] = UInt64.ofNat 542 ∧ ω'[1] = ω[1] ∧
      ω'[7] = UInt64.ofNat q ∧ ω'[8] = UInt64.ofNat c ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (sp + 464) 8 = Num.encodeLE 8 (n + 1) ∧
      (∀ a, a < 4294967296 → (a < sp + 464 ∨ sp + 472 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rc := Handlers.DesignateAlloc.rd8 hc mc
  have rq := Handlers.DesignateAlloc.rd8 hq mq
  have hc' : c % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt hc]; exact hc0
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hsp, rc, rq, hr, hw, hc0, hc', rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨by reg_val, by reg_val, ?_, ?_, by reg_val, ?_, fun a ha h1' => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
      PVM.getD_some', List.lookup_nil, Option.getD_none]
    all_goals try rd_simp []
    all_goals try rfl
    all_goals try (congr 1; omega)
    all_goals try simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1, h5, Nat.mod_eq_of_lt hn,
      Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega), Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hq]
    all_goals try (congr 1; omega)

/-- **14546**: back to the head 8540. -/
theorem il_back {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory) :
    FreeStepsH p R 14546 ω μ x 8540 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go []

end Services.Bootstrap.Acc.Handlers.InstrLoop
