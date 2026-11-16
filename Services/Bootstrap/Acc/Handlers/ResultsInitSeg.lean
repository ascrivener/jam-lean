import Services.Bootstrap.Acc.Handlers.ResStoreSeg
import Services.Bootstrap.Acc.Handlers.NoCall

/-!
# Row 9: the empty results write and the checkpoint, the caller's segments (8416 … 8492)

Spec `onWorkItem`'s `store key (encodeResults [])` then `op AOp.checkpoint` (GP v0.8.0 Appendix B:
Ω_W, then Ω_C), with key = `Key.results package item`:
- `r9_pre` (8416 → 36170): the tag-2 key value at sp + 1568 (the `u16` 2, the item's `u16` from
  sp + 176 at sp + 1570, the 32 octets at sp + 312 at sp + 1572), the results' ptr and length
  (sp + 456, sp + 464) in ω₇, ω₈, the key value's address in ω₉, and the call of 36170 (return
  address 294);
- `r9_ok` (8477 → 8490): ω₇'s low octet is 255 (`Ok`); `r9_err` (8477 → 15361): otherwise
  (`unwrap` of `Err`);
- `r9_ck` (8490 → 8492): `checkpoint` (18) under `accContractS`: ω₇ := the stream's head, y := x;
- `ASem.step_checkpoint`: the operation's step, y := x.
-/

namespace Services.Bootstrap.ASem
open PVM JAM Services.Bootstrap.Spec

/-- **`checkpoint`** (Ω_C at the operation's gas 2⁶³ ≥ 𝖬_C): y := x, the reply (). -/
theorem step_checkpoint (env : AccEnv) (c : AccCtx) : step env .checkpoint c = some ((), (c.1, c.1)) := by
  simp [step, call, AccHost.dispatch, AccHost.checkpoint, AccHost.charge, charged, opGas, Constants.CgasC]

end Services.Bootstrap.ASem

namespace Services.Bootstrap.Acc.Handlers.ResultsInit

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.Alloc Services.Bootstrap.Acc Services.Bootstrap.Spec
  Services.Bootstrap.Acc.Handlers.KeyEnc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **8416 … 8471**: the tag-2 key value at sp + 1568 (the `u16` 2; the low two octets of the word v at
    sp + 176 at sp + 1570; the 32 octets at sp + 312, the words q₀ … q₃, at sp + 1572), ω₇ := the word
    rp at sp + 456, ω₈ := the word n at sp + 464, ω₉ := sp + 1568, and the call of 36170 with return
    address 294. -/
theorem r9_pre {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp q0 q1 q2 q3 v rp n : Nat) (h1 : ω[1] = UInt64.ofNat sp)
    (hsp : 65536 ≤ sp ∧ sp + 1632 < 4294967296)
    (m0 : μ.readN (sp + 312) 8 = Num.encodeLE 8 q0) (m1 : μ.readN (sp + 320) 8 = Num.encodeLE 8 q1)
    (m2 : μ.readN (sp + 328) 8 = Num.encodeLE 8 q2) (m3 : μ.readN (sp + 336) 8 = Num.encodeLE 8 q3)
    (hq0 : q0 < 2 ^ 64) (hq1 : q1 < 2 ^ 64) (hq2 : q2 < 2 ^ 64) (hq3 : q3 < 2 ^ 64)
    (mv : μ.readN (sp + 176) 8 = Num.encodeLE 8 v) (hv : v < 2 ^ 64)
    (mrp : μ.readN (sp + 456) 8 = Num.encodeLE 8 rp) (hrp : rp < 2 ^ 64)
    (mn : μ.readN (sp + 464) 8 = Num.encodeLE 8 n) (hn : n < 2 ^ 64)
    (hr : ∀ a, sp + 176 ≤ a → a < sp + 472 → μ.readable a = true)
    (hw : ∀ a, sp + 1568 ≤ a → a < sp + 1604 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 8416 ω μ x 36170 ω' μ' x 17 ∧
      ω'[0] = UInt64.ofNat 294 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat (sp + 1572) ∧
      ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat rp ∧ ω'[8] = UInt64.ofNat n ∧ ω'[9] = UInt64.ofNat (sp + 1568) ∧
      μ'.readN (sp + 1568) 2 = Num.encodeLE 2 2 ∧ μ'.readN (sp + 1570) 2 = Num.encodeLE 2 v ∧
      μ'.readN (sp + 1572) 8 = Num.encodeLE 8 q0 ∧ μ'.readN (sp + 1580) 8 = Num.encodeLE 8 q1 ∧
      μ'.readN (sp + 1588) 8 = Num.encodeLE 8 q2 ∧ μ'.readN (sp + 1596) 8 = Num.encodeLE 8 q3 ∧
      (∀ a, a < 4294967296 → (a < sp + 1568 ∨ sp + 1604 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r0 := Handlers.DesignateAlloc.rd8 hq0 m0
  have r1 := Handlers.DesignateAlloc.rd8 hq1 m1
  have r2 := Handlers.DesignateAlloc.rd8 hq2 m2
  have r3 := Handlers.DesignateAlloc.rd8 hq3 m3
  have rv := Handlers.DesignateAlloc.rd8 hv mv
  have rrp := Handlers.DesignateAlloc.rd8 hrp mrp
  have rn := Handlers.DesignateAlloc.rd8 hn mn
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hsp, r0, r1, r2, r3, rv, rrp, rn, hr, hw, bs_36170, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨by reg_val, ?_, ?_, by reg_val, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      fun a ha h1' => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
      PVM.getD_some', List.lookup_nil, Option.getD_none]
    all_goals try rd_simp []
    all_goals try rfl
    all_goals try (congr 1; omega)
    all_goals try simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1]
    all_goals try (congr 1; omega)
    all_goals try exact PVM.encodeLE_mod 2 v

/-- **8477 … 8481, `Ok`**: ω₇'s low octet is 255; on to 8490, ω₁ and ω₆ kept. -/
theorem r9_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (h7 : ω[7] = UInt64.ofNat 18446744073709551615) :
    ∃ ω', FreeStepsH p R 8477 ω μ x 8490 ω' μ x 2 ∧ ω'[1] = ω[1] ∧ ω'[6] = ω[6] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h7, bs_8490]
  · exact ⟨by reg_val, by reg_val⟩

/-- **8477 … 8487, `Err`** (ω₇ = 3, `set`'s code for FULL): on to the trap at 15361. -/
theorem r9_err {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (h7 : ω[7] = UInt64.ofNat 3) : ∃ ω', FreeStepsH p R 8477 ω μ x 15361 ω' μ x 4 := by
  rw [show ω = regsNF ω [] from rfl]
  exact ⟨_, by pvm_go [h7]⟩

/-- **8490, `checkpoint`** (18) under `accContractS`: ω₇ := the stream's head, y := x, memory kept;
    a step of `YIn` for y ∈ {c.y, c.x}. -/
theorem r9_ck {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : AccEnv) (c : AccCtx)
    (f : Stream) (ω : Regs) (μ : Memory) :
    FreeStepsH p (YIn (accContractS env) c.2 c.1) 8490 ω μ (c, f) 8492 (setR7 ω (f 0)) μ ((c.1, c.1), f.tail) 1 :=
  FreeStepsH.host_decode (d_8490 (p := p) (P := P))
    ⟨.inr ⟨.inr rfl, rfl, rfl, by simp, rfl, rfl⟩, .inr rfl⟩ .refl

end Services.Bootstrap.Acc.Handlers.ResultsInit
