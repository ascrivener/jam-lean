import Services.Bootstrap.Acc.Handlers.InstrLoopFor

/-!
# R5, the instruction loop's entry (8492 → 8554)

Spec `onWorkItem`'s `for i in is do …` (GP v0.8.0 Appendix B, Ω_W; bootstrap's own loop), entered after
row 9's checkpoint (8492, a fall-through) with the decoded instructions' `Vec` { cap c at sp + 240, ptr b
in ω₆, len |is| at sp + 248 } and the empty results `Vec` { 0, dangling, 0 } at sp + 448:
- `VecOwn`: the `Vec` owns its instructions (as `IterOwn` does for the `IntoIter`), `vecFree` the buffers
  its drop frees;
- `EntryHyp`: what holds at 8492 (the contract R2 provides);
- `il_entry` (|is| ≠ 0): `il_setup1` sets up the `IntoIter` at sp + 472, the counter and the flag, and
  `LoopInv` holds at 8554 for is and [] against the entry's memory and state, with G = `vecFree`.
-/

namespace Services.Bootstrap.Acc.Handlers.InstrLoop

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.Alloc Services.Bootstrap.Acc Services.Bootstrap.Spec Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Acc.Handlers.Results Services.Bootstrap.Acc.Handlers.InstrRep
  Services.Bootstrap.Acc.Handlers.RowEleven Services.Bootstrap.Acc.Handlers.ResultsDrop

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **8492, the fall-through** after row 9's checkpoint: on to 8493, registers kept. -/
theorem il_ft {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory) :
    ∃ ω', FreeStepsH p R 8492 ω μ x 8493 ω' μ x 1 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go []
  · exact ⟨by reg_val, by reg_val, by reg_val⟩

theorem flatMap_range_congr {f g : Nat → List Nat} : ∀ (m : Nat), (∀ k, k < m → f k = g k) →
    (List.range m).flatMap f = (List.range m).flatMap g
  | 0, _ => rfl
  | m + 1, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, flatMap_range_congr m fun k hk => h k (by omega),
      h m (by omega)]

/-- The buffers the drop of the `Vec` { cap c, ptr b } with m instructions frees: each slot's `foot`, then
    the buffer if c ≠ 0 (`iterFree` for an `IntoIter` with cur = b). -/
def vecFree (B : InstrRep) (μ : Memory) (b c m : Nat) : List Nat :=
  ((List.range m).flatMap fun k => B.foot (slot μ b k)) ++ optBuf c b

/-- **The decoded instructions' ownership** (the `Vec` { cap c, ptr b }, against the allocator state st),
    as `IterOwn` with cur = b: each slot represents its instruction; the freed buffers are pairwise
    distinct, each the data of an allocated chunk; if is ≠ [], c ≠ 0 and the slots lie in the buffer's
    chunk. -/
structure VecOwn (B : InstrRep) (μ : Memory) (st : State) (b c : Nat) (is : List Spec.Instr) : Prop where
  rep : ∀ k (h : k < is.length), B.rep is[k] (slot μ b k) μ
  nodup : (vecFree B μ b c is.length).Nodup
  owned : ∀ q ∈ vecFree B μ b c is.length, ∃ d ∈ chunks st, d.used = true ∧ d.addr + 32 = q
  slots : is ≠ [] → c ≠ 0 ∧ ∃ d ∈ chunks st, d.used = true ∧ d.addr + 32 = b ∧
    b + 232 * is.length ≤ d.addr + 32 * d.size

/-- **The loop's entry state** (8492, memory μ, allocator state st), for the instructions `is` in the
    `Vec` { cap c at sp + 240, ptr b, len |is| at sp + 248 }: the allocator's context and the stack room;
    the `Vec` owns is (`VecOwn`), b 8-aligned with the slots below 2⁶⁴; row 11's `TailHyp` with the empty
    results `Vec` (cap 0, a dangling pointer below 32, len 0); the instructions' buffers and `tailFree`
    pairwise distinct; the frame constants 2⁶³ at sp + 184, 2⁶³ + 1 at sp + 216, 678 at sp + 200. -/
structure EntryHyp (B : InstrRep) (code : ByteArray) (pb S0 S1 sp b c : Nat) (is : List Spec.Instr)
    (μ : Memory) (st : State) : Prop where
  H : HeapCtxC code pb S0 S1 μ st
  hsp : 2147483648 + 4096 ≤ sp ∧ S0 + 4096 ≤ sp ∧ sp + 1632 ≤ S1
  hs8 : sp % 8 = 0
  mc : rdN μ (sp + 240) 8 = c
  ml : rdN μ (sp + 248) 8 = is.length
  V : VecOwn B μ st b c is
  hb8 : b % 8 = 0
  hb : b + 232 * is.length < 2 ^ 64
  T : TailHyp code pb S0 S1 μ st sp
  h448 : rdN μ (sp + 448) 8 = 0
  h456 : rdN μ (sp + 456) 8 < 32
  h464 : rdN μ (sp + 464) 8 = 0
  hnd : (vecFree B μ b c is.length ++ tailFree μ sp).Nodup
  c184 : rdN μ (sp + 184) 8 = 9223372036854775808
  c216 : rdN μ (sp + 216) 8 = 9223372036854775809
  c200 : rdN μ (sp + 200) 8 = 678

/-- `TailHyp` survives a run that keeps every allocated chunk with its data and the frame's words off
    sp + 160 … 168; `tailFree` is unchanged. -/
theorem TailHyp.keepW {code : ByteArray} {pb S0 S1 : Nat} {μ μ' : Memory} {st st' : State} {sp : Nat}
    (T : TailHyp code pb S0 S1 μ st sp) (H' : HeapCtxC code pb S0 S1 μ' st') (hk : ChunksKept μ st μ' st')
    (fr : ∀ a, sp ≤ a → a < sp + 472 → (a < sp + 160 ∨ sp + 168 ≤ a) → μ'.read a = μ.read a) :
    TailHyp code pb S0 S1 μ' st' sp ∧ tailFree μ' sp = tailFree μ sp := by
  have e : ∀ o, o + 8 ≤ 472 → (o + 8 ≤ 160 ∨ 168 ≤ o) → rdN μ' (sp + o) 8 = rdN μ (sp + o) 8 := fun o ho ho' =>
    rdN_frame fun j hj => fr _ (by omega) (by omega) (by omega)
  have hr : resPtrs μ' (rdN μ (sp + 456) 8) (rdN μ (sp + 464) 8) =
      resPtrs μ (rdN μ (sp + 456) 8) (rdN μ (sp + 464) 8) := resPtrs_keep T.O hk _ (Nat.le_refl _)
  have e456 := e 456 (by omega) (by omega)
  have e464 := e 464 (by omega) (by omega)
  have e448 := e 448 (by omega) (by omega)
  have e128 := e 128 (by omega) (by omega)
  have e104 := e 104 (by omega) (by omega)
  have e264 := e 264 (by omega) (by omega)
  have e272 := e 272 (by omega) (by omega)
  have tf : tailFree μ' sp = tailFree μ sp := by
    unfold tailFree tailBufs
    rw [e456, e464, e448, e128, e104, e264, e272, hr]
  refine ⟨⟨H', T.hsp, ?_, ?_, ?_, ?_⟩, tf⟩
  · rw [e456, e464]; exact T.O.keep hk
  · rw [e456, e464, e448, hr]; exact T.b1.keep hk
  · rw [e456, e464, e448, e128, e104, hr]
    exact T.b2.keep hk
  · rw [e456, e464, e448, e128, e104, e264, e272, hr]
    exact T.b3.keep hk

/-- **The loop's entry, 8492 → 8554** (some instructions): from `EntryHyp`, the `IntoIter` { b, b, c,
    b + 232·|is| } at sp + 472, the counter 0, the flag 0, and `LoopInv` at 8554 for is and no results,
    against the entry's memory μ and state st, with G = `vecFree` (the buffers of the instructions), for
    any context satisfying Inv. -/
theorem il_entry {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (B : InstrRep) {code : ByteArray}
    {pb S0 S1 : Nat} (Inv : AccCtx → Prop) (x : X) (ω : Regs) (μ : Memory) (st : State) (sp b c : Nat)
    (is : List Spec.Instr) (hn0 : is ≠ []) (h1 : ω[1] = UInt64.ofNat sp) (h6 : ω[6] = UInt64.ofNat b)
    (E : EntryHyp B code pb S0 S1 sp b c is μ st) :
    ∃ ω' μ' N, FreeStepsH p R 8492 ω μ x 8554 ω' μ' x N ∧ ω'[5] = ω[5] ∧
      ∀ (c0 : AccCtx) (f : Stream), Inv c0 →
        LoopInv B code pb S0 S1 sp Inv μ st (vecFree B μ b c is.length) (is.any isZomb) is.length is []
          ⟨8554, ω', μ', c0, f⟩ := by
  have H := E.H
  have hT := H.hS1
  have hSt := H.st
  obtain ⟨hs1, hs2, hs3⟩ := E.hsp
  have hb := E.hb
  have hlen0 : is.length ≠ 0 := fun h => hn0 (List.length_eq_zero_iff.1 h)
  obtain ⟨hc0, d, hd, hu, hda, hde⟩ := E.V.slots hn0
  have hcl : c < 2 ^ 64 := by rw [← E.mc]; exact rdN_lt8 μ _
  obtain ⟨ω0, run0, e1, e5, e6⟩ := il_ft (R := R) (P := P) x ω μ
  obtain ⟨ω', μ', run1, a1, a5, a6, m472, m480, m488, m496, m504, m160, fr, rd, wr⟩ :=
    il_setup1 (R := R) (P := P) x ω0 μ sp b c is.length (e1.trans h1) (e6.trans h6) ⟨by omega, by omega⟩ hb hcl
      hlen0 (by rw [← E.mc]; exact KeyEnc.readN_enc μ _ 8) (by rw [← E.ml]; exact KeyEnc.readN_enc μ _ 8)
      (fun a h1 h2 => Memory.readable_of_writable (hSt a (by omega) (by omega)))
      (fun a h1 h2 => hSt a (by omega) (by omega)) (fun a h1 h2 => hSt a (by omega) (by omega))
  refine ⟨ω', μ', _, run0.trans run1, a5.trans e5, fun c0 f hinv => ?_⟩
  have heap1 : ∀ a, a < 2147483648 → μ'.read a = μ.read a := fun a ha =>
    fr a (by omega) (.inl (by omega)) (.inl (by omega))
  have H' : HeapCtxC code pb S0 S1 μ' st := HeapKeep.keepHi H heap1 wr
  have hk : ChunksKept μ st μ' st := fun d hd _ => ⟨hd, fun a ha => heap1 a (data_lt H hd ha)⟩
  have r472 : rdN μ' (sp + 472) 8 = b := DesignateAlloc.rd8 (by omega) m472
  have r480 : rdN μ' (sp + 480) 8 = b := DesignateAlloc.rd8 (by omega) m480
  have r488 : rdN μ' (sp + 488) 8 = c := DesignateAlloc.rd8 hcl m488
  have r496 : rdN μ' (sp + 496) 8 = b + 232 * is.length := DesignateAlloc.rd8 hb m496
  have r504 : rdN μ' (sp + 504) 8 = 0 := DesignateAlloc.rd8 (by decide) m504
  have r160 : rdN μ' (sp + 160) 8 = 0 := DesignateAlloc.rd8 (by decide) m160
  have frw : ∀ o, o + 8 ≤ 1632 → (o + 8 ≤ 160 ∨ 168 ≤ o) → (o + 8 ≤ 472 ∨ 512 ≤ o) →
      rdN μ' (sp + o) 8 = rdN μ (sp + o) 8 := fun o h1 h2 h3 =>
    rdN_frame fun j hj => fr _ (by omega) (by omega) (by omega)
  -- the slots
  have hsl : ∀ k, k < is.length → slot μ' b k = slot μ b k := fun k hk' =>
    Memory.readN_congr fun j hj => heap1 _ (data_lt H hd (a := b + 232 * k + j) ⟨by omega, by
      have : 232 * k + 232 ≤ 232 * is.length := by omega
      omega⟩)
  have hvf : vecFree B μ' b c is.length = vecFree B μ b c is.length := by
    unfold vecFree; rw [flatMap_range_congr _ fun k hk' => by rw [hsl k hk']]
  have hIF : iterFree B μ' (sp + 472) is.length = vecFree B μ b c is.length := by
    unfold iterFree
    rw [show sp + 472 + 8 = sp + 480 by omega, show sp + 472 + 16 = sp + 488 by omega, r480, r488, r472, ← hvf]
    rfl
  have I : IterOwn B μ' st (sp + 472) is := by
    refine ⟨?_, fun k hk' => ?_, ?_, ?_, fun _ => ?_⟩
    · rw [show sp + 472 + 24 = sp + 496 by omega, show sp + 472 + 8 = sp + 480 by omega, r496, r480]
    · rw [show sp + 472 + 8 = sp + 480 by omega, r480, hsl k hk']
      refine B.frame _ _ μ μ' st (E.V.rep k hk') fun q hq => ?_
      obtain ⟨e, he, heu, heq⟩ := E.V.owned q (List.mem_append_left _ (List.mem_flatMap.2
        ⟨k, List.mem_range.2 hk', hq⟩))
      exact ⟨e, he, heu, heq, (hk e he heu).2⟩
    · rw [hIF]; exact E.V.nodup
    · rw [hIF]; exact E.V.owned
    · rw [show sp + 472 + 16 = sp + 488 by omega, show sp + 472 + 8 = sp + 480 by omega,
        show sp + 472 + 24 = sp + 496 by omega, r488, r472, r480, r496]
      exact ⟨hc0, d, hd, hu, hda, Nat.le_refl _, hde⟩
  obtain ⟨T', tf⟩ := E.T.keepW H' hk fun a h1 h2 h3 => fr a (by omega) (.inl h2) h3
  have w448 : rdN μ' (sp + 448) 8 = 0 := (frw 448 (by omega) (by omega) (by omega)).trans E.h448
  have w456 : rdN μ' (sp + 456) 8 = rdN μ (sp + 456) 8 := frw 456 (by omega) (by omega) (by omega)
  have w464 : rdN μ' (sp + 464) 8 = 0 := (frw 464 (by omega) (by omega) (by omega)).trans E.h464
  have LA : LoopAt B code pb S0 S1 sp is [] false μ' st := by
    refine ⟨H', ⟨by omega, by omega, by omega⟩, I, T', w464, Nat.zero_le _, ⟨fun k hk' => absurd hk' (by simp),
      fun j hj => absurd hj (by simp)⟩, ?_, fun j hj => absurd hj (by simp), fun _ => by rw [w456]; exact E.h456,
      fun h => absurd w448 h, r160, ?_, ?_, ?_⟩
    · rw [hIF, tf]; exact E.hnd
    · rw [frw 184 (by omega) (by omega) (by omega)]; exact E.c184
    · rw [frw 216 (by omega) (by omega) (by omega)]; exact E.c216
    · rw [frw 200 (by omega) (by omega) (by omega)]; exact E.c200
  have hstab : ∀ a, a < 4294967296 → StableKeep sp a → μ'.read a = μ.read a := fun a h0 h => by
    unfold StableKeep at h; exact fr a h0 (by omega) (by omega)
  refine ⟨.inr ⟨rfl, by rw [a6, e6, h6, r480], hn0⟩, a1.trans (e1.trans h1), hinv,
    ⟨st, false, LA, by simp, fun d hd hu hG => ⟨hd, (hk d hd hu).2, by rw [hIF]; exact hG, ?_, ?_⟩⟩,
    by rw [r480]; exact E.hb8, by rw [r504]; omega, by simp, fun a ha => ⟨fr a (by omega) (.inl (by omega))
      (.inl (by omega)), rd a⟩, hstab⟩
  · rw [w448]; simp [optBuf]
  · simp [resPtrs]

end Services.Bootstrap.Acc.Handlers.InstrLoop
