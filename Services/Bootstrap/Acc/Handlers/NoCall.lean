import Services.Bootstrap.Acc.Handlers.Dispatch

/-!
# The accumulate handlers that make no host call

GP v0.8.0 plays no part here beyond the PVM (§A): these handlers only move octets. Each summary
follows the pattern of `Dispatch.lean`: from the dispatch point 8822 to 14278 with the result at
`RES`, or to the trap.

- `LookedUp { data: None }` (tag 18): `Err(Lookup)`, at 9193 → 13199.
- `LookedUp { data: Some(d) }`: `Ok(Data(d))`, at 9193 → 9202. The `Vec<u8>` (capacity, pointer,
  length) moves into the result; nothing is copied or freed.
- `AssignForGasCost` with an empty queue whose `Vec` has capacity 0, as the decode leaves an empty
  `Vec` (`Decode.VecEmpty`): `Ok(Unit)`, at 11173 → 13541. The binary also stores the core (`u16`)
  at sp + 1496 and the assigner (`u32`) at sp + 1568, for the `assign` it does not make.
- `Panic` (tag 16): the table sends it straight to the trap at 15361.
-/

namespace Services.Bootstrap.Acc.Handlers

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

macro "post_simp" : tactic => `(tactic| (
  all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
    ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, PVM.Memory.readN_writeN_same,
    PVM.Memory.readN_writeN_disjoint, PVM.Memory.read_writeN_disjoint, PVM.Memory.readable_writeN,
    PVM.Memory.writable_writeN, PVM.Num.length_encodeLE, List.length_cons, List.length_nil, PVM.two32]))

/-- **`LookedUp { data: None }`** (tag 18, the data word 2⁶⁴ − 1 at slot + 8): no host call, result
    `Err(Lookup)` (the octets 255, 6 at `RES`). Memory changes only at `RES` (2 octets) and
    sp + 1380 (4). -/
theorem lookedUp_none {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (bs : List UInt8) (hD : AtDispatch ω μ bs)
    (hdisc : bs.take 8 = Num.encodeLE 8 9223372036854775825)
    (hnone : (bs.drop 8).take 8 = Num.encodeLE 8 18446744073709551615) :
    ∃ ω' μ', FreeStepsH p R 8822 ω μ x 14278 ω' μ' x 40 ∧ ω'[1] = ω[1] ∧
      μ'.readN RES 2 = [255, 6] ∧ KeepsExcept μ μ' [(RES, 2), (4278058532, 4)] ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have h1 := hD.sp
  have h6 := hD.r6
  have c216 := hD.c216
  have hw := hD.frame
  have hrt := hD.tabR
  have hr : ∀ a, 4278057152 ≤ a → a < 4278059008 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have disc := slot_word0 hD.slotB hdisc
  have none := slot_word hD.slotB 8 (by decide) hnone
  have tab : μ.readN 65808 4 = [118, 0, 255, 255] := tab_entry hD.tab 18 (by decide)
  simp only [Nat.reduceAdd] at disc none
  clear hD hdisc hnone
  obtain ⟨v192, hv192, m192⟩ := word_exists μ 4278057344
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [m192, hv192, jts, h1, h6, c216, disc, none, tab, hw, hr, hrt]
  case post =>
    refine ⟨?_, ?_, fun a ha hrs => ?_, fun a => ?_, fun a => ?_⟩
    · post_simp
    · simp only [RES, Memory.readN, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
        List.map_nil, List.cons_append]
      simp (disch := omega) only [PVM.Memory.writeN_cons, PVM.Memory.writeN_nil, PVM.read_write_eq',
        PVM.read_write_ne', Nat.add_zero]
      rfl
    · simp only [RES, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, or_false, forall_eq] at hrs
      post_simp
    all_goals post_simp

/-- **`LookedUp { data: Some(d) }`** (tag 18): no host call, result `Ok(Data(d))`. The `Vec<u8>`'s
    words (capacity `cap` < 2⁶⁴ − 1, pointer, length) at slot + 8 … + 32 become the result's words
    at `RES` + 8 … + 32, after the octet 5 at `RES`. Memory changes only at `RES` (1 octet),
    `RES` + 8 (24) and sp + 1380 (4). -/
theorem lookedUp_some {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (bs : List UInt8) (hD : AtDispatch ω μ bs) (cap ptr len : Nat)
    (hcap : cap < 18446744073709551615) (hptr : ptr < 18446744073709551616)
    (hlen : len < 18446744073709551616)
    (hdisc : bs.take 8 = Num.encodeLE 8 9223372036854775825)
    (hc : (bs.drop 8).take 8 = Num.encodeLE 8 cap) (hp : (bs.drop 16).take 8 = Num.encodeLE 8 ptr)
    (hl : (bs.drop 24).take 8 = Num.encodeLE 8 len) :
    ∃ ω' μ', FreeStepsH p R 8822 ω μ x 14278 ω' μ' x 40 ∧ ω'[1] = ω[1] ∧
      μ'.read RES = 5 ∧ μ'.readN (RES + 8) 8 = Num.encodeLE 8 cap ∧
      μ'.readN (RES + 16) 8 = Num.encodeLE 8 ptr ∧ μ'.readN (RES + 24) 8 = Num.encodeLE 8 len ∧
      KeepsExcept μ μ' [(RES, 1), (RES + 8, 24), (4278058532, 4)] ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have h1 := hD.sp
  have h6 := hD.r6
  have c216 := hD.c216
  have hw := hD.frame
  have hrt := hD.tabR
  have hr : ∀ a, 4278057152 ≤ a → a < 4278059008 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have disc := slot_word0 hD.slotB hdisc
  have mcap := slot_word hD.slotB 8 (by decide) hc
  have mptr := slot_word hD.slotA 16 (by decide) hp
  have mlen := slot_word hD.slotA 24 (by decide) hl
  have tab : μ.readN 65808 4 = [118, 0, 255, 255] := tab_entry hD.tab 18 (by decide)
  have rcap : rdN μ 4278058304 8 = cap := DecodeLoop.rdN_of mcap (by omega)
  have rptr : rdN μ 4278057912 8 = ptr := DecodeLoop.rdN_of mptr (by omega)
  have rlen : rdN μ 4278057920 8 = len := DecodeLoop.rdN_of mlen (by omega)
  simp only [Nat.reduceAdd] at disc mcap mptr mlen
  have rdisc : rdN μ 4278058296 8 = 9223372036854775825 := DecodeLoop.rdN_of disc (by decide)
  have r216 : rdN μ 4278057368 8 = 9223372036854775809 := DecodeLoop.rdN_of c216 (by decide)
  have rtab : rdN μ 65808 4 = 4294901878 := by rw [← rdN_fold, tab]; rfl
  clear hD hdisc hc hp hl
  obtain ⟨v192, hv192, m192⟩ := word_exists μ 4278057344
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [DecodeLoop.rdN_of m192 hv192, hv192, jts, h1, h6, r216, rdisc, rcap, rptr, rlen, tab, rtab, hw, hr, hrt, rdN_writeN_disjoint, ↓rdN_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, fun a ha hrs => ?_, fun a => ?_, fun a => ?_⟩
    · post_simp
    · simp only [RES]
      post_simp
      simp (disch := omega) only [PVM.Memory.writeN_cons, PVM.Memory.writeN_nil, PVM.read_write_eq']
      rfl
    · simp only [RES, Nat.reduceAdd]
      post_simp
    · simp only [RES, Nat.reduceAdd]
      post_simp
    · simp only [RES, Nat.reduceAdd]
      post_simp
    · simp only [RES, Nat.reduceAdd, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, or_false,
        forall_eq] at hrs
      post_simp
    all_goals post_simp

/-- **`AssignForGasCost` with an empty queue** (tag 24; the queue's `Vec` has capacity 0 and length
    0, as `Decode.VecEmpty` leaves it): no host call, result `Ok(Unit)` (the octet 0 at `RES`).
    Memory changes only at `RES` (1 octet), sp + 1380 (4), sp + 1496 (2, the core) and sp + 1568
    (4, the assigner). -/
theorem assignForGasCost_empty {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (bs : List UInt8) (hD : AtDispatch ω μ bs)
    (hdisc : bs.take 8 = Num.encodeLE 8 9223372036854775831)
    (hc : (bs.drop 8).take 8 = Num.encodeLE 8 0) (hl : (bs.drop 24).take 8 = Num.encodeLE 8 0) :
    ∃ ω' μ', FreeStepsH p R 8822 ω μ x 14278 ω' μ' x 40 ∧ ω'[1] = ω[1] ∧ μ'.read RES = 0 ∧
      KeepsExcept μ μ' [(RES, 1), (4278058532, 4), (4278058648, 2), (4278058720, 4)] ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have h1 := hD.sp
  have h6 := hD.r6
  have c216 := hD.c216
  have hw := hD.frame
  have hrt := hD.tabR
  have hr : ∀ a, 4278057152 ≤ a → a < 4278059008 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have disc := slot_word0 hD.slotB hdisc
  have mcap := slot_word hD.slotA 8 (by decide) hc
  have mlen := slot_word hD.slotA 24 (by decide) hl
  have tab : μ.readN 65832 4 = [206, 0, 255, 255] := tab_entry hD.tab 24 (by decide)
  simp only [Nat.reduceAdd] at disc mcap mlen
  clear hD hdisc hc hl
  obtain ⟨va, hva, ma⟩ := bytes_exist μ 4278058328 4
  obtain ⟨vc, hvc, mc⟩ := bytes_exist μ 4278058332 2
  obtain ⟨vp, hvp, mp⟩ := word_exists μ 4278057912
  obtain ⟨v192, hv192, m192⟩ := word_exists μ 4278057344
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [m192, hv192, ma, hva, mc, hvc, mp, hvp, jts, h1, h6, c216, disc, mcap, mlen, tab, hw, hr, hrt]
  case post =>
    refine ⟨?_, ?_, fun a ha hrs => ?_, fun a => ?_, fun a => ?_⟩
    · post_simp
    · simp only [RES]
      post_simp
      simp (disch := omega) only [PVM.Memory.writeN_cons, PVM.Memory.writeN_nil, PVM.read_write_eq']
      rfl
    · simp only [RES, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, or_false, forall_eq] at hrs
      post_simp
    all_goals post_simp

/-- The trap at 15361: ☇ (GP §A.5.1), registers and memory as they are. -/
theorem trap_15361 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (ω : Regs) (μ : Memory) :
    FreeExit p 15361 ω μ .panic ω μ := by
  have hd := d_15361 (p := p) (P := P)
  have hs : P.freeStep 15361 ω μ = (.panic, P.next 15361, ω, μ) := by
    simp [Program.freeStep, hd.2.1, Program.exec, Program.finalState, memoryException]
  have := FreeExit.step (p := p) hd.1 hs (by decide)
  simpa using this

/-- **`Panic`** (tag 16): the jump table sends it straight to the trap at 15361, so accumulate ends
    in ☇ with no host call and the context as it was. (Ψ_A then reports the exceptional dimension,
    the last checkpoint: `Acc/Checkpoint.lean`, `psiARun_eq`.) -/
theorem panic {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (bs : List UInt8) (hD : AtDispatch ω μ bs)
    (hdisc : bs.take 8 = Num.encodeLE 8 9223372036854775823) :
    ∃ ω' μ', FreeRunH p R 8822 ω μ x .panic ω' μ' x := by
  have h1 := hD.sp
  have h6 := hD.r6
  have c216 := hD.c216
  have hw := hD.frame
  have hrt := hD.tabR
  have hr : ∀ a, 4278057152 ≤ a → a < 4278059008 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have disc := slot_word0 hD.slotB hdisc
  have tab : μ.readN 65800 4 = [120, 1, 255, 255] := tab_entry hD.tab 16 (by decide)
  clear hD hdisc
  have run : ∃ ω' μ', FreeStepsH p R 8822 ω μ x 15361 ω' μ' x 20 := by
    obtain ⟨v192, hv192, m192⟩ := word_exists μ 4278057344
    rw [show ω = regsNF ω [] from rfl]
    refine ⟨?ω', ?μ', ?run⟩
    case run => pvm_go [m192, hv192, jts, h1, h6, c216, disc, tab, hw, hr, hrt]
  obtain ⟨ω', μ', hs⟩ := run
  exact ⟨ω', μ', hs.run (.exit (FreeRun.exit (trap_15361 (P := P) ω' μ')) (by simp))⟩

end Services.Bootstrap.Acc.Handlers
