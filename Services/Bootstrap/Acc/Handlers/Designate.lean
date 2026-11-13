import Services.Bootstrap.Acc.Handlers.Checkpoint
import Services.Bootstrap.Acc.ContractC

/-!
# The `Designate` handler (tag 13)

`Designate { validators }` carries a `Vec` of validator keys (336 octets each, GP §6.3 K) at + 8 of
the instruction: capacity, pointer, length. From the dispatch point:
1. 10017: the `Vec` is copied to sp + 1496, and 49597 is called with ω₅ = sp + 1496 and ω₆ = its
   length, return address 354.
2. 49597: a buffer of 336 · len octets is allocated (`alloc_impl`, 41177), the keys are copied into
   it (58508, four fields per key), and `designate` (Ω_D, id 17) is called at 49874.
3. Back at 10070, a message of 19 octets is allocated, logged and freed, as in `Upgrade`.

This file proves step 1: `toEntry`.
-/

namespace Services.Bootstrap.Acc.Handlers.Designate

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Acc
  Services.Bootstrap.Acc.Handlers

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **From the dispatch to 49597**: for `Designate` (the discriminant 2⁶³ + 12), the dispatch
    reaches 10017. That copies the `Vec` (capacity `c`, pointer `q`, length `n`, at + 8 of the
    instruction) to sp + 1496, pushes a 72-octet frame (return address 354 at sp − 8), and jumps to
    49597 with ω₅ = sp + 1496 and ω₆ = n. No host call is made, so any `R`. -/
theorem toEntry {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] {X : Type}
    {R : HostRel X} (x : X) (ω : Regs) (μ : Memory) (bs : List UInt8) (hD : AtDispatch ω μ bs)
    (c q n : Nat)
    (hdisc : bs.take 8 = Num.encodeLE 8 9223372036854775820)
    (hc : (bs.drop 8).take 8 = Num.encodeLE 8 c) (hq : (bs.drop 16).take 8 = Num.encodeLE 8 q)
    (hn : (bs.drop 24).take 8 = Num.encodeLE 8 n)
    (hc64 : c < 18446744073709551616) (hq64 : q < 18446744073709551616)
    (hn64 : n < 18446744073709551616)
    (hws : ∀ a, 4278057128 ≤ a → a < 4278057152 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 8822 ω μ x 49597 ω' μ' x 40 ∧
      ω'[0] = UInt64.ofNat 354 ∧ ω'[1] = UInt64.ofNat 4278057080 ∧
      ω'[5] = UInt64.ofNat 4278058648 ∧ ω'[6] = UInt64.ofNat n ∧
      μ'.readN 4278058648 8 = Num.encodeLE 8 c ∧ μ'.readN 4278058656 8 = Num.encodeLE 8 q ∧
      μ'.readN 4278058664 8 = Num.encodeLE 8 n ∧ μ'.readN 4278057144 8 = Num.encodeLE 8 354 ∧
      KeepsExcept μ μ' [(4278058532, 4), (4278058648, 24), (4278057128, 24)] ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have h1 := hD.sp
  have h6 := hD.r6
  have c216 := hD.c216
  have hw := hD.frame
  have hrt := hD.tabR
  have hr : ∀ a, 4278057152 ≤ a → a < 4278059008 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hrs : ∀ a, 4278057128 ≤ a → a < 4278057152 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hws a h1 h2)
  have disc := slot_word0 hD.slotB hdisc
  have mc := slot_word hD.slotA 8 (by decide) hc
  have mq := slot_word hD.slotA 16 (by decide) hq
  have mn := slot_word hD.slotA 24 (by decide) hn
  have tab : μ.readN 65788 4 = [152, 0, 255, 255] := tab_entry hD.tab 13 (by decide)
  obtain ⟨v192, hv192, m192⟩ := word_exists μ 4278057344
  simp only [Nat.reduceAdd] at mc mq mn
  clear hD hdisc hc hq hn
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run =>
    pvm_go [m192, hv192, jts, h1, h6, c216, disc, mc, mq, mn, hc64, hq64, hn64, tab, hw, hr, hrt,
      hws, hrs]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha hrs => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp
    all_goals try rfl
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hrs
    post_simp

/-- **HUH: between `alloc` and `dealloc`**, from `alloc`'s return (10092) with a block at
    ω₇ = ptr ≠ 0: the 19-octet message (two words, and the low half of the word at sp + 24 at
    + 15) is written at ptr and logged (`log`, 100: ω₇ := WHAT), then `dealloc(ptr, 19, 1)` (40613)
    is called with return address ω₀ = 358 (10164). Memory changes only at ptr … ptr + 19. -/
theorem huhMid {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (cap : Nat)
    (hcap : Constants.Cgasunknown ≤ cap) (hcap' : cap < 18446744073709551616) (env : AccEnv)
    (x : AccCtx) (ω : Regs) (μ : Memory) (ptr : Nat) (h1 : ω[1] = UInt64.ofNat 4278057152)
    (h7 : ω[7] = UInt64.ofNat ptr) (hp0 : ptr ≠ 0) (hp : ptr + 19 ≤ 4294967296)
    (hw : ∀ a, ptr ≤ a → a < ptr + 19 → μ.writable a = true)
    (hr24 : ∀ a, 4278057176 ≤ a → a < 4278057184 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p (accContractCK cap env) 10092 ω μ x 40613 ω' μ' x 30 ∧
      ω'[0] = UInt64.ofNat 358 ∧ ω'[1] = ω[1] ∧ ω'[7] = UInt64.ofNat ptr ∧ ω'[8] = UInt64.ofNat 19 ∧
      ω'[9] = UInt64.ofNat 1 ∧ KeepsExcept μ μ' [(ptr, 19)] ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, ptr ≤ a → a < ptr + 19 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hp64 : ptr < 18446744073709551616 := by omega
  obtain ⟨v24, hv24, m24⟩ := word_exists μ 4278057176
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run =>
    refine FreeStepsH.mono (FreeStepsH.trans (i' := 10148) (ω' := ?w1) (μ' := ?m1) (x' := x)
      (n₁ := 20) (n₂ := 6) ?a (FreeStepsH.logAccK cap hcap hcap' env (d_10148 (p := p) (P := P)) ?b))
      (by omega)
    case a => pvm_go [h1, h7, hp0, hp64, hw, hr, m24, hv24, hr24]
    case b => pvm_go [JAM.setR7, bs_40613]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, fun a ha hrs => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hrs
    post_simp

/-- **HUH: to `alloc(19, 1)`**: back at 10070 with the result's index b ≠ 255 in ω₇ (HUH gives 7,
    the table at 69076), the call of `alloc` (40494) for the 19-octet message, return address 356
    (10092). No host call, so any `R`. -/
theorem huhToAlloc {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] {X : Type}
    {R : HostRel X} (x : X) (ω : Regs) (μ : Memory) (b : Nat) (h7 : ω[7] = UInt64.ofNat b)
    (hb : b < 255) :
    ∃ ω', FreeStepsH p R 10070 ω μ x 40494 ω' μ x 6 ∧
      ω'[0] = UInt64.ofNat 356 ∧ ω'[1] = ω[1] ∧ ω'[7] = UInt64.ofNat 19 ∧ ω'[8] = UInt64.ofNat 1 := by
  have hb' : b % 256 ≠ 255 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h7, bitwise_and_m255, hb', bs_40494]
  · refine ⟨?_, ?_, ?_, ?_⟩
    all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat]

/-- **HUH: `alloc` returned null** (ω₇ = 0 at 10092): the trap at 15367 (☇, GP §A.5.1). -/
theorem huhNull {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] {X : Type}
    {R : HostRel X} (x : X) (ω : Regs) (μ : Memory) (h7 : ω[7] = 0) :
    ∃ ω' μ', FreeRunH p R 10092 ω μ x .panic ω' μ' x := by
  have run : ∃ ω', FreeStepsH p R 10092 ω μ x 15367 ω' μ x 3 := by
    rw [show ω = regsNF ω [] from rfl]
    refine ⟨?ω', ?run⟩
    case run => pvm_go [h7]
  obtain ⟨ω', hs⟩ := run
  have hd := d_15367 (p := p) (P := P)
  have hst : P.freeStep 15367 ω' μ = (.panic, P.next 15367, ω', μ) := by
    simp [Program.freeStep, hd.2.1, Program.exec, Program.finalState, memoryException]
  have he := FreeExit.step (p := p) hd.1 hst (by decide)
  exact ⟨ω', μ, hs.run (.exit (FreeRun.exit (by simpa using he)) (by simp))⟩

/-- **HUH: the result** (10164, back from `dealloc` with ω₁ = sp): `Err` with index 10 (the octets
    255, 10 at `RES`); then, if the input `Vec`'s capacity c (its copy at sp + 1496) is not 0, on to
    13303 (its buffer freed), else to the tail (14278). No host call, so any `R`. -/
theorem huhResult {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] {X : Type}
    {R : HostRel X} (x : X) (ω : Regs) (μ : Memory) (c : Nat) (h1 : ω[1] = UInt64.ofNat 4278057152)
    (hc : c < 18446744073709551616) (mc : μ.readN 4278058648 8 = Num.encodeLE 8 c)
    (hw : ∀ a, 4278058152 ≤ a → a < 4278058154 → μ.writable a = true)
    (hrc : ∀ a, 4278058648 ≤ a → a < 4278058656 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 10164 ω μ x (if c = 0 then 14278 else 13303) ω'
      ((μ.writeN 4278058153 [UInt8.ofNat 10]).writeN 4278058152 [UInt8.ofNat 255]) x 5 ∧
      ω'[1] = ω[1] ∧ ω'[8] = UInt64.ofNat c := by
  have hr : ∀ a, 4278058152 ≤ a → a < 4278058154 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have rc : rdN μ 4278058648 8 = c := by
    show Num.decodeLE _ = _
    rw [mc, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hc]
  rw [show ω = regsNF ω [] from rfl]
  by_cases h0 : c = 0
  · subst h0
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · simp only [↓reduceIte]
      pvm_go [h1, hw, hr, hrc, rc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_⟩
      all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat]
  · have h0' : c % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt hc]; exact h0
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · simp only [h0, ↓reduceIte]
      pvm_go [h1, hw, hr, hrc, rc, h0', rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_⟩
      all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat]

end Services.Bootstrap.Acc.Handlers.Designate
