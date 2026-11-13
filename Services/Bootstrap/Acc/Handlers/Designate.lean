import Services.Bootstrap.Acc.Handlers.Checkpoint

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

end Services.Bootstrap.Acc.Handlers.Designate
