import Services.Bootstrap.Acc.Handlers.Checkpoint
import Services.Bootstrap.Acc.ContractC

/-!
# The `Assign` handler (tag 12)

`Assign { core, assigner, queue }` carries the core index (u16, at + 36 of the instruction), the
assigner (u32, at + 32) and a `Vec` of 32-octet authorizer hashes at + 8 (capacity, pointer,
length). From the dispatch point:
1. 12096: the `Vec` is copied to sp + 1568; the core index and the assigner go to sp − 14 and
   sp − 12; a frame of 80 octets is pushed at S = sp − 96 with their addresses at S and S + 8 and the
   length n at S + 24; then 40215 with ω₅ = 32 · n and ω₆ the hashes' address.
2. 40215: a buffer of 32 · n + 3 octets is allocated (`alloc_impl`), the hashes copied into it
   (`AssignLoop`), `assign` (Ω_A, id 16) is called at 40397 and the buffer freed (`free_impl`).

This file proves step 1: `toEntry`.
-/

namespace Services.Bootstrap.Acc.Handlers.Assign

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Acc
  Services.Bootstrap.Acc.Handlers

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **From the dispatch to 40215**: for `Assign` (the discriminant 2⁶³ + 11), the dispatch reaches
    12096, which copies the `Vec` (capacity c, pointer q, length n, at + 8 of the instruction) to
    sp + 1568, the core index (u16 at + 36) to sp − 14 and the assigner (u32 at + 32) to sp − 12,
    pushes two frames (S = sp − 96) and jumps to 40215 with ω₅ = 32 · n, ω₆ = q. No host call, so
    any `R`. -/
theorem toEntry {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] {X : Type}
    {R : HostRel X} (x : X) (ω : Regs) (μ : Memory) (bs : List UInt8) (hD : AtDispatch ω μ bs)
    (c q n core a : Nat)
    (hdisc : bs.take 8 = Num.encodeLE 8 9223372036854775819)
    (hc : (bs.drop 8).take 8 = Num.encodeLE 8 c) (hq : (bs.drop 16).take 8 = Num.encodeLE 8 q)
    (hn : (bs.drop 24).take 8 = Num.encodeLE 8 n)
    (ha : (bs.drop 32).take 4 = Num.encodeLE 4 a) (hcore : (bs.drop 36).take 2 = Num.encodeLE 2 core)
    (hc64 : c < 18446744073709551616) (hq64 : q < 18446744073709551616)
    (hn64 : 32 * n < 18446744073709551616) (ha32 : a < 4294967296) (hcore16 : core < 65536)
    (hws : ∀ a, 4278057056 ≤ a → a < 4278057152 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 8822 ω μ x 40215 ω' μ' x 60 ∧
      ω'[1] = UInt64.ofNat 4278057056 ∧ ω'[5] = UInt64.ofNat (32 * n) ∧ ω'[6] = UInt64.ofNat q ∧
      μ'.readN 4278057056 8 = Num.encodeLE 8 4278057138 ∧
      μ'.readN 4278057064 8 = Num.encodeLE 8 4278057140 ∧
      μ'.readN 4278057080 8 = Num.encodeLE 8 n ∧
      μ'.readN 4278057138 2 = Num.encodeLE 2 core ∧ μ'.readN 4278057140 4 = Num.encodeLE 4 a ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have h1 := hD.sp
  have h6 := hD.r6
  have c216 := hD.c216
  have hw := hD.frame
  have hrt := hD.tabR
  have hr : ∀ a, 4278057152 ≤ a → a < 4278059008 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hrs : ∀ a, 4278057056 ≤ a → a < 4278057152 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hws a h1 h2)
  have disc := slot_word0 hD.slotB hdisc
  have mc := slot_word hD.slotA 8 (by decide) hc
  have mq := slot_word hD.slotA 16 (by decide) hq
  have mn := slot_word hD.slotA 24 (by decide) hn
  have ma : μ.readN 4278058328 4 = Num.encodeLE 4 a := by
    rw [Decode.Loop.readN_sub μ 4278058296 232 32 4 bs hD.slotB (by decide), ha]
  have mcore : μ.readN 4278058332 2 = Num.encodeLE 2 core := by
    rw [Decode.Loop.readN_sub μ 4278058296 232 36 2 bs hD.slotB (by decide), hcore]
  have tab : μ.readN 65784 4 = [246, 0, 255, 255] := tab_entry hD.tab 12 (by decide)
  obtain ⟨v192, hv192, m192⟩ := word_exists μ 4278057344
  simp only [Nat.reduceAdd] at mc mq mn
  clear hD hdisc hc hq hn ha hcore
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run =>
    pvm_go [m192, hv192, jts, h1, h6, c216, disc, mc, mq, mn, ma, mcore, hc64, hq64, hn64, ha32, hcore16,
      tab, hw, hr, hrt, hws, hrs]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp
    all_goals try rfl
    all_goals try (congr 1; omega)
    all_goals (congr 1; split <;> omega)

end Services.Bootstrap.Acc.Handlers.Assign
