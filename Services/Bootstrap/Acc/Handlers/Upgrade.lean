import Services.Bootstrap.Acc.Handlers.Checkpoint

/-!
# The `Upgrade` handler (tag 1)

`Upgrade { code_hash, min_item_gas, min_memo_gas }`:
1. the 32-octet code hash is copied to sp + 1568, and `upgrade` (Ω_U, id 20, GP v0.8.0 eq.
   `accinvocation`) is called at 11792 with ω₇ = sp + 1568, ω₈ = `min_item_gas`, ω₉ =
   `min_memo_gas`, after pushing the return address 428 (11798) at sp − 8;
2. 49541 checks ω₇: anything but OK traps (the SDK's `expect`, Q8); OK pops and returns to 11798;
3. `alloc(9, 1)`, a 9-octet log message, `log`, `dealloc`, as for `Checkpoint`;
4. the result `Ok(Unit)` and the drop of the instruction value, returning to 14278.

This file proves step 1 up to the check: `toCheck`.
-/

namespace Services.Bootstrap.Acc.Handlers.Upgrade

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Acc
  Services.Bootstrap.Acc.Handlers

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- Ω_U (`upgrade`, id 20) when the 32 octets at ω₇ are readable, as Ψ_A's handler gives it at the
    contract's gas: OK, and x_s's code hash and gas limits set from them and ω₈, ω₉. -/
theorem upgrade_eq (env : AccEnv) (ω : Regs) (μ : Memory) (x : AccCtx) (h : List UInt8)
    (hm : AccHost.readMem μ (reg ω 7) 32 = some h) :
    accHostFn env 20 (UInt64.ofNat hostCostMax) ω μ x =
      ⟨.cont, (accHostFn env 20 (UInt64.ofNat hostCostMax) ω μ x).gas, setR7 ω Result.OK, μ,
        (x.1.setSelf { x.1.self with codeHash := h, minAccGas := reg ω 8, minMemoGas := reg ω 9 },
          x.2)⟩ := by
  simp [accHostFn, AccHost.dispatch, AccHost.upgrade, AccHost.charge, charged, hm, AccHost.r7,
    AccHost.updX, hostCostMax, Constants.CgasU]

/-- **From the dispatch through `upgrade`**: for `Upgrade` (the discriminant 2⁶³, the code hash
    c at slot + 8, `min_item_gas` g at slot + 40, `min_memo_gas` m at slot + 48), the handler calls
    Ω_U with the hash's copy at sp + 1568, which sets x_s's code hash to c and its gas limits to g
    and m, and returns OK (ω₇ = 0). It reaches the check at 49541 with the return address 428 at
    sp − 8 and ω₁ = sp − 8. Memory changes only at sp + 1380 (4 octets), sp + 1568 (32) and
    sp − 8 (8). -/
theorem toCheck {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : AccEnv) (x : AccCtx)
    (ω : Regs) (μ : Memory) (bs : List UInt8) (hD : AtDispatch ω μ bs) (c : List UInt8) (g m : Nat)
    (hg64 : g < 18446744073709551616) (hm64 : m < 18446744073709551616)
    (hdisc : bs.take 8 = Num.encodeLE 8 9223372036854775808) (hc : (bs.drop 8).take 32 = c)
    (hg : (bs.drop 40).take 8 = Num.encodeLE 8 g) (hm : (bs.drop 48).take 8 = Num.encodeLE 8 m)
    (hws : ∀ a, 4278057144 ≤ a → a < 4278057152 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (accContractC env) 8822 ω μ x 49541 ω' μ'
      (x.1.setSelf { x.1.self with codeHash := c, minAccGas := g, minMemoGas := m }, x.2) 40 ∧
      ω'[1] = UInt64.ofNat 4278057144 ∧ ω'[7] = UInt64.ofNat 0 ∧
      μ'.readN 4278057144 8 = Num.encodeLE 8 428 ∧
      KeepsExcept μ μ' [(4278058532, 4), (4278058720, 32), (4278057144, 8)] ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have h1 := hD.sp
  have h6 := hD.r6
  have c216 := hD.c216
  have hw := hD.frame
  have hrt := hD.tabR
  have hr : ∀ a, 4278057152 ≤ a → a < 4278059008 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hrs : ∀ a, 4278057144 ≤ a → a < 4278057152 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hws a h1 h2)
  have disc := slot_word0 hD.slotB hdisc
  have mg := slot_word hD.slotB 40 (by decide) hg
  have mm := slot_word hD.slotB 48 (by decide) hm
  have mc : μ.readN 4278057904 32 = c := by
    rw [Decode.Loop.readN_sub μ 4278057896 232 8 32 bs hD.slotA (by decide), hc]
  have tab : μ.readN 65740 4 = [226, 0, 255, 255] := tab_entry hD.tab 1 (by decide)
  obtain ⟨w0, hw0, m0⟩ := word_exists μ 4278057904
  obtain ⟨w1, hw1, m1⟩ := word_exists μ 4278057912
  obtain ⟨w2, hw2, m2⟩ := word_exists μ 4278057920
  obtain ⟨w3, hw3, m3⟩ := word_exists μ 4278057928
  obtain ⟨v192, hv192, m192⟩ := word_exists μ 4278057344
  simp only [Nat.reduceAdd] at mg mm
  clear hD hdisc hc hg hm
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run =>
    refine FreeStepsH.mono (FreeStepsH.trans (i' := 11792) (ω' := ?w1) (μ' := ?m1) (x' := x)
      (n₁ := 30) (n₂ := 1) ?a (FreeStepsH.accHostC env (h := 20) (by unfold AccGasFreeId; decide)
        (d_11792 (p := p) (P := P)) rfl ?hs ?b)) (by omega)
    case a => pvm_go [m192, hv192, m0, hw0, m1, hw1, m2, hw2, m3, hw3, jtsA, h1, h6, c216, disc, mg,
      mm, tab, hw, hr, hrt, hws, hrs]
    case hs =>
      rw [upgrade_eq env _ _ x c ?hread]
      case hread =>
        have hrr := rangeReadable_of' (μ := ((((((μ.writeN 4278058532 (Num.encodeLE 4 (v192 % 4294967296))).writeN 4278058720 (Num.encodeLE 8 w0)).writeN
                      4278058728 (Num.encodeLE 8 w1)).writeN 4278058736 (Num.encodeLE 8 w2)).writeN
              4278058744 (Num.encodeLE 8 w3)).writeN 4278057144
          [UInt8.ofNat 172, UInt8.ofNat 1, UInt8.ofNat 0, UInt8.ofNat 0, UInt8.ofNat 0, UInt8.ofNat 0, UInt8.ofNat 0,
            UInt8.ofNat 0])) (a := 4278058720) (n := 32) (fun j h1 h2 => by
              simp only [PVM.Memory.readable_writeN]; exact hr j (by omega) (by omega)) (by decide)
        simp only [AccHost.readMem, reg, PVM.getElem_regsNF, PVM.lookup_cons_nat, Regs.get,
          PVM.regIdx_val_7, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some', UInt64.toNat_ofNat',
          Nat.reduceMod, hrr, Option.some.injEq]
        rw [show (32 : Nat) = 8 + 24 from rfl, Memory.readN_split, show (24 : Nat) = 8 + 16 from rfl,
          Memory.readN_split, show (16 : Nat) = 8 + 8 from rfl, Memory.readN_split]
        simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_same, PVM.Memory.readN_writeN_disjoint,
          PVM.Num.length_encodeLE, List.length_cons, List.length_nil, PVM.two32, Nat.reduceAdd]
        rw [← m0, ← m1, ← m2, ← m3, ← mc, show (32 : Nat) = 8 + 24 from rfl, Memory.readN_split,
          show (24 : Nat) = 8 + 16 from rfl, Memory.readN_split, show (16 : Nat) = 8 + 8 from rfl,
          Memory.readN_split]
    case b =>
      sorry
  case post =>
    sorry

end Services.Bootstrap.Acc.Handlers.Upgrade
