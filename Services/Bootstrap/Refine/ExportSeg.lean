import Services.Bootstrap.Refine.Export
import Services.Bootstrap.Refine.PassLoop
import Services.Bootstrap.Decode.DeallocCall

/-!
# Refine's `Export` handler: one segment

One pass of the segment loop (5653 … 5653, or 5810 after the last): `export` (host 8, Ω_E, GP v0.8.0
Appendix B.4) of segment g's octets, the `format!` of the result (a hypothesis, `ExportFmtOk`, discharged by
the fmt summaries), the `log` and the `String`'s `dealloc`.
-/

namespace Services.Bootstrap.Refine.ExportSeg

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeR
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Refine.PassLoop Services.Bootstrap.Refine.HostSteps Services.Bootstrap.Refine.Export

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- The context after Ω_E of the sl octets at sp (`exportCtx` with ω₇ = sp, ω₈ = sl). -/
def expSeg (env : RefineHost.Env) (sp sl : Nat) (μ : Memory) (x : RefineCtx) : RefineCtx :=
  if env.exportOffset + x.2.length ≥ Constants.Cmaxpackageexports then x
  else (x.1, x.2 ++ [μ.readN sp (min sl Constants.Csegmentsize) ++
    List.replicate (Constants.Csegmentsize - min sl Constants.Csegmentsize) 0])

theorem exportCtx_eq {env : RefineHost.Env} {ω : Regs} {μ : Memory} {x : RefineCtx} {sp sl : Nat}
    (h7 : ω[7] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat sl) (hsp : sp < 18446744073709551616)
    (hsl : sl < 18446744073709551616) : exportCtx env ω μ x = expSeg env sp sl μ x := by
  have e7 : reg ω 7 = sp := by unfold reg; rw [show ω.get 7 = ω[7] from rfl, h7]; simp; omega
  have e8 : reg ω 8 = sl := by unfold reg; rw [show ω.get 8 = ω[8] from rfl, h8]; simp; omega
  unfold exportCtx expSeg; rw [e7, e8]

/-- A range whose octets are all readable passes the host's page-by-page check. -/
theorem rangeReadable_of {μ : Memory} {a n : Nat} (h : ∀ j, a ≤ j → j < a + n → μ.readable j = true)
    (hb : a + n ≤ 2 ^ 32) : μ.rangeReadable a n = true := by
  unfold Memory.rangeReadable
  by_cases hn : n = 0
  · simp [hn]
  have hn' : (n == 0) = false := by simp [hn]
  rw [hn', Bool.false_or, Bool.and_eq_true, List.all_eq_true]
  refine ⟨by simp [hb], fun k hk => ?_⟩
  simp only [List.mem_range] at hk
  have hpg : pageSize = 4096 := rfl
  have hk' : (a / pageSize + k) * pageSize ≤ a + n - 1 := by
    rw [hpg] at hk ⊢
    have := Nat.div_mul_le_self (a + n - 1) 4096
    have : a / 4096 + k ≤ (a + n - 1) / 4096 := by omega
    calc (a / 4096 + k) * 4096 ≤ (a + n - 1) / 4096 * 4096 := Nat.mul_le_mul_right _ this
      _ ≤ a + n - 1 := by omega
  let j := max a ((a / pageSize + k) * pageSize)
  have hj : μ.readable j = true := h j (Nat.le_max_left _ _) (by simp only [j]; omega)
  have hpage : j / pageSize = a / pageSize + k := by
    simp only [j, hpg] at hk' ⊢
    rcases Nat.le_total a ((a / 4096 + k) * 4096) with h1 | h1
    · rw [Nat.max_eq_right h1]; simp
    · rw [Nat.max_eq_left h1]
      have : k = 0 := by omega
      subst this; simp
  simp only [Memory.readable] at hj ⊢
  rw [← hpage]
  simpa [hpg, Nat.mul_div_cancel] using hj

/-- The `Result<u64, HostCallError>` at r as `xs2` lays it out: `Ok` (tag 0) or `Err` with a code below 8. -/
def ResultAt (μ : Memory) (r : Nat) : Prop :=
  μ.readN r 1 = [UInt8.ofNat 0] ∨ ∃ c, c < 8 ∧ μ.readN r 1 = [UInt8.ofNat 1] ∧ μ.readN (r + 1) 1 = [UInt8.ofNat c]

/-- **`Export`'s log line** (59375 … 5751), as a hypothesis: `format!("Exported slice: {:?} -> {:?}", seg,
    result)` (template 66196, arguments (M + 552, 1250) and (M + 560, 692)) into the `String` at M + 584, from
    refine's frame at M with the allocator's context, the segment's `Vec<u8>` (address at M + 552) and its
    octets readable, and the result laid out (`ResultAt`): the run returns to 5751 with the context unchanged,
    ω₁, ω₅, ω₆ kept, the allocator's context for some heap s', every allocated chunk of s kept with its data,
    the stack from M up kept apart from the `String`, and the `String` `{cap, ptr, len}` at M + 584, its buffer
    a fresh chunk when cap ≠ 0; or an allocation fails. To be discharged by the fmt summaries (`FmtCall`,
    `vec_u8_ok` and the `Result` argument). -/
def ExportFmtOk (p : ByteArray) (cap0 : Nat) (env : RefineHost.Env) (pb S0 S1 : Nat) : Prop :=
  ∀ (x : RefineCtx) (ω : Regs) (μ : Memory) (s : State) (M g sp sl : Nat),
    HeapCtx env pb S0 S1 μ s → S0 + 456 ≤ M → M + 648 ≤ S1 → M % 8 = 0 →
    ω[0] = UInt64.ofNat 182 → ω[1] = UInt64.ofNat M → ω[7] = UInt64.ofNat (M + 584) →
    ω[8] = UInt64.ofNat 66196 → ω[9] = UInt64.ofNat (M + 168) →
    μ.readN (M + 168) 8 = Num.encodeLE 8 (M + 552) → μ.readN (M + 176) 8 = Num.encodeLE 8 1250 →
    μ.readN (M + 184) 8 = Num.encodeLE 8 (M + 560) → μ.readN (M + 192) 8 = Num.encodeLE 8 692 →
    μ.readN (M + 552) 8 = Num.encodeLE 8 g → μ.readN (g + 8) 8 = Num.encodeLE 8 sp →
    μ.readN (g + 16) 8 = Num.encodeLE 8 sl → (∀ a, g ≤ a → a < g + 24 → μ.readable a = true) →
    (∀ a, sp ≤ a → a < sp + sl → μ.readable a = true) → sp + sl < 4294967296 → ResultAt μ (M + 560) →
    (∃ (ω' : Regs) (μ' : Memory) (s' : State) (N cap ptr len : Nat),
      FreeStepsH p (refineContractK cap0 env) 59375 ω μ x 5751 ω' μ' x N ∧ HeapCtx env pb S0 S1 μ' s' ∧
      ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      (∀ a, a < 4294967296 → M ≤ a → (a < M + 584 ∨ M + 608 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ d ∈ chunks s, d.used = true → d ∈ chunks s' ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
      μ'.readN (M + 584) 8 = Num.encodeLE 8 cap ∧ μ'.readN (M + 592) 8 = Num.encodeLE 8 ptr ∧
      μ'.readN (M + 600) 8 = Num.encodeLE 8 len ∧ cap < 536870912 ∧ ptr < 4294967296 ∧ len ≤ cap ∧
      (cap = 0 ∨ ∃ c ∈ chunks s', c.used = true ∧ c.addr + 32 = ptr ∧ ∀ d ∈ chunks s, d.used = true → d ≠ c)) ∨
    ∃ N, ExhaustsX env cap0 pb p 59375 ω μ x N

theorem setR7_getElem (ω : Regs) (v k : Nat) (hk : k < 13) (h7 : k ≠ 7) : (setR7 ω v)[k] = ω[k] := by
  simp only [setR7, Vector.getElem_set]
  split <;> simp_all

theorem setR7_getElem7 (ω : Regs) (v : Nat) : (setR7 ω v)[7] = UInt64.ofNat v := by
  simp [setR7, Vector.getElem_set]

theorem expSeg_congr {env : RefineHost.Env} {sp sl : Nat} {μ μ' : Memory} {x : RefineCtx}
    (h : ∀ a, sp ≤ a → a < sp + sl → μ'.read a = μ.read a) : expSeg env sp sl μ' x = expSeg env sp sl μ x := by
  unfold expSeg
  rw [Memory.readN_congr (fun j hj => h _ (by omega) (by omega))]

/-- **One segment of `Export`** (5653 … 5653, or 5810 after the last): segment g (`{cap, sp, sl}`, its octets
    readable) is exported (Ω_E: the context becomes `expSeg env sp sl μ x`), the result formatted
    (`ExportFmtOk`) and logged, and the `String` freed; ω₅ := g + 24. The allocator's context holds for some
    heap s' keeping every allocated chunk of s with its data, and the stack from M up is kept apart from
    M + 160 … M + 200 and M + 552 … M + 608. Or an allocation fails. -/
theorem seg {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (env : RefineHost.Env)
    (cap0 : Nat) (hcap1 : 134217728 ≤ cap0) (hcap0 : cap0 < 18446744073709551616) {pb S0 S1 : Nat}
    (fmt : ExportFmtOk p cap0 env pb S0 S1) (x : RefineCtx) (ω : Regs) (μ : Memory) (s : State)
    (H : HeapCtx env pb S0 S1 μ s) (M g sp sl en : Nat)
    (hM : S0 + 456 ≤ M ∧ M + 648 ≤ S1 ∧ 2147484104 ≤ M ∧ M % 8 = 0)
    (hg : g + 24 ≤ 2147483648) (hsp : sp + sl ≤ 2147483648) (hen : en < 18446744073709551616)
    (hoff : env.exportOffset + x.2.length < 18446744073709551615)
    (h1 : ω[1] = UInt64.ofNat M) (h5 : ω[5] = UInt64.ofNat g)
    (s8 : μ.readN (g + 8) 8 = Num.encodeLE 8 sp) (s16 : μ.readN (g + 16) 8 = Num.encodeLE 8 sl)
    (s152 : μ.readN (M + 152) 8 = Num.encodeLE 8 en)
    (rg : ∀ a, g ≤ a → a < g + 24 → μ.readable a = true) (rd : ∀ a, sp ≤ a → a < sp + sl → μ.readable a = true) :
    (∃ (ω' : Regs) (μ' : Memory) (s' : State) (N : Nat),
      FreeStepsH p (refineContractK cap0 env) 5653 ω μ x (if g + 24 = en then 5810 else 5653) ω' μ'
        (expSeg env sp sl μ x) N ∧ HeapCtx env pb S0 S1 μ' s' ∧
      ω'[1] = UInt64.ofNat M ∧ ω'[5] = UInt64.ofNat (g + 24) ∧
      (∀ a, a < 4294967296 → M ≤ a → (a < M + 160 ∨ M + 200 ≤ a) → (a < M + 552 ∨ M + 608 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ d ∈ chunks s, d.used = true → d ∈ chunks s' ∧ ∀ a, InData d a → μ'.read a = μ.read a)) ∨
    ∃ N, ExhaustsX env cap0 pb p 5653 ω μ x N := by
  obtain ⟨hS0M, hMS1, hM2, hM8⟩ := hM
  have hS1 := H.hS1
  have wst := H.st
  -- 1. the `export` call's arguments
  obtain ⟨ω1, μ1, run1, a1, a5, a6, a7, a8, a552, afr, ard, awr⟩ := xs1 (p := p) (P := P)
    (R := refineContractK cap0 env) x ω μ M g sp sl ⟨by omega, by omega, hM8⟩ (by omega) (Or.inl (by omega))
    (by omega) (by omega) h1 h5 s8 s16 (fun a h1 h2 => rg a (by omega) (by omega))
    (fun a h1 h2 => wst a (by omega) (by omega))
  -- 2. `export` (Ω_E)
  have hrr : μ1.rangeReadable (reg ω1 7) (min (reg ω1 8) Constants.Csegmentsize) = true := by
    have e7 : reg ω1 7 = sp := by unfold reg; rw [show ω1.get 7 = ω1[7] from rfl, a7]; simp; omega
    have e8 : reg ω1 8 = sl := by unfold reg; rw [show ω1.get 8 = ω1[8] from rfl, a8]; simp; omega
    rw [e7, e8]
    exact rangeReadable_of (fun a h1 h2 => by rw [ard]; exact rd a h1 (by omega)) (by omega)
  have hx1 : exportCtx env ω1 μ1 x = expSeg env sp sl μ x := by
    rw [exportCtx_eq a7 a8 (by omega) (by omega)]
    exact expSeg_congr (fun a h1 h2 => afr a (by omega) (Or.inl (by omega)))
  have hv : exportR7 env x < 18446744073709551615 := by
    unfold exportR7; split
    · unfold Result.FULL; decide
    · omega
  -- 3. the result laid out, and the `format!` call
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, b168, b176, b184, b192, bok, berr, bfr, brd, bwr⟩ :=
    xs2 (p := p) (P := P) (R := refineContractK cap0 env) (expSeg env sp sl μ x) (setR7 ω1 (exportR7 env x)) μ1 M
    (exportR7 env x) ⟨by omega, by omega, hM8⟩ (by omega) (by omega)
    (by rw [setR7_getElem _ _ 1 (by decide) (by decide), a1, h1]) (setR7_getElem7 _ _)
    (fun a h1 h2 => by rw [awr]; exact wst a (by omega) (by omega))
    (fun a h1 h2 => by rw [awr]; exact wst a (by omega) (by omega))
  have pre2 : FreeStepsH p (refineContractK cap0 env) 5653 ω μ x 59375 ω2 μ2 (expSeg env sp sl μ x) _ :=
    run1.trans (FreeStepsH.exportRef cap0 ⟨by omega, hcap0⟩ env (d_5664 (p := p) (P := P)) hrr (by rw [hx1]; exact run2))
  have k2 : ∀ a, a < 4294967296 → (a < M + 168 ∨ M + 200 ≤ a) → (a < M + 552 ∨ M + 576 ≤ a) →
      μ2.read a = μ.read a := fun a h0 h1 h2 => by
    rw [bfr a h0 h1 (by omega), afr a h0 (by omega)]
  have H2 : HeapCtx env pb S0 S1 μ2 s := Decode.GrowOne.ctx_high H (fun a ha => k2 a (by omega) (by omega)
    (by omega)) (fun a => by rw [bwr, awr])
  have hres : ResultAt μ2 (M + 560) := by
    by_cases hok : exportR7 env x < 18446744073709551607
    · exact Or.inl (bok hok).1
    · obtain ⟨e0, e1⟩ := berr (by omega)
      exact Or.inr ⟨18446744073709551614 - exportR7 env x, by omega, e0, e1⟩
  sorry

end Services.Bootstrap.Refine.ExportSeg

