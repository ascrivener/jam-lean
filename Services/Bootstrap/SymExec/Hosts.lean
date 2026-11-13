import Services.Bootstrap.Acc.Inputs.FetchStep
import Services.Bootstrap.SymExec.Prog

/-!
EXPERIMENTAL (symexec Phase 2, `docs/symexec-spike.md`): host calls the executor follows, as
host effects (`HostEff`) with their contract lemmas (`EffOk`).
* `logEff`: `ecalli 100` (`log`, JIP-1), an id neither refine's dispatcher (GP eq.
  `refinemutator`) nor accumulate's (GP eq. `accinvocation`) defines: it charges 𝖬_∅ and returns
  WHAT in ω₇. `refine_log` and `acc_log` for any cap of at least 𝖬_∅ = 1000.
* `fetch0Eff v o f z`: `fetch` (id 2, Ω_Y, GP Appendix B) of kind 0, the protocol parameters
  ℰ(params) = v, with ω₇ = o, ω₈ = f, ω₉ = z: it writes `fetchSlice v f z` at o and sets
  ω₇ = |v|. `refine_fetch0` and `acc_fetch0` for the full-chain parameters and any cap of at
  least 𝖬_{Y,0} = 390.
-/

namespace Services.Bootstrap.SymExec

open PVM PVM.SymExec JAM Services.Bootstrap.Code

/-- `log` (id 100): ω₇ := WHAT. -/
def logEff : HostEff := { out := [(7, Result.WHAT)] }

/-- The host table with `log` only. -/
def logHosts : NTree (List HostEff) := .node .leaf 100 [logEff] .leaf

theorem hregs_log (ω : Regs) : hregs ω [(7, Result.WHAT)] = setR7 ω Result.WHAT := rfl

/-- Refine's contract, at any cap 𝖬_∅ ≤ cap < 2^64, allows `log`. -/
theorem refine_log {cap : Nat} (h1 : Constants.Cgasunknown ≤ cap) (h2 : cap < 2 ^ 64)
    (env : RefineHost.Env) : EffOk (refineContractK cap env) 100 logEff := by
  intro ω μ x _ _
  have hc : (UInt64.ofNat cap).toNat = cap := by simp [Nat.mod_eq_of_lt h2]
  have hg : ¬((cap : Int) - Constants.Cgasunknown < 0) := by omega
  refine ⟨Or.inr (Or.inr (by decide)), ?_, ?_⟩ <;>
    simp [toHostFn, RefineHost.dispatch, RefineHost.unknown, hc, hg, logEff, hregs_log, hmem]

/-- Accumulate's contract, at any cap 𝖬_∅ ≤ cap < 2^64, allows `log`. -/
theorem acc_log {cap : Nat} (h1 : Constants.Cgasunknown ≤ cap) (h2 : cap < 2 ^ 64)
    (env : AccEnv) : EffOk (Acc.accContractK cap env) 100 logEff := by
  intro ω μ x _ _
  have hc : (UInt64.ofNat cap).toNat = cap := by simp [Nat.mod_eq_of_lt h2]
  have hg : ¬((cap : Int) - Constants.Cgasunknown < 0) := by omega
  refine ⟨⟨by decide, by decide⟩, ?_, ?_⟩ <;>
    simp [accHostFn, AccHost.dispatch, hc, hg, logEff, hregs_log, hmem]

theorem refine_logHosts {cap : Nat} (h1 : Constants.Cgasunknown ≤ cap) (h2 : cap < 2 ^ 64)
    (env : RefineHost.Env) : HostOk (refineContractK cap env) logHosts :=
  ⟨fun e he => by simp only [List.mem_singleton] at he; subst he; exact refine_log h1 h2 env,
    trivial, trivial⟩

theorem acc_logHosts {cap : Nat} (h1 : Constants.Cgasunknown ≤ cap) (h2 : cap < 2 ^ 64)
    (env : AccEnv) : HostOk (Acc.accContractK cap env) logHosts :=
  ⟨fun e he => by simp only [List.mem_singleton] at he; subst he; exact acc_log h1 h2 env,
    trivial, trivial⟩

/-! ## `fetch` of the protocol parameters -/

/-- The octets `fetch` writes for a value v with ω₈ = f and ω₉ = z: v_{f′…+l}, where
    f′ = min(f, |v|) and l = min(z, |v| − f′) (GP Appendix B, Ω_Y). -/
def fetchSlice (v : List UInt8) (f z : Nat) : List UInt8 :=
  (v.drop (min f v.length)).take (min z (v.length - min f v.length))

/-- `fetch` (id 2) of kind ω₁₀ = 0, the protocol parameters, whose encoding is v: with ω₇ = o,
    ω₈ = f, ω₉ = z, it writes `fetchSlice v f z` at o and sets ω₇ = |v|. -/
def fetch0Eff (v : List UInt8) (o f z : Nat) : HostEff :=
  { pre := [(7, o), (8, f), (9, z), (10, 0)]
    wr := if (fetchSlice v f z).length = 0 then none
      else some (o, (fetchSlice v f z).length, Num.decodeLE (fetchSlice v f z))
    out := [(7, v.length)] }

theorem hmem_fetch0 (μ : Memory) (v : List UInt8) (o f z : Nat) :
    hmem μ (fetch0Eff v o f z).wr = μ.writeN o (fetchSlice v f z) := by
  unfold fetch0Eff
  split
  · rename_i h; simp only [hmem]; rw [List.eq_nil_of_length_eq_zero h]; rfl
  · simp only [hmem]; rw [encodeLE_decodeLE]

theorem fetch0_regs {ω : Regs} {v : List UInt8} {o f z : Nat}
    (hp : ∀ p ∈ (fetch0Eff v o f z).pre, ∀ hr : p.1 < 13, (ω.get ⟨p.1, hr⟩).toNat = p.2) :
    reg ω 7 = o ∧ reg ω 8 = f ∧ reg ω 9 = z ∧ reg ω 10 = 0 :=
  ⟨hp (7, o) (by simp [fetch0Eff]) (by simp), hp (8, f) (by simp [fetch0Eff]) (by simp),
    hp (9, z) (by simp [fetch0Eff]) (by simp), hp (10, 0) (by simp [fetch0Eff]) (by simp)⟩

theorem fetch0_writable {μ : Memory} {v : List UInt8} {o f z : Nat}
    (ho : o + (fetchSlice v f z).length ≤ 2 ^ 32)
    (hw : ∀ w, (fetch0Eff v o f z).wr = some w → ∀ t, w.1 ≤ t → t < w.1 + w.2.1 → μ.writable t = true) :
    μ.rangeWritable o (fetchSlice v f z).length = true := by
  by_cases h0 : (fetchSlice v f z).length = 0
  · rw [h0]; simp [Memory.rangeWritable]
  · exact Acc.rangeWritable_of ho fun t h1 h2 =>
      hw (o, (fetchSlice v f z).length, Num.decodeLE (fetchSlice v f z))
        (by simp only [fetch0Eff, if_neg h0]) t h1 h2

/-- Refine's contract allows `fetch` of the parameters, when they are the full-chain ones
    (`env.fetch.params = Params.full`), at any cap 390 ≤ cap < 2^64 (𝖬_{Y,0} = 390). -/
theorem refine_fetch0 {cap : Nat} (h1 : 390 ≤ cap) (h2 : cap < 2 ^ 64) (env : RefineHost.Env)
    (hpar : env.fetch.params = Params.full) (o f z : Nat)
    (ho : o + (fetchSlice Params.full.encode f z).length ≤ 2 ^ 32) :
    EffOk (refineContractK cap env) 2 (fetch0Eff Params.full.encode o f z) := by
  intro ω μ x hp hw
  obtain ⟨h7, h8, h9, h10⟩ := fetch0_regs hp
  have hwr := fetch0_writable ho hw
  have hc : (UInt64.ofNat cap).toNat = cap := by simp [Nat.mod_eq_of_lt h2]
  have hlen : (fetchSlice Params.full.encode f z).length =
      min z (Params.full.encode.length - min f Params.full.encode.length) := by
    simp only [fetchSlice, List.length_take, List.length_drop]; omega
  rw [hlen] at hwr
  have hY : Constants.CgasY (if (0 : Nat) < 16 then some 0 else none) = (390, 0) := rfl
  have hm : memGas 0 z = 0 := by simp [memGas]
  have hg : ¬ cap < 390 + 0 := by omega
  refine ⟨Or.inr (Or.inl rfl), by decide, ?_⟩
  simp only [toHostFn, RefineHost.dispatch, hostFetch, charged, h7, h8, h9, h10, hc, hY, hm, hg,
    ite_false, writeValue, fetchValue, hpar]
  have hL : Params.full.encode.length = 122 := Params.encode_length _
  rw [hL] at hwr
  rw [hmem_fetch0]
  simp [hwr, fetchSlice, fetch0Eff, hregs, setR7, hL]

/-- Accumulate's contract allows `fetch` of the parameters, when they are the full-chain ones
    (`env.params = Params.full`), at any cap 390 ≤ cap < 2^64 (𝖬_{Y,0} = 390). -/
theorem acc_fetch0 {cap : Nat} (h1 : 390 ≤ cap) (h2 : cap < 2 ^ 64) (env : AccEnv)
    (hpar : env.params = Params.full) (o f z : Nat)
    (ho : o + (fetchSlice Params.full.encode f z).length ≤ 2 ^ 32) :
    EffOk (Acc.accContractK cap env) 2 (fetch0Eff Params.full.encode o f z) := by
  intro ω μ x hp hw
  obtain ⟨h7, h8, h9, h10⟩ := fetch0_regs hp
  have hwr := fetch0_writable ho hw
  have hc : (UInt64.ofNat cap).toNat = cap := by simp [Nat.mod_eq_of_lt h2]
  have hlen : (fetchSlice Params.full.encode f z).length =
      min z (Params.full.encode.length - min f Params.full.encode.length) := by
    simp only [fetchSlice, List.length_take, List.length_drop]; omega
  rw [hlen] at hwr
  have hY : Constants.CgasY (if (0 : Nat) < 16 then some 0 else none) = (390, 0) := rfl
  have hm : memGas 0 z = 0 := by simp [memGas]
  have hg : ¬ cap < 390 + 0 := by omega
  refine ⟨⟨by decide, by decide⟩, by decide, ?_⟩
  simp only [accHostFn, AccHost.dispatch, hostFetch, charged, h7, h8, h9, h10, hc, hY, hm, hg,
    ite_false, writeValue, fetchValue, hpar]
  have hL : Params.full.encode.length = 122 := Params.encode_length _
  rw [hL] at hwr
  rw [hmem_fetch0]
  simp [hwr, fetchSlice, fetch0Eff, hregs, setR7, hL]

/-- Bootstrap's code table, following `log`. -/
def progLog : Prog := { prog with hosts := logHosts }

/-- Example: the `log` call at pc 4770 (BTail1 S49), through refine's contract. -/
theorem log4770_ok : check ⟨[], [], [], [], []⟩ progLog ⟨[], []⟩ ⟨[(7, .const Result.WHAT)], []⟩ []
    4770 4772 1 = true := by decide +kernel

theorem log4770 {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (x : RefineCtx)
    (ω : Regs) (μ : Memory) :
    ∃ ω' μ', FreeStepsH p (refineContract env) 4770 ω μ x 4772 ω' μ' x 1 ∧
      ω'[7] = UInt64.ofNat Result.WHAT := by
  obtain ⟨ω', μ', hrun, ⟨r7, -⟩, -⟩ :=
    check_sound log4770_ok (hyp (p := p) (P := P)) [] trivial trivial ω μ trivial trivial trivial
      trivial trivial x (refine_logHosts (cap := hostCostMax) (by decide) (by decide) env)
  exact ⟨ω', μ', hrun, r7⟩

/-- Example: PrefixC's steps 32 … 47 (pc 47481 to 47574), through the length query
    `fetch` of the parameters at pc 47490 (ω₇ = ω₈ = ω₉ = 0; ω₇ := 122). -/
theorem prefixC2_ok :
    check { ub := [], lb := [], rd := [], wr := [(⟨none, 4278057984⟩, 8)], sep := [] }
      { prog with hosts := .node .leaf 2 [fetch0Eff Params.full.encode 0 0 0] .leaf }
      { regs := [(1, .const 4278057960), (10, .const 0), (11, .const 0), (12, .const 0)], cells := [] }
      { regs := [(1, .const 4278057960), (4, .reg0 4), (5, .const 122), (6, .const 196792),
          (7, .const 206848)]
        cells := [(⟨none, 4278057984⟩, 8, .const 0)] }
      [(⟨none, 4278057984⟩, 8)] 47481 47574 16 = true := by decide +kernel

end Services.Bootstrap.SymExec
