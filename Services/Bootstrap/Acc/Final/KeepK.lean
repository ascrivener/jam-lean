import Services.Bootstrap.Acc.Wrappers.GrowS
import Services.Bootstrap.Acc.Checkpoint
import Services.Bootstrap.Fmt.ReallocCopyInst
import Services.Bootstrap.Fmt.InfoStep
import Services.Bootstrap.Fmt.LogSteps
import Services.Bootstrap.Acc.ContractC
import Services.Bootstrap.Acc.Impl.ROKeepS

/-!
# Runs under accumulate's gas-capped contract as runs of the stream contract

T2's final composition (`accumulate_spec`) chains summaries stated under `accContractK cap env` (the
start-up, the inputs decode) into an `Impl` under `accContractS env`. Two lifts:

- **`FreeStepsH.yinK`**: every `accContractK` step is an `accContractS` step with the answer stream
  kept, and keeps y (no `checkpoint`: GP v0.8.0 eq. `accinvocation`, only Ω_C writes y;
  `accHostFn_ctx_snd`). So a run under `accContractK` from y = a is a run under `YIn (accContractS env) a b`.
- **`accKeepK`**: `accContractK` restricted to steps that keep the whole context (x, y). A run under it
  keeps the context and is a run under `KeepCtx (accContractS env)` (`FreeStepsH.keepS`). The
  allocator's calls meet `AllocOk` / `ReallocOk` under it (`grow_heap` keeps the context), and the
  `info` and `log` steps are its steps.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap Services.Bootstrap.Fmt

/-- **An `accContractK` step is an `accContractS` step keeping y and the stream.** -/
theorem accContractK_S {cap : Nat} {env : AccEnv} {h : Nat} {ω : Regs} {μ : Memory} {x : AccCtx}
    {ω' : Regs} {μ' : Memory} {x' : AccCtx} (f : Stream)
    (hs : accContractK cap env h ω μ x .cont ω' μ' x') :
    x'.2 = x.2 ∧ accContractS env h ω μ (x, f) .cont ω' μ' (x', f) := by
  obtain ⟨hgf, hno, he⟩ := hs
  refine ⟨?_, .inl ⟨hgf, hno, rfl, UInt64.ofNat cap, he⟩⟩
  have hc := congrArg PVM.HostResult.ctx he
  simp only at hc
  rcases accHostFn_ctx_snd env h (UInt64.ofNat cap) ω μ x with h2 | ⟨h18, -⟩
  · rw [← hc]; exact h2
  · exact absurd h18 hgf.2

/-- **A run under `accContractK` is a run under `YIn (accContractS env) a b`** from y = a, keeping y
    and the stream. -/
theorem FreeStepsH.yinK {p : ByteArray} {cap : Nat} {env : AccEnv} (a b : Implications) (f : Stream)
    {i : Nat} {ω : Regs} {μ : Memory} {x : AccCtx} {i' : Nat} {ω' : Regs} {μ' : Memory} {x' : AccCtx}
    {n : Nat} (run : FreeStepsH p (accContractK cap env) i ω μ x i' ω' μ' x' n) (ha : x.2 = a) :
    x'.2 = a ∧ FreeStepsH p (YIn (accContractS env) a b) i ω μ (x, f) i' ω' μ' (x', f) n := by
  induction run with
  | refl => exact ⟨ha, .refl⟩
  | pad _ ih => exact ⟨(ih ha).1, .pad (ih ha).2⟩
  | next hn hc _ ih => exact ⟨(ih ha).1, .next hn hc (ih ha).2⟩
  | host hP hc hst hr _ ih =>
    obtain ⟨e2, hS⟩ := accContractK_S f hr
    have ha' := e2.trans ha
    exact ⟨(ih ha').1, .host hP hc hst ⟨hS, .inl ha'⟩ (ih ha').2⟩

/-- **`accContractK` restricted to steps that keep the context.** -/
def accKeepK (cap : Nat) (env : AccEnv) : HostRel AccCtx :=
  fun h ω μ x s ω' μ' x' => accContractK cap env h ω μ x s ω' μ' x' ∧ x' = x

/-- **A run under `accKeepK` keeps the context, and is a run under `KeepCtx (accContractS env)`** with
    the stream kept. -/
theorem FreeStepsH.keepS {p : ByteArray} {cap : Nat} {env : AccEnv} (f : Stream)
    {i : Nat} {ω : Regs} {μ : Memory} {x : AccCtx} {i' : Nat} {ω' : Regs} {μ' : Memory} {x' : AccCtx}
    {n : Nat} (run : FreeStepsH p (accKeepK cap env) i ω μ x i' ω' μ' x' n) :
    x' = x ∧ FreeStepsH p (KeepCtx (accContractS env)) i ω μ (x, f) i' ω' μ' (x, f) n := by
  induction run with
  | refl => exact ⟨rfl, .refl⟩
  | pad _ ih => exact ⟨ih.1, .pad ih.2⟩
  | next hn hc _ ih => exact ⟨ih.1, .next hn hc ih.2⟩
  | host hP hc hst hr _ ih =>
    obtain ⟨hk, rfl⟩ := hr
    exact ⟨ih.1, .host hP hc hst ⟨(accContractK_S f hk).2, rfl⟩ ih.2⟩

/-- A run under `accKeepK` is one under `accContractK`. -/
theorem FreeStepsH.ofKeepK {p : ByteArray} {cap : Nat} {env : AccEnv}
    {i : Nat} {ω : Regs} {μ : Memory} {x : AccCtx} {i' : Nat} {ω' : Regs} {μ' : Memory} {x' : AccCtx}
    {n : Nat} (run : FreeStepsH p (accKeepK cap env) i ω μ x i' ω' μ' x' n) :
    FreeStepsH p (accContractK cap env) i ω μ x i' ω' μ' x' n :=
  run.weaken fun _ _ _ _ _ _ _ hr => hr.1

/-- An `accGrowK` step is an `accKeepK` step (`grow_heap` keeps the context). -/
theorem accGrowK_keepK {cap : Nat} {env : AccEnv} {h : Nat} {ω : Regs} {μ : Memory} {x : AccCtx}
    {ω' : Regs} {μ' : Memory} {x' : AccCtx} (hs : accGrowK cap env h ω μ x .cont ω' μ' x') :
    accKeepK cap env h ω μ x .cont ω' μ' x' := by
  obtain ⟨rfl, hk⟩ := hs
  refine ⟨hk, ?_⟩
  have := congrArg PVM.HostResult.ctx hk.2.2
  rw [grow_ctx] at this
  exact this.symm

/-- **`AllocOk` under `accKeepK`**, for any refine host with accumulate's code, cap ≥ 2²⁷. -/
theorem allocOk_keepK {p : ByteArray} {P : Program} [Code.HasCode p P] (env : AccEnv) (envH : RefineHost.Env)
    (he : envH.code = env.code) (cap pb S0 S1 : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) :
    AllocOk p (accKeepK cap env) envH pb S0 S1 := by
  rw [AllocOk_iff, he]
  exact (allocOkC_heapHost (p := p) (P := P) (accHeapHost env) cap pb S0 S1 hcap1 hcap).weaken
    fun _ _ _ _ _ _ _ hr => accGrowK_keepK hr

/-- **`ReallocOk` under `accKeepK`**, for any refine host with accumulate's code, cap ≥ 2²⁷. -/
theorem reallocOk_keepK {p : ByteArray} {P : Program} [Code.HasCode p P] (env : AccEnv) (envH : RefineHost.Env)
    (he : envH.code = env.code) (cap pb S0 S1 : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) :
    ReallocOk p (accKeepK cap env) envH pb S0 S1 := by
  have h : ReallocCopyOk p (accKeepK cap env) envH pb S0 S1 := by
    unfold ReallocCopyOk; rw [he]
    exact (reallocCopyOkC_heapHost (p := p) (P := P) (accHeapHost env) cap pb S0 S1 hcap1 hcap).weaken
      fun _ _ _ _ _ _ _ hr => accGrowK_keepK hr
  exact h.toReallocOk

/-- **`info` of the service itself is an `accKeepK` step** (as `FreeStepsH.infoSelf`). -/
theorem FreeStepsH.infoSelfK (cap : Nat) (hcap : 703 ≤ cap ∧ cap < 2 ^ 64) (env : AccEnv)
    {p : ByteArray} {P : Program} {i n : Nat} {ω : Regs} {μ : Memory} {x : AccCtx} {a : ServiceAccount}
    {o z : Nat} {i'' : Nat} {ω'' : Regs} {μ'' : Memory} {x'' : AccCtx} {k : Nat}
    (hd : deblob p i = some P ∧ P.decode i = some (.oneImm .ecalli 6) ∧ P.next i = n ∧
      P.blockCost (P.blockStartOf i) ≤ stepCostCap)
    (ha : x.1.state.accounts.get? x.1.id = some a)
    (h7 : ω[7] = UInt64.ofNat 18446744073709551615) (h8 : ω[8] = UInt64.ofNat o)
    (h9 : ω[9] = UInt64.ofNat 0) (h10 : ω[10] = UInt64.ofNat z) (ho : o + z ≤ 2 ^ 32)
    (hw : ∀ b, o ≤ b → b < o + z → μ.writable b = true)
    (rest : FreeStepsH p (accKeepK cap env) n (setR7 ω (infoValue a).length)
      (μ.writeN o ((infoValue a).take (min z (infoValue a).length))) x i'' ω'' μ'' x'' k) :
    FreeStepsH p (accKeepK cap env) i ω μ x i'' ω'' μ'' x'' (k + 1) := by
  apply FreeStepsH.host_decode hd _ rest
  refine ⟨?_, rfl⟩
  have hrw : μ.rangeWritable o (min z (infoValue a).length) = true :=
    rangeWritable_of (by omega) (fun b h1 h2 => hw b h1 (by omega))
  have r7 : reg ω 7 = 2 ^ 64 - 1 := by simp [reg, Regs.get, Fin.getElem_fin, h7]
  have r8 : reg ω 8 = o := by simp [reg, Regs.get, Fin.getElem_fin, h8]; omega
  have r9 : reg ω 9 = 0 := by simp [reg, Regs.get, Fin.getElem_fin, h9]
  have r10 : reg ω 10 = z := by simp [reg, Regs.get, Fin.getElem_fin, h10]; omega
  have hc : ¬ (cap % 18446744073709551616 < 703) := by rw [Nat.mod_eq_of_lt hcap.2]; omega
  refine ⟨by unfold AccGasFreeId; decide, by decide, ?_⟩
  simp only [accHostFn, AccHost.dispatch, hostInfo, charged, writeValue, UInt64.toNat_ofNat', Constants.CgasI,
    UInt64.reduceToNat, Nat.reducePow, hc, ↓reduceIte, r7, r8, r9, r10, ha, Option.map_some, Nat.zero_min,
    Nat.sub_zero, List.drop_zero, hrw, Bool.not_true, Bool.false_eq_true]

/-- **A `log` step** (id 100) is an `accKeepK` step (as `Fmt.FreeStepsH.logAcc`). -/
theorem FreeStepsH.logKeepK (cap : Nat) (hcap : 1000 ≤ cap ∧ cap < 2 ^ 64) (env : AccEnv)
    {p : ByteArray} {P : Program} {i n : Nat} {ω : Regs} {μ : Memory} {x : AccCtx}
    {i'' : Nat} {ω'' : Regs} {μ'' : Memory} {x'' : AccCtx} {k : Nat}
    (hd : deblob p i = some P ∧ P.decode i = some (.oneImm .ecalli 100) ∧ P.next i = n ∧
      P.blockCost (P.blockStartOf i) ≤ stepCostCap)
    (rest : FreeStepsH p (accKeepK cap env) n (setR7 ω Result.WHAT) μ x i'' ω'' μ'' x'' k) :
    FreeStepsH p (accKeepK cap env) i ω μ x i'' ω'' μ'' x'' (k + 1) := by
  apply FreeStepsH.host_decode hd _ rest
  refine ⟨?_, rfl⟩
  have hc : ¬ ((cap : Int) - ((1000 : Nat) : Int) < 0) := by omega
  refine ⟨by unfold AccGasFreeId; decide, by decide, ?_⟩
  simp only [accHostFn, AccHost.dispatch, UInt64.toNat_ofNat', UInt64.reduceToNat, Nat.reducePow,
    Constants.Cgasunknown, Nat.mod_eq_of_lt hcap.2, hc, ↓reduceIte]

/-- **`accContractK` keeps what is not writable** off the heap's 48 … pb (as `accContractS_keepsRO`). -/
theorem accContractK_keepsRO (cap : Nat) (env : AccEnv) {pb : Nat} (hbd : heapBounds env.code = (48, pb)) :
    KeepsRO (accContractK cap env) 48 pb := by
  intro h ω μ x ω' μ' x' hr
  obtain ⟨-, -, he⟩ := hr
  have hs : (accHostFn env h (UInt64.ofNat cap) ω μ x).status = .cont := by rw [he]
  have hm : (accHostFn env h (UInt64.ofNat cap) ω μ x).mem = μ' := by rw [he]
  rw [← hm]
  exact accHostFn_keep env hbd h (UInt64.ofNat cap) ω μ x hs

/-- A run under a contract keeping what is not writable keeps the octets below 196608 (as
    `Acc.ro_keep`, here without its heavier imports). -/
theorem ro_keep0 {X : Type} {R : HostRel X} {p : ByteArray} {pb : Nat} (hR : KeepsRO R 48 pb)
    {i i' n : Nat} {ω ω' : Regs} {μ μ' : Memory} {x x' : X} (run : FreeStepsH p R i ω μ x i' ω' μ' x' n)
    (hro : ∀ a, a < 196608 → μ.writable a = false) :
    ∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a ∧ μ'.writable a = false := by
  intro a ha
  have k := FreeStepsH.keepRO_of hR run
  have hp := k.1 (a / pageSize) (.inl (by unfold pageSize; omega))
  refine ⟨k.2 a (by unfold two32; omega) (.inl (by unfold pageSize; omega)) (hro a ha), ?_, ?_⟩
  · unfold Memory.readable; rw [hp]
  · have := hro a ha
    unfold Memory.writable at this ⊢; rw [hp]; exact this

end Services.Bootstrap.Acc
