import Services.Bootstrap.Acc.Final.Impl
import Services.Bootstrap.Acc.Impl.Lift
import Services.Bootstrap.Refine.Milestone

/-!
# T2: bootstrap's accumulate implements `Spec.accumulate` (`accumulate_spec`)

`docs/bootstrap-target.md`, T2: for a service whose code is bootstrap's, Ψ_A (GP v0.8.0 eq.
`accinvocation`) reports what `Spec.accumulate` does under `ASem` (the GP accumulate host functions),
for some number of steps of the spec: its state, deferred transfers, yield and provisions are
`ASem.outcome (ASem.run n (Spec.accumulate C t) …)`. Moreover that run of the spec finished, or Ψ_M ran
out of gas, or the binary reached heap exhaustion (`AccAbort`).

Proof: `acc_impl` (the run implements the spec program and halts) through the lift `psiA_of_impl`.
-/

namespace Services.Bootstrap.Acc.Final

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.CodeX
  Services.Bootstrap.CodeF Services.Bootstrap.Acc Services.Bootstrap.Fmt Services.Bootstrap.Bridge
  Services.Bootstrap.Prefix Services.Bootstrap.Acc.Handlers.InstrRep

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem infoValue_length (a : ServiceAccount) : (infoValue a).length = a.codeHash.length + 64 := by
  simp only [infoValue, Codec.fixed, List.length_append, Num.length_encodeLE]

/-- The credited state keeps every account's code hash. -/
theorem credit_codeHash (e : PartialState) (s : Nat) (inputs : List AccumulateInput) (a' : ServiceAccount)
    (h : (ASem.credit e s inputs).accounts.get? s = some a') :
    ∃ a, e.accounts.get? s = some a ∧ a'.codeHash = a.codeHash := by
  unfold ASem.credit at h
  cases he : e.accounts.get? s with
  | none => rw [he] at h; simp only at h; rw [he] at h; cases h
  | some a =>
    rw [he] at h
    simp only [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert_self, Option.some.injEq] at h
    exact ⟨a, rfl, by rw [← h]⟩

/-- **Y's memory holds `AccRO`**, for a blob with the vendored blob's read-only data. -/
theorem accRO_initial (hvend : AccVendoredFacts) (jb vb : JamBlob) (hvb : vendored = some vb)
    (hro : jb.ro = vb.ro) (hl : layoutOk jb = true) (a : ByteArray) (ha : a.size ≤ inputSize) :
    AccRO (initialMemory jb a) := by
  obtain ⟨vb', hvb', -, t1, t2, t3, t4, t5, t6⟩ := hvend
  obtain rfl : vb' = vb := Option.some.inj (hvb'.symm.trans hvb)
  have tabR : ∀ o l, o + l ≤ 11608 → (initialMemory jb a).readN (65536 + o) l = (vb'.ro.toList.drop o).take l :=
    fun o l h => by rw [Refine.Milestone.initialMemory_readN_ro jb a hl ha o l h, hro]
  have rdR : ∀ x, 65536 ≤ x → x < 77144 → (initialMemory jb a).readable x = true :=
    (startMem_initial jb a hl ha).ro
  have e1 : (initialMemory jb a).readN 66464 42 = accTmplBytes := by
    rw [show (66464 : Nat) = 65536 + 928 from rfl, tabR _ _ (by omega)]; exact t1
  have e2 : (initialMemory jb a).readN 77040 16 = [36, 10, 0, 0, 0, 0, 0, 0, 32, 10, 0, 0, 0, 0, 0, 0] := by
    rw [show (77040 : Nat) = 65536 + 11504 from rfl, tabR _ _ (by omega)]; exact t2
  have e3 : (initialMemory jb a).readN 65956 14 = [116, 114, 97, 110, 115, 102, 101, 114, 45, 99, 111, 117, 110, 116] := by
    rw [show (65956 : Nat) = 65536 + 420 from rfl, tabR _ _ (by omega)]; exact t3
  have e4 : (initialMemory jb a).readN 69056 20 =
      [178, 250, 254, 255, 180, 250, 254, 255, 176, 250, 254, 255, 182, 250, 254, 255, 184, 250, 254, 255] := by
    rw [show (69056 : Nat) = 65536 + 3520 from rfl, tabR _ _ (by omega)]; exact t4
  have e5 : (initialMemory jb a).readN 68680 24 = [1, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 35, 0, 0, 0, 0, 0, 0, 0] := by
    rw [show (68680 : Nat) = 65536 + 3144 from rfl, tabR _ _ (by omega)]; exact t5
  have e6 : (initialMemory jb a).readN 65736 100 = Handlers.jumpTab := by
    rw [show (65736 : Nat) = 65536 + 200 from rfl, tabR _ _ (by omega)]; exact t6
  have sub : ∀ (o n k m : Nat) (l : List UInt8), (initialMemory jb a).readN o n = l → k + m ≤ n →
      (initialMemory jb a).readN (o + k) m = (l.drop k).take m := fun o n k m l h hk => by
    rw [← h]
    apply List.ext_getElem
    · simp [Memory.length_readN]; omega
    · intro j h1 h2
      simp only [Memory.length_readN] at h1
      simp [Memory.readN, List.getElem_map, List.getElem_range, Nat.add_assoc]
  refine ⟨e1, ⟨?_, ?_, fun x h1 h2 => rdR x h1 h2⟩, ⟨?_, fun x h1 h2 => rdR x (by omega) (by omega), ?_, ?_,
    fun x h1 h2 => rdR x (by omega) (by omega)⟩, ⟨⟨1, ?_, by decide, by decide⟩, ⟨5, ?_, by decide, by decide⟩,
    ⟨35, ?_, by decide, by decide⟩, fun x h1 h2 => rdR x (by omega) (by omega), e6,
    fun x h1 h2 => rdR x (by omega) (by omega)⟩⟩
  · unfold rdN; rw [show (77040 : Nat) = 77040 + 0 from rfl, sub _ _ 0 8 _ e2 (by omega)]; rfl
  · unfold rdN; rw [show (77048 : Nat) = 77040 + 8 from rfl, sub _ _ 8 8 _ e2 (by omega)]; rfl
  · rw [e3]; decide +kernel
  · unfold rdN; rw [show (69072 : Nat) = 69056 + 16 from rfl, sub _ _ 16 4 _ e4 (by omega)]; rfl
  · unfold rdN; rw [show (69056 : Nat) = 69056 + 0 from rfl, sub _ _ 0 4 _ e4 (by omega)]; rfl
  · rw [show (68680 : Nat) = 68680 + 0 from rfl, sub _ _ 0 8 _ e5 (by omega)]; rfl
  · rw [show (68688 : Nat) = 68680 + 8 from rfl, sub _ _ 8 8 _ e5 (by omega)]; rfl
  · rw [show (68696 : Nat) = 68680 + 16 from rfl, sub _ _ 16 8 _ e5 (by omega)]; rfl

/-- **T2: bootstrap's accumulate implements `Spec.accumulate`** (`docs/bootstrap-target.md`, T2; GP
    v0.8.0 eq. `accinvocation`). Let s be a service whose code (in the state **e**′ with the incoming
    transfers credited) is bootstrap's (`IsBootstrapCode`), with timeslot t and service id below 2³², and
    at most 89 accumulation inputs, each within `InputSized`. Then for some n, Ψ_A's state, deferred
    transfers, yield and provisions are those of `ASem.run n (Spec.accumulate C t)` from (x₀, x₀),
    x₀ = I(**e**′, s), under the GP accumulate host functions; and that run of the spec finished (`done`
    or `panicked`), or Ψ_M ran out of gas (∞), or a run of the binary from instruction 5 reached heap
    exhaustion (`AccAbort`: a failed allocation or an allocation-failure trap; Adam's standing decision).

    **Named hypotheses** (each listed in `docs/whats-proven.md`):
    - `AccVendoredFacts`: the read-only slices accumulate reads, in the vendored blob (step 10);
    - `AccHyps B C`, for bootstrap's code: `AccLogFail` (the first log line's failure tail),
      `InputsGlob` (the inputs decode keeps the statics), `Utf8Call`, `LogFmt`, `KeyFmt`, `ItemLogFmt`
      (formatting and log sites, frame-only), `OutDecH` (R3, the output decode), `InstrLogH`, `ResultLogH`
      (G4), `HandlerH` (R6, every instruction's handler implements `onInstr`), `PushH`, `ExtendH`,
      `OkEncH` (R8/R9, the results writer), `DropInstrsH` (the instructions' drop);
    - `InfoFits e s`: the service's code hash is shorter than 2⁶⁴ − 73 octets;
    - `ValuesFit` (decided 2026-11-15): storage values, preimages and encoded inputs shorter than 2⁶³;
    - G3 (temporary, decided): at most 89 inputs, each `InputSized` (hashes of 32 octets, work outputs
      and auth traces of at most 16384 octets).
    The constants: maxRecent = 2·𝖢·𝖨 for the full parameters (𝖢 = 341, 𝖨 = 16). -/
theorem accumulate_spec (B : InstrRep) (C : Spec.Consts) (hmax : C.maxRecent = 2 * 341 * 16)
    (hvend : AccVendoredFacts) (hyps : AccHyps B C)
    (η : List UInt8) (e : PartialState) (t s g : Nat) (inputs : List AccumulateInput)
    (code : ByteArray) (hcode : ASem.codeOf (ASem.credit e s inputs) s = some code)
    (hboot : IsBootstrapCode code) (ht : t < 4294967296) (hs : s < 4294967296)
    (hn : inputs.length ≤ 89) (hsz : ∀ i ∈ inputs, InputSized i)
    (hfit : ValuesFit (ASem.accEnv η t inputs code) (initImplications (ASem.credit e s inputs) s t η))
    (hinfo : InfoFits e s) :
    let o := psiA Params.full η e t s g inputs
    let x₀ := initImplications (ASem.credit e s inputs) s t η
    let env := ASem.accEnv η t inputs code
    let args : ByteArray := ⟨(Codec.nat t ++ Codec.nat s ++ Codec.nat inputs.length).toArray⟩
    ∃ n, (o.state, o.xfers, o.yield, o.provisions) = ASem.outcome (ASem.run n (Spec.accumulate C t) env (x₀, x₀)) ∧
      ((ASem.run n (Spec.accumulate C t) env (x₀, x₀)).1 ≠ .stopped ∨
        (psiM code 5 (UInt64.ofNat g) args (accHostFn env) (x₀, x₀)).2.1 = .oog ∨
        ∃ (p : ByteArray) (ω : Regs) (μ : Memory) (f : Stream) (s' : St Stream),
          standardInit code args = some (p, ω, μ) ∧
          Reaches p (accContractS env) ⟨5, ω, μ, (x₀, x₀), f⟩ s' ∧ AccAbort s') := by
  intro o x₀ env args
  obtain ⟨hsize, jb, vb, hjb, hvb, hro, hrw, hhp, hss, hheap, hcc, hccX, hccA, hccF⟩ := hboot
  have hvend' := hvend
  obtain ⟨vb', hvb', hlay', -⟩ := hvend'
  have hvv : vb' = vb := Option.some.inj (hvb'.symm.trans hvb)
  subst hvv
  have hlay : layoutOk jb = true := by unfold layoutOk; rw [hro, hrw, hhp, hss]; exact hlay'
  obtain ⟨P, hP⟩ := checkCode_sound hcc
  haveI i1 : HasCode jb.code P := ⟨hP⟩
  haveI i2 : HasCodeX jb.code P := HasCodeX.of hP hccX
  haveI i3 : HasCodeA jb.code P := HasCodeA.of hP hccA
  haveI i4 : HasCodeF jb.code P := HasCodeF.of hP hccF
  -- the arguments
  have hTl := encodeNat_len_le5 t ht
  have hSl := encodeNat_len_le5 s hs
  have hNl := encodeNat_len_le5 inputs.length (by omega)
  have hlist : args.toList = Blob.encodeNat t ++ Blob.encodeNat s ++ Blob.encodeNat inputs.length := by
    rw [ByteArray.toList_eq_data]
    simp [args, Codec.nat]
  have hasize : args.size = (Blob.encodeNat t).length + (Blob.encodeNat s).length +
      (Blob.encodeNat inputs.length).length := by
    rw [← ByteArray.length_toList', hlist]; simp only [List.length_append]
  have ha : args.size ≤ inputSize := by rw [hasize]; simp only [inputSize]; omega
  have hSM := startMem_initial jb args hlay ha
  have hZ := startMemZ_initial jb args hlay ha
  have hlay2 := hlay
  simp only [layoutOk, Bool.and_eq_true, beq_iff_eq] at hlay2
  obtain ⟨⟨⟨⟨⟨hros, hrws⟩, hheapP⟩, hstack⟩, _⟩, _⟩ := hlay2
  have hY0 : standardInit code args = some (jb.code, initialRegs args, initialMemory jb args) := by
    have hfit' : ¬(5 * zoneSize + roundZone jb.ro.size + roundZone (jb.rw.size + jb.heapPages * pageSize) +
        roundZone jb.stackSize + inputSize > 2 ^ 32) := by
      rw [hros, hrws, hheapP, hstack]; decide
    unfold standardInit validJamBlob?
    rw [ite_eq_right (by omega), hjb, Option.bind_some, ite_eq_right hfit']
    rfl
  have hrs : rwStart jb = 196608 := by simp [rwStart, hros, roundZone, zoneSize]
  have hmem := PVM.initialMemory_readN_args jb args (by simp [roStart, zoneSize, hros, two32])
    (by simp [hrs, hrws, two32]) (by simp [argStart, zoneSize, inputSize, two32] at ha ⊢; omega)
  rw [hlist] at hmem
  -- the service's own account
  obtain ⟨a', ha'⟩ : ∃ a', (ASem.credit e s inputs).accounts.get? s = some a' := by
    unfold ASem.codeOf at hcode
    cases h : (ASem.credit e s inputs).accounts.get? s with
    | none => rw [h] at hcode; cases hcode
    | some a' => exact ⟨a', rfl⟩
  obtain ⟨a, hea, hch⟩ := credit_codeHash e s inputs a' ha'
  have hlen : (infoValue a').length < 18446744073709551607 := by
    rw [infoValue_length, hch]; have := hinfo a hea; omega
  -- the hypotheses for this code
  have hH : AccHypsAt B C t jb.code P env :=
    hyps code jb ⟨hsize, jb, vb', hjb, hvb, hro, hrw, hhp, hss, hheap, hcc, hccX, hccA, hccF⟩ hjb P i1 i2 i3 i4
      env t rfl rfl
  have himpl : ∀ f : Stream, Impl jb.code (accContractS env) env AccAbort (Spec.accumulate C t)
      (Halts jb.code (accContractS env)) ⟨5, initialRegs args, initialMemory jb args, (x₀, x₀), f⟩ := by
    intro f
    rw [initRegs_eq]
    exact acc_impl (p := jb.code) (P := P) B C hmax env hheap rfl hH (initialMemory jb args) hSM hZ
      (initialMemory_stack_zero jb args hlay ha) (accRO_initial hvend jb vb' hvb hro hlay args ha)
      s inputs.length args.size ht hs rfl hasize.symm
      (by show _ = Blob.encodeNat t ++ Blob.encodeNat s ++ Blob.encodeNat inputs.length
          simpa [argStart, zoneSize, inputSize] using hmem)
      (fun j h1 h2 => PVM.initialMemory_readable_args jb args j (by simp [argStart, zoneSize, inputSize]; omega)
        (by simp [argStart, zoneSize, inputSize] at h2 ⊢; omega))
      x₀ a' ha' hlen hn hsz hfit f
  obtain ⟨n, h1, h2⟩ := psiA_of_impl η e t s g inputs code hcode (by omega) hY0 (Spec.accumulate C t) AccAbort himpl
  refine ⟨n, h1, ?_⟩
  rcases h2 with h2 | h2 | ⟨f, s', h3, h4⟩
  · exact .inl h2
  · exact .inr (.inl h2)
  · exact .inr (.inr ⟨jb.code, initialRegs args, initialMemory jb args, f, s', hY0, h3, h4⟩)

end Services.Bootstrap.Acc.Final
