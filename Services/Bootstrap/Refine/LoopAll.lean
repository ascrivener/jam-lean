import Services.Bootstrap.Refine.ExportElem

/-!
# Refine's transform loop over every instruction kind of the milestone

`loop_all` runs the transform loop (5042 … 5042) over n instructions, each passed through (`PassOk`: an index
of `Pass.PassK`, its slot the instruction's own octets) or exported (`ExportOk`: an `ExportSegs`, its slot
`Exported(ns)`, the host context its segments exported). The chunks to keep `Kp k` and the host context
`ctx k` are given per instruction. GP v0.8.0 Appendix B.4 (Ψ_R running bootstrap's code);
`Spec.refine`'s `is.mapM (refineInstr C)`.
-/

namespace Services.Bootstrap.Refine.LoopAll

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeR
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA Services.Bootstrap.Refine.Pass
  Services.Bootstrap.Refine.PassLoop

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- Fewer chunks to keep: `PInv` holds for any `Kp'` within `Kp`. -/
theorem PInv.mono_kp {env : RefineHost.Env} {pb S0 S1 M E n : Nat} {ce : Chunk} {capI : Nat} {μ0 : Memory}
    {Kp Kp' : Chunk → Prop} {O : Nat → List UInt8 → Prop} {k : Nat} {ω : Regs} {μ : Memory} {s : State}
    (st : PInv env pb S0 S1 M E n ce capI μ0 Kp O k ω μ s) (h : ∀ d, Kp' d → Kp d) :
    PInv env pb S0 S1 M E n ce capI μ0 Kp' O k ω μ s where
  h1 := st.h1
  cur := st.cur
  en := st.en
  c128 := st.c128
  c136 := st.c136
  c48 := st.c48
  c40 := st.c40
  c16 := st.c16
  c24 := st.c24
  c32 := st.c32
  i0 := st.i0
  i8 := st.i8
  i16 := st.i16
  i24 := st.i24
  out := by
    obtain ⟨cap, ptr, a, b, c, d, e, f, g, i⟩ := st.out
    exact ⟨cap, ptr, a, b, c, d, e, f,
      g.imp id (fun ⟨c, hc, h1, h2, h3, h4, h5⟩ => ⟨c, hc, h1, h2, h3, h4, fun hk => h5 (h c hk)⟩), i⟩
  H := st.H
  hce := st.hce
  data := st.data
  kp := fun d hd => st.kp d (h d hd)
  fr := st.fr

/-- **Instruction k passed through**: an index of `PassK` (its tag word in μ0), its output slot `O k`
    satisfied by its own octets; the chunks to keep may shrink and the context is unchanged. -/
def PassOk (μ0 : Memory) (E k : Nat) (Kp Kp' : Chunk → Prop) (O : Nat → List UInt8 → Prop) (x x' : RefineCtx) :
    Prop :=
  ∃ t, PassK t (rdN μ0 (E + 232 * k + 44) 1) ∧
    μ0.readN (E + 232 * k) 8 = Num.encodeLE 8 (9223372036854775807 + t) ∧ O k (μ0.readN (E + 232 * k) 232) ∧
    (∀ d, Kp' d → Kp d) ∧ x' = x

/-- **Instruction k exported**: an `ExportSegs` laid out as `ExportElem.export_step` needs, its output slot
    `O k` satisfied by `Exported(ns)`, the context afterwards `ExportSeg.expUpTo env μ0 ptrv x ns`. -/
def ExportOk (env : RefineHost.Env) (μ0 : Memory) (E k : Nat) (ce : Chunk) (Kp Kp' : Chunk → Prop)
    (O : Nat → List UInt8 → Prop) (x x' : RefineCtx) : Prop :=
  ∃ (capv ptrv ns : Nat) (co : Chunk) (capf qf lf : Nat → Nat),
    μ0.readN (E + 232 * k) 8 = Num.encodeLE 8 (9223372036854775807 + 10) ∧
    μ0.readN (E + 232 * k + 8) 8 = Num.encodeLE 8 capv ∧
    μ0.readN (E + 232 * k + 16) 8 = Num.encodeLE 8 ptrv ∧
    μ0.readN (E + 232 * k + 24) 8 = Num.encodeLE 8 ns ∧
    24 * capv < 18446744073709551616 ∧ ns ≤ capv ∧ ptrv + 24 * ns + 8 ≤ 2147483648 ∧
    (capv ≠ 0 → Kp co ∧ co ≠ ce ∧ co.addr + 32 = ptrv) ∧
    (∀ a, ptrv ≤ a → a < ptrv + 24 * ns → InData co a) ∧
    (∀ i, i < ns → μ0.readN (ptrv + 24 * i) 8 = Num.encodeLE 8 (capf i) ∧
      μ0.readN (ptrv + 24 * i + 8) 8 = Num.encodeLE 8 (qf i) ∧ μ0.readN (ptrv + 24 * i + 16) 8 = Num.encodeLE 8 (lf i)) ∧
    (∀ i, i < ns → capf i < 18446744073709551616) ∧ (∀ i, i < ns → qf i + lf i ≤ 2147483648) ∧
    (∀ i, i < ns → capf i ≠ 0 → qf i ≠ co.addr + 32 ∧ ∀ j, j < ns → j ≠ i → capf j ≠ 0 → qf j ≠ qf i) ∧
    (∀ i, i < ns → capf i ≠ 0 → ∃ c, Kp c ∧ c ≠ ce ∧ c.addr + 32 = qf i) ∧
    (∀ i, i < ns → ∀ a, qf i ≤ a → a < qf i + lf i → ∃ d, Kp d ∧ InData d a) ∧
    env.exportOffset + x.2.length + ns < 18446744073709551615 ∧
    (∀ d, Kp' d → Kp d ∧ (capv ≠ 0 → d ≠ co) ∧ ∀ i, i < ns → capf i ≠ 0 → d.addr + 32 ≠ qf i) ∧
    (∀ (μ' : Memory) (a : Nat), μ'.readN a 8 = Num.encodeLE 8 (9223372036854775807 + 20) →
      μ'.readN (a + 8) 8 = Num.encodeLE 8 ns → O k (μ'.readN a 232)) ∧
    x' = ExportSeg.expUpTo env μ0 ptrv x ns

/-- **The transform loop** (5042 … 5042): from `PInv 0` with the context `ctx 0`, the n instructions, each
    passed through or exported, reach `PInv n` (the chunks to keep `Kp n`) with the context `ctx n`; or an
    allocation fails. -/
theorem loop_all {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P]
    (env : RefineHost.Env) (cap0 : Nat) (hcap1 : 134217728 ≤ cap0) (hcap0 : cap0 < 18446744073709551616)
    {pb S0 S1 : Nat} (fmt : ExportSeg.ExportFmtOk p cap0 env pb S0 S1) (μ0 : Memory) {hb : Nat}
    {M E n capI : Nat} {ce : Chunk} (Kp : Nat → Chunk → Prop) (O : Nat → List UInt8 → Prop)
    (ctx : Nat → RefineCtx) (L : LayP S0 S1 M E n ce)
    (elem : ∀ k, k < n → PassOk μ0 E k (Kp k) (Kp (k + 1)) O (ctx k) (ctx (k + 1)) ∨
      ExportOk env μ0 E k ce (Kp k) (Kp (k + 1)) O (ctx k) (ctx (k + 1)))
    (ω : Regs) (μ : Memory) (s : State) (st : PInv env pb S0 S1 M E n ce capI μ0 (Kp 0) O 0 ω μ s) :
    (∃ (s' : State) (ω' : Regs) (μ' : Memory) (N : Nat),
      FreeStepsH p (refineContractK cap0 env) 5042 ω μ (ctx 0) 5042 ω' μ' (ctx n) N ∧
      PInv env pb S0 S1 M E n ce capI μ0 (Kp n) O n ω' μ' s') ∨
    ∃ N, ExhaustsX env cap0 pb p 5042 ω μ (ctx 0) N := by
  have step : ∀ k ω μ y, k < n → (y = ctx k ∧ ∃ s, PInv env pb S0 S1 M E n ce capI μ0 (Kp k) O k ω μ s) →
      (∃ ω' μ' y' N, FreeStepsH p (refineContractK cap0 env) 5042 ω μ y 5042 ω' μ' y' N ∧
        (y' = ctx (k + 1) ∧ ∃ s, PInv env pb S0 S1 M E n ce capI μ0 (Kp (k + 1)) O (k + 1) ω' μ' s)) ∨
      ∃ N, ExhaustsX env cap0 pb p 5042 ω μ y N := by
    intro k ω μ y hk ⟨hy, s, st⟩
    subst hy
    rcases elem k hk with ⟨t, ht, sD0, hO, hK, hx⟩ | hex
    · obtain ⟨cap, ptr, vc, -, -, -, hcapn, -⟩ := st.out
      by_cases hkc : k = cap
      · subst hkc
        rcases step_full (p := p) (P := P) (hb := hb) env cap0 hcap1 hcap0 (ctx k) ω μ μ0 s L k hk t ht sD0 hO st
            vc with ⟨s1, ω1, μ1, run1, st1⟩ | hx'
        · exact Or.inl ⟨ω1, μ1, ctx k, _, run1, hx.symm, s1, PInv.mono_kp st1 hK⟩
        · exact Or.inr ⟨_, ExhaustsX.of hx'⟩
      · obtain ⟨ω1, μ1, run1, st1⟩ := step_room (p := p) (P := P) env (ctx k) ω μ μ0 s L k hk t ht sD0 hO st
          (fun c hc => by
            intro h; subst h
            have h1 := congrArg Num.decodeLE (vc.symm.trans hc)
            rw [Num.decodeLE_encodeLE, Num.decodeLE_encodeLE] at h1
            have := L.hn
            omega)
        exact Or.inl ⟨ω1, μ1, ctx k, _, run1, hx.symm, s, PInv.mono_kp st1 hK⟩
    · obtain ⟨capv, ptrv, ns, co, capf, qf, lf, sD0, sv8, sv16, sv24, hcv, hnc, hp, hco, hcoD, hw0, hcap, hql, hq,
        hcs, hsd, hoff, hK', hO, hx⟩ := hex
      rcases ExportElem.export_step (p := p) (P := P) (hb := hb) env cap0 hcap1 hcap0 fmt (ctx k) ω μ μ0 s L k hk
          capv ptrv ns co capf qf lf sD0 sv8 sv16 sv24 hcv hnc hp hco hcoD hw0 hcap hql hq hcs hsd hoff hK' hO st with
        ⟨s1, ω1, μ1, N, run1, st1⟩ | hx'
      · exact Or.inl ⟨ω1, μ1, _, N, run1, hx.symm, s1, st1⟩
      · exact Or.inr hx'
  rcases LoopG.loopE (p := p) (R := refineContractK cap0 env) 5042 n
      (fun k ω μ y => y = ctx k ∧ ∃ s, PInv env pb S0 S1 M E n ce capI μ0 (Kp k) O k ω μ s)
      (fun i ω μ y => ∃ N, ExhaustsX env cap0 pb p i ω μ y N)
      (fun run ⟨N, h⟩ => ⟨_, ExhaustsX.pre run h⟩) step n 0 ω μ (ctx 0) (by omega) ⟨rfl, s, st⟩ with
    ⟨ω', μ', y, N, run, rfl, s', st'⟩ | hx
  · exact Or.inl ⟨s', ω', μ', N, run, st'⟩
  · exact Or.inr hx

end Services.Bootstrap.Refine.LoopAll
