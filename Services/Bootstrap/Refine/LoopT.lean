import Services.Bootstrap.Refine.LoopAll
import Services.Bootstrap.Refine.LookupStep2
import Services.Bootstrap.Refine.ExitRun

/-!
# Refine's transform loop for T1c: pass-through, `Export` and eager `Lookup` steps

`loop_t` runs the transform loop (5042 … 5042) over n instructions, each passed through (`PassOkT`), exported
(`ExportOkT`) or an eager `Lookup` (`LookupOk`). Unlike `LoopAll.loop_all`, the snapshot μ0, the chunks to keep `Kp`
and the output slots' octets `B` are carried existentially from step to step (an eager `Lookup` rebases μ0 and adds
its preimage's chunk to `Kp`), together with a caller's invariant `Inv k μ0 Kp B`. The output slots are described by
their exact octets (`PInv.exact`). GP v0.8.0 Appendix B.4 (Ψ_R running bootstrap's code); `Spec.refine`'s
`is.mapM (refineInstr C)`.
-/

namespace Services.Bootstrap.Refine.LoopT

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeR
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA Services.Bootstrap.Refine.Pass
  Services.Bootstrap.Refine.PassLoop Services.Bootstrap.Refine.LoopAll Services.Bootstrap.Refine.LookupStep2

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- A weaker slot property for the slots already written: `PInv` holds for any `O'` implied by `O` below k. -/
theorem PInv.mono_O {env : RefineHost.Env} {pb S0 S1 M E n : Nat} {ce : Chunk} {capI : Nat} {μ0 : Memory}
    {Kp : Chunk → Prop} {O O' : Nat → List UInt8 → Prop} {i k : Nat} {ω : Regs} {μ : Memory} {s : State}
    (st : PInv env pb S0 S1 M E n ce capI μ0 Kp O i k ω μ s) (h : ∀ j bs, j < k → O j bs → O' j bs) :
    PInv env pb S0 S1 M E n ce capI μ0 Kp O' i k ω μ s where
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
  c8 := st.c8
  i0 := st.i0
  i8 := st.i8
  i16 := st.i16
  i24 := st.i24
  out := by
    obtain ⟨cap, ptr, a, b, c, d, e, f, g, i⟩ := st.out
    exact ⟨cap, ptr, a, b, c, d, e, f, g, fun j hj => h j _ hj (i j hj)⟩
  H := st.H
  hce := st.hce
  data := st.data
  kp := st.kp
  fr := st.fr

/-- **The written slots by their octets**: `PInv` with the slot property "the octets are `B j`", for the octets the
    slots hold. -/
theorem PInv.exact {env : RefineHost.Env} {pb S0 S1 M E n : Nat} {ce : Chunk} {capI : Nat} {μ0 : Memory}
    {Kp : Chunk → Prop} {O : Nat → List UInt8 → Prop} {i k : Nat} {ω : Regs} {μ : Memory} {s : State}
    (st : PInv env pb S0 S1 M E n ce capI μ0 Kp O i k ω μ s) :
    ∃ B : Nat → List UInt8, PInv env pb S0 S1 M E n ce capI μ0 Kp (fun j bs => bs = B j) i k ω μ s ∧
      ∀ j, j < k → O j (B j) := by
  obtain ⟨cap, ptr, a, b, c, d, e, f, g, hO⟩ := st.out
  refine ⟨fun j => μ.readN (ptr + 232 * j) 232, ?_, fun j hj => hO j hj⟩
  exact
    { h1 := st.h1, cur := st.cur, en := st.en, c128 := st.c128, c136 := st.c136, c48 := st.c48, c40 := st.c40,
      c16 := st.c16, c24 := st.c24, c32 := st.c32, c8 := st.c8, i0 := st.i0, i8 := st.i8, i16 := st.i16,
      i24 := st.i24, out := ⟨cap, ptr, a, b, c, d, e, f, g, fun j _ => rfl⟩, H := st.H, hce := st.hce,
      data := st.data, kp := st.kp, fr := st.fr }

/-- `LUSlot` read off the slot's 232 octets. -/
def LUSlotB (bs : List UInt8) (v : Option (List UInt8)) (buf : Nat) : Prop :=
  bs.take 8 = Num.encodeLE 8 9223372036854775825 ∧
  match v with
  | none => (bs.drop 8).take 8 = Num.encodeLE 8 18446744073709551615
  | some d => (bs.drop 8).take 8 = Num.encodeLE 8 d.length ∧ (bs.drop 16).take 8 = Num.encodeLE 8 buf ∧
      (bs.drop 24).take 8 = Num.encodeLE 8 d.length

theorem luslotB_of {μ : Memory} {a : Nat} {v : Option (List UInt8)} {buf : Nat} (h : LUSlot μ a v buf) :
    LUSlotB (μ.readN a 232) v buf := by
  have r := fun o l (hol : o + l ≤ 232) => Decode.Loop.readN_sub μ a 232 o l _ rfl hol
  obtain ⟨h0, h1⟩ := h
  have r0 := r 0 8 (by omega)
  simp only [Nat.add_zero, List.drop_zero] at r0
  refine ⟨by rw [← r0]; exact h0, ?_⟩
  cases v with
  | none => rw [← r 8 8 (by omega)]; exact h1
  | some d =>
    obtain ⟨e1, e2, e3⟩ := h1
    exact ⟨by rw [← r 8 8 (by omega)]; exact e1, by rw [← r 16 8 (by omega)]; exact e2,
      by rw [← r 24 8 (by omega)]; exact e3⟩

/-- **Instruction k passed through** (with the written slots `B`): `PassOk` with slot property `Q` for slot k, and the
    invariant after it for any slot octets that keep `B` below k and satisfy `Q` at k. -/
def PassOkT (μ0 : Memory) (E k : Nat) (Kp : Chunk → Prop) (B : Nat → List UInt8) (x x' : RefineCtx)
    (Inv' : Memory → (Chunk → Prop) → (Nat → List UInt8) → Prop) : Prop :=
  ∃ (Kp' : Chunk → Prop) (Q : List UInt8 → Prop),
    PassOk μ0 E k Kp Kp' (fun j bs => (j < k → bs = B j) ∧ (j = k → Q bs)) x x' ∧
    ∀ B' : Nat → List UInt8, (∀ j, j < k → B' j = B j) → Q (B' k) → Inv' μ0 Kp' B'

/-- **Instruction k exported** (with the written slots `B`): `ExportOk` with slot property `Q` for slot k. -/
def ExportOkT (env : RefineHost.Env) (μ0 : Memory) (E k : Nat) (ce : Chunk) (Kp : Chunk → Prop)
    (B : Nat → List UInt8) (x x' : RefineCtx) (Inv' : Memory → (Chunk → Prop) → (Nat → List UInt8) → Prop) : Prop :=
  ∃ (Kp' : Chunk → Prop) (Q : List UInt8 → Prop),
    ExportOk env μ0 E k ce Kp Kp' (fun j bs => (j < k → bs = B j) ∧ (j = k → Q bs)) x x' ∧
    ∀ B' : Nat → List UInt8, (∀ j, j < k → B' j = B j) → Q (B' k) → Inv' μ0 Kp' B'

/-- **Instruction k an eager `Lookup`** of the hash h in service svc (with the written slots `B`), laid out as
    `LookupStep2.lookup_step` needs; the context is unchanged; the invariant after it for any snapshot and chunks to
    keep related by `LUOwn`, slot k holding `LookedUp(lookupOf env svc h)`, a new kept chunk lying apart from the input's
    chunk and the kept ones, in the heap. -/
def LookupOk (env : RefineHost.Env) (cap0 : Nat) (μ0 : Memory) (E k : Nat) (ce : Chunk) (Kp : Chunk → Prop)
    (B : Nat → List UInt8) (x x' : RefineCtx) (Inv' : Memory → (Chunk → Prop) → (Nat → List UInt8) → Prop) : Prop :=
  ∃ (svc : Nat) (h : List UInt8),
    μ0.readN (E + 232 * k) 8 = Num.encodeLE 8 (9223372036854775807 + 8) ∧
    rdN μ0 (E + 232 * k + 44) 1 ≠ 0 ∧
    μ0.readN (E + 232 * k + 8) 4 = Num.encodeLE 4 svc ∧ svc < 4294967296 ∧
    μ0.readN (E + 232 * k + 12) 32 = h ∧
    (∀ d, LookupStep.lookupOf env svc h = some d → d.length < 9223372036854775808) ∧
    (∀ d, LookupStep.lookupOf env svc h = some d →
      Constants.CgasHconst + memGas Constants.CgasHlinear d.length ≤ cap0) ∧
    x' = x ∧
    ∀ (μ0' : Memory) (Kp' : Chunk → Prop) (B' : Nat → List UInt8) (buf : Nat),
      (∀ j, j < k → B' j = B j) → LUSlotB (B' k) (LookupStep.lookupOf env svc h) buf →
      LUOwn μ0 μ0' Kp Kp' (LookupStep.lookupOf env svc h) buf →
      (∀ c, Kp' c → ¬ Kp c → c ≠ ce ∧ (∀ a, InData c a → ¬ InData ce a ∧ ∀ d, Kp d → ¬ InData d a) ∧
        c.addr + 32 * c.size ≤ 2147483648) →
      Inv' μ0' Kp' B'

/-- **The transform loop for T1c** (5042 … 5042, or from 5054): from `PInv 0` with the written slots `B` and the
    invariant `Inv 0`, the n instructions, each passed through, exported or an eager `Lookup` (`elem`, given the
    invariant before it), reach `PInv n` at 5042 with some snapshot, chunks to keep and slots satisfying `Inv n`, the
    context `ctx n`; or an allocation fails. Named hypotheses: `ExportFmtOk`, `LookupFmtOk`, and the drop table's
    entry for index 8 (`htab`). -/
theorem loop_t {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P]
    (env : RefineHost.Env) (cap0 : Nat) (hcap1 : 134217728 ≤ cap0) (hcap0 : cap0 < 18446744073709551616)
    {pb S0 S1 : Nat} {ro : List UInt8} (fmt : ExportSeg.ExportFmtOk p cap0 env pb S0 S1 ro)
    (lfmt : LookupFmt.LookupFmtOk p cap0 env pb S0 S1 ro) (htab : (ro.drop 32).take 4 = Lookup.dropEntry8)
    {hb : Nat} {M E n capI : Nat} {ce : Chunk} (ctx : Nat → RefineCtx) (L : LayP S0 S1 M E n ce)
    (Inv : Nat → Memory → (Chunk → Prop) → (Nat → List UInt8) → Prop)
    (elem : ∀ k μ0 Kp B, k < n → Inv k μ0 Kp B →
      PassOkT μ0 E k Kp B (ctx k) (ctx (k + 1)) (Inv (k + 1)) ∨
      ExportOkT env μ0 E k ce Kp B (ctx k) (ctx (k + 1)) (Inv (k + 1)) ∨
      LookupOk env cap0 μ0 E k ce Kp B (ctx k) (ctx (k + 1)) (Inv (k + 1)))
    (i : Nat) (hi : i = 5042 ∨ 0 < n)
    (ω : Regs) (μ : Memory) (s : State) (hro : RoData.RoIs ro μ)
    (rtab : ∀ a, 65568 ≤ a → a < 65572 → μ.readable a = true)
    (μ0 : Memory) (Kp : Chunk → Prop) (B : Nat → List UInt8) (hinv : Inv 0 μ0 Kp B)
    (st : PInv env pb S0 S1 M E n ce capI μ0 Kp (fun j bs => bs = B j) i 0 ω μ s) :
    (∃ (s' : State) (ω' : Regs) (μ' : Memory) (N : Nat) (μ0' : Memory) (Kp' : Chunk → Prop)
        (B' : Nat → List UInt8),
      FreeStepsH p (refineContractK cap0 env) i ω μ (ctx 0) 5042 ω' μ' (ctx n) N ∧
      PInv env pb S0 S1 M E n ce capI μ0' Kp' (fun j bs => bs = B' j) 5042 n ω' μ' s' ∧ Inv n μ0' Kp' B') ∨
    ∃ N, ExhaustsX env cap0 pb p i ω μ (ctx 0) N := by
  obtain ⟨hS0M, hMS1, hM2, hM8⟩ := L.hM
  -- the loop's state before instruction k
  let St : Nat → Regs → Memory → RefineCtx → Prop := fun k ω μ y =>
    y = ctx k ∧ RoData.RoIs ro μ ∧ (∀ a, 65568 ≤ a → a < 65572 → μ.readable a = true) ∧
    ∃ s μ0 Kp B, Inv k μ0 Kp B ∧ PInv env pb S0 S1 M E n ce capI μ0 Kp (fun j bs => bs = B j) 5042 k ω μ s
  -- after one step: exact slots and the invariant
  have fin : ∀ k (ω : Regs) (μ : Memory) (ω' : Regs) (μ' : Memory) (s s' : State) (μ0' : Memory)
      (Kp' : Chunk → Prop) (Q : List UInt8 → Prop) (B : Nat → List UInt8) N j,
      (∀ B' : Nat → List UInt8, (∀ j, j < k → B' j = B j) → Q (B' k) → Inv (k + 1) μ0' Kp' B') →
      PInv env pb S0 S1 M E n ce capI μ0' Kp' (fun j bs => (j < k → bs = B j) ∧ (j = k → Q bs)) 5042 (k + 1) ω'
        μ' s' →
      ∀ y', FreeStepsH p (refineContractK cap0 env) j ω μ (ctx k) 5042 ω' μ' y' N → y' = ctx (k + 1) →
      RoData.RoIs ro μ → (∀ a, 65568 ≤ a → a < 65572 → μ.readable a = true) → HeapCtx env pb S0 S1 μ s →
      ∃ ω' μ' y' N, FreeStepsH p (refineContractK cap0 env) j ω μ (ctx k) 5042 ω' μ' y' N ∧ St (k + 1) ω' μ' y' := by
    intro k ω μ ω' μ' s s' μ0' Kp' Q B N j hI st' y' run hy hro hrt H
    obtain ⟨B', st'', hB⟩ := PInv.exact st'
    refine ⟨ω', μ', y', N, run, hy, RoData.RoIs.keep H run hro, fun a h1 h2 => ?_, s', μ0', Kp', B',
      hI B' (fun j hj => ((hB j (by omega)).1 hj)) ((hB k (by omega)).2 rfl), st''⟩
    obtain ⟨-, kr⟩ := ExitRun.ro_keep H run (a := 65568) (l := 4) (by omega)
    rw [kr a h1 h2]; exact hrt a h1 h2
  -- one instruction, from either entry
  have step : ∀ j k ω μ y, k < n →
      (y = ctx k ∧ RoData.RoIs ro μ ∧ (∀ a, 65568 ≤ a → a < 65572 → μ.readable a = true) ∧
        ∃ s μ0 Kp B, Inv k μ0 Kp B ∧ PInv env pb S0 S1 M E n ce capI μ0 Kp (fun j bs => bs = B j) j k ω μ s) →
      (∃ ω' μ' y' N, FreeStepsH p (refineContractK cap0 env) j ω μ y 5042 ω' μ' y' N ∧ St (k + 1) ω' μ' y') ∨
      ∃ N, ExhaustsX env cap0 pb p j ω μ y N := by
    intro j k ω μ y hk ⟨hy, hro, hrt, s, μ0, Kp, B, hI, st⟩
    subst hy
    rcases elem k μ0 Kp B hk hI with ⟨Kp', Q, ⟨t, ht, sD0, hO, hK, hx⟩, hI'⟩ | ⟨Kp', Q, hex, hI'⟩ | hlk
    · -- passed through
      have stO : PInv env pb S0 S1 M E n ce capI μ0 Kp (fun j bs => (j < k → bs = B j) ∧ (j = k → Q bs)) j k ω μ s :=
        PInv.mono_O st (fun j bs hj h => ⟨fun _ => h, fun e => absurd e (by omega)⟩)
      obtain ⟨cap, ptr, vc, -, -, -, hcapn, -⟩ := st.out
      by_cases hkc : k = cap
      · subst hkc
        rcases step_full (p := p) (P := P) (hb := hb) env cap0 hcap1 hcap0 (ctx k) ω μ μ0 s L k hk t ht sD0 hO stO
            vc with ⟨s1, ω1, μ1, run1, st1⟩ | hx'
        · exact Or.inl (fin k ω μ ω1 μ1 s s1 μ0 Kp' Q B _ j hI' (PInv.mono_kp st1 hK) _ run1 hx.symm hro hrt st.H)
        · exact Or.inr ⟨_, ExhaustsX.of hx'⟩
      · obtain ⟨ω1, μ1, run1, st1⟩ := step_room (p := p) (P := P) env (ctx k) ω μ μ0 s L k hk t ht sD0 hO stO
          (fun c hc => by
            intro h; subst h
            have h1 := congrArg Num.decodeLE (vc.symm.trans hc)
            rw [Num.decodeLE_encodeLE, Num.decodeLE_encodeLE] at h1
            have := L.hn
            omega)
        exact Or.inl (fin k ω μ ω1 μ1 s s μ0 Kp' Q B _ j hI' (PInv.mono_kp st1 hK) _ run1 hx.symm hro hrt st.H)
    · -- exported
      have stO : PInv env pb S0 S1 M E n ce capI μ0 Kp (fun j bs => (j < k → bs = B j) ∧ (j = k → Q bs)) j k ω μ s :=
        PInv.mono_O st (fun j bs hj h => ⟨fun _ => h, fun e => absurd e (by omega)⟩)
      obtain ⟨capv, ptrv, ns, co, capf, qf, lf, sD0, sv8, sv16, sv24, hcv, hnc, hp, hco, hcoD, hw0, hcap, hql, hq,
        hcs, hsd, hK', hO, hx⟩ := hex
      rcases ExportElem.export_step (p := p) (P := P) (hb := hb) env cap0 hcap1 hcap0 fmt (ctx k) ω μ μ0 s hro L k hk
          capv ptrv ns co capf qf lf sD0 sv8 sv16 sv24 hcv hnc hp hco hcoD hw0 hcap hql hq hcs hsd hK' hO stO with
        ⟨s1, ω1, μ1, N, run1, st1⟩ | hx'
      · exact Or.inl (fin k ω μ ω1 μ1 s s1 μ0 Kp' Q B _ j hI' st1 _ run1 hx.symm hro hrt st.H)
      · exact Or.inr hx'
    · -- an eager `Lookup`
      obtain ⟨svc, h, sD0, hflag, sv, hsvc, sh, hlen, hgas, hx, hI'⟩ := hlk
      let v := LookupStep.lookupOf env svc h
      have stO : PInv env pb S0 S1 M E n ce capI μ0 Kp
          (fun j bs => (j < k → bs = B j) ∧ (j = k → ∃ buf, LUSlotB bs v buf)) j k ω μ s :=
        PInv.mono_O st (fun j bs hj h => ⟨fun _ => h, fun e => absurd e (by omega)⟩)
      rcases lookup_step (p := p) (P := P) (hb := hb) env cap0 hcap1 hcap0 lfmt htab (ctx k) ω μ μ0 s hro hrt L k hk
          svc h sD0 hflag sv hsvc sh hlen hgas
          (fun μ' a buf hl => ⟨fun h => absurd h (by omega), fun _ => ⟨buf, luslotB_of hl⟩⟩) stO with
        ⟨s1, ω1, μ1, μ01, Kp1, N, ptr', run1, st1, vp1, hp1, hlu, hown, hce'⟩ | hx'
      · refine Or.inl (fin k ω μ ω1 μ1 s s1 μ01 Kp1 (fun bs => bs = μ1.readN (ptr' + 232 * k) 232) B _ j
          (fun B' hB' hk' => hI' μ01 Kp1 B' _ hB' (by rw [hk']; exact luslotB_of hlu) hown ?_) ?_ _ run1 hx.symm hro hrt
          st.H)
        · -- the adopted chunk lies apart
          intro c hc1 hc2
          have hwf := st1.H.wf
          obtain ⟨hcm, hcu, -⟩ := st1.kp c hc1
          obtain ⟨hc0, -, hcT⟩ := Decode.VecU8.chunk_in hwf hcm hcu
          have hbT := st1.H.hbT
          have hne := hce' c hc1 hc2
          refine ⟨hne, fun a ha => ⟨fun hb => ?_, fun d hd hb => ?_⟩, by omega⟩
          · have := chunk_apart hwf hcm st1.hce.1 hne
            unfold InData at ha hb; omega
          · have hd' : Kp1 d := by
              revert hown
              generalize LookupStep.lookupOf env svc h = w
              intro hown
              unfold LUOwn at hown
              cases w with
              | none => rw [hown.2]; exact hd
              | some dd =>
                rcases hown with ⟨-, -, -, e⟩ | ⟨ch, -, -, -, e, -⟩
                · rw [e]; exact hd
                · rw [e]; exact Or.inl hd
            obtain ⟨hdm, -, -⟩ := st1.kp d hd'
            have := chunk_apart hwf hcm hdm (fun e => hc2 (e ▸ hd))
            unfold InData at ha hb; omega
        · -- slot k by its octets
          obtain ⟨cap, ptr, a1, a2, a3, a4, a5, a6, a7, hO1⟩ := st1.out
          have hpp : ptr = ptr' := by
            have := congrArg Num.decodeLE (a2.symm.trans vp1)
            simp only [Num.decodeLE_encodeLE] at this; omega
          subst hpp
          exact
            { h1 := st1.h1, cur := st1.cur, en := st1.en, c128 := st1.c128, c136 := st1.c136, c48 := st1.c48,
              c40 := st1.c40, c16 := st1.c16, c24 := st1.c24, c32 := st1.c32, c8 := st1.c8, i0 := st1.i0,
              i8 := st1.i8, i16 := st1.i16, i24 := st1.i24,
              out := ⟨cap, ptr, a1, a2, a3, a4, a5, a6, a7, fun j hj =>
                ⟨fun h => (hO1 j hj).1 h, fun e => by subst e; rfl⟩⟩,
              H := st1.H, hce := st1.hce, data := st1.data, kp := st1.kp, fr := st1.fr }
      · exact Or.inr hx'
  -- the remaining instructions, from the loop head
  have rest : ∀ m k ω μ y, k + m = n → St k ω μ y →
      (∃ ω' μ' y' N, FreeStepsH p (refineContractK cap0 env) 5042 ω μ y 5042 ω' μ' y' N ∧ St n ω' μ' y') ∨
      ∃ N, ExhaustsX env cap0 pb p 5042 ω μ y N :=
    LoopG.loopE (p := p) (R := refineContractK cap0 env) 5042 n St
      (fun i ω μ y => ∃ N, ExhaustsX env cap0 pb p i ω μ y N)
      (fun run ⟨N, h⟩ => ⟨_, ExhaustsX.pre run h⟩) (fun k ω μ y hk q => step 5042 k ω μ y hk q)
  have done : ∀ ω' μ' y N, FreeStepsH p (refineContractK cap0 env) i ω μ (ctx 0) 5042 ω' μ' y N → St n ω' μ' y →
      (∃ (s' : State) (ω' : Regs) (μ' : Memory) (N : Nat) (μ0' : Memory) (Kp' : Chunk → Prop)
        (B' : Nat → List UInt8),
      FreeStepsH p (refineContractK cap0 env) i ω μ (ctx 0) 5042 ω' μ' (ctx n) N ∧
      PInv env pb S0 S1 M E n ce capI μ0' Kp' (fun j bs => bs = B' j) 5042 n ω' μ' s' ∧ Inv n μ0' Kp' B') := by
    rintro ω' μ' y N run ⟨rfl, -, -, s', μ0', Kp', B', hI, st'⟩
    exact ⟨s', ω', μ', N, μ0', Kp', B', run, st', hI⟩
  by_cases hn : n = 0
  · have hi' : i = 5042 := by omega
    subst hi'
    rcases rest 0 0 ω μ (ctx 0) (by omega) ⟨rfl, hro, rtab, s, μ0, Kp, B, hinv, st⟩ with ⟨ω', μ', y, N, run, hS⟩ | hx
    · exact Or.inl (done ω' μ' y N run hS)
    · exact Or.inr hx
  · rcases step i 0 ω μ (ctx 0) (by omega) ⟨rfl, hro, rtab, s, μ0, Kp, B, hinv, st⟩ with
      ⟨ω1, μ1, y1, N1, run1, hS1⟩ | hx
    · obtain rfl : y1 = ctx 1 := hS1.1
      rcases rest (n - 1) 1 ω1 μ1 (ctx 1) (by omega) hS1 with ⟨ω', μ', y, N, run, hS⟩ | hx
      · exact Or.inl (done ω' μ' y _ (run1.trans run) hS)
      · obtain ⟨N, hx⟩ := hx
        exact Or.inr ⟨_, ExhaustsX.pre run1 hx⟩
    · exact Or.inr hx

end Services.Bootstrap.Refine.LoopT
