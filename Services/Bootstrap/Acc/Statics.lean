import Services.Bootstrap.AccBParams
import Services.Bootstrap.Acc.Start

/-!
# The accumulate prologue stores the chain parameters C and I

The SDK's prologue fetches the protocol parameters (`fetch`, kind 0) and checks them; its `apply()`
(55971 … 56337, called from 44466) then copies them into the read-write statics 196616 … 196791. Two
of them are read later by bootstrap's accumulate code (Handlers A's row 8, the recent-work-item ring
of size 2·𝖢·𝖨, `Spec.Consts.maxRecent`):

- 𝖢 = `coreCount`, the u16 at 196616 (`store_u16` at 56279, after the check 2 ≤ 𝖢 ≤ 341);
- 𝖨 = `maxPackageItems`, the u64 at 196696 (`store_u64` at 56205, of a u16 field).

`AccBParams` (38875 → 6429, `env.params = Params.full`) runs through `apply()` but does not keep these
octets at its last cut. `run` here re-checks its last two pieces (`seg160s`, `seg176s`, by the symbolic
executor) with cuts that also carry the two cells, and so states them at 6429 along with
`AccBParams.St177`. For `Params.full`, 𝖢 = 341 and 𝖨 = 16 (GP v0.8.0, appendix I.4.4: `Ccorecount`,
`Cmaxpackageitems`); `full_coreCount` / `full_maxPackageItems` state that these are the model's values.
The code facts of 56205 and 56279 are in `Code` (refine runs the same prologue), so no new tier is needed.
-/

namespace Services.Bootstrap.Acc.Statics

open PVM JAM Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeA Services.Bootstrap.Acc Services.Bootstrap.AccBParams Services.Bootstrap.AccBParams.E128 PVM.SymExec

set_option maxRecDepth 100000

theorem full_coreCount : Params.full.coreCount = 341 := rfl
theorem full_maxPackageItems : Params.full.maxPackageItems = 16 := rfl

/-- The two parameter cells: 𝖢 (2 octets at 196616) and 𝖨 (8 octets at 196696). -/
def statCells : List (Aff × Nat × SVal) :=
  [(⟨none, 196616⟩, 2, .const 341), (⟨none, 196696⟩, 8, .const 16)]

/-- Cut 176 (pc 44484, after `apply()` returned), with the parameter cells. -/
def cut176s : Cut := { cut176 with cells := cut176.cells ++ statCells }

/-- Cut 177 (pc 6429), with the parameter cells. -/
def cut177s : Cut := { cut177 with cells := cut177.cells ++ statCells }

/-- `S160` … `S175` (250 steps, pc 42882 to pc 44484, through `apply()`), with the cells at the end. -/
theorem seg160s {X : Type} {R : HostRel X} {p : ByteArray} {P : Program} [Services.Bootstrap.Code.HasCode p P] [Services.Bootstrap.CodeX.HasCodeX p P] [Services.Bootstrap.CodeA.HasCodeA p P] (LA : Nat) (hB : BHold [LA] ub) (hLB : LBHold [LA] lb)
    (μ₀ : Memory) (ω : Regs) (μ : Memory) (h : cut160.Holds [LA] μ₀ ω μ) (x : X) :
    ∃ ω' μ', FreeStepsH p R 42882 ω μ x 44484 ω' μ' x 250 ∧ cut176s.Holds [LA] μ₀ ω' μ' :=
  seg_sound (lb := lb) (sep := []) (by decide +kernel) (Services.Bootstrap.SymExec.hypAll (p := p) (P := P)) hB hLB
    (fun _ _ => trivial) h x

/-- `S176` (10 steps, pc 44484 to pc 6429), keeping the cells. -/
theorem seg176s {X : Type} {R : HostRel X} {p : ByteArray} {P : Program} [Services.Bootstrap.Code.HasCode p P] [Services.Bootstrap.CodeX.HasCodeX p P] [Services.Bootstrap.CodeA.HasCodeA p P] (LA : Nat) (hB : BHold [LA] ub) (hLB : LBHold [LA] lb)
    (μ₀ : Memory) (ω : Regs) (μ : Memory) (h : cut176s.Holds [LA] μ₀ ω μ) (x : X) :
    ∃ ω' μ', FreeStepsH p R 44484 ω μ x 6429 ω' μ' x 10 ∧ cut177s.Holds [LA] μ₀ ω' μ' :=
  seg_sound (lb := lb) (sep := []) (by decide +kernel) (Services.Bootstrap.SymExec.hypAll (p := p) (P := P)) hB hLB
    (fun _ _ => trivial) h x

/-- **Cut 128 to cut 177** (`AccBParams.E128.run`), also stating 𝖢 and 𝖨 at 196616 / 196696. -/
theorem run128 (p : ByteArray) (P : Program) [HasCode p P] [HasCodeX p P] [HasCodeA p P] (env : AccEnv) (ω : Regs) (μ : Memory)
    (x : AccCtx) (LA : Nat) (hLA : 3 ≤ LA ∧ LA ≤ 15) (ω₀ : Regs) (μ₀ : Memory) (h : St128 LA ω₀ μ₀ ω μ) :
    ∃ ω' μ', FreeStepsH p (accContract env) 68846 ω μ x 6429 ω' μ' x 772 ∧ St177 LA ω₀ μ₀ ω' μ' ∧
      μ'.readN 196616 2 = Num.encodeLE 2 341 ∧ μ'.readN 196696 8 = Num.encodeLE 8 16 := by
  have c128 : cut128.Holds [LA] μ ω μ :=
    ⟨⟨h.hreg1, h.hreg4, h.hreg8, h.hreg9, h.hreg10, h.hreg11, trivial⟩,
      ⟨(cell_of_list h.hm_196636_4 rfl), (cell_of_list h.hm_206512_8 rfl), (cell_of_list h.hm_206520_8 rfl), (cell_of_list h.hm_206824_8 rfl), (cell_of_list h.hm_206832_8 rfl), (cell_of_list h.hm_206848_4 rfl), (cell_of_list h.hm_206880_8 rfl), (cell_of_list h.hm_207025_7 rfl), (cell_of_list h.hm_207032_2 rfl), (cell_of_list h.hm_207044_4 rfl), (cell_of_list h.hm_207048_4 rfl), (cell_of_list h.hm_4278056464_8 rfl), (cell_of_list h.hm_4278056472_8 rfl), (cell_of_list h.hm_4278056480_8 rfl), (cell_of_list h.hm_4278056488_8 rfl), (cell_of_list h.hm_4278056496_8 rfl), (cell_of_list h.hm_4278056504_8 rfl), (cell_of_list h.hm_4278056512_8 rfl), (cell_of_list h.hm_4278056520_8 rfl), (cell_of_list h.hm_4278056532_2 rfl), (cell_of_list h.hm_4278056536_8 rfl), (cell_of_list h.hm_4278056560_8 rfl), (cell_of_list h.hm_4278056568_8 rfl), (cell_of_list h.hm_4278056576_8 rfl), (cell_of_list h.hm_4278056584_8 rfl), (cell_of_list h.hm_4278056592_8 rfl), (cell_of_list h.hm_4278056600_8 rfl), (cell_of_list h.hm_4278056608_8 rfl), (cell_of_list h.hm_4278056616_8 rfl), (cell_of_list h.hm_4278056624_8 rfl), (cell_of_list h.hm_4278056632_8 rfl), (cell_of_list h.hm_4278056640_8 rfl), (cell_of_list h.hm_4278056648_8 rfl), (cell_of_list h.hm_4278056656_8 rfl), (cell_of_list h.hm_4278056664_8 rfl), (cell_of_list h.hm_4278056672_8 rfl), (cell_of_list h.hm_4278056680_8 rfl), (cell_of_list h.hm_4278056688_8 rfl), (cell_of_list h.hm_4278056696_8 rfl), (cell_of_list h.hm_4278056704_8 rfl), (cell_of_list h.hm_4278056712_8 rfl), (cell_of_list h.hm_4278056720_8 rfl), (cell_of_list h.hm_4278056728_8 rfl), (cell_of_list h.hm_4278056736_8 rfl), (cell_of_list h.hm_4278056744_8 rfl), (cell_of_list h.hm_4278056752_8 rfl), (cell_of_list h.hm_4278056760_8 rfl), (cell_of_list h.hm_4278056776_8 rfl), (cell_of_list h.hm_4278056784_8 rfl), (cell_of_list h.hm_4278056792_8 rfl), (cell_of_list h.hm_4278057106_6 rfl), (cell_of_list h.hm_4278057128_8 rfl), (cell_of_list h.hm_4278057144_8 rfl), h.hbn_4278057136_8, trivial⟩,
      ⟨rng_rd (lo := 196636) (hi := 196640) h.hrd_196636_196640, rng_rd (lo := 206512) (hi := 206528) h.hrd_206512_206528, rng_rd (lo := 206824) (hi := 206840) h.hrd_206824_206840, rng_rd (lo := 206848) (hi := 206852) h.hrd_206848_206852, rng_rd (lo := 206880) (hi := 206888) h.hrd_206880_206888, rng_rd (lo := 207025) (hi := 207034) h.hrd_207025_207034, rng_rd (lo := 207044) (hi := 207052) h.hrd_207044_207052, rng_rd (lo := 4278056464) (hi := 4278056528) h.hrd_4278056464_4278056528, rng_rd (lo := 4278056532) (hi := 4278056768) h.hrd_4278056532_4278056768, rng_rd (lo := 4278056776) (hi := 4278056928) h.hrd_4278056776_4278056928, rng_rd (lo := 4278056976) (hi := 4278057152) h.hrd_4278056976_4278057152, trivial⟩,
      ⟨rng_wr (lo := 196608) (hi := 196618) h.hw_196608_196618, rng_wr (lo := 196620) (hi := 196668) h.hw_196620_196668, rng_wr (lo := 196672) (hi := 196792) h.hw_196672_196792, rng_wr (lo := 206512) (hi := 206520) h.hw_206512_206520, rng_wr (lo := 206824) (hi := 206840) h.hw_206824_206840, rng_wr (lo := 206848) (hi := 206852) h.hw_206848_206852, rng_wr (lo := 206880) (hi := 206896) h.hw_206880_206896, rng_wr (lo := 4278056464) (hi := 4278056528) h.hw_4278056464_4278056528, rng_wr (lo := 4278056532) (hi := 4278056560) h.hw_4278056532_4278056560, rng_wr (lo := 4278056776) (hi := 4278056928) h.hw_4278056776_4278056928, rng_wr (lo := 4278056976) (hi := 4278057106) h.hw_4278056976_4278057106, rng_wr (lo := 4278057112) (hi := 4278057128) h.hw_4278057112_4278057128, rng_wr (lo := 4278058720) (hi := 4278058736) h.hw_4278058720_4278058736, trivial⟩,
      fun _ _ _ => rfl, rfl⟩
  obtain ⟨ω144, μ144, run144, c144⟩ := E128.seg128 (R := accContract env) (p := p) (P := P) LA ⟨(Nat.lt_succ_of_le hLA.2), trivial⟩ ⟨hLA.1, trivial⟩ μ ω μ c128 x
  obtain ⟨ω160, μ160, run160, c160⟩ := E128.seg144 (R := accContract env) (p := p) (P := P) LA ⟨(Nat.lt_succ_of_le hLA.2), trivial⟩ ⟨hLA.1, trivial⟩ μ ω144 μ144 c144 x
  obtain ⟨ω176, μ176, run176, c176⟩ := seg160s (R := accContract env) (p := p) (P := P) LA ⟨(Nat.lt_succ_of_le hLA.2), trivial⟩ ⟨hLA.1, trivial⟩ μ ω160 μ160 c160 x
  obtain ⟨ω177, μ177, run177, c177⟩ := seg176s (R := accContract env) (p := p) (P := P) LA ⟨(Nat.lt_succ_of_le hLA.2), trivial⟩ ⟨hLA.1, trivial⟩ μ ω176 μ176 c176 x
  obtain ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, -⟩, ⟨m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, -⟩, -, -, hfr, hpg⟩ := c177
  exact ⟨ω177, μ177, (run144.trans (run160.trans (run176.trans run177))),
    ⟨{hreg0 := r0
      hreg1 := r1
      hreg2 := r2
      hreg3 := r3
      hreg4 := r4
      hreg6 := r5
      hreg7 := r6
      hreg8 := r7
      hreg9 := r8
      hreg10 := r9
      hreg11 := r10
      hreg12 := r11
      hreg5 := r12
      hm_206512_8 := list_of_cell rfl m0
      hm_206824_8 := list_of_cell rfl m1
      hm_206832_8 := list_of_cell rfl m2
      hm_206848_4 := list_of_cell rfl m3
      hm_206880_8 := list_of_cell rfl m4
      hm_206888_4 := list_of_cell rfl m5
      hm_4278058720_8 := list_of_cell rfl m6
      hbn_4278058728_8 := m7
      fr := fun a ha => by
            simp only [C177, C176, C175, C174, C173, C172, C171, C170, C169, C168, C167, C166, C165, C164, C163, C162, C161, C160, C159, C158, C157, C156, C155, C154, C153, C152, C151, C150, C149, C148, C147, C146, C145, C144, C143, C142, C141, C140, C139, C138, C137, C136, C135, C134, C133, C132, C131, C130, C129, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not, not_and, Nat.not_lt] at ha
            rw [hfr a (by show a < 4294967296; omega) (out_of_bool (by simp only [cut177s, cut177, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_self_eq_true, Bool.true_and, Bool.or_eq_true, decide_eq_true_eq]; omega))]
            exact h.fr a (by simp_all)
      rdq := fun a => (readable_pages hpg a).trans (h.rdq a)
      wrq := fun a => (writable_pages hpg a).trans (h.wrq a) }, m8, m9⟩⟩


/-- **The prologue, 38875 → 6429** (`AccBParams.chain`), also stating the parameter statics:
    [196616]₂ = 𝖢 = 341 and [196696]₈ = 𝖨 = 16 (`Params.full`). -/
theorem chain (p : ByteArray) (P : Program) [HasCode p P] [HasCodeX p P] [HasCodeA p P] (env : AccEnv) (ω : Regs) (μ : Memory)
    (x : AccCtx) (LA : Nat) (hLA : 3 ≤ LA ∧ LA ≤ 15) (ω₀ : Regs) (μ₀ : Memory) (h : St0 LA ω₀ μ₀ ω μ) :
    ∃ ω' μ', FreeStepsH p (accContract env) 38875 ω μ x 6429 ω' μ' x 2820 ∧ St177 LA ω₀ μ₀ ω' μ' ∧
      μ'.readN 196616 2 = Num.encodeLE 2 Params.full.coreCount ∧
      μ'.readN 196696 8 = Num.encodeLE 8 Params.full.maxPackageItems := by
  obtain ⟨ω1, μ1, run1, h1⟩ := E0.run p P env ω μ x LA hLA ω₀ μ₀ h
  obtain ⟨ω2, μ2, run2, h2⟩ := E64.run p P env ω1 μ1 x LA hLA ω₀ μ₀ h1
  obtain ⟨ω3, μ3, run3, h3, hc, hi⟩ := run128 p P env ω2 μ2 x LA hLA ω₀ μ₀ h2
  exact ⟨ω3, μ3, (run1.trans (run2.trans run3)), h3, hc, hi⟩

/-- **Accumulate's start-up to 6429 with the parameter statics** (`Acc.start_to_6429`, with `chain` in
    place of `AccBParams.chain`): at 6429, [196616]₂ = 𝖢 and [196696]₈ = 𝖨 for the environment's
    parameters (`env.params = Params.full`). -/
theorem start_to_6429_statics (p : ByteArray) (P : Program) [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : AccEnv) (henv : heapBounds env.code = (48, 1044430)) (hpar : env.params = Params.full)
    (μ : Memory) (hμ : Prefix.StartMem μ)
    (hz : ∀ a, 4278050816 ≤ a → a < 4278059008 → μ.read a = 0)
    (LA : Nat) (hLA : 3 ≤ LA ∧ LA ≤ 15) (x : AccCtx) :
    ∃ ω₁ μ₁ ω' μ', FreeStepsH p (accContract env) 5 (Prefix.initRegs LA) μ x 6429 ω' μ' x 3420 ∧
      AccBParams.St177 LA ω₁ μ₁ ω' μ' ∧
      μ'.readN 196616 2 = Num.encodeLE 2 env.params.coreCount ∧
      μ'.readN 196696 8 = Num.encodeLE 8 env.params.maxPackageItems := by
  obtain ⟨ω₁, μ₁, run1, h38⟩ := prefixC_start p P env henv hpar μ hμ hz LA hLA x
  obtain ⟨ω', μ', run2, h177, hc, hi⟩ := chain p P env ω₁ μ₁ x LA hLA ω₁ μ₁ (bparams_start μ hμ hz LA _ ω₁ μ₁ h38)
  rw [hpar]
  exact ⟨ω₁, μ₁, ω', μ', run1.trans run2, h177, hc, hi⟩

end Services.Bootstrap.Acc.Statics
