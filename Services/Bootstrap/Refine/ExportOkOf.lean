import Services.Bootstrap.Refine.LoopAll
import Services.Bootstrap.Refine.ExportSeg
import Services.Bootstrap.Decode.VecVecOwn
import Services.Bootstrap.Spec

/-!
# `ExportOk` from the decoded `ExportSegs` slot

The transform loop's `LoopAll.ExportOk` for instruction k, built from what the decode leaves:
`export_ok_big` from `VecVecOwn.VecVecRepC` (the segments and their buffer in chunks of the heap) and
`export_ok_empty` from the slot of `Export { data: [] }`. The host context afterwards is stated on the
segments themselves: `expD` (Ω_E of one segment, GP v0.8.0 Appendix B.7 `export`, the reply ignored),
folded over the segments (`Spec.refineInstr`'s `for d in ds do op (ROp.exportSeg d)`).
-/

namespace Services.Bootstrap.Refine.ExportOkOf

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Refine.LoopAll Services.Bootstrap.Decode.VecVecOwn

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- The context after Ω_E of the segment d (`ExportSeg.expSeg` on the octets themselves): at most
    `Cmaxpackageexports` exports, each d cut or zero-padded to `Csegmentsize`. GP v0.8.0 Appendix B.7 (export). -/
def expD (env : RefineHost.Env) (d : List UInt8) (x : RefineCtx) : RefineCtx :=
  if env.exportOffset + x.2.length ≥ Constants.Cmaxpackageexports then x
  else (x.1, x.2 ++ [d.take (min d.length Constants.Csegmentsize) ++
    List.replicate (Constants.Csegmentsize - min d.length Constants.Csegmentsize) 0])

/-- The context after exporting the segments ds in order. -/
def expDs (env : RefineHost.Env) (ds : List (List UInt8)) (x : RefineCtx) : RefineCtx :=
  ds.foldl (fun y d => expD env d y) x

theorem expSeg_eq {env : RefineHost.Env} {μ : Memory} {q : Nat} {d : List UInt8} {x : RefineCtx}
    (h : μ.readN q d.length = d) : ExportSeg.expSeg env q d.length μ x = expD env d x := by
  unfold ExportSeg.expSeg expD
  rw [← readN_take μ q d.length _ (Nat.min_le_left _ _), h]

/-- `ExportSeg.expUpTo` over segments laid out as words {cap, ptr, len} at ptr + 24j whose octets are ds[j]. -/
theorem expUpTo_eq {env : RefineHost.Env} {μ : Memory} {ptr : Nat} {ds : List (List UInt8)} {qs : Nat → Nat}
    (x : RefineCtx)
    (hw : ∀ j (hj : j < ds.length), rdN μ (ptr + 24 * j + 8) 8 = qs j ∧ rdN μ (ptr + 24 * j + 16) 8 = ds[j].length ∧
      μ.readN (qs j) ds[j].length = ds[j]) :
    ∀ m, m ≤ ds.length → ExportSeg.expUpTo env μ ptr x m = expDs env (ds.take m) x := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm
    obtain ⟨h1, h2, h3⟩ := hw m (by omega)
    unfold ExportSeg.expUpTo
    rw [h1, h2, ih (by omega), expSeg_eq h3]
    unfold expDs
    rw [show List.take (m + 1) ds = List.take m ds ++ [ds[m]] from List.take_succ_eq_append_getElem (by omega),
      List.foldl_append]
    rfl

theorem expD_bound {env : RefineHost.Env} {B : Nat} (hB : Constants.Cmaxpackageexports ≤ B) (d : List UInt8)
    (x : RefineCtx) (h : env.exportOffset + x.2.length ≤ B) : env.exportOffset + (expD env d x).2.length ≤ B := by
  unfold expD
  split
  · exact h
  · simp only [List.length_append, List.length_cons, List.length_nil]; omega

theorem expDs_bound {env : RefineHost.Env} {B : Nat} (hB : Constants.Cmaxpackageexports ≤ B) (ds : List (List UInt8)) :
    ∀ (x : RefineCtx), env.exportOffset + x.2.length ≤ B → env.exportOffset + (expDs env ds x).2.length ≤ B := by
  induction ds with
  | nil => intro x h; exact h
  | cons d ds ih => intro x h; exact ih _ (expD_bound hB d x h)

/-- **`ExportOk` for `Export { data: [] }`**: the slot {2⁶³ + 9, cap 0, ptr 8, len 0} exports nothing. -/
theorem export_ok_empty {env : RefineHost.Env} {μ0 : Memory} {E k : Nat} {ce : Chunk} {Kp Kp' : Chunk → Prop}
    {O : Nat → List UInt8 → Prop} {x x' : RefineCtx}
    (hs : let bs := μ0.readN (E + 232 * k) 232
      bs.take 8 = Num.encodeLE 8 9223372036854775817 ∧ (bs.drop 8).take 8 = Num.encodeLE 8 0 ∧
        (bs.drop 16).take 8 = Num.encodeLE 8 8 ∧ (bs.drop 24).take 8 = Num.encodeLE 8 0)
    (hK : ∀ d, Kp' d → Kp d)
    (hO : ∀ bs, bs.take 8 = Num.encodeLE 8 9223372036854775827 → (bs.drop 8).take 8 = Num.encodeLE 8 0 → O k bs)
    (hx : x' = x) :
    ExportOk env μ0 E k ce Kp Kp' O x x' := by
  obtain ⟨s0, s8, s16, s24⟩ := hs
  have sub : ∀ o, o + 8 ≤ 232 → μ0.readN (E + 232 * k + o) 8 = ((μ0.readN (E + 232 * k) 232).drop o).take 8 :=
    fun o h => Decode.Loop.readN_sub μ0 _ 232 o 8 _ rfl h
  refine ⟨0, 8, 0, ce, fun _ => 0, fun _ => 0, fun _ => 0, ?_, by rw [sub 8 (by omega)]; exact s8,
    by rw [sub 16 (by omega)]; exact s16, by rw [sub 24 (by omega)]; exact s24, by decide, Nat.le_refl _,
    by decide, fun h => absurd rfl h, fun a h1 h2 => by omega, fun i hi => absurd hi (Nat.not_lt_zero _),
    fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => absurd hi (Nat.not_lt_zero _),
    fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => absurd hi (Nat.not_lt_zero _),
    fun i hi => absurd hi (Nat.not_lt_zero _),
    fun d h => ⟨hK d h, fun h => absurd rfl h, fun i hi => absurd hi (Nat.not_lt_zero _)⟩, ?_, by rw [hx]; rfl⟩
  · rw [← readN_take μ0 _ 232 8 (by omega)]; exact s0
  · intro μ' a h0 h8
    apply hO
    · rw [readN_take μ' a 232 8 (by omega)]; exact h0
    · rw [← Decode.Loop.readN_sub μ' a 232 8 8 _ rfl (by omega)]; exact h8

/-- **`ExportOk` for `Export { data: ds }`, 1 ≤ |ds|**: from the decoded slot (`VecVecRepC` at
    discriminant 2⁶³ + 9, its chunks cs), the chunks to keep `Kp` holding cs and none of them the
    instructions' chunk ce, and `Kp'` (kept after this instruction) none of cs, nor sharing an address
    with one: the context afterwards is ds exported in order (`expDs`). -/
theorem export_ok_big {env : RefineHost.Env} {μ0 : Memory} {E k : Nat} {ce : Chunk} {Kp Kp' : Chunk → Prop}
    {O : Nat → List UInt8 → Prop} {x x' : RefineCtx} {ds : List (List UInt8)} {cs : List Chunk}
    (hrep : VecVecRepC (9223372036854775807 + 10) ds cs (μ0.readN (E + 232 * k) 232) μ0)
    (hb : 24 * ds.length < 1073741760) (hds : ∀ d ∈ ds, d.length < 1073741760)
    (hcs : ∀ c ∈ cs, Kp c ∧ c ≠ ce)
    (hK : ∀ d, Kp' d → Kp d ∧ d ∉ cs ∧ ∀ c ∈ cs, d.addr ≠ c.addr)
    (hO : ∀ bs, bs.take 8 = Num.encodeLE 8 9223372036854775827 → (bs.drop 8).take 8 = Num.encodeLE 8 ds.length →
      O k bs)
    (hx : x' = expDs env ds x) :
    ExportOk env μ0 E k ce Kp Kp' O x x' := by
  obtain ⟨h0, q, qs, co, h8, h16, h24, hj, hco, hcou, hcoa, hcoe, hz, hne, hqne, hqd, hq8, hqs⟩ := hrep
  have sub : ∀ o, o + 8 ≤ 232 → μ0.readN (E + 232 * k + o) 8 = ((μ0.readN (E + 232 * k) 232).drop o).take 8 :=
    fun o h => Decode.Loop.readN_sub μ0 _ 232 o 8 _ rfl h
  have gl : ∀ i (hi : i < ds.length), (ds.getD i []).length = ds[i].length := fun i hi => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  have hlt : ∀ i (hi : i < ds.length), ds[i].length < 1073741760 := fun i hi => hds _ (List.getElem_mem hi)
  refine ⟨ds.length, q, ds.length, co, fun i => (ds.getD i []).length, qs, fun i => (ds.getD i []).length,
    ?_, by rw [sub 8 (by omega)]; exact h8, by rw [sub 16 (by omega)]; exact h16,
    by rw [sub 24 (by omega)]; exact h24, by omega, Nat.le_refl _, hq8,
    fun _ => ⟨(hcs co hco).1, (hcs co hco).2, hcoa⟩, inData_of hcoa hcoe, fun i hi => ?_, fun i hi => ?_,
    fun i hi => ?_, fun i hi hc => ?_, fun i hi hc => ?_, fun i hi a ha1 ha2 => ?_,
    fun d hd => ?_, ?_, ?_⟩
  · rw [← readN_take μ0 _ 232 8 (by omega)]; exact h0
  · simp only [gl i hi]; exact ⟨(hj i hi).1, (hj i hi).2.1, (hj i hi).2.2.1⟩
  · simp only [gl i hi]; have := hlt i hi; omega
  · simp only [gl i hi]; exact hqs i hi
  · simp only [gl i hi] at hc
    exact ⟨by rw [hcoa]; exact hqne i hi hc, fun j hj' hji hcj => by
      simp only [gl j hj'] at hcj; exact hqd j i hj' hi hji hcj hc⟩
  · simp only [gl i hi] at hc
    obtain ⟨c, hc, -, -, hca, -⟩ := hne i hi hc
    exact ⟨c, (hcs c hc).1, (hcs c hc).2, hca⟩
  · simp only [gl i hi] at ha2
    by_cases h0 : ds[i].length = 0
    · omega
    · obtain ⟨c, hc, -, -, hca, hce⟩ := hne i hi h0
      exact ⟨c, (hcs c hc).1, inData_of hca hce a ha1 ha2⟩
  · obtain ⟨hk, hnc, hna⟩ := hK d hd
    refine ⟨hk, fun _ e => hnc (e ▸ hco), fun i hi hc e => ?_⟩
    simp only [gl i hi] at hc
    obtain ⟨c, hc, -, -, hca, -⟩ := hne i hi hc
    exact hna c hc (by omega)
  · intro μ' a e0 e8
    apply hO
    · rw [readN_take μ' a 232 8 (by omega)]; exact e0
    · rw [← Decode.Loop.readN_sub μ' a 232 8 8 _ rfl (by omega)]; exact e8
  · rw [hx, expUpTo_eq (qs := qs) x (fun j hj' => ⟨Decode.VecEmpty.rd8 (by have := hqs j hj'; omega) (hj j hj').2.1,
      Decode.VecEmpty.rd8 (by have := hlt j hj'; omega) (hj j hj').2.2.1, (hj j hj').2.2.2⟩) _ (Nat.le_refl _),
      List.take_length]

end Services.Bootstrap.Refine.ExportOkOf
