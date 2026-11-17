import Services.Bootstrap.Refine.PkgH
import Services.Bootstrap.Refine.ProvideEmpty
import Services.Bootstrap.Refine.GapEmpty

/-!
# T1c's decode package for every instruction refine passes through

`pkg_all` dispatches on the instruction x to the per-form packages of `PkgT`, `PkgH`, `ProvideEmpty` and `GapEmpty`:
every well-formed instruction other than `ImportSegs`, `RandomStorageRefine`, `ExportSegs` and an eager `Lookup`
(`PassKind`), whose encoding is at most 2^24 octets. The two global words it reads are the start-up's: the core count
341 at 196616 (`Designate`'s 𝖢, GP v0.8.0 B.7) and the auth-queue length 80 at 196680 (`Assign`'s 𝖰). GP v0.8.0
Appendix B.4 (Ψ_R), B.7 (the instruction list).
-/

namespace Services.Bootstrap.Refine.PkgAll

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeA
  Services.Bootstrap.Refine.Kinds Services.Bootstrap.Refine.PkgT Services.Bootstrap.Refine.PkgH

/-- The instructions refine passes through unchanged and T1c's packages cover: all but `ImportSegs`,
    `RandomStorageRefine` (excluded by T1c's hypotheses), `ExportSegs` and an eager `Lookup` (their own loop steps). -/
def PassKind : Spec.Instr → Prop
  | .importSegs _ | .randomStorageRefine .. | .exportSegs _ => False
  | .lookup _ _ e => e = false
  | _ => True

/-- **The decode package of any instruction refine passes through** (`PassKind`), well-formed for C, with
    |x.encode| ≤ 2^24; the global words 𝖢 = 341 (196616) and 𝖰 = 80 (196680) as the start-up leaves them, and C's
    validator count and auth-queue length at most 3𝖢 and equal to 𝖰. -/
theorem pkg_all {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (gl : Nat → UInt8)
    (hgD : (List.range 2).map (fun k => gl (196616 + k)) = Num.encodeLE 2 341)
    (hgA : (List.range 8).map (fun k => gl (196680 + k)) = Num.encodeLE 8 80)
    (C : Spec.Consts) (hmax : C.maxValCount ≤ 1023) (hQ : C.authQueueLen = 80)
    (x : Spec.Instr) (hw : x.WF C) (hk : PassKind x) (hlen : x.encode.length ≤ 16777216) :
    DecPkg env K pb gl p P x (PassSlot env K pb p P C x) := by
  have fx : MFixed x → DecPkg env K pb gl p P x (PassSlot env K pb p P C x) :=
    fun hm => pkg_fixed env K pb hK1 hK gl C x hm hw
  cases x with
  | createService h l g m b memo r f id =>
    rcases r with _ | _ | ⟨d0, ds⟩
    · exact pkg_csNone env K pb hK1 hK gl C h l g m b memo f id hw
    · exact pkg_csEmpty env K pb hK1 hK gl C h l g m b memo f id hw
    · exact pkg_csSome env K pb hK1 hK gl C h l g m b memo _ f id hw (by simp) hlen
  | upgrade => exact fx trivial
  | transfer => exact fx trivial
  | zombify => exact fx trivial
  | eject => exact fx trivial
  | deleteItems ks =>
    rcases ks with _ | ⟨k0, ks⟩
    · exact pkg_deleteItemsEmpty env K pb hK1 hK gl C
    · exact pkg_deleteItems env K pb hK1 hK gl C _ hw (by simp) hlen
  | solicit => exact fx trivial
  | forget => exact fx trivial
  | lookup s h e => exact fx hk
  | importSegs => exact hk.elim
  | exportSegs => exact hk.elim
  | bless m a v r z =>
    rcases z with _ | ⟨z0, zs⟩
    · exact pkg_blessEmpty env K pb hK1 hK gl C m a v r hw
    · exact pkg_bless env K pb hK1 hK gl C m a v r _ hw (by simp) hlen
  | assign c q a =>
    exact pkg_assign env K pb hK1 hK gl 80 (by decide) hgA (by decide) C (by rw [hQ]) c q a hw
  | designate ks =>
    rcases ks with _ | ⟨k0, ks⟩
    · exact pkg_designateEmpty env K pb hK1 hK gl C hw
    · exact pkg_designate env K pb hK1 hK gl 341 hgD C (by omega) _ hw (by simp) hlen
  | yield => exact fx trivial
  | checkpoint => exact fx trivial
  | panic => exact fx trivial
  | provide sv pre =>
    rcases pre with h | _ | ⟨d0, ds⟩
    · exact pkg_provideHash env K pb hK1 hK gl C sv h hw
    · exact ProvideEmpty.pkg_provideInlineEmpty env K pb hK1 hK gl C sv hw
    · exact pkg_provideInline env K pb hK1 hK gl C sv _ hw (by simp) hlen
  | lookedUp d =>
    rcases d with _ | _ | ⟨d0, ds⟩
    · exact pkg_luNone env K pb hK1 hK gl C
    · exact pkg_luEmpty env K pb hK1 hK gl C
    · exact pkg_luSome env K pb hK1 hK gl C _ (by simp) hlen
  | imported ds =>
    rcases ds with _ | ⟨d0, ds⟩
    · exact pkg_importedEmpty env K pb hK1 hK gl C
    · exact pkg_imported env K pb hK1 hK gl C _ hw (by simp) hlen
  | exported => exact fx trivial
  | randomStorageRefine => exact hk.elim
  | randomStorageAccumulate ks =>
    rcases ks with _ | _ | ⟨k0, ks⟩
    · exact pkg_rsaErr env K pb hK1 hK gl C
    · exact GapEmpty.pkg_rsaEmpty env K pb hK1 hK gl C hw
    · exact pkg_rsaOk env K pb hK1 hK gl C _ hw (by simp) hlen
  | benchmark => exact fx trivial
  | assignForGasCost c q a =>
    rcases q with _ | ⟨q0, qs⟩
    · exact GapEmpty.pkg_assignGasEmpty env K pb hK1 hK gl C c a hw
    · exact pkg_assignGas env K pb hK1 hK gl C c _ a hw (by simp) hlen

end Services.Bootstrap.Refine.PkgAll
