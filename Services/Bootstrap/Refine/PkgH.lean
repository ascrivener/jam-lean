import Services.Bootstrap.Refine.PkgT
import Services.Bootstrap.Refine.ElemsSmallC
import Services.Bootstrap.Refine.ElemsBigC
import Services.Bootstrap.Refine.MixedKinds

/-!
# T1c's per-instruction decode packages (part 2: the forms with a heap buffer)

`PkgT.DecPkg … x (PassSlot … x)` for the variable-width kinds' forms whose decode allocates: the element decoders of
`ElemsSmallC` (one batch) or `ElemsBigC` (the large sizes), and `VecVecOwn.vecvec_elem_bigC` for `DeleteItems` and
`Imported`, with the slots of `SlotHeap` / `SlotVV`. The sizes come from |x.encode| ≤ 2^24 (Ψ_M's argument limit,
GP v0.8.0 Appendix A.7). `Designate` reads the core count 𝖢 and `Assign` the queue length 𝖰 from the globals `gl`
(the start-up's copies of the protocol parameters, `StartupConsts`). GP v0.8.0 B.7, Appendix C (ℰ).
-/

namespace Services.Bootstrap.Refine.PkgH

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeA
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.Loop Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Encode.GrowH Services.Bootstrap.Refine.SlotT Services.Bootstrap.Refine.Pass
  Services.Bootstrap.Refine.SlotHeap Services.Bootstrap.Refine.PkgT

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- `PassSlot` owning the decode's chunks, from the slot's word and `SlotOK`. -/
theorem passSlot_own {env : RefineHost.Env} {K pb : Nat} {p : ByteArray} {P : Program} {C : Spec.Consts}
    {x : Spec.Instr} {cs : List Chunk} {bs : List UInt8} {μr : Memory} (D : Nat)
    (hW : PassW D (Num.decodeLE ((bs.drop 44).take 1))) (h0 : bs.take 8 = Num.encodeLE 8 D)
    (hS : SlotOK env K pb p P (DRt C 0) x.encode bs (· ∈ cs) μr) : PassSlot env K pb p P C x cs bs μr :=
  ⟨D, (· ∈ cs), hW, h0, hS, fun _ h => h⟩

/-- The keeping hypothesis at μr itself. -/
theorem keep_refl (cs : List Chunk) (μr : Memory) : ∀ c ∈ cs, ∀ a, InData c a → μr.read a = μr.read a :=
  fun _ _ _ _ => rfl

/-- **`RandomStorageAccumulate(Some ks)`**, 1 ≤ |ks|. -/
theorem pkg_rsaOk {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (gl : Nat → UInt8)
    (C : Spec.Consts) (ks : List (List UInt8)) (hw : (Spec.Instr.randomStorageAccumulate (some ks)).WF C)
    (hn1 : 1 ≤ ks.length) (hlen : (Spec.Instr.randomStorageAccumulate (some ks)).encode.length ≤ 16777216) :
    DecPkg env K pb gl p P (.randomStorageAccumulate (some ks))
      (PassSlot env K pb p P C (.randomStorageAccumulate (some ks))) := by
  have hw' : Spec.short ks ∧ ∀ k ∈ ks, k.length = 32 := hw ks rfl
  have hfl := flatten_len32 ks hw'.2
  have he : (Spec.Instr.randomStorageAccumulate (some ks)).encode =
      22 :: 0 :: (Blob.encodeNat ks.length ++ ks.flatten) := by
    simp [Spec.Instr.encode, Spec.vec, Codec.nat]
  rw [he] at hlen ⊢
  simp only [List.length_cons, List.length_append] at hlen
  have hstep : ∀ cs bs μr, (∀ μ'' : Memory, (∀ c ∈ cs, ∀ a, InData c a → μ''.read a = μr.read a) →
      Decode.RandomStorage.RandomStorageOkRep ks.length ks.flatten bs μ'' ∧ OwnsBuf cs bs 16 (32 * ks.length)) →
      PassSlot env K pb p P C (.randomStorageAccumulate (some ks)) cs bs μr := fun cs bs μr hR =>
    passSlot_own _ (passW_idx (by unfold PassIdx; omega)) (hR μr (keep_refl cs μr)).1.1
      (he ▸ slotOK_rsaOk env K pb hK1 hK C ks hw hn1 cs bs μr hR)
  by_cases hs : ks.length ≤ 512
  · exact ⟨_, _, fun F RD hL => ElemsSmallC.random_storage_ok_elemC env K pb hK1 hK gl F RD hL ks.length ⟨hn1, hs⟩
      ks.flatten hfl, hstep⟩
  · exact ⟨_, _, fun F RD hL => ElemsBigC.random_storage_ok_elem_bigC env K pb hK1 hK gl F RD hL ks.length
      ⟨by omega, by omega⟩ ks.flatten hfl, hstep⟩

/-- **`Designate(ks)`**, 1 ≤ |ks|, with the core count Cc at 196616 and C's limit within 3 Cc. -/
theorem pkg_designate {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (gl : Nat → UInt8)
    (Cc : Nat) (gv : (List.range 2).map (fun k => gl (196616 + k)) = Num.encodeLE 2 Cc)
    (C : Spec.Consts) (hmax : C.maxValCount ≤ 3 * Cc % 65536)
    (ks : List (List UInt8)) (hw : (Spec.Instr.designate ks).WF C)
    (hn1 : 1 ≤ ks.length) (hlen : (Spec.Instr.designate ks).encode.length ≤ 16777216) :
    DecPkg env K pb gl p P (.designate ks) (PassSlot env K pb p P C (.designate ks)) := by
  have hw0 := hw
  obtain ⟨hm, -, hks⟩ := hw
  have hfl := flatten_len 336 ks hks
  have he : (Spec.Instr.designate ks).encode = 13 :: (Blob.encodeNat ks.length ++ ks.flatten) := by
    simp [Spec.Instr.encode, Spec.vec, Codec.nat]
  rw [he] at hlen ⊢
  simp only [List.length_cons, List.length_append] at hlen
  have hstep : ∀ cs bs μr, (∀ μ'' : Memory, (∀ c ∈ cs, ∀ a, InData c a → μ''.read a = μr.read a) →
      Decode.Designate.DesignateRep ks.length ks.flatten bs μ'' ∧ OwnsBuf cs bs 16 (336 * ks.length)) →
      PassSlot env K pb p P C (.designate ks) cs bs μr := fun cs bs μr hR =>
    passSlot_own _ (passW_idx (by unfold PassIdx; omega)) (hR μr (keep_refl cs μr)).1.1
      (he ▸ slotOK_designate env K pb hK1 hK C ks hw0 hn1 cs bs μr hR)
  by_cases hs : ks.length ≤ 48
  · exact ⟨_, _, fun F RD hL => ElemsSmallC.designate_elemC env K pb hK1 hK gl F RD hL Cc gv ks.length ⟨hn1, hs⟩
      (by omega) ks.flatten hfl, hstep⟩
  · exact ⟨_, _, fun F RD hL => ElemsBigC.designate_elem_bigC env K pb hK1 hK gl F RD hL Cc gv ks.length
      ⟨by omega, by omega⟩ (by omega) ks.flatten hfl, hstep⟩

/-- **`Bless(m, a, v, r, z)`**, 1 ≤ |z|. -/
theorem pkg_bless {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (gl : Nat → UInt8)
    (C : Spec.Consts) (m a v r : Nat) (z : List (Nat × Nat)) (hw : (Spec.Instr.bless m a v r z).WF C)
    (hn1 : 1 ≤ z.length) (hlen : (Spec.Instr.bless m a v r z).encode.length ≤ 16777216) :
    DecPkg env K pb gl p P (.bless m a v r z) (PassSlot env K pb p P C (.bless m a v r z)) := by
  have hw0 := hw
  generalize hit : (z.map (fun (s, g) => Codec.fixed 4 s ++ Codec.fixed 8 g)).flatten = items
  have hil : items.length = 12 * z.length := by
    rw [← hit]
    have := flatten_len 12 (z.map (fun (s, g) => Codec.fixed 4 s ++ Codec.fixed 8 g))
      (fun k hk => by
        obtain ⟨⟨s, g⟩, -, rfl⟩ := List.mem_map.mp hk
        simp [Codec.fixed])
    simpa using this
  have he : (Spec.Instr.bless m a v r z).encode = 11 :: (Codec.fixed 4 m ++ Codec.fixed 4 a ++ Codec.fixed 4 v ++
      Codec.fixed 4 r ++ Blob.encodeNat z.length ++ items) := by
    rw [← hit]; simp [Spec.Instr.encode, Spec.vec, Codec.nat]
  rw [he] at hlen ⊢
  simp only [List.length_cons, List.length_append] at hlen
  have hstep : ∀ cs bs μr, (∀ μ'' : Memory, (∀ c ∈ cs, ∀ a, InData c a → μ''.read a = μr.read a) →
      Decode.Bless.BlessRep (Codec.fixed 4 m) (Codec.fixed 4 a) (Codec.fixed 4 v) (Codec.fixed 4 r) z.length items
        bs μ'' ∧ OwnsBuf cs bs 16 (16 * z.length)) →
      PassSlot env K pb p P C (.bless m a v r z) cs bs μr := fun cs bs μr hR =>
    passSlot_own _ (passW_idx (by unfold PassIdx; omega)) (hR μr (keep_refl cs μr)).1.1
      (he ▸ slotOK_bless env K pb hK1 hK C m a v r z hw0 hn1 cs bs μr (by rw [hit]; exact hR))
  by_cases hs : z.length ≤ 1024
  · exact ⟨_, _, fun F RD hL => ElemsSmallC.bless_elemC env K pb hK1 hK gl F RD hL _ _ _ _ (by simp [Codec.fixed])
      (by simp [Codec.fixed]) (by simp [Codec.fixed]) (by simp [Codec.fixed]) z.length ⟨hn1, hs⟩ items hil, hstep⟩
  · exact ⟨_, _, fun F RD hL => ElemsBigC.bless_elem_bigC env K pb hK1 hK gl F RD hL _ _ _ _ (by simp [Codec.fixed])
      (by simp [Codec.fixed]) (by simp [Codec.fixed]) (by simp [Codec.fixed]) z.length ⟨by omega, by omega⟩ items
      hil, hstep⟩

/-- **`LookedUp(Some d)`**, 1 ≤ |d|. -/
theorem pkg_luSome {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (gl : Nat → UInt8)
    (C : Spec.Consts) (d : List UInt8) (hn1 : 1 ≤ d.length)
    (hlen : (Spec.Instr.lookedUp (some d)).encode.length ≤ 16777216) :
    DecPkg env K pb gl p P (.lookedUp (some d)) (PassSlot env K pb p P C (.lookedUp (some d))) := by
  have he : (Spec.Instr.lookedUp (some d)).encode = 18 :: 1 :: (Blob.encodeNat d.length ++ d) := by
    simp [Spec.Instr.encode, Spec.opt, Spec.bytes, Codec.nat]
  rw [he] at hlen ⊢
  simp only [List.length_cons, List.length_append] at hlen
  have hstep : ∀ cs bs μr, (∀ μ'' : Memory, (∀ c ∈ cs, ∀ a, InData c a → μ''.read a = μr.read a) →
      Decode.LookupProvideElem.LookedUpSomeRep d.length d bs μ'' ∧ OwnsBuf cs bs 16 d.length) →
      PassSlot env K pb p P C (.lookedUp (some d)) cs bs μr := fun cs bs μr hR =>
    passSlot_own _ (passW_idx (by unfold PassIdx; omega)) (hR μr (keep_refl cs μr)).1.1
      (he ▸ slotOK_luSome env K pb hK1 hK C d (by omega) hn1 cs bs μr hR)
  by_cases hs : d.length ≤ 16384
  · exact ⟨_, _, fun F RD hL => ElemsSmallC.looked_up_some_elemC env K pb hK1 hK gl F RD hL d.length ⟨hn1, hs⟩ d rfl,
      hstep⟩
  · exact ⟨_, _, fun F RD hL => ElemsBigC.looked_up_some_elem_bigC env K pb hK1 hK gl F RD hL d.length
      ⟨by omega, by omega⟩ d rfl, hstep⟩

/-- **`Provide(s, Inline d)`**, 1 ≤ |d|. -/
theorem pkg_provideInline {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (gl : Nat → UInt8)
    (C : Spec.Consts) (sv : Nat) (d : List UInt8) (hw : (Spec.Instr.provide sv (.inline d)).WF C)
    (hn1 : 1 ≤ d.length) (hlen : (Spec.Instr.provide sv (.inline d)).encode.length ≤ 16777216) :
    DecPkg env K pb gl p P (.provide sv (.inline d)) (PassSlot env K pb p P C (.provide sv (.inline d))) := by
  have he : (Spec.Instr.provide sv (.inline d)).encode =
      17 :: (Codec.fixed 4 sv ++ 1 :: (Blob.encodeNat d.length ++ d)) := by
    simp [Spec.Instr.encode, Spec.bytes, Codec.nat]
  rw [he] at hlen ⊢
  simp only [List.length_cons, List.length_append] at hlen
  have hstep : ∀ cs bs μr, (∀ μ'' : Memory, (∀ c ∈ cs, ∀ a, InData c a → μ''.read a = μr.read a) →
      Decode.LookupProvideElem.ProvideInlineRep (Codec.fixed 4 sv) d.length d bs μ'' ∧ OwnsBuf cs bs 24 d.length) →
      PassSlot env K pb p P C (.provide sv (.inline d)) cs bs μr := fun cs bs μr hR =>
    passSlot_own _ (passW_idx (by unfold PassIdx; omega)) (hR μr (keep_refl cs μr)).1.1
      (he ▸ slotOK_provideInline env K pb hK1 hK C sv d hw hn1 cs bs μr hR)
  by_cases hs : d.length ≤ 16384
  · exact ⟨_, _, fun F RD hL => ElemsSmallC.provide_inline_elemC env K pb hK1 hK gl F RD hL _
      (by simp [Codec.fixed]) d.length ⟨hn1, hs⟩ d rfl, hstep⟩
  · exact ⟨_, _, fun F RD hL => ElemsBigC.provide_inline_elem_bigC env K pb hK1 hK gl F RD hL _
      (by simp [Codec.fixed]) d.length ⟨by omega, by omega⟩ d rfl, hstep⟩

/-- **`AssignForGasCost(c, q, a)`**, 1 ≤ |q|. -/
theorem pkg_assignGas {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (gl : Nat → UInt8)
    (C : Spec.Consts) (c : Nat) (qs : List (List UInt8)) (a : Nat)
    (hw : (Spec.Instr.assignForGasCost c qs a).WF C) (hn1 : 1 ≤ qs.length)
    (hlen : (Spec.Instr.assignForGasCost c qs a).encode.length ≤ 16777216) :
    DecPkg env K pb gl p P (.assignForGasCost c qs a) (PassSlot env K pb p P C (.assignForGasCost c qs a)) := by
  have hw0 := hw
  obtain ⟨-, -, hks, -⟩ := hw
  have hfl := flatten_len32 qs hks
  have he : (Spec.Instr.assignForGasCost c qs a).encode =
      24 :: (Codec.fixed 2 c ++ Blob.encodeNat qs.length ++ qs.flatten ++ Codec.fixed 4 a) := by
    simp [Spec.Instr.encode, Spec.vec, Codec.nat]
  rw [he] at hlen ⊢
  simp only [List.length_cons, List.length_append] at hlen
  have hstep : ∀ cs bs μr, (∀ μ'' : Memory, (∀ c ∈ cs, ∀ a, InData c a → μ''.read a = μr.read a) →
      Decode.AssignGas.AssignGasRep (Codec.fixed 2 c) qs.length qs.flatten (Codec.fixed 4 a) bs μ'' ∧
        OwnsBuf cs bs 16 (32 * qs.length)) →
      PassSlot env K pb p P C (.assignForGasCost c qs a) cs bs μr := fun cs bs μr hR =>
    passSlot_own _ (passW_idx (by unfold PassIdx; omega)) (hR μr (keep_refl cs μr)).1.1
      (he ▸ slotOK_assignGas env K pb hK1 hK C c qs a hw0 hn1 cs bs μr hR)
  by_cases hs : qs.length ≤ 512
  · exact ⟨_, _, fun F RD hL => ElemsSmallC.assign_gas_elemFC env K pb F RD hL hK1 hK gl qs.length ⟨hn1, hs⟩ _ _ _
      (by simp [Codec.fixed]) hfl (by simp [Codec.fixed]), hstep⟩
  · exact ⟨_, _, fun F RD hL => ElemsBigC.assign_gas_elem_bigC env K pb F RD hL hK1 hK gl qs.length
      ⟨by omega, by omega⟩ _ _ _ (by simp [Codec.fixed]) hfl (by simp [Codec.fixed]), hstep⟩

/-- **`Assign(c, q, a)`**, with the word G at 196680 whose low 32 bits are C's queue length. -/
theorem pkg_assign {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (gl : Nat → UInt8)
    (G : Nat) (hG : G < 18446744073709551616)
    (gv : (List.range 8).map (fun k => gl (196680 + k)) = Num.encodeLE 8 G)
    (hGn : 1 ≤ G % 4294967296 ∧ G % 4294967296 ≤ 512)
    (C : Spec.Consts) (hQ : C.authQueueLen = G % 4294967296) (c : Nat) (qs : List (List UInt8)) (a : Nat)
    (hw : (Spec.Instr.assign c qs a).WF C) :
    DecPkg env K pb gl p P (.assign c qs a) (PassSlot env K pb p P C (.assign c qs a)) := by
  have hw0 := hw
  obtain ⟨-, hql, hks, -⟩ := hw
  have hfl := flatten_len32 qs hks
  have hn : qs.length = G % 4294967296 := hql.trans hQ
  have he : (Spec.Instr.assign c qs a).encode = 12 :: (Codec.fixed 2 c ++ qs.flatten ++ Codec.fixed 4 a) := by
    simp [Spec.Instr.encode]
  rw [he]
  refine ⟨_, _, fun F RD hL => ElemsSmallC.assign_elemFC env K pb F RD hL hK1 hK gl G hG gv hGn _ _ _
    (by simp [Codec.fixed]) (by rw [hfl, hn]) (by simp [Codec.fixed]), fun cs bs μr hR => ?_⟩
  rw [← hn] at hR
  exact passSlot_own _ (passW_idx (by unfold PassIdx; omega)) (hR μr (keep_refl cs μr)).1.1
    (he ▸ slotOK_assign env K pb hK1 hK C c qs a hw0 (by omega) cs bs μr hR)

/-- **`CreateService` with code `Some d`**, 1 ≤ |d| (its word 0 is |d| < 2^63, `PassW`'s niche). -/
theorem pkg_csSome {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (gl : Nat → UInt8)
    (C : Spec.Consts) (h : List UInt8) (l g m b : Nat) (memo d : List UInt8) (f : Nat) (id : Option Nat)
    (hw : (Spec.Instr.createService h l g m b memo (some d) f id).WF C) (hn1 : 1 ≤ d.length)
    (hlen : (Spec.Instr.createService h l g m b memo (some d) f id).encode.length ≤ 16777216) :
    DecPkg env K pb gl p P (.createService h l g m b memo (some d) f id)
      (PassSlot env K pb p P C (.createService h l g m b memo (some d) f id)) := by
  have hw0 := hw
  obtain ⟨hh, -, -, -, -, hmemo, -, -, -⟩ := hw
  have he : (Spec.Instr.createService h l g m b memo (some d) f id).encode =
      0 :: (h ++ Codec.fixed 8 l ++ Codec.fixed 8 g ++ Codec.fixed 8 m ++ Codec.fixed 8 b ++ memo ++
        (1 :: (Blob.encodeNat d.length ++ d)) ++ Codec.fixed 8 f ++ Spec.opt (Codec.fixed 4) id) := by
    simp [Spec.Instr.encode, Spec.opt, Spec.bytes, Codec.nat]
  rw [he] at hlen ⊢
  simp only [List.length_cons, List.length_append] at hlen
  have hstep : ∀ cs bs μr, (∀ μ'' : Memory, (∀ c ∈ cs, ∀ a, InData c a → μ''.read a = μr.read a) →
      Decode.CreateServiceElem.CreateServiceSomeRep d.length d h (Codec.fixed 8 l) (Codec.fixed 8 g)
        (Codec.fixed 8 m) (Codec.fixed 8 b) memo (Codec.fixed 8 f) (Spec.opt (Codec.fixed 4) id) bs μ'' ∧
      OwnsBuf cs bs 8 d.length) →
      PassSlot env K pb p P C (.createService h l g m b memo (some d) f id) cs bs μr := fun cs bs μr hR => by
    obtain ⟨⟨q, h0, -⟩, -⟩ := (hR μr (keep_refl cs μr)).1
    exact passSlot_own _ (Or.inr (Or.inl (by omega))) h0
      (he ▸ slotOK_csSome env K pb hK1 hK C h l g m b memo d f id hw0 hn1 cs bs μr hR)
  by_cases hs : d.length ≤ 16384
  · exact ⟨_, _, fun F RD hL => ElemsSmallC.create_service_some_elemC env K pb hK1 hK gl F RD hL _ _ _ _ _ _ _ _ hh
      (by simp [Codec.fixed]) (by simp [Codec.fixed]) (by simp [Codec.fixed]) (by simp [Codec.fixed]) hmemo
      (by simp [Codec.fixed]) (optU32_of id) d.length ⟨hn1, hs⟩ d rfl, hstep⟩
  · exact ⟨_, _, fun F RD hL => ElemsBigC.create_service_some_elem_bigC env K pb hK1 hK gl F RD hL _ _ _ _ _ _ _ _
      hh (by simp [Codec.fixed]) (by simp [Codec.fixed]) (by simp [Codec.fixed]) (by simp [Codec.fixed]) hmemo
      (by simp [Codec.fixed]) (optU32_of id) d.length ⟨by omega, by omega⟩ d rfl, hstep⟩

/-- **`DeleteItems(ks)`**, 1 ≤ |ks|. -/
theorem pkg_deleteItems {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (gl : Nat → UInt8)
    (C : Spec.Consts) (ks : List (List UInt8)) (hw : (Spec.Instr.deleteItems ks).WF C) (hn1 : 1 ≤ ks.length)
    (hlen : (Spec.Instr.deleteItems ks).encode.length ≤ 16777216) :
    DecPkg env K pb gl p P (.deleteItems ks) (PassSlot env K pb p P C (.deleteItems ks)) := by
  have he := SlotVV.encode_deleteItems ks
  rw [he] at hlen ⊢
  simp only [List.length_cons, List.length_append] at hlen
  have h1 := MixedKinds.encs_len ks
  refine ⟨_, _, fun F RD hL => Decode.VecVecOwn.vecvec_elem_bigC env K pb hK1 hK gl F RD hL 5 21522 990 1088 1090
    9223372036854775812 (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) ks ⟨hn1, by omega⟩
    (fun e he' => by have := MixedKinds.encs_item ks e he'; omega), fun cs bs μr hR => ?_⟩
  exact passSlot_own _ (passW_idx (by unfold PassIdx; omega)) (hR μr (keep_refl cs μr)).1
    (he ▸ SlotVV.slotOK_deleteItems env K pb hK1 hK C ks hw cs bs μr hR)

/-- **`Imported(ds)`**, 1 ≤ |ds|. -/
theorem pkg_imported {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (gl : Nat → UInt8)
    (C : Spec.Consts) (ds : List (List UInt8)) (hw : (Spec.Instr.imported ds).WF C) (hn1 : 1 ≤ ds.length)
    (hlen : (Spec.Instr.imported ds).encode.length ≤ 16777216) :
    DecPkg env K pb gl p P (.imported ds) (PassSlot env K pb p P C (.imported ds)) := by
  have he := SlotVV.encode_imported ds
  rw [he] at hlen ⊢
  simp only [List.length_cons, List.length_append] at hlen
  have h1 := MixedKinds.encs_len ds
  refine ⟨_, _, fun F RD hL => Decode.VecVecOwn.vecvec_elem_bigC env K pb hK1 hK gl F RD hL 19 22072 1022 1170 1172
    9223372036854775826 (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)) ds ⟨hn1, by omega⟩
    (fun e he' => by have := MixedKinds.encs_item ds e he'; omega), fun cs bs μr hR => ?_⟩
  exact passSlot_own _ (passW_idx (by unfold PassIdx; omega)) (hR μr (keep_refl cs μr)).1
    (he ▸ SlotVV.slotOK_imported env K pb hK1 hK C ds hw cs bs μr hR)

end Services.Bootstrap.Refine.PkgH
