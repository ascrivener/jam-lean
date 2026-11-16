import Services.Bootstrap.Refine.SlotHeap
import Services.Bootstrap.Encode.ArmsHVecDeleteItems
import Services.Bootstrap.Encode.ArmsHVecImported
import Services.Bootstrap.Decode.VecVecOwn
import Services.Bootstrap.Decode.ExportEmpty

/-!
# T1c's `DeleteItems` and `Imported` output slots

A passed-through `DeleteItems(ks)` (tag 5) or `Imported(ds)` (tag 19) leaves a `Vec<Vec<u8>>` slot. When the decode
gives it with its chunks (`Decode.VecVecOwn.VecVecRepC`), it is `SlotT.SlotOK` for the kind's encoding, owning those
chunks: the encoder arm `delete_itemsH_232` / `importedH_232` with `DeleteItemsRepAt q qs` / `ImportedRepAt q qs` and
the heap octets `VecVecSrcH q qs`, the `Debug` predicate, and the drop's `DropVecH.VVAt`. With no elements the decode
gives `Decode.ExportEmpty.VecEmptyRep` ({cap 0, ptr 8, len 0}), which owns nothing and whose drop is `VVAt` with c0 = 0.
GP v0.8.0 Appendix C (ℰ).
-/

namespace Services.Bootstrap.Refine.SlotVV

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeA
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA Services.Bootstrap.Encode.GrowH
  Services.Bootstrap.Refine.SlotT Services.Bootstrap.Refine.DropVecH Services.Bootstrap.Refine.DropVecW
  Services.Bootstrap.Refine.SlotHeap

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- The two vector-of-vectors kinds: dispatch index t and the drop arm's addresses (`DropOutH.VK`). -/
theorem vk_of {t : Nat} (ht : t = 5 ∨ t = 19) : ∃ arm head nxt back ret, DropOutH.VK t arm head nxt back ret := by
  rcases ht with rfl | rfl
  · exact ⟨_, _, _, _, _, Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  · exact ⟨_, _, _, _, _, Or.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- **The facts of a decoded `Vec<Vec<u8>>` slot the exit needs** (`VecVecRepC` with discriminant 2^63 − 1 + t, t ∈
    {5, 19}, the chunks cs allocated): its array q and items' addresses qs as the encoder takes them, the heap octets
    `VecVecSrcH q qs` inside chunks of cs, and the drop's `VVAt`. -/
theorem vv_facts {t : Nat} (ht : t = 5 ∨ t = 19) (ks : List (List UInt8)) (cs : List Chunk) (μ : Memory)
    (s : State) (el : Nat)
    (hC : Decode.VecVecOwn.VecVecRepC (9223372036854775807 + t) ks cs (μ.readN el 232) μ)
    (ho : ∀ d ∈ cs, d ∈ chunks s ∧ d.used = true) :
    ∃ q qs, (μ.readN el 232).take 8 = Num.encodeLE 8 (9223372036854775807 + t) ∧
      ((μ.readN el 232).drop 8).take 8 = Num.encodeLE 8 ks.length ∧
      ((μ.readN el 232).drop 16).take 8 = Num.encodeLE 8 q ∧
      ((μ.readN el 232).drop 24).take 8 = Num.encodeLE 8 ks.length ∧
      (∀ j (hj : j < ks.length),
        μ.readN (q + 24 * j) 8 = Num.encodeLE 8 ks[j].length ∧ μ.readN (q + 24 * j + 8) 8 = Num.encodeLE 8 (qs j) ∧
        μ.readN (q + 24 * j + 16) 8 = Num.encodeLE 8 ks[j].length ∧ μ.readN (qs j) ks[j].length = ks[j]) ∧
      q < 18446744073709551616 ∧ (∀ j (hj : j < ks.length), qs j < 18446744073709551616) ∧
      (∀ q' m, VecVecSrcH q qs ks q' m → ∃ c, c ∈ cs ∧ c.addr + 32 ≤ q' ∧ q' + m ≤ c.addr + 32 * c.size) ∧
      VVAt μ s el (· ∈ cs) := by
  obtain ⟨h0, q, qs, co, h8, h16, h24, hj, hco, hcou, hcoq, hcoS, hemp, hne, hneq, hdist, hq31, hqs31⟩ := hC
  -- the items' chunks
  obtain ⟨f, hf⟩ : ∃ f : Nat → Chunk, ∀ j (hj : j < ks.length), ks[j].length ≠ 0 →
      f j ∈ cs ∧ (f j).used = true ∧ f j ≠ co ∧ (f j).addr + 32 = qs j ∧
      qs j + ks[j].length ≤ (f j).addr + 32 * (f j).size :=
    ⟨fun j => if h : ∃ hj : j < ks.length, ks[j].length ≠ 0 then Classical.choose (hne j h.1 h.2) else co,
      fun j hj hl => by
        rw [dif_pos ⟨hj, hl⟩]
        obtain ⟨a, b, c, d, e⟩ := Classical.choose_spec (hne j hj hl)
        exact ⟨a, b, c, d, e⟩⟩
  have r := fun o l (hol : o + l ≤ 232) => Decode.Loop.readN_sub μ el 232 o l _ rfl hol
  have r0 := r 0 8 (by omega)
  simp only [Nat.add_zero, List.drop_zero] at r0
  have hgl : ∀ i (hi : i < ks.length), (ks.getD i []).length = ks[i].length := fun i hi => by
    rw [List.getD_eq_getElem _ _ hi]
  refine ⟨q, qs, h0, h8, h16, h24, hj, by omega, fun j hj => by have := hqs31 j hj; omega, ?_, ?_⟩
  · rintro q' m (⟨hm, rfl, rfl⟩ | ⟨j, hj, hm, rfl, rfl⟩)
    · exact ⟨co, hco, by omega, hcoS⟩
    · obtain ⟨a, -, -, d, e⟩ := hf j hj (by omega)
      exact ⟨f j, a, by omega, e⟩
  · obtain ⟨arm, head, nxt, back, ret, hvk⟩ := vk_of ht
    refine ⟨t, arm, head, nxt, back, ret, ks.length, q, ks.length, fun i => (ks.getD i []).length, qs, f, co, hvk,
      by rw [r0]; exact h0, by rw [r 8 8 (by omega)]; exact h8, by rw [r 16 8 (by omega)]; exact h16,
      by rw [r 24 8 (by omega)]; exact h24, fun i hi => ?_, fun _ => ⟨hcoq, (ho co hco).1, hcou, hco⟩, by omega,
      fun h => h, by omega, fun i hi => ?_, fun i hi hci => ?_, fun i i' hi hi' hii hci hci' => ?_, fun a h1 h2 => ?_⟩
    · rw [hgl i hi]; exact ⟨(hj i hi).1, (hj i hi).2.1⟩
    · have := hqs31 i hi
      have : ks[i].length < 2147483648 := by omega
      rw [hgl i hi]; omega
    · rw [hgl i hi] at hci
      obtain ⟨a, b, c, d, -⟩ := hf i hi hci
      exact ⟨d, (ho _ a).1, b, a, c⟩
    · rw [hgl i hi] at hci; rw [hgl i' hi'] at hci'
      intro he
      have d1 := (hf i hi hci).2.2.2.1
      have d2 := (hf i' hi' hci').2.2.2.1
      rw [he] at d1
      exact hdist i i' hi hi' hii hci hci' (d1.symm.trans d2)
    · exact ⟨by omega, by omega⟩

theorem encode_deleteItems (ks : List (List UInt8)) :
    (Spec.Instr.deleteItems ks).encode = 5 :: (Blob.encodeNat ks.length ++ (Decode.VecVecU8.encs ks).flatten) := by
  simp [Spec.Instr.encode, Spec.vec, Spec.bytes, Decode.VecVecU8.encs, Codec.nat]

theorem encode_imported (ds : List (List UInt8)) :
    (Spec.Instr.imported ds).encode = 19 :: (Blob.encodeNat ds.length ++ (Decode.VecVecU8.encs ds).flatten) := by
  simp [Spec.Instr.encode, Spec.vec, Spec.bytes, Decode.VecVecU8.encs, Codec.nat]

/-- `DeleteItemsRepAt q qs` depends on memory only through `VecVecSrcH q qs`. -/
theorem vvRep_keep {q : Nat} {qs : Nat → Nat} {ks : List (List UInt8)} {μ μ' : Memory}
    (hk : ∀ q' m, VecVecSrcH q qs ks q' m → μ'.readN q' m = μ.readN q' m)
    (h : ∀ j (hj : j < ks.length),
      μ.readN (q + 24 * j) 8 = Num.encodeLE 8 ks[j].length ∧ μ.readN (q + 24 * j + 8) 8 = Num.encodeLE 8 (qs j) ∧
      μ.readN (q + 24 * j + 16) 8 = Num.encodeLE 8 ks[j].length ∧ μ.readN (qs j) ks[j].length = ks[j]) :
    ∀ j (hj : j < ks.length),
      μ'.readN (q + 24 * j) 8 = Num.encodeLE 8 ks[j].length ∧ μ'.readN (q + 24 * j + 8) 8 = Num.encodeLE 8 (qs j) ∧
      μ'.readN (q + 24 * j + 16) 8 = Num.encodeLE 8 ks[j].length ∧ μ'.readN (qs j) ks[j].length = ks[j] := by
  intro j hj
  obtain ⟨a, b, c, d⟩ := h j hj
  have hA : ∀ q' m, SrcAtP q (24 * ks.length) q' m → μ'.readN q' m = μ.readN q' m :=
    fun q' m h => hk q' m (Or.inl h)
  have hB : ∀ q' m, SrcAtP (qs j) ks[j].length q' m → μ'.readN q' m = μ.readN q' m :=
    fun q' m h => hk q' m (Or.inr ⟨j, hj, h⟩)
  refine ⟨?_, ?_, ?_, src_keep hB d⟩
  · rw [sub_keep hA (o := 24 * j) (l := 8) (by omega)]; exact a
  · rw [show q + 24 * j + 8 = q + (24 * j + 8) by omega, sub_keep hA (o := 24 * j + 8) (l := 8) (by omega)]
    rw [show q + (24 * j + 8) = q + 24 * j + 8 by omega]; exact b
  · rw [show q + 24 * j + 16 = q + (24 * j + 16) by omega, sub_keep hA (o := 24 * j + 16) (l := 8) (by omega)]
    rw [show q + (24 * j + 16) = q + 24 * j + 16 by omega]; exact c

/-- **`DeleteItems(ks)`'s decoded slot is good**: the slot `VecVecRepC (2^63 + 4) ks cs` in every memory keeping cs as
    μr. -/
theorem slotOK_deleteItems {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (C : Spec.Consts) (ks : List (List UInt8)) (hw : (Spec.Instr.deleteItems ks).WF C)
    (cs : List Chunk) (bs : List UInt8) (μr : Memory)
    (hR : ∀ μ : Memory, (∀ c ∈ cs, ∀ a, InData c a → μ.read a = μr.read a) →
      Decode.VecVecOwn.VecVecRepC 9223372036854775812 ks cs bs μ) :
    SlotOK env K pb p P (DRt C 0) (Spec.Instr.deleteItems ks).encode bs (· ∈ cs) μr := by
  intro μ s el hel ho
  obtain ⟨hsh, hks⟩ := hw
  have hC := hR μ (fun c hc a ha => (ho c hc).2.2 a ha)
  rw [← hel] at hC
  obtain ⟨q, qs, h0, h8, h16, h24, hj, hq, hqs, hsrc, hvv⟩ :=
    vv_facts (t := 5) (Or.inl rfl) ks cs μ s el hC (fun d hd => ⟨(ho d hd).1, (ho d hd).2.1⟩)
  have hloc : ∀ (bs : List UInt8) (μ μ' : Memory), (∀ q' m, VecVecSrcH q qs ks q' m →
      μ'.readN q' m = μ.readN q' m) → Encode.Enc.DeleteItemsRepAt q qs ks bs μ →
      Encode.Enc.DeleteItemsRepAt q qs ks bs μ' :=
    fun bs μ μ' hk ⟨e0, e8, e16, e24, e⟩ => ⟨e0, e8, e16, e24, vvRep_keep hk e⟩
  have hrep : Encode.Enc.DeleteItemsRepAt q qs ks (μ.readN el 232) μ := ⟨h0, h8, h16, h24, hj⟩
  rw [encode_deleteItems]
  refine ⟨Encode.Enc.DeleteItemsRepAt q qs ks, Encode.Enc.DeleteItemsRepAt q qs ks, VecVecSrcH q qs ks,
    delete_itemsH_232 env K pb hK1 hK q qs ks hsh hq (fun j hj => hks _ (List.getElem_mem hj)) hqs, hrep, hrep,
    fun bs μ h => ⟨.deleteItems ks, ⟨hsh, hks⟩, (Encode.Enc.deleteItemsRep_iff ks bs μ).mpr ⟨q, qs, h⟩⟩,
    hloc, hloc, hsrc, Or.inr (Or.inl (Or.inl hvv))⟩

/-- **`Imported(ds)`'s decoded slot is good**: the slot `VecVecRepC (2^63 + 18) ds cs` in every memory keeping cs as
    μr. -/
theorem slotOK_imported {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (C : Spec.Consts) (ds : List (List UInt8)) (hw : (Spec.Instr.imported ds).WF C)
    (cs : List Chunk) (bs : List UInt8) (μr : Memory)
    (hR : ∀ μ : Memory, (∀ c ∈ cs, ∀ a, InData c a → μ.read a = μr.read a) →
      Decode.VecVecOwn.VecVecRepC 9223372036854775826 ds cs bs μ) :
    SlotOK env K pb p P (DRt C 0) (Spec.Instr.imported ds).encode bs (· ∈ cs) μr := by
  intro μ s el hel ho
  obtain ⟨hsh, hks⟩ := hw
  have hC := hR μ (fun c hc a ha => (ho c hc).2.2 a ha)
  rw [← hel] at hC
  obtain ⟨q, qs, h0, h8, h16, h24, hj, hq, hqs, hsrc, hvv⟩ :=
    vv_facts (t := 19) (Or.inr rfl) ds cs μ s el hC (fun d hd => ⟨(ho d hd).1, (ho d hd).2.1⟩)
  have hloc : ∀ (bs : List UInt8) (μ μ' : Memory), (∀ q' m, VecVecSrcH q qs ds q' m →
      μ'.readN q' m = μ.readN q' m) → Encode.Enc.ImportedRepAt q qs ds bs μ →
      Encode.Enc.ImportedRepAt q qs ds bs μ' :=
    fun bs μ μ' hk ⟨e0, e8, e16, e24, e⟩ => ⟨e0, e8, e16, e24, vvRep_keep hk e⟩
  have hrep : Encode.Enc.ImportedRepAt q qs ds (μ.readN el 232) μ := ⟨h0, h8, h16, h24, hj⟩
  rw [encode_imported]
  refine ⟨Encode.Enc.ImportedRepAt q qs ds, Encode.Enc.ImportedRepAt q qs ds, VecVecSrcH q qs ds,
    importedH_232 env K pb hK1 hK q qs ds hsh hq (fun j hj => hks _ (List.getElem_mem hj)) hqs, hrep, hrep,
    fun bs μ h => ⟨.imported ds, ⟨hsh, hks⟩, (Encode.Enc.vecVecRep_iff ds bs μ).mpr ⟨q, qs, h⟩⟩,
    hloc, hloc, hsrc, Or.inr (Or.inl (Or.inl hvv))⟩

/-- **An empty `Vec<Vec<u8>>` slot** (`VecEmptyRep (2^63 − 1 + t)`, t ∈ {5, 19}: {cap 0, ptr 8, len 0}) is a `VVAt`
    owning nothing. -/
theorem vvAt_empty {t : Nat} (ht : t = 5 ∨ t = 19) (μ : Memory) (s : State) (el : Nat) (own : Chunk → Prop)
    (hE : Decode.ExportEmpty.VecEmptyRep (9223372036854775807 + t) (μ.readN el 232)) : VVAt μ s el own := by
  obtain ⟨e0, e8, e16, e24⟩ := hE
  have r := fun o l (hol : o + l ≤ 232) => Decode.Loop.readN_sub μ el 232 o l _ rfl hol
  have r0 := r 0 8 (by omega)
  simp only [Nat.add_zero, List.drop_zero] at r0
  obtain ⟨arm, head, nxt, back, ret, hvk⟩ := vk_of ht
  exact ⟨t, arm, head, nxt, back, ret, 0, 8, 0, fun _ => 0, fun _ => 0, fun _ => ⟨0, 0, false⟩, ⟨0, 0, false⟩, hvk,
    by rw [r0]; exact e0, by rw [r 8 8 (by omega)]; exact e8, by rw [r 16 8 (by omega)]; exact e16,
    by rw [r 24 8 (by omega)]; exact e24, fun i hi => absurd hi (Nat.not_lt_zero _), fun h => absurd rfl h,
    by omega, fun h => absurd rfl h, by omega, fun i hi => absurd hi (Nat.not_lt_zero _),
    fun i hi => absurd hi (Nat.not_lt_zero _), fun i _ hi => absurd hi (Nat.not_lt_zero _),
    fun a h1 h2 => absurd h2 (by omega)⟩

/-- The empty slot's `DeleteItemsRepAt` / `ImportedRepAt` body, with q = 8: no item to read. -/
theorem empty_items (μ : Memory) :
    ∀ j (hj : j < ([] : List (List UInt8)).length),
      μ.readN (8 + 24 * j) 8 = Num.encodeLE 8 ([] : List (List UInt8))[j].length ∧
      μ.readN (8 + 24 * j + 8) 8 = Num.encodeLE 8 ((fun _ => 0 : Nat → Nat) j) ∧
      μ.readN (8 + 24 * j + 16) 8 = Num.encodeLE 8 ([] : List (List UInt8))[j].length ∧
      μ.readN ((fun _ => 0 : Nat → Nat) j) ([] : List (List UInt8))[j].length = ([] : List (List UInt8))[j] :=
  fun j hj => absurd hj (Nat.not_lt_zero _)

/-- **`DeleteItems([])`'s decoded slot is good** (`VecEmptyRep (2^63 + 4)`), owning nothing. -/
theorem slotOK_deleteItemsEmpty {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (C : Spec.Consts) (bs : List UInt8) (μr : Memory)
    (hE : Decode.ExportEmpty.VecEmptyRep 9223372036854775812 bs) :
    SlotOK env K pb p P (DRt C 0) (Spec.Instr.deleteItems []).encode bs (fun _ => False) μr := by
  intro μ s el hel _
  rw [← hel] at hE
  have hrep : Encode.Enc.DeleteItemsRepAt 8 (fun _ => 0) [] (μ.readN el 232) μ :=
    ⟨hE.1, hE.2.1, hE.2.2.1, hE.2.2.2, empty_items μ⟩
  have hloc : ∀ (bs : List UInt8) (μ μ' : Memory), (∀ q' m, VecVecSrcH 8 (fun _ => 0) [] q' m →
      μ'.readN q' m = μ.readN q' m) → Encode.Enc.DeleteItemsRepAt 8 (fun _ => 0) [] bs μ →
      Encode.Enc.DeleteItemsRepAt 8 (fun _ => 0) [] bs μ' :=
    fun bs μ μ' _ ⟨e0, e8, e16, e24, _⟩ => ⟨e0, e8, e16, e24, empty_items μ'⟩
  rw [encode_deleteItems]
  refine ⟨Encode.Enc.DeleteItemsRepAt 8 (fun _ => 0) [], Encode.Enc.DeleteItemsRepAt 8 (fun _ => 0) [],
    VecVecSrcH 8 (fun _ => 0) [],
    delete_itemsH_232 env K pb hK1 hK 8 (fun _ => 0) [] (by decide) (by decide) (fun j hj => absurd hj (Nat.not_lt_zero _))
      (fun j hj => absurd hj (Nat.not_lt_zero _)), hrep, hrep,
    fun bs μ h => ⟨.deleteItems [], ⟨by decide, by simp⟩,
      (Encode.Enc.deleteItemsRep_iff [] bs μ).mpr ⟨8, fun _ => 0, h⟩⟩,
    hloc, hloc, ?_, Or.inr (Or.inl (Or.inl (vvAt_empty (t := 5) (Or.inl rfl) μ s el _ hE)))⟩
  rintro q' m (⟨hm, -, rfl⟩ | ⟨j, hj, -⟩)
  · simp at hm
  · exact absurd hj (Nat.not_lt_zero _)

/-- **`Imported([])`'s decoded slot is good** (`VecEmptyRep (2^63 + 18)`), owning nothing. -/
theorem slotOK_importedEmpty {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (C : Spec.Consts) (bs : List UInt8) (μr : Memory)
    (hE : Decode.ExportEmpty.VecEmptyRep 9223372036854775826 bs) :
    SlotOK env K pb p P (DRt C 0) (Spec.Instr.imported []).encode bs (fun _ => False) μr := by
  intro μ s el hel _
  rw [← hel] at hE
  have hrep : Encode.Enc.ImportedRepAt 8 (fun _ => 0) [] (μ.readN el 232) μ :=
    ⟨hE.1, hE.2.1, hE.2.2.1, hE.2.2.2, empty_items μ⟩
  have hloc : ∀ (bs : List UInt8) (μ μ' : Memory), (∀ q' m, VecVecSrcH 8 (fun _ => 0) [] q' m →
      μ'.readN q' m = μ.readN q' m) → Encode.Enc.ImportedRepAt 8 (fun _ => 0) [] bs μ →
      Encode.Enc.ImportedRepAt 8 (fun _ => 0) [] bs μ' :=
    fun bs μ μ' _ ⟨e0, e8, e16, e24, _⟩ => ⟨e0, e8, e16, e24, empty_items μ'⟩
  rw [encode_imported]
  refine ⟨Encode.Enc.ImportedRepAt 8 (fun _ => 0) [], Encode.Enc.ImportedRepAt 8 (fun _ => 0) [],
    VecVecSrcH 8 (fun _ => 0) [],
    importedH_232 env K pb hK1 hK 8 (fun _ => 0) [] (by decide) (by decide) (fun j hj => absurd hj (Nat.not_lt_zero _))
      (fun j hj => absurd hj (Nat.not_lt_zero _)), hrep, hrep,
    fun bs μ h => ⟨.imported [], ⟨by decide, by simp⟩,
      (Encode.Enc.vecVecRep_iff [] bs μ).mpr ⟨8, fun _ => 0, h⟩⟩,
    hloc, hloc, ?_, Or.inr (Or.inl (Or.inl (vvAt_empty (t := 19) (Or.inr rfl) μ s el _ hE)))⟩
  rintro q' m (⟨hm, -, rfl⟩ | ⟨j, hj, -⟩)
  · simp at hm
  · exact absurd hj (Nat.not_lt_zero _)

end Services.Bootstrap.Refine.SlotVV
