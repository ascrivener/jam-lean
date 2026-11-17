import Services.Bootstrap.Decode.ExportEmpty
import Services.Bootstrap.Decode.Bless
import Services.Bootstrap.Decode.Designate
import Services.Bootstrap.Decode.DesignateHeap
import Services.Bootstrap.Decode.LookedUp
import Services.Bootstrap.Decode.RandomStorage
import Services.Bootstrap.Decode.LoopAPassC

/-!
# The heap kinds' empty and no-buffer forms, as elements of the decode loop

The frame-level decoders of the variable-width kinds' forms that allocate nothing (GP v0.8.0 B.7, the bootstrap
service's instruction list), stated at the decode loop's frame base F as `Loop.ElemOkF` (and as `ElemOkAFC`, owning no
chunk):

* `bless_emptyF`: `Bless { …, always_acc: [] }`, encoded 11 :: m ++ a ++ d ++ r ++ [0] (`Bless.bless_empty`);
* `designate_emptyF`: `Designate { keys: [] }`, encoded [13, 0] (`Designate.designate_empty`; it reads the core count at
  196616, so its form `ElemOkFG` also takes the globals readable, which the heap context gives);
* `looked_up_emptyF`: `LookedUp { data: Some [] }`, encoded [18, 1, 0] (`LookedUp.looked_up_empty`);
* `random_storage_errF`: `RandomStorageAccumulate(Err(()))`, encoded [22, 1] (`RandomStorage.random_storage_err`).

The empty `Vec`s these leave are `{cap 0, ptr 8, len 0}` (Bless) or `{cap 0, ptr 1, len 0}` (Designate, LookedUp).
-/

namespace Services.Bootstrap.Refine.EmptyElems

open PVM Picoalloc Services.Bootstrap Services.Bootstrap.Code JAM Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.Loop Services.Bootstrap.Decode.LoopA Services.Bootstrap.Decode.Elems
  Services.Bootstrap.Decode.HeapCtx

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- The slot of a variant with an empty `Vec` at word 8: the discriminant W, then `{cap 0, ptr q, len 0}`. -/
def VecNilRep (W q : Nat) (bs : List UInt8) : Prop :=
  bs.take 8 = Num.encodeLE 8 W ∧ (bs.drop 8).take 8 = Num.encodeLE 8 0 ∧
    (bs.drop 16).take 8 = Num.encodeLE 8 q ∧ (bs.drop 24).take 8 = Num.encodeLE 8 0

/-- `Bless` with no entries: `VecNilRep (2^63 + 10) 8` and the four `u32`s at 32, 36, 40, 44. -/
def BlessEmptyRep (m a d r : List UInt8) (bs : List UInt8) : Prop :=
  VecNilRep 9223372036854775818 8 bs ∧ (bs.drop 32).take 4 = m ∧ (bs.drop 36).take 4 = a ∧
    (bs.drop 40).take 4 = d ∧ (bs.drop 44).take 4 = r

/-- `RandomStorageAccumulate(Err(()))`: the discriminant 2^63 + 21 and the niche word 2^64 − 1. -/
def RSAErrRep0 (bs : List UInt8) : Prop :=
  bs.take 8 = Num.encodeLE 8 9223372036854775829 ∧ (bs.drop 8).take 8 = Num.encodeLE 8 18446744073709551615

theorem nil_rep {μ : Memory} {F W q : Nat} (eO : μ.readN (F + 120) 8 = Num.encodeLE 8 W)
    (eO8 : μ.readN (F + 120 + 8) 8 = Num.encodeLE 8 0) (eO16 : μ.readN (F + 120 + 16) 8 = Num.encodeLE 8 q)
    (eO24 : μ.readN (F + 120 + 24) 8 = Num.encodeLE 8 0) : VecNilRep W q (μ.readN (F + 120) 232) :=
  ⟨(slot_parts μ (F + 120) 0 8 (by omega)).1.trans eO, (slot_parts μ (F + 120) 8 8 (by omega)).2.trans eO8,
    (slot_parts μ (F + 120) 16 8 (by omega)).2.trans eO16, (slot_parts μ (F + 120) 24 8 (by omega)).2.trans eO24⟩

/-- **`Bless` with no always-accumulate entries** (tag 11, four `u32`s m a d r, then ℰ(0)). -/
theorem bless_emptyF {p : ByteArray} {P : Program} [HasCode p P] (F RD : Nat) (hL : Lay F RD)
    (m a d r : List UInt8) (hm : m.length = 4) (ha : a.length = 4) (hd : d.length = 4) (hr : r.length = 4) :
    ElemOkF p P F RD (11 :: (m ++ a ++ d ++ r ++ [0])) (BlessEmptyRep m a d r) := by
  have hL' := hL
  obtain ⟨l1, l2, l3, l4⟩ := hL'
  intro X R x ω μ ptr len v5 v6 h1 h5 h6 h7 tagr rP rL hlen hlen' hptr hpb pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr
  have hl : (11 :: (m ++ a ++ d ++ r ++ [0])).length - 1 = 17 := by simp [hm, ha, hd, hr]
  simp only [hl, List.headD_cons, List.tail_cons] at tagr hlen hptr hpb pay rpay ⊢
  simp only [List.append_assoc] at pay
  have p1 : μ.readN (ptr + 4) 13 = a ++ (d ++ (r ++ [0])) := by
    rw [readN_sub μ ptr 17 4 13 _ pay (by omega), List.drop_left' hm,
      List.take_of_length_le (by simp [ha, hd, hr])]
  have p2 : μ.readN (ptr + 4 + 4) 9 = d ++ (r ++ [0]) := by
    rw [readN_sub μ (ptr + 4) 13 4 9 _ p1 (by omega), List.drop_left' ha,
      List.take_of_length_le (by simp [hd, hr])]
  have p3 : μ.readN (ptr + 4 + 4 + 4) 5 = r ++ [0] := by
    rw [readN_sub μ (ptr + 4 + 4) 9 4 5 _ p2 (by omega), List.drop_left' hd,
      List.take_of_length_le (by simp [hr])]
  have p4 : μ.readN (ptr + 4 + 4 + 4 + 4) 1 = [0] := by
    rw [readN_sub μ (ptr + 4 + 4 + 4) 5 4 1 _ p3 (by omega), List.drop_left' hr]; rfl
  have q0 : μ.readN ptr 4 = m := by
    rw [show μ.readN ptr 4 = μ.readN (ptr + 0) 4 by rfl, readN_sub μ ptr 17 0 4 _ pay (by omega), List.drop_zero,
      List.take_left' hm]
  have q4 : μ.readN (ptr + 4) 4 = a := by
    rw [show μ.readN (ptr + 4) 4 = μ.readN (ptr + 4 + 0) 4 by rfl, readN_sub μ (ptr + 4) 13 0 4 _ p1 (by omega),
      List.drop_zero, List.take_left' ha]
  have q8 : μ.readN (ptr + 8) 4 = d := by
    rw [show μ.readN (ptr + 8) 4 = μ.readN (ptr + 4 + 4 + 0) 4 by rfl,
      readN_sub μ (ptr + 4 + 4) 9 0 4 _ p2 (by omega), List.drop_zero, List.take_left' hd]
  have q12 : μ.readN (ptr + 12) 4 = r := by
    rw [show μ.readN (ptr + 12) 4 = μ.readN (ptr + 4 + 4 + 4 + 0) 4 by rfl,
      readN_sub μ (ptr + 4 + 4 + 4) 5 0 4 _ p3 (by omega), List.drop_zero, List.take_left' hr]
  have hzero : μ.read (ptr + 16) = 0 := by
    rw [show ptr + 16 = ptr + 4 + 4 + 4 + 4 by omega]
    simpa [Memory.readN] using p4
  obtain ⟨ω', μ', run, -, e1, e5, e6, eO, eO8, eO16, eO24, e32, e36, e40, e44, eR0, eR8, efr, erd, ewr⟩ :=
    Decode.Bless.bless_empty (p := p) (P := P) (R := R) x ω μ F (F + 120) 18 723 v5 v6 RD ptr len
      (loopFrame F RD hL ω μ v5 v6 h1 h5 s0 s5 s6 hv5 hv6 ws) (by omega) h6 h7 (by simpa using tagr) tab rt
      ⟨by omega, by omega⟩ ⟨hptr, by omega⟩ ⟨hlen, hlen'⟩ hzero rP rL (Or.inr (by omega)) (Or.inl (by omega))
      (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (by omega)
      (fun a h1 h2 => ws a (by omega) (by omega)) wr (fun a h1 h2 => ws a (by omega) (by omega))
      (fun a h1 h2 => rpay a h1 h2)
  refine ⟨ω', μ', run.mono (by omega), e1, e5, e6, eR0, eR8, ⟨9223372036854775818, by decide, eO, by decide⟩,
    ⟨nil_rep eO eO8 eO16 eO24, ?_, ?_, ?_, ?_⟩, fun a h0 h1 h2 h3 => efr a h0 (by omega) h2 (by omega), erd, ewr⟩
  · rw [(slot_parts μ' (F + 120) 32 4 (by omega)).2, e32, q0]
  · rw [(slot_parts μ' (F + 120) 36 4 (by omega)).2, e36, q4]
  · rw [(slot_parts μ' (F + 120) 40 4 (by omega)).2, e40, q8]
  · rw [(slot_parts μ' (F + 120) 44 4 (by omega)).2, e44, q12]

/-- **`LookedUp { data: Some [] }`** (tag 18, encoded [18, 1, 0]). -/
theorem looked_up_emptyF {p : ByteArray} {P : Program} [HasCode p P] (F RD : Nat) (hL : Lay F RD) :
    ElemOkF p P F RD [18, 1, 0] (VecNilRep 9223372036854775825 1) := by
  have hL' := hL
  obtain ⟨l1, l2, l3, l4⟩ := hL'
  intro X R x ω μ ptr len v5 v6 h1 h5 h6 h7 tagr rP rL hlen hlen' hptr hpb pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_one_sub_one, List.headD_cons,
    List.tail_cons] at tagr hlen hptr hpb pay rpay ⊢
  have h2 : μ.read ptr = 1 ∧ μ.read (ptr + 1) = 0 := by
    simp [Memory.readN, List.range_succ] at pay
    exact pay
  obtain ⟨ω', μ', run, -, e1, e5, e6, eO, eO8, eO16, eO24, eR0, eR8, efr, erd, ewr⟩ :=
    Decode.LookedUp.looked_up_empty (p := p) (P := P) (R := R) x ω μ F (F + 120) 18 723 v5 v6 RD ptr len
      (loopFrame F RD hL ω μ v5 v6 h1 h5 s0 s5 s6 hv5 hv6 ws) (by omega) h6 h7 (by simpa using tagr) tab rt
      ⟨by omega, by omega⟩ ⟨hptr, by omega⟩ ⟨hlen, hlen'⟩ rP rL h2.1 h2.2 (Or.inr (by omega))
      (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega)) (Or.inl (by omega)) (by omega)
      (fun a h1 h2 => ws a (by omega) (by omega)) wr (fun a h1 h2 => ws a (by omega) (by omega))
      (fun a h1 h2 => rpay a h1 h2)
  exact ⟨ω', μ', run.mono (by omega), e1, e5, e6, eR0, eR8, ⟨9223372036854775825, by decide, eO, by decide⟩,
    nil_rep eO eO8 eO16 eO24, fun a h0 h1 h2 h3 => efr a h0 (by omega) h2 (by omega), erd, ewr⟩

/-- **`RandomStorageAccumulate(Err(()))`** (tag 22, encoded [22, 1]). -/
theorem random_storage_errF {p : ByteArray} {P : Program} [HasCode p P] (F RD : Nat) (hL : Lay F RD) :
    ElemOkF p P F RD [22, 1] RSAErrRep0 := by
  have hL' := hL
  obtain ⟨l1, l2, l3, l4⟩ := hL'
  intro X R x ω μ ptr len v5 v6 h1 h5 h6 h7 tagr rP rL hlen hlen' hptr hpb pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_one_sub_one, List.headD_cons,
    List.tail_cons] at tagr hlen hptr hpb pay rpay ⊢
  have herr : μ.read ptr = 1 := by simpa [Memory.readN] using pay
  obtain ⟨ω', μ', run, -, e1, e5, e6, eO, eO8, eR0, eR8, efr, erd, ewr⟩ :=
    Decode.RandomStorage.random_storage_err (p := p) (P := P) (R := R) x ω μ F (F + 120) 18 723 v5 v6 RD ptr len
      (loopFrame F RD hL ω μ v5 v6 h1 h5 s0 s5 s6 hv5 hv6 ws) (by omega) h6 h7 (by simpa using tagr) tab rt
      ⟨by omega, by omega⟩ ⟨hptr, by omega⟩ ⟨hlen, hlen'⟩ rP rL herr (Or.inr (by omega))
      (Or.inl (by omega)) (Or.inr (by omega)) (Or.inl (by omega)) (by omega)
      (fun a h1 h2 => ws a (by omega) (by omega)) wr (fun a h1 h2 => ws a (by omega) (by omega))
      (rpay ptr (Nat.le_refl _) (by omega))
  exact ⟨ω', μ', run.mono (by omega), e1, e5, e6, eR0, eR8, ⟨9223372036854775829, by decide, eO, by decide⟩,
    ⟨(slot_parts μ' (F + 120) 0 8 (by omega)).1.trans eO, (slot_parts μ' (F + 120) 8 8 (by omega)).2.trans eO8⟩,
    fun a h0 h1 h2 h3 => efr a h0 (by omega) h2 (by omega), erd, ewr⟩

/-- `ElemOkF` for a decoder that also reads the core count at 196616: the same, given those octets readable. -/
def ElemOkFG (p : ByteArray) (P : Program) (F RD : Nat) (enc : List UInt8) (Rep : List UInt8 → Prop) : Prop :=
  ∀ (X : Type) (R : HostRel X) (x : X) (ω : Regs) (μ : Memory) (ptr len v5 v6 : Nat),
    (∀ a, 196616 ≤ a → a < 196618 → μ.readable a = true) →
    ω[1] = UInt64.ofNat F → ω[5] = UInt64.ofNat (F + 120) → ω[6] = UInt64.ofNat RD →
    ω[7] = UInt64.ofNat 0 → μ.read F = enc.headD 0 →
    μ.readN RD 8 = Num.encodeLE 8 ptr → μ.readN (RD + 8) 8 = Num.encodeLE 8 len →
    enc.length - 1 ≤ len → len < 4294967296 → 65536 ≤ ptr → ptr + enc.length + 72 ≤ 4278050816 →
    μ.readN ptr (enc.length - 1) = enc.tail →
    (∀ a, ptr ≤ a → a < ptr + (enc.length - 1) → μ.readable a = true) →
    μ.readN (F + 48) 8 = Num.encodeLE 8 18 → μ.readN (F + 40) 8 = Num.encodeLE 8 v5 →
    μ.readN (F + 32) 8 = Num.encodeLE 8 v6 → v5 < 18446744073709551616 → v6 < 18446744073709551616 →
    μ.readN 67476 100 = Decode.Tag.table → (∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true) →
    (∀ a, 4278050816 ≤ a → a < (F + 584) → μ.writable a = true) →
    (∀ a, RD ≤ a → a < (RD + 16) → μ.writable a = true) →
    ∃ ω' μ', FreeStepsH p R 20626 ω μ x 723 ω' μ' x 4000 ∧
      ω'[1] = UInt64.ofNat (F + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN RD 8 = Num.encodeLE 8 (ptr + (enc.length - 1)) ∧
      μ'.readN (RD + 8) 8 = Num.encodeLE 8 (len - (enc.length - 1)) ∧
      (∃ W, W < 18446744073709551616 ∧ μ'.readN (F + 120) 8 = Num.encodeLE 8 W ∧
        W ≠ 18446744073709551614) ∧
      Rep (μ'.readN (F + 120) 232) ∧
      (∀ a, a < 4294967296 → (a < 4278050816 ∨ (F + 32) ≤ a) → (a < RD ∨ (RD + 16) ≤ a) →
        (a < (F + 120) ∨ (F + 352) ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a)

/-- **`Designate { keys: [] }`** (tag 13, encoded [13, 0]). -/
theorem designate_emptyF {p : ByteArray} {P : Program} [HasCode p P] (F RD : Nat) (hL : Lay F RD) :
    ElemOkFG p P F RD [13, 0] (VecNilRep 9223372036854775820 1) := by
  have hL' := hL
  obtain ⟨l1, l2, l3, l4⟩ := hL'
  intro X R x ω μ ptr len v5 v6 hc h1 h5 h6 h7 tagr rP rL hlen hlen' hptr hpb pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_one_sub_one, List.headD_cons,
    List.tail_cons] at tagr hlen hptr hpb pay rpay ⊢
  have hzero : μ.read ptr = 0 := by simpa [Memory.readN] using pay
  obtain ⟨ω', μ', run, -, e1, e5, e6, eO, eO8, eO16, eO24, eR0, eR8, efr, erd, ewr⟩ :=
    Decode.Designate.designate_empty (p := p) (P := P) (R := R) x ω μ F (F + 120) 18 723 v5 v6 RD ptr len
      (loopFrame F RD hL ω μ v5 v6 h1 h5 s0 s5 s6 hv5 hv6 ws) (by omega) h6 h7 (by simpa using tagr) tab rt hc
      ⟨by omega, by omega⟩ ⟨hptr, by omega⟩ ⟨hlen, hlen'⟩ hzero rP rL (Or.inr (by omega))
      (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega)) (Or.inl (by omega)) (by omega)
      (fun a h1 h2 => ws a (by omega) (by omega)) wr (fun a h1 h2 => ws a (by omega) (by omega))
      (rpay ptr (Nat.le_refl _) (by omega))
  exact ⟨ω', μ', run.mono (by omega), e1, e5, e6, eR0, eR8, ⟨9223372036854775820, by decide, eO, by decide⟩,
    nil_rep eO eO8 eO16 eO24, fun a h0 h1 h2 h3 => efr a h0 (by omega) h2 (by omega), erd, ewr⟩

/-- `ElemOkAF.of_elemOkF` for `ElemOkFG`: the heap context makes the globals readable. -/
theorem of_elemOkFG {env : RefineHost.Env} {cap pb : Nat} {gl : Nat → UInt8} {p : ByteArray} {P : Program}
    {enc : List UInt8} {Rep : List UInt8 → Prop} {F RD : Nat}
    (hL : Lay F RD) (h : ElemOkFG p P F RD enc Rep) :
    ElemOkAF env cap pb gl p P F RD 4000 enc (fun bs _ => Rep bs) := by
  intro x ω μ ptr len v5 v6 s h1 h5 h6 h7 tag rP rL hl hl' hp hp' pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr H _ _
  obtain ⟨l1, l2, l3, l4⟩ := hL
  obtain ⟨ω', μ', run, e1, e5, e6, eR0, eR8, eW, eRep, efr, erd, ewr⟩ :=
    h RefineCtx (refineContractK cap env) x ω μ ptr len v5 v6
      (fun a h1 h2 => Memory.readable_of_writable (Decode.Designate.glob_writable' H ⟨by omega, by omega⟩)) h1 h5 h6 h7 tag rP rL hl hl' hp hp' pay rpay
      s0 s5 s6 hv5 hv6 tab rt ws wr
  have low : ∀ a, a < 2147483648 → μ'.read a = μ.read a := fun a ha =>
    efr a (by omega) (by omega) (by omega) (by omega)
  obtain ⟨ph, h48, hhb, hpg, hHTs, hHT⟩ := H.pages
  refine Or.inl ⟨ω', μ', s, run, e1, e5, e6, eR0, eR8, eW,
    { wf := H.wf, rep := H.rep.congr_lock H.wf H.hb0 H.hbT (fun a _ ha2 _ => low a ha2), fo := H.fo,
      lock := by rw [rdN_frame fun j hj => low _ (by omega)]; exact H.lock, hb0 := H.hb0, hbT := H.hbT,
      hA := H.hA, bd := H.bd, pages := ⟨ph, h48, hhb, HeapPages.of_eq hpg ewr, hHTs, hHT⟩, hSb := H.hSb,
      hS1 := H.hS1, st := fun a h1 h2 => by rw [ewr]; exact H.st a h1 h2,
      ro := fun a ha => by rw [ewr]; exact H.ro a ha },
    fun c hc _ => hc, fun c hc _ a ha => low a ?_, ⟨[], by simp, fun _ _ => eRep⟩,
    fun a h h0 h2 h3 => efr a h0 (Or.inr h) h2 h3, fun a ha => low a (by omega), fun a _ => erd a,
    fun a ha => low a (by unfold Glob at ha; omega), fun a _ => ewr a⟩
  have ht := H.wf.2.2.2.1
  unfold TilesOk at ht
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have := ht.mem_lt c hc
  have := H.hbT
  unfold InData at ha
  omega


end Services.Bootstrap.Refine.EmptyElems
