import Services.Bootstrap.Decode.Elems
import Services.Bootstrap.Decode.LoopA
import Services.Bootstrap.Decode.CreateServiceHeap
import Services.Bootstrap.Decode.CreateServiceEmpty

/-!
# `CreateService`, as an element of the decode loop

`CreateService` (tag 0; GP v0.8.0 B.7, the bootstrap service's instruction list) with the encoding
`0 :: (h ++ u₁ ++ u₂ ++ u₃ ++ u₄ ++ arr ++ ov ++ u₅ ++ ou)` (h the 32-octet code hash, u₁ … u₄ and u₅
`u64`s, arr the 128-octet array, ov the `Option<Vec<u8>>`, ou the `Option<u32>`: [0], or 1 :: u with u
its 4 octets), stated at the decode loop's frame base F (the tag at F, the slot at F + 120, the reader
at RD, laid out as `Lay F RD`):

* `create_service_noneF`: ov = [0] (`None`), as an `ElemOkF`, and `create_service_none_elem`, the same as
  an `ElemOkAF` (nothing is allocated);
* `create_service_some_elem`: ov = 1 :: ℰ(n) ++ bytes (`Some(bytes)`, 1 ≤ n = |bytes| ≤ 16384), as an
  `ElemOkAF`, from `CreateService.create_service_heap`: the octets land in a fresh chunk of the heap, or
  the `alloc` fails;
* `create_service_empty_elem`: ov = [1, 0] (`Some([])`), as an `ElemOkAF` that allocates nothing (its
  run, 4400 steps, is longer than `ElemOkF`'s 4000, so it is not stated as an `ElemOkF`).

`CreateService` is the enum's dataful variant: there is no discriminant word, and the
`Option<Vec<u8>>`'s capacity word at the slot's start is the niche (2^64 − 1 for `None`).
-/

namespace Services.Bootstrap.Decode.CreateServiceElem

open PVM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc JAM
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA Services.Bootstrap.Decode.Loop
  Services.Bootstrap.Decode.Elems

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **`CreateService`'s slot, but for the `Option<Vec<u8>>`'s words** (at 0, 8, 16): the `Option<u32>`
    ou's tag as a `u32` at 24 and, for `Some`, its 4 octets at 28; the hash h at 32; the `u64`s u₁ … u₄ at
    64, 72, 80, 88; the array at 96; the `u64` u₅ at 224. -/
def CSFields (h u1 u2 u3 u4 arr u5 ou : List UInt8) (bs : List UInt8) : Prop :=
  (bs.drop 24).take 4 = Num.encodeLE 4 (ou.headD 0).toNat ∧ (ou.headD 0 = 1 → (bs.drop 28).take 4 = ou.tail) ∧
  (bs.drop 32).take 32 = h ∧ (bs.drop 64).take 8 = u1 ∧ (bs.drop 72).take 8 = u2 ∧
  (bs.drop 80).take 8 = u3 ∧ (bs.drop 88).take 8 = u4 ∧ (bs.drop 96).take 128 = arr ∧
  (bs.drop 224).take 8 = u5

/-- **`CreateService` with `Option<Vec<u8>>` = `None`'s slot**: the niche word 2^64 − 1 at 0, and
    `CSFields`. -/
def CreateServiceNoneRep (h u1 u2 u3 u4 arr u5 ou : List UInt8) (bs : List UInt8) : Prop :=
  bs.take 8 = Num.encodeLE 8 18446744073709551615 ∧ CSFields h u1 u2 u3 u4 arr u5 ou bs

/-- The shapes of an `Option<u32>`'s encoding: [0], or 1 :: u with u 4 octets. -/
def OptU32Enc (ou : List UInt8) : Prop := ou = [0] ∨ ∃ u : List UInt8, u.length = 4 ∧ ou = 1 :: u

theorem OptU32Enc.length {ou : List UInt8} (h : OptU32Enc ou) : 1 ≤ ou.length ∧ ou.length ≤ 5 := by
  rcases h with rfl | ⟨u, hu, rfl⟩ <;> simp [*]

/-- The pieces of `CreateService`'s payload (simp set). -/
macro "cs_pieces" : tactic => `(tactic| simp [List.drop_append, List.take_append, List.drop_eq_nil_of_le,
  List.take_of_length_le, *])

/-- A piece B of A ++ B ++ C, by position. -/
theorem piece {α : Type} (A B C : List α) (i m : Nat) (hi : A.length = i) (hm : B.length = m) :
    ((A ++ B ++ C).drop i).take m = B := by
  subst hi hm; simp

/-- The slot's fields from reads at O. -/
theorem cs_fields (μ : Memory) (O : Nat) (h u1 u2 u3 u4 arr u5 ou : List UInt8)
    (e24 : μ.readN (O + 24) 4 = Num.encodeLE 4 (ou.headD 0).toNat)
    (e28 : ou.headD 0 = 1 → μ.readN (O + 28) 4 = ou.tail)
    (e32 : μ.readN (O + 32) 32 = h) (e64 : μ.readN (O + 64) 8 = u1) (e72 : μ.readN (O + 72) 8 = u2)
    (e80 : μ.readN (O + 80) 8 = u3) (e88 : μ.readN (O + 88) 8 = u4) (e96 : μ.readN (O + 96) 128 = arr)
    (e224 : μ.readN (O + 224) 8 = u5) :
    CSFields h u1 u2 u3 u4 arr u5 ou (μ.readN O 232) := by
  refine ⟨?_, fun h1 => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(slot_parts μ O 24 4 (by decide)).2]; exact e24
  · rw [(slot_parts μ O 28 4 (by decide)).2]; exact e28 h1
  · rw [(slot_parts μ O 32 32 (by decide)).2]; exact e32
  · rw [(slot_parts μ O 64 8 (by decide)).2]; exact e64
  · rw [(slot_parts μ O 72 8 (by decide)).2]; exact e72
  · rw [(slot_parts μ O 80 8 (by decide)).2]; exact e80
  · rw [(slot_parts μ O 88 8 (by decide)).2]; exact e88
  · rw [(slot_parts μ O 96 128 (by decide)).2]; exact e96
  · rw [(slot_parts μ O 224 8 (by decide)).2]; exact e224

/-- **`CreateService { …, Option<Vec<u8>>: None, … }`** (tag 0): the encoding
    0 :: (h ++ u₁ ++ u₂ ++ u₃ ++ u₄ ++ arr ++ [0] ++ u₅ ++ ou) decodes to `CreateServiceNoneRep`. -/
theorem create_service_noneF {p : ByteArray} {P : Program} [HasCode p P] (F RD : Nat) (hL : Lay F RD)
    (h u1 u2 u3 u4 arr u5 ou : List UInt8) (hh : h.length = 32) (h1 : u1.length = 8) (h2 : u2.length = 8)
    (h3 : u3.length = 8) (h4 : u4.length = 8) (harr : arr.length = 128) (h5 : u5.length = 8)
    (hou : OptU32Enc ou) :
    ElemOkF p P F RD (0 :: (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ [0] ++ u5 ++ ou))
      (CreateServiceNoneRep h u1 u2 u3 u4 arr u5 ou) := by
  have hL' := hL
  obtain ⟨l1, l2, l3, l4⟩ := hL'
  have hol := hou.length
  intro X R x ω μ ptr len v5 v6 g1 g5 g6 g7 tag rP rL hlen hlen' hptr hpb pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr
  obtain ⟨k, hk⟩ : ∃ k, ou.length = k := ⟨_, rfl⟩
  have hL0 : (0 :: (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ [0] ++ u5 ++ ou)).length - 1 = 201 + k := by
    simp [hh, h1, h2, h3, h4, harr, h5, hk]; omega
  simp only [hL0, List.headD_cons, List.tail_cons] at tag hlen hptr hpb pay rpay ⊢
  have sub : ∀ i m, i + m ≤ 201 + k → μ.readN (ptr + i) m =
      ((h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ [0] ++ u5 ++ ou).drop i).take m :=
    fun i m him => readN_sub μ ptr (201 + k) i m _ pay him
  have hF : F = (F - 384) + 384 := by omega
  have Fr := loopFrame (p := p) (P := P) F RD hL ω μ v5 v6 g1 g5 s0 s5 s6 hv5 hv6 ws
  rw [hF] at Fr tag
  rw [show F - 384 + 384 + 120 = F + 120 by omega] at Fr
  have hnone : μ.read (ptr + 192) = 0 := by
    have e := sub 192 1 (by omega)
    have : ((h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ [0] ++ u5 ++ ou).drop 192).take 1 = [0] := by cs_pieces
    rw [this] at e
    simpa [Memory.readN] using e
  have hpay : μ.readN (ptr + 201) ou.length = ou := by
    rw [sub 201 ou.length (by omega)]
    cs_pieces
  obtain ⟨ω', μ', run, -, e1, e5, e6, eO, e24, e28, e32, e64, e72, e80, e88, e96, e224, eR0, eR8, efr, erd, ewr⟩ :=
    CreateService.create_service_none (p := p) (P := P) (R := R) x ω μ (F - 384) (F + 120) 18 723 v5 v6 RD ptr len ou
      Fr ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ g6 g7 tag tab rt ⟨by omega, by omega⟩ ⟨hptr, by omega⟩ hou
      ⟨by omega, hlen'⟩ rP rL hnone hpay (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => ws a (by omega) (by omega)) wr (fun a h1 h2 => ws a (by omega) (by omega))
      (fun a h1 h2 => rpay a h1 (by omega))
  refine ⟨ω', μ', run.mono (by omega), by rw [e1]; congr 1; omega, e5, e6, by rw [eR0]; congr 1; omega,
    by rw [eR8]; congr 1; omega, ⟨18446744073709551615, by decide, eO, by decide⟩,
    ⟨by rw [readN_take _ _ 232 8 (by decide)]; exact eO, cs_fields μ' (F + 120) h u1 u2 u3 u4 arr u5 ou e24 e28
      ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩, fun a h0 h1 h2 h3 => efr a h0 (by omega) h2 h3, erd, ewr⟩
  · rw [e32, show ptr = ptr + 0 by rfl, sub 0 32 (by omega)]; cs_pieces
  · rw [e64, sub 32 8 (by omega)]; cs_pieces
  · rw [e72, sub 40 8 (by omega)]; cs_pieces
  · rw [e80, sub 48 8 (by omega)]; cs_pieces
  · rw [e88, sub 56 8 (by omega)]; cs_pieces
  · rw [e96, sub 64 128 (by omega)]; cs_pieces
  · rw [e224, sub 193 8 (by omega)]; cs_pieces

/-- **`CreateService { …, Option<Vec<u8>>: None, … }`, as an `ElemOkAF`**: `create_service_noneF`, which
    allocates nothing. -/
theorem create_service_none_elem {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (cap pb : Nat) (gl : Nat → UInt8) (F RD : Nat) (hL : Lay F RD)
    (h u1 u2 u3 u4 arr u5 ou : List UInt8) (hh : h.length = 32) (h1 : u1.length = 8) (h2 : u2.length = 8)
    (h3 : u3.length = 8) (h4 : u4.length = 8) (harr : arr.length = 128) (h5 : u5.length = 8)
    (hou : OptU32Enc ou) :
    ElemOkAF env cap pb gl p P F RD 4000 (0 :: (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ [0] ++ u5 ++ ou))
      (fun bs _ => CreateServiceNoneRep h u1 u2 u3 u4 arr u5 ou bs) :=
  ElemOkAF.of_elemOkF hL (create_service_noneF F RD hL h u1 u2 u3 u4 arr u5 ou hh h1 h2 h3 h4 harr h5 hou)

/-- **`CreateService` with `Option<Vec<u8>>` = `Some(bytes)`'s slot**: the `Vec` `{cap n, ptr q, len n}`
    at 0 for some q whose n octets are `bytes` (in the heap μ), and `CSFields`. -/
def CreateServiceSomeRep (n : Nat) (bytes h u1 u2 u3 u4 arr u5 ou : List UInt8) (bs : List UInt8)
    (μ : Memory) : Prop :=
  (∃ q, bs.take 8 = Num.encodeLE 8 n ∧ (bs.drop 8).take 8 = Num.encodeLE 8 q ∧
    (bs.drop 16).take 8 = Num.encodeLE 8 n ∧ μ.readN q n = bytes) ∧ CSFields h u1 u2 u3 u4 arr u5 ou bs

/-- **`CreateService { …, Option<Vec<u8>>: Some(bytes), … }`, as an element of the decode loop** (tag 0):
    the encoding 0 :: (h ++ u₁ ++ u₂ ++ u₃ ++ u₄ ++ arr ++ (1 :: ℰ(n) ++ bytes) ++ u₅ ++ ou), with
    1 ≤ n = |bytes| ≤ 16384, decodes to `CreateServiceSomeRep`, the octets a fresh chunk of the heap; or
    the `alloc` fails. -/
theorem create_service_some_elem {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (cap pb : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (gl : Nat → UInt8)
    (F RD : Nat) (hL : Lay F RD)
    (h u1 u2 u3 u4 arr u5 ou : List UInt8) (hh : h.length = 32) (h1 : u1.length = 8) (h2 : u2.length = 8)
    (h3 : u3.length = 8) (h4 : u4.length = 8) (harr : arr.length = 128) (h5 : u5.length = 8)
    (hou : OptU32Enc ou) (n : Nat) (hn : 1 ≤ n ∧ n ≤ 16384) (bytes : List UInt8) (hb : bytes.length = n) :
    ElemOkAF env cap pb gl p P F RD (2 * n + 5600)
      (0 :: (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ (1 :: (Blob.encodeNat n ++ bytes)) ++ u5 ++ ou))
      (CreateServiceSomeRep n bytes h u1 u2 u3 u4 arr u5 ou) := by
  intro x ω μ ptr len v5 v6 st g1 g5 g6 g7 tag rP rL hl hl' hp hp' pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr H _
    ⟨cp, hcp, hcpu, hcpl, hcph⟩
  have Fr := loopFrame (p := p) (P := P) F RD hL ω μ v5 v6 g1 g5 s0 s5 s6 hv5 hv6 ws
  obtain ⟨l1, l2, l3, l4⟩ := hL
  have hol := hou.length
  obtain ⟨w, hW⟩ : ∃ w, (Blob.encodeNat n).length = w := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, ou.length = k := ⟨_, rfl⟩
  have hL0 : (0 :: (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ (1 :: (Blob.encodeNat n ++ bytes)) ++ u5 ++ ou)).length - 1
      = 201 + w + n + k := by
    simp [hh, h1, h2, h3, h4, harr, h5, hk, hW, hb]; omega
  simp only [hL0, List.headD_cons, List.tail_cons] at tag hl hp' pay rpay hcph ⊢
  have sub : ∀ i m, i + m ≤ 201 + w + n + k → μ.readN (ptr + i) m =
      ((h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ (1 :: (Blob.encodeNat n ++ bytes)) ++ u5 ++ ou).drop i).take m :=
    fun i m him => readN_sub μ ptr (201 + w + n + k) i m _ pay him
  have hF : F = (F - 384) + 384 := by omega
  rw [hF] at Fr tag
  rw [show F - 384 + 384 + 120 = F + 120 by omega] at Fr
  have hsome : μ.read (ptr + 192) = 1 := by
    have e := sub 192 1 (by omega)
    have : ((h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ (1 :: (Blob.encodeNat n ++ bytes)) ++ u5 ++ ou).drop 192).take 1
        = [1] := by cs_pieces
    rw [this] at e
    simpa [Memory.readN] using e
  have henc : μ.readN (ptr + 193) (Blob.encodeNat n).length = Blob.encodeNat n := by
    rw [sub 193 _ (by omega)]
    rw [show h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ (1 :: (Blob.encodeNat n ++ bytes)) ++ u5 ++ ou =
      (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ [1]) ++ Blob.encodeNat n ++ (bytes ++ u5 ++ ou) by simp]
    exact piece _ _ _ _ _ (by simp [hh, h1, h2, h3, h4, harr]) rfl
  have hitems : μ.readN (ptr + 193 + w) n = bytes := by
    rw [show ptr + 193 + w = ptr + (193 + w) by omega, sub (193 + w) n (by omega)]
    rw [show h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ (1 :: (Blob.encodeNat n ++ bytes)) ++ u5 ++ ou =
      (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ [1] ++ Blob.encodeNat n) ++ bytes ++ (u5 ++ ou) by simp]
    exact piece _ _ _ _ _ (by simp [hh, h1, h2, h3, h4, harr, hW]; omega) hb
  have hu5 : μ.readN (ptr + 193 + w + n) 8 = u5 := by
    rw [show ptr + 193 + w + n = ptr + (193 + w + n) by omega, sub (193 + w + n) 8 (by omega)]
    exact piece _ _ _ _ _ (by simp [hh, h1, h2, h3, h4, harr, hW, hb]; omega) h5
  have hpay : μ.readN (ptr + 201 + w + n) ou.length = ou := by
    rw [show ptr + 201 + w + n = ptr + (201 + w + n) by omega, sub (201 + w + n) ou.length (by omega)]
    rw [← List.append_nil (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ (1 :: (Blob.encodeNat n ++ bytes)) ++ u5 ++ ou)]
    exact piece _ _ _ _ _ (by simp [hh, h1, h2, h3, h4, harr, hW, hb, h5]; omega) rfl
  rcases CreateService.create_service_heap (p := p) (P := P) (hb := 0) env cap hcap1 hcap x ω μ st (F - 384)
      (F + 120) 18 723 v5 v6 RD ptr len n pb S0 S1 ou Fr g6 g7 tag tab rt H (by unfold S0; omega)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by unfold S1; omega⟩ hn hou
      ⟨by rw [hW]; omega, hl'⟩ ⟨cp, hcp, hcpu, hcpl, by rw [hW]; omega⟩ rP rL hsome henc
      (by rw [hW]; exact hpay) with
    ⟨q, s', ω', μ', ha, run, -, e1, e5, e6, eO, eO8, eO16, edat, e24, e28, e32, e64, e72, e80, e88, e96, e224,
      eR0, eR8, H', keep, hnew, hfresh, kd, efr, elo, egl, ewr⟩ | ⟨hna, ω', μ', run, f7⟩
  · rw [hW] at edat eR0 eR8 e224
    refine Or.inl ⟨ω', μ', s', run, by rw [e1]; congr 1; omega, e5, e6, by rw [eR0]; congr 1; omega,
      by rw [eR8]; congr 1; omega, ⟨n, by omega, eO, by omega⟩, H', keep, kd, ?_,
      fun a h0 h1 h2 h3 => efr a h1 (by omega) h2 (by omega), fun a ha => (elo a ha).1,
      fun a ha => (elo a ha).2, egl, fun a ha => ewr a (by unfold S0; omega)⟩
    refine ⟨[⟨q - 32, (n + 31) / 32 + 1, true⟩], fun c hc => ?_, fun μ'' hag => ?_⟩
    · simp only [List.mem_singleton] at hc
      subst hc
      exact ⟨hnew, rfl, hfresh⟩
    · have hqm := VecU8.chunk_in H'.wf hnew rfl
      have hb' := H'.hb0
      simp only at hqm
      refine ⟨⟨q, by rw [readN_take _ _ 232 8 (by decide)]; exact eO, ?_, ?_, ?_⟩,
        cs_fields μ' (F + 120) h u1 u2 u3 u4 arr u5 ou e24 e28 ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
      · rw [← readN_sub μ' (F + 120) 232 8 8 _ rfl (by decide)]; exact eO8
      · rw [← readN_sub μ' (F + 120) 232 16 8 _ rfl (by decide)]; exact eO16
      · rw [Memory.readN_congr (fun j hj => hag _ (List.mem_singleton.mpr rfl) _
          ⟨by simp only; omega, by simp only; omega⟩), edat]
        exact hitems
      · rw [e32, show ptr = ptr + 0 by rfl, sub 0 32 (by omega)]; cs_pieces
      · rw [e64, sub 32 8 (by omega)]; cs_pieces
      · rw [e72, sub 40 8 (by omega)]; cs_pieces
      · rw [e80, sub 48 8 (by omega)]; cs_pieces
      · rw [e88, sub 56 8 (by omega)]; cs_pieces
      · rw [e96, sub 64 128 (by omega)]; cs_pieces
      · rw [e224]; exact hu5
  · exact Or.inr ((Exhausts.of_alloc run f7 hna).mono (by omega))

/-- **`CreateService` with `Option<Vec<u8>>` = `Some([])`'s slot**: the empty `Vec` `{cap 0, ptr 1, len 0}`
    at 0, and `CSFields`. -/
def CreateServiceEmptyRep (h u1 u2 u3 u4 arr u5 ou : List UInt8) (bs : List UInt8) : Prop :=
  bs.take 8 = Num.encodeLE 8 0 ∧ (bs.drop 8).take 8 = Num.encodeLE 8 1 ∧ (bs.drop 16).take 8 = Num.encodeLE 8 0 ∧
  CSFields h u1 u2 u3 u4 arr u5 ou bs

/-- **`CreateService { …, Option<Vec<u8>>: Some([]), … }`, as an element of the decode loop** (tag 0):
    the encoding 0 :: (h ++ u₁ ++ u₂ ++ u₃ ++ u₄ ++ arr ++ [1, 0] ++ u₅ ++ ou) decodes to
    `CreateServiceEmptyRep`, nothing allocated (the allocator's state kept, as in
    `LoopA.ElemOkAF.of_elemOkF`). -/
theorem create_service_empty_elem {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (cap pb : Nat) (gl : Nat → UInt8) (F RD : Nat) (hL : Lay F RD)
    (h u1 u2 u3 u4 arr u5 ou : List UInt8) (hh : h.length = 32) (h1 : u1.length = 8) (h2 : u2.length = 8)
    (h3 : u3.length = 8) (h4 : u4.length = 8) (harr : arr.length = 128) (h5 : u5.length = 8)
    (hou : OptU32Enc ou) :
    ElemOkAF env cap pb gl p P F RD 4400 (0 :: (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ [1, 0] ++ u5 ++ ou))
      (fun bs _ => CreateServiceEmptyRep h u1 u2 u3 u4 arr u5 ou bs) := by
  have hL' := hL
  obtain ⟨l1, l2, l3, l4⟩ := hL'
  have hol := hou.length
  intro x ω μ ptr len v5 v6 s g1 g5 g6 g7 tag rP rL hlen hlen' hptr hpb pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr H _ _
  obtain ⟨k, hk⟩ : ∃ k, ou.length = k := ⟨_, rfl⟩
  have hL0 : (0 :: (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ [1, 0] ++ u5 ++ ou)).length - 1 = 202 + k := by
    simp [hh, h1, h2, h3, h4, harr, h5, hk]; omega
  simp only [hL0, List.headD_cons, List.tail_cons] at tag hlen hptr hpb pay rpay ⊢
  have sub : ∀ i m, i + m ≤ 202 + k → μ.readN (ptr + i) m =
      ((h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ [1, 0] ++ u5 ++ ou).drop i).take m :=
    fun i m him => readN_sub μ ptr (202 + k) i m _ pay him
  have hF : F = (F - 384) + 384 := by omega
  have Fr := loopFrame (p := p) (P := P) F RD hL ω μ v5 v6 g1 g5 s0 s5 s6 hv5 hv6 ws
  rw [hF] at Fr tag
  rw [show F - 384 + 384 + 120 = F + 120 by omega] at Fr
  have hsome : μ.read (ptr + 192) = 1 := by
    have e := sub 192 1 (by omega)
    have : ((h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ [1, 0] ++ u5 ++ ou).drop 192).take 1 = [1] := by cs_pieces
    rw [this] at e
    simpa [Memory.readN] using e
  have hzero : μ.read (ptr + 193) = 0 := by
    have e := sub 193 1 (by omega)
    have : ((h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ [1, 0] ++ u5 ++ ou).drop 193).take 1 = [0] := by cs_pieces
    rw [this] at e
    simpa [Memory.readN] using e
  have hpay : μ.readN (ptr + 202) ou.length = ou := by
    rw [sub 202 ou.length (by omega)]
    cs_pieces
  obtain ⟨ω', μ', run, -, e1, e5, e6, eO, eO8, eO16, e24, e28, e32, e64, e72, e80, e88, e96, e224, eR0, eR8, efr,
      erd, ewr⟩ :=
    CreateService.create_service_empty (p := p) (P := P) (R := refineContractK cap env) x ω μ (F - 384) (F + 120) 18
      723 v5 v6 RD ptr len ou Fr ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ g6 g7 tag tab rt ⟨by omega, by omega⟩
      ⟨hptr, by omega⟩ hou ⟨by omega, hlen'⟩ rP rL hsome hzero hpay (by omega) (by omega) (by omega) (by omega)
      (by omega) (fun a h1 h2 => ws a (by omega) (by omega)) wr (fun a h1 h2 => ws a (by omega) (by omega))
      (fun a h1 h2 => rpay a h1 (by omega))
  have eRep : CreateServiceEmptyRep h u1 u2 u3 u4 arr u5 ou (μ'.readN (F + 120) 232) := by
    refine ⟨by rw [readN_take _ _ 232 8 (by decide)]; exact eO, ?_, ?_,
      cs_fields μ' (F + 120) h u1 u2 u3 u4 arr u5 ou e24 e28 ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
    · rw [← readN_sub μ' (F + 120) 232 8 8 _ rfl (by decide)]; exact eO8
    · rw [← readN_sub μ' (F + 120) 232 16 8 _ rfl (by decide)]; exact eO16
    · rw [e32, show ptr = ptr + 0 by rfl, sub 0 32 (by omega)]; cs_pieces
    · rw [e64, sub 32 8 (by omega)]; cs_pieces
    · rw [e72, sub 40 8 (by omega)]; cs_pieces
    · rw [e80, sub 48 8 (by omega)]; cs_pieces
    · rw [e88, sub 56 8 (by omega)]; cs_pieces
    · rw [e96, sub 64 128 (by omega)]; cs_pieces
    · rw [e224, sub 194 8 (by omega)]; cs_pieces
  -- nothing allocated: the allocator's context kept, as in `ElemOkAF.of_elemOkF`
  have low : ∀ a, a < 2147483648 → μ'.read a = μ.read a := fun a ha =>
    efr a (by omega) (by omega) (by omega) (by omega)
  obtain ⟨ph, h48, hhb, hpg, hHTs, hHT⟩ := H.pages
  refine Or.inl ⟨ω', μ', s, run, by rw [e1]; congr 1; omega, e5, e6, by rw [eR0]; congr 1; omega,
    by rw [eR8]; congr 1; omega, ⟨0, by decide, eO, by decide⟩,
    { wf := H.wf, rep := H.rep.congr_lock H.wf H.hb0 H.hbT (fun a _ ha2 _ => low a ha2), fo := H.fo,
      lock := by rw [rdN_frame fun j hj => low _ (by omega)]; exact H.lock, hb0 := H.hb0, hbT := H.hbT,
      hA := H.hA, bd := H.bd, pages := ⟨ph, h48, hhb, HeapPages.of_eq hpg ewr, hHTs, hHT⟩, hSb := H.hSb,
      hS1 := H.hS1, st := fun a h1 h2 => by rw [ewr]; exact H.st a h1 h2,
      ro := fun a ha => by rw [ewr]; exact H.ro a ha },
    fun c hc _ => hc, fun c hc _ a ha => low a ?_, ⟨[], by simp, fun _ _ => eRep⟩,
    fun a h h0 h2 h3 => efr a h0 (by omega) h2 h3, fun a ha => low a (by omega), fun a _ => erd a,
    fun a ha => low a (by unfold Glob at ha; omega), fun a _ => ewr a⟩
  have ht := H.wf.2.2.2.1
  unfold TilesOk at ht
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have := ht.mem_lt c hc
  have := H.hbT
  unfold InData at ha
  omega

end Services.Bootstrap.Decode.CreateServiceElem
