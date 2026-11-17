import Services.Bootstrap.Decode.ProvideInline
import Services.Bootstrap.Decode.Elems
import Services.Bootstrap.Refine.EmptyElems
import Services.Bootstrap.Refine.PkgT

/-!
# `Provide { service, preimage: Inline([]) }` as an element of the decode loop

The encoding 17 :: ℰ₄(s) ++ [1, 0] (GP v0.8.0 B.7): `Provide`'s `Inline` path (`Provide.pi_pre`, with n = 0), the
empty `read_vec` (`VecU8.vec_u8_empty`: nothing read or allocated, the `Vec` `{cap 0, ptr 1, len 0}`) and the store of
the variant (`Provide.pi_post`): the slot holds the discriminant 2^63 + 16, the tag 1, the empty `Vec` at 16 and the
service's octets at 48. `provide_inline_emptyF` is that, as a `Loop.ElemOkF`.
-/

namespace Services.Bootstrap.Refine.ProvideEmpty

open PVM Services.Bootstrap Services.Bootstrap.Code JAM Services.Bootstrap.Decode.Loop
  Services.Bootstrap.Decode.Elems Services.Bootstrap.Decode.Provide

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- The slot of `Provide(s, Inline [])`. -/
def ProvideEmptyRep (s : List UInt8) (bs : List UInt8) : Prop :=
  bs.take 8 = Num.encodeLE 8 9223372036854775824 ∧ (bs.drop 8).take 1 = [1] ∧
    (bs.drop 16).take 8 = Num.encodeLE 8 0 ∧ (bs.drop 24).take 8 = Num.encodeLE 8 1 ∧
    (bs.drop 32).take 8 = Num.encodeLE 8 0 ∧ (bs.drop 48).take 4 = s

theorem rd8' {μ : Memory} {a w : Nat} (hw : w < 18446744073709551616) (h : μ.readN a 8 = Num.encodeLE 8 w) :
    rdN μ a 8 = w := by
  unfold rdN; rw [h, Num.decodeLE_encodeLE]; omega

/-- **`Provide(s, Inline [])`** (tag 17, encoded 17 :: s ++ [1, 0]). -/
theorem provide_inline_emptyF {p : ByteArray} {P : Program} [HasCode p P] (F RD : Nat) (hL : Lay F RD)
    (s : List UInt8) (hs : s.length = 4) :
    ElemOkF p P F RD (17 :: (s ++ [1, 0])) (ProvideEmptyRep s) := by
  have hL' := hL
  obtain ⟨l1, l2, l3, l4⟩ := hL'
  intro X R x ω μ ptr len v5 v6 h1 h5 h6 h7 tagr rP rL hlen hlen' hptr hpb pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr
  have hl : (17 :: (s ++ [1, 0])).length - 1 = 6 := by simp [hs]
  simp only [hl, List.headD_cons, List.tail_cons] at tagr hlen hptr hpb pay rpay ⊢
  have Fr := loopFrame (p := p) (P := P) F RD hL ω μ v5 v6 h1 h5 s0 s5 s6 hv5 hv6 ws
  have hs4 : μ.readN ptr 4 = s := by
    rw [show μ.readN ptr 4 = μ.readN (ptr + 0) 4 by rfl, readN_sub μ ptr 6 0 4 _ pay (by omega), List.drop_zero,
      List.take_left' hs]
  have htail : μ.readN (ptr + 4) 2 = [1, 0] := by
    rw [readN_sub μ ptr 6 4 2 _ pay (by omega), List.drop_left' hs]; rfl
  have hinl : μ.read (ptr + 4) = 1 := by simp [Memory.readN, List.range_succ] at htail; exact htail.1
  have henc : μ.readN (ptr + 5) (Blob.encodeNat 0).length = Blob.encodeNat 0 := by
    have h1' : (Blob.encodeNat 0) = [0] := by decide
    rw [h1']
    simp [Memory.readN, List.range_succ] at htail
    simp [Memory.readN, htail.2]
  have hw1 : (Blob.encodeNat 0).length = 1 := by decide
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, atag, apark, a982, aO, ard, aR0, aR8, afr, ard', awr⟩ :=
    pi_pre (p := p) (P := P) (R := R) x ω μ F (F + 120) 18 723 v5 v6 RD ptr len 0 Fr ⟨by omega, l2⟩
      h6 h7 (by simpa using tagr) tab rt ⟨by omega, by omega⟩ ⟨by omega, by rw [hw1]; omega⟩ (by omega)
      ⟨by rw [hw1]; omega, hlen'⟩ hinl henc rP rL (Or.inr (by omega)) (Or.inl (by rw [hw1]; omega))
      (Or.inl (by rw [hw1]; omega)) (by omega) (fun a h1 h2 => ws a (by omega) (by omega)) wr
      (fun a h1 h2 => rpay a h1 (by rw [hw1] at h2; omega))
  rw [hw1] at aR0 aR8
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, bO, bO8, bO16, bfr, brd, bwr⟩ :=
    Decode.VecU8.vec_u8_empty (p := p) (P := P) (R := R) x ω1 μ1 (F - 152) (F - 152 + 80) RD (len - 5 - 1) 1168
      25153 (F + 120) RD ⟨by omega, by omega⟩ a0 a1 a5 a6 a7 a8 a9 (by omega) (by omega) (by decide) jte_583
      bs_25153 (by omega) (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (rd8' (by omega) aR8)
      (fun a h1 h2 => by rw [ard']; exact Memory.readable_of_writable (wr a (by omega) (by omega)))
      (fun a h1 h2 => by rw [awr]; exact ws a (by omega) (by omega))
      (fun a h1 h2 => by rw [awr]; exact ws a (by omega) (by omega))
  have k2 : ∀ a, a < 4294967296 → (a < F - 152 - 96 ∨ F - 152 ≤ a) → (a < F - 152 + 80 ∨ F - 152 + 104 ≤ a) →
      μ2.read a = μ1.read a := bfr
  have k21 : ∀ a, F - 152 ≤ a → a < F + 56 → (a < F - 152 + 80 ∨ F - 152 + 104 ≤ a) → (a < RD ∨ RD + 16 ≤ a) →
      μ2.read a = μ1.read a := fun a h1 h2 h3 _ => k2 a (by omega) (Or.inr h1) h3
  obtain ⟨ω3, μ3, run3, z0, z1, z5, z6, zO, zO8, zO16, zO24, zO32, zO48, zfr, zrd, zwr⟩ :=
    pi_post (p := p) (P := P) (R := R) x ω2 μ2 F (F + 120) 18 723 v5 v6 0 1 0 (rdN μ1 (F - 152 + 8) 8) RD
      ⟨by omega, by omega⟩ (by omega) (Or.inr (by omega)) b1 b5 (by decide) (by decide) (by decide) (rdN_lt64 _ _)
      (by omega)
      (by rw [show F - 152 + 80 = F - 152 + 80 by rfl]; exact bO)
      (by rw [show F - 152 + 88 = F - 152 + 80 + 8 by omega]; exact bO8)
      (by rw [show F - 152 + 96 = F - 152 + 80 + 16 by omega]; exact bO16)
      (by rw [Memory.readN_congr (fun j hj => k21 _ (by omega) (by omega) (by omega) (by omega))]; exact atag)
      (by rw [Memory.readN_congr (fun j hj => k21 _ (by omega) (by omega) (by omega) (by omega))]
          exact (encodeLE_rdN _ _ _).symm)
      (by rw [Memory.readN_congr (fun j hj => k21 _ (by omega) (by omega) (by omega) (by omega))]; exact a982)
      (by rw [Memory.readN_congr (fun j hj => k21 _ (by omega) (by omega) (by omega) (by omega))]; exact aO)
      (by rw [Memory.readN_congr (fun j hj => k21 _ (by omega) (by omega) (by omega) (by omega))]; exact ard)
      (by rw [Memory.readN_congr (fun j hj => (k21 _ (by omega) (by omega) (by omega) (by omega)).trans
            (afr _ (by omega) (by omega) (by omega)))]; exact Fr.s0)
      (by rw [Memory.readN_congr (fun j hj => (k21 _ (by omega) (by omega) (by omega) (by omega)).trans
            (afr _ (by omega) (by omega) (by omega)))]; exact Fr.s5)
      (by rw [Memory.readN_congr (fun j hj => (k21 _ (by omega) (by omega) (by omega) (by omega)).trans
            (afr _ (by omega) (by omega) (by omega)))]; exact Fr.s6)
      Fr.hret Fr.hjt Fr.hbt Fr.hv5 Fr.hv6
      (fun a h1 h2 => by rw [bwr, awr]; exact ws a (by omega) (by omega))
      (fun a h1 h2 => by rw [bwr, awr]; exact ws a (by omega) (by omega))
      (fun a h1 h2 => by rw [brd, ard']; exact Memory.readable_of_writable (ws a (by omega) (by omega)))
  have run := run1.trans (run2.trans run3)
  refine ⟨ω3, μ3, run.mono (by omega), z1, z5, z6, ?_, ?_, ⟨9223372036854775824, by decide, zO, by decide⟩,
    ⟨(slot_parts μ3 (F + 120) 0 8 (by omega)).1.trans zO, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [Memory.readN_congr (fun j hj => zfr _ (by omega) (by omega) (by omega)),
      Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega) (by omega))]; exact aR0
  · rw [Memory.readN_congr (fun j hj => zfr _ (by omega) (by omega) (by omega)),
      Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega) (by omega))]; exact aR8
  · rw [(slot_parts μ3 (F + 120) 8 1 (by omega)).2]; simp [Memory.readN, zO8]
  · exact (slot_parts μ3 (F + 120) 16 8 (by omega)).2.trans zO16
  · exact (slot_parts μ3 (F + 120) 24 8 (by omega)).2.trans zO24
  · exact (slot_parts μ3 (F + 120) 32 8 (by omega)).2.trans zO32
  · rw [(slot_parts μ3 (F + 120) 48 4 (by omega)).2, zO48, ← Decode.U32Hash.take_encodeLE, encodeLE_rdN, apark, hs4]
  · intro a h0 h1 h2 h3
    rw [zfr a h0 (by omega) (by omega), bfr a h0 (by omega) (by omega)]
    exact afr a h0 (by omega) h2
  · intro a; rw [zrd, brd, ard']
  · intro a; rw [zwr, bwr, awr]

section
open Picoalloc Services.Bootstrap.CodeX Services.Bootstrap.CodeA Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Encode.GrowH Services.Bootstrap.Refine.SlotT
  Services.Bootstrap.Refine.Pass Services.Bootstrap.Refine.PkgT

/-- **`Provide(s, Inline [])`'s decoded slot is good**, owning nothing. -/
theorem slotOK_provideInlineEmpty {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (C : Spec.Consts) (sv : Nat) (hw : (Spec.Instr.provide sv (.inline [])).WF C) (bs : List UInt8) (μr : Memory)
    (hE : ProvideEmptyRep (Codec.fixed 4 sv) bs) :
    SlotOK env K pb p P (DRt C 0) (Spec.Instr.provide sv (.inline [])).encode bs (fun _ => False) μr := by
  intro μ s el hel _
  obtain ⟨h0, h8, h16, h24, h32, h48⟩ := hE
  let R := EncProvide.ProvideInlineRepAt (Codec.fixed 4 sv) 0 1 []
  have hz : ∀ μ : Memory, μ.readN 1 0 = [] := fun μ => by simp [Memory.readN]
  have hloc : ∀ (bs : List UInt8) (μ μ' : Memory), (∀ q m, SrcAtP 1 0 q m →
      μ'.readN q m = μ.readN q m) → R bs μ → R bs μ' :=
    fun bs μ μ' _ ⟨e0, e1, e2, e8, e16, e24, _⟩ => ⟨e0, e1, e2, e8, e16, e24, hz μ'⟩
  have hrep : R (μ.readN el 232) μ :=
    ⟨by rw [hel]; exact h0, by rw [hel]; exact h8, by rw [hel]; exact h48, by rw [hel]; exact h16,
      by rw [hel]; exact h24, by rw [hel]; exact h32, hz μ⟩
  have henc : (Spec.Instr.provide sv (.inline [])).encode =
      17 :: (Codec.fixed 4 sv ++ 1 :: (Blob.encodeNat 0 ++ [])) := by
    simp [Spec.Instr.encode, Spec.bytes, Codec.nat]
  have rd := fun o l (hol : o + l ≤ 232) => Decode.Loop.readN_sub μ el 232 o l _ hel hol
  have r0 := rd 0 8 (by omega)
  simp only [Nat.add_zero, List.drop_zero] at r0
  rw [henc]
  refine ⟨R, R, SrcAtP 1 0,
    EncProvide.provide_inlineH env K pb hK1 hK (Codec.fixed 4 sv) 0 1 [] (by simp [Codec.fixed]) rfl (by decide)
      (by decide), hrep, hrep,
    fun bs μ h => ⟨.provide sv (.inline []), hw, (EncProvide.provideInlineRep_iff _ 0 [] bs μ).mpr ⟨_, h⟩⟩,
    hloc, hloc, fun q m h => absurd h.1 (by simp),
    Or.inr (Or.inr ⟨false, 1, ⟨0, 0, false⟩, ?_, by omega, fun h => absurd h (by simp)⟩)⟩
  refine Or.inr (Or.inr (Or.inl ⟨1, 0, by omega, by omega, by rw [r0]; exact h0,
    by rw [rd 8 1 (by omega)]; exact h8, by rw [rd 16 8 (by omega)]; exact h16,
    by rw [rd 24 8 (by omega)]; exact h24, by simp⟩))

/-- **`Provide(s, Inline [])`'s package.** -/
theorem pkg_provideInlineEmpty {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (gl : Nat → UInt8)
    (C : Spec.Consts) (sv : Nat) (hw : (Spec.Instr.provide sv (.inline [])).WF C) :
    DecPkg env K pb gl p P (.provide sv (.inline [])) (PassSlot env K pb p P C (.provide sv (.inline []))) := by
  have he : (Spec.Instr.provide sv (.inline [])).encode = 17 :: (Codec.fixed 4 sv ++ [1, 0]) := by
    simp [Spec.Instr.encode, Spec.bytes, Codec.nat]; rfl
  refine pkg_ofF (fun F RD hL => he ▸ provide_inline_emptyF F RD hL _ (by simp [Codec.fixed]))
    (fun cs bs μr hb => ?_)
  exact passSlot_noown _ (passW_idx (t := 17) (by unfold PassIdx; omega)) hb.1
    (slotOK_provideInlineEmpty env K pb hK1 hK C sv hw bs μr hb)

end

end Services.Bootstrap.Refine.ProvideEmpty
