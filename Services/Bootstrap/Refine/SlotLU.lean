import Services.Bootstrap.Refine.SlotT
import Services.Bootstrap.Encode.ArmsH
import Services.Bootstrap.Encode.ArmsHFixed
import Services.Bootstrap.Encode.ArmsHFixed2
import Services.Bootstrap.Refine.LoopT

/-!
# T1c's `LookedUp` output slots

`slotW_lu`: an output slot holding `LookedUp(v)` (`LoopT.LUSlotB`: the discriminant 2^63 + 17, then `None`'s niche
word, or `Some(Vec)` {|d|, buf, |d|} with d at buf in a chunk the slot owns, or buf anything for d = []) is what the exit
needs (`SlotT.SlotW`): the encoder arm `looked_up_noneH` / `looked_up_someH`, the `Debug` predicate, and the drop's
`LUAt`. It serves both the eager `Lookup` step's slot and a passed-through `LookedUp`. GP v0.8.0 Appendix C (ℰ).
-/

namespace Services.Bootstrap.Refine.SlotLU

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeA
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA Services.Bootstrap.Encode.GrowH
  Services.Bootstrap.Refine.SlotT Services.Bootstrap.Refine.LoopT
  Services.Bootstrap.Refine.DropVecH Services.Bootstrap.Refine.DropVecW

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **A `LookedUp(v)` output slot is what the exit needs**: the slot at el holds `LookedUp(v)` with buffer word buf;
    for v = some d with d ≠ [], d lies at buf in an owned allocated chunk. -/
theorem slotW_lu {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (C : Spec.Consts) (v : Option (List UInt8)) (hv : ∀ d, v = some d → d.length < 4294967296)
    (buf : Nat) (hbuf : buf < 18446744073709551616) (el : Nat) (μ : Memory) (s : State) (own : Chunk → Prop)
    (hb : LUSlotB (μ.readN el 232) v buf)
    (hd : ∀ d, v = some d → d ≠ [] → μ.readN buf d.length = d ∧ ∃ ch, own ch ∧ ch ∈ chunks s ∧
      ch.used = true ∧ ch.addr + 32 = buf ∧ buf + d.length ≤ ch.addr + 32 * ch.size) :
    SlotW env K pb p P (DRt C 0) (Spec.Instr.lookedUp v).encode el μ s own := by
  have r := fun o l (hol : o + l ≤ 232) => Decode.Loop.readN_sub μ el 232 o l _ rfl hol
  have r0 := r 0 8 (by omega)
  simp only [Nat.add_zero, List.drop_zero] at r0
  obtain ⟨b0, b1⟩ := hb
  cases v with
  | none =>
    refine ⟨fun bs _ => bs.take 8 = Num.encodeLE 8 9223372036854775825 ∧
        (bs.drop 8).take 8 = Num.encodeLE 8 18446744073709551615,
      fun bs _ => bs.take 8 = Num.encodeLE 8 9223372036854775825 ∧
        (bs.drop 8).take 8 = Num.encodeLE 8 18446744073709551615, fun _ _ => False,
      (looked_up_noneH env K pb hK1 hK).mono (by decide), ⟨b0, b1⟩, ⟨b0, b1⟩,
      fun bs μ h => ⟨.lookedUp none, ⟨by simp [Spec.Instr.WF], h⟩⟩, fun _ _ _ _ h => h, fun _ _ _ _ h => h,
      fun _ _ h => h.elim, Or.inr (Or.inl (Or.inr ⟨18446744073709551615, rdN μ (el + 16) 8, ⟨0, 0, false⟩,
        by rw [r0]; exact b0, by rw [r 8 8 (by omega)]; exact b1, ?_, rdN_lt64 _ _, Or.inl rfl⟩))⟩
    rw [encodeLE_rdN]
  | some d =>
    obtain ⟨b8, b16, b24⟩ := b1
    have hdl := hv d rfl
    have hloc : ∀ (bs : List UInt8) (μ μ' : Memory), (∀ q m, Encode.GrowH.SrcAtP buf d.length q m →
        μ'.readN q m = μ.readN q m) → Encode.Enc.LookedUpSomeRepAt buf d.length d bs μ →
        Encode.Enc.LookedUpSomeRepAt buf d.length d bs μ' := by
      rintro bs μ μ' hk ⟨e0, e8, e16, e24, e⟩
      refine ⟨e0, e8, e16, e24, ?_⟩
      rcases Nat.eq_zero_or_pos d.length with h0 | h0
      · rw [h0] at e ⊢; simp only [Memory.readN, List.range_zero, List.map_nil] at e ⊢; exact e
      · rw [hk buf d.length ⟨h0, rfl, rfl⟩]; exact e
    have hrep : Encode.Enc.LookedUpSomeRepAt buf d.length d (μ.readN el 232) μ := by
      refine ⟨b0, b8, b16, b24, ?_⟩
      by_cases hne : d = []
      · subst hne; simp [Memory.readN]
      · exact (hd d rfl hne).1
    have henc : (Spec.Instr.lookedUp (some d)).encode = 18 :: 1 :: (Blob.encodeNat d.length ++ d) := by
      simp [Spec.Instr.encode, Spec.opt, Spec.bytes, Codec.nat]
    rw [henc]
    refine ⟨Encode.Enc.LookedUpSomeRepAt buf d.length d, Encode.Enc.LookedUpSomeRepAt buf d.length d,
      Encode.GrowH.SrcAtP buf d.length,
      (looked_up_someH env K pb hK1 hK buf d.length d rfl hdl hbuf).mono (by decide), hrep, hrep,
      fun bs μ h => ⟨.lookedUp (some d), ⟨by simp [Spec.Instr.WF, Spec.short, hdl],
        (Encode.Enc.lookedUpSomeRep_iff d.length d bs μ).mpr ⟨buf, h⟩⟩⟩, hloc, hloc, ?_, ?_⟩
    · rintro q m ⟨h0, rfl, rfl⟩
      have hne : d ≠ [] := fun e => by subst e; simp at h0
      obtain ⟨-, ch, ho, -, -, ha, hs⟩ := hd d rfl hne
      exact ⟨ch, ho, by omega, hs⟩
    · refine Or.inr (Or.inl (Or.inr ⟨d.length, buf, ?_⟩))
      by_cases hne : d = []
      · subst hne
        exact ⟨⟨0, 0, false⟩, by rw [r0]; exact b0, by rw [r 8 8 (by omega)]; exact b8,
          by rw [r 16 8 (by omega)]; exact b16, hbuf, Or.inr (Or.inl rfl)⟩
      · obtain ⟨-, ch, ho, hm, hu, ha, -⟩ := hd d rfl hne
        exact ⟨ch, by rw [r0]; exact b0, by rw [r 8 8 (by omega)]; exact b8, by rw [r 16 8 (by omega)]; exact b16,
          hbuf, Or.inr (Or.inr ⟨by omega, hm, hu, ha, ho⟩)⟩

end Services.Bootstrap.Refine.SlotLU
