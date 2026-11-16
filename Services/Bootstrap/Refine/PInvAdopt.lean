import Services.Bootstrap.Refine.PassLoop

/-!
# The transform loop's state: adopting a fresh chunk

`PInv`'s kept chunks (`Kp`) hold their data as in the snapshot μ0. A handler that allocates a chunk owned by its output
slot (eager `Lookup`'s preimage) makes a chunk whose data is not in μ0. `PInv.adopt` takes it into the kept chunks by
rebasing the snapshot: μ0 with that chunk's data as it is now (`Memory.writeN`). Everything `PInv` reads of μ0 (the
input's chunk, the other kept chunks, the frame words) lies outside that chunk, so it is unchanged.
GP v0.8.0 Appendix B.4 (Ψ_R running bootstrap's code).
-/

namespace Services.Bootstrap.Refine.PassLoop

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

/-- The snapshot μ0 with chunk ch's data as in μ. -/
def snapWith (μ0 μ : Memory) (ch : Chunk) : Memory :=
  μ0.writeN (ch.addr + 32) (μ.readN (ch.addr + 32) (32 * (ch.size - 1)))

/-- Outside ch's data, the rebased snapshot reads as μ0. -/
theorem snapWith_out {μ0 μ : Memory} {ch : Chunk} (hch : ch.addr + 32 * ch.size ≤ 2147483648) (hsz : 0 < ch.size)
    {a : Nat} (ha : a < 4294967296) (hout : a < ch.addr + 32 ∨ ch.addr + 32 * ch.size ≤ a) :
    (snapWith μ0 μ ch).read a = μ0.read a := by
  unfold snapWith
  exact Memory.read_writeN_disjoint μ0 _ _ a (by simp; omega) (by simp; unfold two32; omega)
    (by unfold two32; omega)

/-- In ch's data, the rebased snapshot reads as μ. -/
theorem snapWith_in {μ0 μ : Memory} {ch : Chunk} (hch : ch.addr + 32 * ch.size ≤ 2147483648) {a : Nat}
    (ha : InData ch a) : (snapWith μ0 μ ch).read a = μ.read a := by
  unfold snapWith InData at *
  rw [Memory.read_writeN_readN μ0 μ _ _ _ a ha.1 (by omega) (by unfold two32; omega)]
  congr 1; omega

/-- **Adopting a fresh chunk**: `PInv` with snapshot μ0 and kept chunks `Kp` gives `PInv` with the snapshot rebased on
    the allocated chunk ch (`snapWith`) and ch kept too, when ch is not the input's chunk, not a kept chunk, and not the
    output's buffer. -/
theorem PInv.adopt {env : RefineHost.Env} {pb S0 S1 M E n : Nat} {ce : Chunk} {capI : Nat} {μ0 : Memory}
    {Kp : Chunk → Prop} {O : Nat → List UInt8 → Prop} {i k : Nat} {ω : Regs} {μ : Memory} {s : State}
    (st : PInv env pb S0 S1 M E n ce capI μ0 Kp O i k ω μ s) (hM : 2147483648 ≤ M ∧ M + 632 ≤ 4294967296)
    (ch : Chunk)
    (hch : ch ∈ chunks s) (hu : ch.used = true) (hce : ch ≠ ce) (hK : ∀ d, Kp d → d ≠ ch)
    (hob : ∀ c, μ.readN (M + 256) 8 = Num.encodeLE 8 (c.addr + 32) → c ∈ chunks s → c ≠ ch) :
    PInv env pb S0 S1 M E n ce capI (snapWith μ0 μ ch) (fun d => Kp d ∨ d = ch) O i k ω μ s := by
  have hwf := st.H.wf
  have hbT := st.H.hbT
  have hS1 := st.H.hS1
  obtain ⟨-, -, hchT⟩ := Decode.VecU8.chunk_in hwf hch hu
  have hsz : 0 < ch.size := by
    have ht := hwf.2.2.2.1
    unfold TilesOk at ht
    exact (ht.mem_lt ch hch).2.2
  have hT : ch.addr + 32 * ch.size ≤ 2147483648 := by omega
  -- data of another allocated chunk lies outside ch's
  have apart : ∀ d ∈ chunks s, d.used = true → d ≠ ch → ∀ a, InData d a → (snapWith μ0 μ ch).read a = μ0.read a := by
    intro d hd hdu hne a ha
    have hap := chunk_apart hwf hd hch hne
    have := Decode.VecU8.chunk_in hwf hd hdu
    unfold InData at ha
    exact snapWith_out hT hsz (by omega) (by omega)
  obtain ⟨cap, ptr, vc, vp, vl, hkc, hcapn, hptr, hold, hout⟩ := st.out
  refine
    { h1 := st.h1
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
      out := ⟨cap, ptr, vc, vp, vl, hkc, hcapn, hptr, ?_, hout⟩
      H := st.H
      hce := st.hce
      data := ?_
      kp := ?_
      fr := ?_ }
  · rcases hold with h | ⟨c, hc, hca, hcu, hcs, hcne, hcK⟩
    · exact Or.inl h
    · refine Or.inr ⟨c, hc, hca, hcu, hcs, hcne, fun h => ?_⟩
      rcases h with h | h
      · exact hcK h
      · exact hob c (by rw [hca]; exact vp) hc h
  · intro a ha
    rw [st.data a ha, apart ce st.hce.1 st.hce.2 (fun h => hce h.symm) a ha]
  · intro d hd
    rcases hd with hd | rfl
    · obtain ⟨hdm, hdu, kd⟩ := st.kp d hd
      exact ⟨hdm, hdu, fun a ha => by rw [kd a ha, apart d hdm hdu (hK d hd) a ha]⟩
    · exact ⟨hch, hu, fun a ha => (snapWith_in hT ha).symm⟩
  · intro a ha
    rw [st.fr a ha, snapWith_out hT hsz (by omega) (Or.inr (by omega))]

end Services.Bootstrap.Refine.PassLoop
