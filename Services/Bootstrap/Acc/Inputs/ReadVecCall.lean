import Services.Bootstrap.Acc.Inputs.ReadVec
import Services.Bootstrap.Acc.Inputs.FinishGrowCall
import Services.Bootstrap.Alloc.ReallocFallbackTail

/-!
# One call of accumulate's `Vec<u8>` reader (45643) for 1 … 16384 octets, on the allocator's context

`rv_call`: the reader's `len` octets, inside an allocated chunk, are copied into a fresh block, and
`Vec { cap: len, ptr, len }` is written at `out`. The context `HeapCtxC` is kept for the model's
new state, every allocated chunk keeps its data, and the reader is advanced by `len`. Or the
model's `alloc` fails and the run reaches the trap at 45975 (`handle_error`): heap exhaustion.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- An allocated chunk's data. -/
def InDataA (c : Chunk) (a : Nat) : Prop := c.addr + 32 ≤ a ∧ a < c.addr + 32 * c.size

/-- **An allocated chunk's data is writable** (`LoopA.heap_writable_data` on `HeapCtxC`). -/
theorem heapC_writable_data {code : ByteArray} {pb S0 S1 : Nat} {μ : Memory} {s : State}
    (H : HeapCtxC code pb S0 S1 μ s) {c : Chunk} (hc : c ∈ chunks s) (hu : c.used = true) {a : Nat}
    (ha : InDataA c a) : μ.writable a = true := by
  obtain ⟨ph, h48, hhb, hp, hHTs, hHT⟩ := H.pages
  have hsp := H.wf.2.2.2.2.2.2.2
  unfold SpaceOk at hsp
  have h1 := (hsp c hc).1 hu
  have ht := H.wf.2.2.2.1
  unfold TilesOk at ht
  have hm := ht.mem_lt c hc
  have := H.hb0
  unfold InDataA at ha
  have hq := hp (a / 4096) (by omega) (by omega)
  unfold Memory.writable
  rw [show pageSize = 4096 from rfl, hq]
  simp only [decide_eq_true_eq]; omega

/-- **41175 … 45975**, `finish_grow` wrote `Err` (tag 1 at b + 48): the return to 45773 and the
    branch to the trap at 45975 (`handle_error`). -/
theorem rv_fail {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (b : Nat) (h0 : ω[0] = UInt64.ofNat 2058) (h1 : ω[1] = UInt64.ofNat b)
    (m48 : rdN μ (b + 48) 8 = 1) (hb : b + 96 < 4294967296)
    (hrb : ∀ a, b ≤ a → a < b + 96 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 41175 ω μ x 45975 ω' μ x 5 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run⟩
  case run => pvm_go [h0, h1, m48, hrb, ↓rdN_fold, ↓loadI_fold]


/-- **One call of the `Vec<u8>` reader for 1 … 16384 octets** on `HeapCtxC` (see the module doc).
    The reader `rd` (pointer ip, length rlen) and `out` lie in the caller's frame (from sp up); the
    octets ip … ip + len lie in an allocated chunk's data. -/
theorem rv_call {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : HeapHost X)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    (x : X) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (sp out rd ip rlen len pb S0 S1 : Nat)
    (H : HeapCtxC env.code pb S0 S1 μ s)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat out) (h8 : ω[8] = UInt64.ofNat rd)
    (h9 : ω[9] = UInt64.ofNat len)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ip) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 rlen)
    (hlen : 0 < len ∧ len ≤ 16384) (hrl : len ≤ rlen) (hrl32 : rlen < 4294967296)
    (hsrc : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ip ∧ ip + len ≤ c.addr + 32 * c.size)
    (hsp : 2147483936 ≤ sp ∧ sp % 8 = 0) (hSTk : S0 + 288 ≤ sp)
    (hout : sp ≤ out ∧ out + 24 ≤ S1) (hrd : sp ≤ rd ∧ rd + 16 ≤ S1)
    (dor : out + 24 ≤ rd ∨ rd + 16 ≤ out) :
    (∃ ptr s' ω' μ', alloc (growTo pb) hb 1 ((len + 31) / 32) s = some (ptr, s') ∧
      FreeStepsH p (env.rel cap) 45643 ω μ x 45950 ω' μ' x (7 * len + 1200) ∧
      HeapCtxC env.code pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (⟨ptr - 32, (len + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ ⟨ptr - 32, (len + 31) / 32 + 1, true⟩) ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InDataA c a → μ'.read a = μ.read a) ∧
      rdN μ' out 8 = len ∧ rdN μ' (out + 8) 8 = ptr ∧ rdN μ' (out + 16) 8 = len ∧
      μ'.readN ptr len = μ.readN ip len ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ip + len) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (rlen - len) ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < out ∨ out + 24 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
        μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6]) ∨
    (alloc (growTo pb) hb 1 ((len + 31) / 32) s = none ∧ ∃ ω' μ',
      FreeStepsH p (env.rel cap) 45643 ω μ x 45975 ω' μ' x (7 * len + 1200)) := by
  obtain ⟨ph, h48, hhb, hp, hHTs, hHT⟩ := H.pages
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst := H.st
  have rdN_of : ∀ (μ0 : Memory) (a v : Nat), μ0.readN a 8 = Num.encodeLE 8 v → v < 18446744073709551616 →
      rdN μ0 a 8 = v := fun μ0 a v h hv => by
    unfold rdN; rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (by simpa using hv)]
  -- 1. the entry
  obtain ⟨ω1, μ1, r1, a1, a7, a8, a9, a10, a11, a12, a0, a5, a6, sl0, sl40, s8, s16, s24, s88, s80,
      fr1, rd1, wr1⟩ :=
    rv_entry (p := p) (P := P) (R := env.rel cap) x ω μ sp out rd rlen len h1 h7 h8 h9
      (rdN_of μ _ _ hR8 (by omega)) hlen hrl (by omega) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega))) (Or.inr hrd.1)
      (fun a h1 h2 => hst a (by omega) (by omega))
  have H1 : HeapCtxC env.code pb S0 S1 μ1 s :=
    ⟨H.wf, H.rep.congr_lock H.wf H.hb0 H.hbT fun a _ ha2 _ => fr1 a (by omega) (Or.inl (by omega)), H.fo,
      by rw [rdN_frame fun j hj => fr1 _ (by omega) (Or.inl (by omega))]; exact H.lock, H.hb0, H.hbT, H.hA,
      H.bd, ⟨ph, h48, hhb, HeapPages.of_eq hp wr1, hHTs, hHT⟩, hSb, hS1,
      fun a h1 h2 => by rw [wr1]; exact hst a h1 h2, fun a ha => by rw [wr1]; exact H.ro a ha⟩
  -- 2. `finish_grow` for `len` octets, no current block
  have e1 : len * 1 = len := Nat.mul_one len
  rcases fg_new_call (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω1 μ1 s (sp - 96) (sp - 96 + 48) len 1 1
      pb S0 S1 H1 a1 (by rw [a7]; congr 1; omega) a8 a10 a11 a12 ⟨Nat.le_refl _, by decide⟩ (by omega) (by omega)
      (by omega) (by omega) ⟨by omega, by omega⟩ with
    ⟨ptr, s', ω2, μ2, ha, r2, H2, keep, hnew, hfresh, hk, o0, o8, o16, fr2, e0, e1', e5, e6⟩ |
    ⟨ha, ω2, μ2, r2, H2, o0, o8, o16, fr2, e0, e1', e5, e6⟩
  · left
    rw [e1] at ha hnew hfresh o16
    have hb' := alloc_base H.wf ha
    obtain ⟨c, hcm, hcu, hci1, hci2⟩ := hsrc
    have hcm' := keep c hcm hcu
    have hcs := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hcm hcu
    have hns := Services.Bootstrap.Decode.VecU8.chunk_in H2.wf hnew rfl
    simp only at hns
    have hne : c ≠ ⟨ptr - 32, (len + 31) / 32 + 1, true⟩ := hfresh c hcm hcu
    have ht2 := H2.wf.2.2.2.1
    unfold TilesOk at ht2
    have hdis := Services.Bootstrap.Decode.HeapFrame.Tiles.disjoint ht2 c hcm' _ hnew hne
    simp only at hdis
    have hlt : len ≤ 32 * ((len + 31) / 32) := by omega
    -- the frame base b = sp − 96
    have b48 : sp - 96 + 48 = sp - 48 := by omega
    rw [b48] at o0 o8 o16 fr2
    -- 3. after `finish_grow`: to the chunk's read
    have q2 : ∀ o v, sp - 96 ≤ o → o + 8 ≤ sp - 48 ∨ sp - 24 ≤ o → o + 8 ≤ sp → rdN μ1 o 8 = v →
        rdN μ2 o 8 = v := fun o v h1 h2 h3 hv => by
      rw [rdN_frame fun j hj => fr2 _ (by omega) (by omega) (by omega)]; exact hv
    obtain ⟨ω3, μ3, r3, c0, c1, c5, c6, c7, c8, c9, k24, k32, fr3, rd3, wr3⟩ :=
      rv_mid (p := p) (P := P) (R := env.rel cap) x ω2 μ2 (sp - 96) rd ptr len (by rw [e0, a0]) (by rw [e1', a1])
        (by rw [e5, a5]) (by rw [e6, a6]) (q2 _ _ (by omega) (by omega) (by omega) sl0)
        (q2 _ _ (by omega) (by omega) (by omega) (by rw [show sp - 96 + 16 = sp - 80 by omega]; exact s80))
        (by rw [show sp - 96 + 48 = sp - 48 by omega]; exact o0)
        (by rw [show sp - 96 + 56 = sp - 48 + 8 by omega]; exact o8)
        ⟨by omega, by omega⟩ (by omega) (by omega) (by omega)
        (fun a h1 h2 => H2.st a (by omega) (by omega))
    -- bounds of the block and the source
    have hbase := H.hb0
    have hbT := H.hbT
    obtain ⟨n1, -, n3⟩ := hns
    obtain ⟨u1, -, u3⟩ := hcs
    rw [hb'] at n1 n3
    have hp32 : 206896 ≤ ptr := by omega
    have hpe : ptr + len < 2147483648 := by omega
    have hie : 206896 ≤ ip ∧ ip + len < 2147483648 := by omega
    have hsep : ptr + len + 24 ≤ ip ∨ ip + len + 24 ≤ ptr := by omega
    -- memory facts carried to μ3
    have m3 : ∀ a, a < 4294967296 → sp ≤ a → μ3.read a = μ.read a := fun a h1 h2 => by
      rw [fr3 a h1 (Or.inr (by omega)), fr2 a h1 (by omega) (Or.inr (by omega)), fr1 a h1 (Or.inr h2)]
    have wr2' : ∀ a, μ3.writable a = μ2.writable a := wr3
    have hwb : ∀ a, ptr ≤ a → a < ptr + len → μ3.writable a = true := fun a h1 h2 => by
      rw [wr2']; exact heapC_writable_data H2 hnew rfl ⟨by simp only; omega, by simp only; omega⟩
    have hra : ∀ a, ip ≤ a → a < ip + len → μ3.readable a = true := fun a h1 h2 => by
      apply Memory.readable_of_writable
      rw [wr2']; exact heapC_writable_data H2 hcm' hcu ⟨by omega, by omega⟩
    have hrd3 : μ3.readN rd 8 = Num.encodeLE 8 ip := by
      rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => m3 _ (by omega) (by omega))]; exact hR0
    have hrd8 : μ3.readN (rd + 8) 8 = Num.encodeLE 8 rlen := by
      rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => m3 _ (by omega) (by omega))]; exact hR8
    -- 4. the reader copies the chunk into the block
    obtain ⟨ω4, μ4, r4, d0, d1, d5, d6, d7, q0, q8, qb, fr4, rd4, wr4⟩ :=
      read_any (p := p) (P := P) (R := env.rel cap) x ω3 μ3 2060 45809 (sp - 96) rd ptr ip rlen len c0 c1 c7 c8 c9
        (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_1029]) bs_45809
        ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hrl hrl32
        (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) hsep
        (fun a h1 h2 => by rw [wr2']; exact H2.st a (by omega) (by omega))
        (fun a h1 h2 => by rw [wr2']; exact H2.st a (by omega) (by omega)) hwb hra hrd3 hrd8
    -- the frame words, carried to μ4
    have f4 : ∀ a, sp - 96 ≤ a → a < sp → μ4.read a = μ3.read a := fun a h1 h2 =>
      fr4 a (by omega) (Or.inr h1) (Or.inl (by omega)) (Or.inr (by omega))
    have l4 : ∀ o v, sp - 96 ≤ o → o + 8 ≤ sp → rdN μ3 o 8 = v → rdN μ4 o 8 = v := fun o v h1 h2 hv => by
      rw [rdN_frame fun j hj => f4 _ (by omega) (by omega)]; exact hv
    have l3 : ∀ o v, sp - 96 ≤ o → o + 8 ≤ sp - 72 ∨ sp - 56 ≤ o → o + 8 ≤ sp → rdN μ2 o 8 = v →
        rdN μ3 o 8 = v := fun o v h1 h2 h3 hv => by
      rw [rdN_frame fun j hj => fr3 _ (by omega) (by omega)]; exact hv
    have l1 : ∀ o v, sp - 96 ≤ o → (o + 8 ≤ sp - 72 ∨ sp - 56 ≤ o) ∧ (o + 8 ≤ sp - 48 ∨ sp - 24 ≤ o) →
        o + 8 ≤ sp → rdN μ1 o 8 = v → rdN μ4 o 8 = v := fun o v h1 h2 h3 hv =>
      l4 _ _ h1 h3 (l3 _ _ h1 h2.1 h3 (q2 _ _ h1 h2.2 h3 hv))
    -- 5. the exit: the vector written at `out`
    obtain ⟨ω5, μ5, r5, f0, f1, f5, f6, g0, g8, g16, fr5, rd5, wr5⟩ :=
      rv_exit (p := p) (P := P) (R := env.rel cap) x ω4 μ4 (sp - 96) out ptr len ω[0].toNat ω[5].toNat ω[6].toNat
        (by rw [d1, c1]) (by rw [d5, c5]) (by rw [d6, c6]) d7
        (l1 _ _ (by omega) (by omega) (by omega) (by rw [show sp - 96 + 8 = sp - 88 by omega]; exact s88))
        (l4 _ _ (by omega) (by omega) k24) (l4 _ _ (by omega) (by omega) k32)
        (l1 _ _ (by omega) (by omega) (by omega) (by rw [show sp - 96 + 40 = sp - 56 by omega]; exact sl40))
        (l1 _ _ (by omega) (by omega) (by omega) (by rw [show sp - 96 + 72 = sp - 24 by omega]; exact s24))
        (l1 _ _ (by omega) (by omega) (by omega) (by rw [show sp - 96 + 80 = sp - 16 by omega]; exact s16))
        (l1 _ _ (by omega) (by omega) (by omega) (by rw [show sp - 96 + 88 = sp - 8 by omega]; exact s8))
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega) (Or.inr (by omega))
        (fun a h1 h2 => by
          rw [rd4, rd3]; exact Memory.readable_of_writable (H2.st a (by omega) (by omega)))
        (fun a h1 h2 => by rw [wr4, wr3]; exact H2.st a (by omega) (by omega))
    -- below 2³¹, μ5 reads as μ2 off the new block's data
    have low52 : ∀ a, a < 2147483648 → (a < ptr ∨ ptr + len ≤ a) → μ5.read a = μ2.read a := fun a h1 h2 => by
      rw [fr5 a (by omega) (Or.inl (by omega)), fr4 a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) h2,
        fr3 a (by omega) (Or.inl (by omega))]
    have ww : ∀ a, μ5.writable a = μ2.writable a := fun a => by rw [wr5, wr4, wr3]
    have dec : ∀ v : UInt64, UInt64.ofNat v.toNat = v := fun v => UInt64.ofNat_toNat
    -- the heap data of s: kept by `finish_grow` (off the new headers), then off the new block
    have keepd : ∀ c' ∈ chunks s, c'.used = true → ∀ a, InDataA c' a → μ2.read a = μ.read a := by
      intro c' hc' hu a ha
      have hc'' := keep c' hc' hu
      have hoff := Services.Bootstrap.Alloc.off_hdr_data H2.wf (by rw [hb']; exact H.hb0) (by rw [hb']; exact H.hbT)
        hc'' ha.1 ha.2
      have hcs' := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hc' hu
      unfold InDataA at ha
      rw [hk a ⟨Or.inr hoff.1, hoff.2.1, hoff.2.2⟩, fr1 a (by omega) (Or.inl (by omega))]
    refine ⟨ptr, s', ω5, μ5, ha, ((((r1.trans r2).trans r3).trans r4).trans r5).mono (by omega),
      ⟨H2.wf, Services.Bootstrap.Decode.HeapFrame.Rep.congr_data H2.rep H2.wf (by rw [hb']; exact H.hb0)
        (by rw [hb']; exact H.hbT) hnew (fun a h1 h2 => low52 a h1 (by simp only at h2; omega)),
        H2.fo, by rw [rdN_frame fun j hj => low52 _ (by omega) (Or.inl (by omega))]; exact H2.lock,
        H2.hb0, H2.hbT, H2.hA, H2.bd,
        by obtain ⟨ph2, a2, b2, c2, d2, e2⟩ := H2.pages; exact ⟨ph2, a2, b2, HeapPages.of_eq c2 ww, d2, e2⟩,
        H2.hSb, H2.hS1, fun a h1 h2 => by rw [ww]; exact H2.st a h1 h2, fun a h => by rw [ww]; exact H2.ro a h⟩,
      keep, hnew, fun d hd hu => hfresh d hd hu, ?_, g0, g8, g16, ?_, ?_, ?_, ?_, by rw [f0, dec], ?_,
      by rw [f5, dec], by rw [f6, dec]⟩
    · intro c' hc' hu a ha
      have hc'' := keep c' hc' hu
      have hne' : c' ≠ ⟨ptr - 32, (len + 31) / 32 + 1, true⟩ := hfresh c' hc' hu
      have hd' := Services.Bootstrap.Decode.HeapFrame.Tiles.disjoint ht2 c' hc'' _ hnew hne'
      simp only at hd'
      have hcs' := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hc' hu
      unfold InDataA at ha
      rw [low52 a (by omega) (by omega), keepd c' hc' hu a ha]
    · rw [PVM.Memory.readN_congr (μ := μ4) (fun j hj => fr5 _ (by omega) (Or.inl (by omega))), qb,
        PVM.Memory.readN_congr (μ := μ2) (fun j hj => fr3 _ (by omega) (Or.inl (by omega)))]
      exact PVM.Memory.readN_congr (fun j hj => keepd c hcm hcu _ ⟨by omega, by omega⟩)
    · rw [PVM.Memory.readN_congr (μ := μ4) (fun j hj => fr5 _ (by omega) (by omega))]; exact q0
    · rw [PVM.Memory.readN_congr (μ := μ4) (fun j hj => fr5 _ (by omega) (by omega))]; exact q8
    · intro a h0 hs ho hr
      rw [fr5 a h0 ho, fr4 a h0 (Or.inr (by omega)) hr (Or.inr (by omega)), m3 a h0 hs]
    · rw [f1, h1]; congr 1; omega
  · right
    rw [e1] at ha
    refine ⟨ha, ?_⟩
    obtain ⟨ω3, r3⟩ := rv_fail (p := p) (P := P) (R := env.rel cap) x ω2 μ2 (sp - 96) (by rw [e0, a0])
      (by rw [e1', a1]) (by rw [show sp - 96 + 48 = sp - 48 by omega] at o0; rw [show sp - 96 + 48 = sp - 48 by omega]; exact o0)
      (by omega) (fun a h1 h2 => by
        have := H2.st a (by omega) (by omega)
        exact Memory.readable_of_writable this)
    exact ⟨ω3, μ2, ((r1.trans r2).trans r3).mono (by omega)⟩

end Services.Bootstrap.Acc
