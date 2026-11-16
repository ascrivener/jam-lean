import Services.Bootstrap.Acc.Handlers.RowElevenCore
import Services.Bootstrap.Acc.Handlers.RowElevenTail
import Services.Bootstrap.Acc.Handlers.ResultsAvoid
import Services.Bootstrap.Acc.Impl.Loop
import Services.Bootstrap.Decode.VecU8Heap

/-!
# Row 11 (R7) from 15028: the instructions' drop, then the results write

`row_eleven`: from 15028, the run first drops the instructions' `IntoIter` at sp + 472 (33214, the named
hypothesis `DropInstrsH`, freeing `iterFree`), then continues at 15038 as `row_eleven_core`. It implements
`unless b (store (Key.results package item) (encodeResults rs))` (GP v0.8.0 Appendix B, Ω_W; quirk Q4),
and ends in `R7Post` with `iterFree ++ tailFree` freed.

To carry the tail's facts (`TailHyp`, `LoopHyp`) across the drop, the freed buffers must be none of the
results' chunks: `(iterFree ++ tailFree).Nodup` covers the buffers owned by pointer (`resPtrs`,
`tailBufs`). `ResultsAvoid` (the results' octets lie in chunks not in `iterFree`) covers the rest. For
the items' octets in `ResultsOwn`, chunk uniqueness (`chunk_uniq`) makes its witness the same chunk.
-/

namespace Services.Bootstrap.Acc.Handlers.RowEleven

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.CodeX
  Services.Bootstrap.Spec Services.Bootstrap.Acc Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Acc.Handlers.Results Services.Bootstrap.Acc.Handlers.KeyEnc
  Services.Bootstrap.Acc.Handlers.ResultsInit Services.Bootstrap.Acc.Handlers.ResStore
  Services.Bootstrap.Acc.Handlers.ResultsDrop Services.Bootstrap.Acc.Handlers.InstrRep
open JAM.Codec (fixed)

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- Two chunks of a well-formed heap whose data share an octet are equal. -/
theorem chunk_uniq {s : State} (hwf : WF s) {c d : Chunk} (hc : c ∈ chunks s) (hd : d ∈ chunks s) {a : Nat}
    (ha : InData c a) (hb : InData d a) : c = d := by
  refine Classical.byContradiction fun hne => ?_
  have := Decode.VecU8.data_disj hwf hc hd hne ha
  unfold InData at hb
  omega

theorem mem_resPtrs {μ : Memory} {rp n i q : Nat} (hi : i < n) (hq : q ∈ itemPtrs μ (rp + 144 * i)) :
    q ∈ resPtrs μ rp n := by
  unfold resPtrs
  exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, hq⟩

section KeepX

variable {μ μ' : Memory} {st st' : State} {rp n : Nat} {G : Chunk → Prop}

/-- The chunks with G kept. -/
def ChunksKeptG (G : Chunk → Prop) (μ : Memory) (st : State) (μ' : Memory) (st' : State) : Prop :=
  ∀ d ∈ chunks st, d.used = true → G d → d ∈ chunks st' ∧ ∀ a, InData d a → μ'.read a = μ.read a

/-- The witness chunks of `ResultsOwn` satisfy G: those holding an item octet, and those owned by
    pointer. -/
def OwnG (G : Chunk → Prop) (μ : Memory) (st : State) (rp n : Nat) : Prop :=
  (∀ k, k < 144 * n → ∀ d ∈ chunks st, d.used = true → InData d (rp + k) → G d) ∧
  (∀ d ∈ chunks st, d.used = true → d.addr + 32 ∈ resPtrs μ rp n → G d)

theorem item_keepG (O : ResultsOwn μ st rp n) (hG : OwnG G μ st rp n) (hk : ChunksKeptG G μ st μ' st')
    {i o m : Nat} (hi : i < n) (hom : o + m ≤ 144) :
    rdN μ' (rp + 144 * i + o) m = rdN μ (rp + 144 * i + o) m :=
  rdN_frame fun j hj => by
    obtain ⟨d, hd, hu, hin, -⟩ := O.2.2.1 (144 * i + o + j) (by omega)
    rw [show rp + 144 * i + o + j = rp + (144 * i + o + j) by omega]
    exact (hk d hd hu (hG.1 _ (by omega) d hd hu hin)).2 _ hin

theorem itemPtrs_keepG (O : ResultsOwn μ st rp n) (hG : OwnG G μ st rp n) (hk : ChunksKeptG G μ st μ' st')
    {i : Nat} (hi : i < n) : itemPtrs μ' (rp + 144 * i) = itemPtrs μ (rp + 144 * i) := by
  have e0 := item_keepG O hG hk hi (o := 0) (m := 1) (by omega)
  simp only [Nat.add_zero] at e0
  have e8 := item_keepG O hG hk hi (o := 8) (m := 8) (by omega)
  have e16 := item_keepG O hG hk hi (o := 16) (m := 8) (by omega)
  have e24 := item_keepG O hG hk hi (o := 24) (m := 8) (by omega)
  unfold itemPtrs
  rw [e0, e8, e16, e24]
  by_cases h5 : rdN μ (rp + 144 * i) 1 = 5
  · rw [if_pos h5, if_pos h5]
  · rw [if_neg h5, if_neg h5]
    by_cases hv : 6 ≤ rdN μ (rp + 144 * i) 1 ∧ rdN μ (rp + 144 * i) 1 < 255
    · rw [if_pos hv, if_pos hv]
      suffices hin : innerPtrs μ' (rdN μ (rp + 144 * i + 16) 8) (rdN μ (rp + 144 * i + 24) 8) =
          innerPtrs μ (rdN μ (rp + 144 * i + 16) 8) (rdN μ (rp + 144 * i + 24) 8) by rw [hin]
      by_cases hL : rdN μ (rp + 144 * i + 24) 8 = 0
      · rw [hL]; simp [innerPtrs]
      · obtain ⟨hc, d, hd, hu, hq, hend⟩ := O.2.2.2 i hi hv.1 hv.2 hL
        have hmem : d.addr + 32 ∈ resPtrs μ rp n := by
          refine mem_resPtrs hi ?_
          unfold itemPtrs
          rw [if_neg h5, if_pos hv, if_neg hc, hq]
          exact List.mem_append_right _ (List.mem_singleton_self _)
        have hk' := (hk d hd hu (hG.2 d hd hu hmem)).2
        apply innerPtrs_congr
        intro j hj
        exact ⟨rdN_frame fun l hl => hk' _ ⟨by omega, by omega⟩,
          rdN_frame fun l hl => hk' _ ⟨by omega, by omega⟩⟩
    · rw [if_neg hv, if_neg hv]

theorem resPtrs_keepG (O : ResultsOwn μ st rp n) (hG : OwnG G μ st rp n) (hk : ChunksKeptG G μ st μ' st') :
    ∀ k, k ≤ n → resPtrs μ' rp k = resPtrs μ rp k
  | 0, _ => by simp [resPtrs]
  | k + 1, h => by
    rw [resPtrs_succ, resPtrs_succ, resPtrs_keepG O hG hk k (by omega), itemPtrs_keepG O hG hk (by omega)]

/-- **`ResultsOwn` survives a run that keeps the chunks with G**, when its witness chunks satisfy G. -/
theorem ResultsOwn.keepG (O : ResultsOwn μ st rp n) (hG : OwnG G μ st rp n) (hk : ChunksKeptG G μ st μ' st') :
    ResultsOwn μ' st' rp n := by
  have hr := resPtrs_keepG O hG hk n (Nat.le_refl _)
  refine ⟨hr ▸ O.1, fun q hq => ?_, fun k hk' => ?_, fun i hi h6 h255 hL => ?_⟩
  · obtain ⟨d, hd, hu, ha⟩ := O.2.1 q (hr ▸ hq)
    exact ⟨d, (hk d hd hu (hG.2 d hd hu (ha ▸ hr ▸ hq))).1, hu, ha⟩
  · obtain ⟨d, hd, hu, hin, hn⟩ := O.2.2.1 k hk'
    exact ⟨d, (hk d hd hu (hG.1 k hk' d hd hu hin)).1, hu, hin, hr ▸ hn⟩
  · have e0 := item_keepG O hG hk hi (o := 0) (m := 1) (by omega)
    simp only [Nat.add_zero] at e0
    rw [item_keepG O hG hk hi (o := 8) (m := 8) (by omega), item_keepG O hG hk hi (o := 16) (m := 8) (by omega)]
    rw [item_keepG O hG hk hi (o := 24) (m := 8) (by omega)] at hL ⊢
    rw [e0] at h6 h255
    obtain ⟨hc, d, hd, hu, hq, hend⟩ := O.2.2.2 i hi h6 h255 hL
    have hmem : d.addr + 32 ∈ resPtrs μ rp n := by
      refine mem_resPtrs hi ?_
      have h5 : rdN μ (rp + 144 * i) 1 ≠ 5 := by omega
      unfold itemPtrs
      rw [if_neg h5, if_pos ⟨h6, h255⟩, if_neg hc, hq]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    exact ⟨hc, d, (hk d hd hu (hG.2 d hd hu hmem)).1, hu, hq, hend⟩

end KeepX

/-- The chunks whose data address is not in F. -/
def NotIn (F : List Nat) (d : Chunk) : Prop := d.addr + 32 ∉ F

theorem BufOK.keepF {st st' : State} {FR F : List Nat} {c q : Nat} {μ μ' : Memory}
    (hk : ChunksKeptG (NotIn F) μ st μ' st') (hq : c ≠ 0 → q ∉ F) (h : BufOK st FR c q) : BufOK st' FR c q :=
  fun hc => by
    obtain ⟨⟨d, hd, hu, ha⟩, hn⟩ := h hc
    exact ⟨⟨d, (hk d hd hu (by unfold NotIn; rw [ha]; exact hq hc)).1, hu, ha⟩, hn⟩

theorem optBuf_mem {c q : Nat} (hc : c ≠ 0) : q ∈ optBuf c q := by
  unfold optBuf; rw [if_neg hc]; exact List.mem_singleton_self _

/-- **`TailHyp` survives a run that keeps every allocated chunk not in F with its data and the frame's
    words**, when F avoids `tailFree` and every chunk holding an item octet is not in F; `tailFree` is
    unchanged. -/
theorem TailHyp.keepF {code : ByteArray} {pb S0 S1 : Nat} {μ μ' : Memory} {st st' : State} {sp : Nat}
    {F : List Nat} (T : TailHyp code pb S0 S1 μ st sp) (H' : HeapCtxC code pb S0 S1 μ' st')
    (hk : ChunksKeptG (NotIn F) μ st μ' st') (hdis : ∀ q ∈ tailFree μ sp, q ∉ F)
    (hI : ∀ k, k < 144 * rdN μ (sp + 464) 8 → ∀ d ∈ chunks st, d.used = true →
      InData d (rdN μ (sp + 456) 8 + k) → d.addr + 32 ∉ F)
    (fr : ∀ a, sp ≤ a → a < sp + 472 → μ'.read a = μ.read a) :
    TailHyp code pb S0 S1 μ' st' sp ∧ tailFree μ' sp = tailFree μ sp := by
  have e : ∀ o, o + 8 ≤ 472 → rdN μ' (sp + o) 8 = rdN μ (sp + o) 8 := fun o ho =>
    rdN_frame fun j hj => fr _ (by omega) (by omega)
  have hG : OwnG (NotIn F) μ st (rdN μ (sp + 456) 8) (rdN μ (sp + 464) 8) :=
    ⟨hI, fun d _ _ hm => hdis _ (by unfold tailFree; exact List.mem_append_left _ hm)⟩
  have hr : resPtrs μ' (rdN μ (sp + 456) 8) (rdN μ (sp + 464) 8) =
      resPtrs μ (rdN μ (sp + 456) 8) (rdN μ (sp + 464) 8) := resPtrs_keepG T.O hG hk _ (Nat.le_refl _)
  have tf : tailFree μ' sp = tailFree μ sp := by
    unfold tailFree tailBufs
    rw [e 456 (by omega), e 464 (by omega), e 448 (by omega), e 128 (by omega), e 104 (by omega),
      e 264 (by omega), e 272 (by omega), hr]
  have hb : ∀ q ∈ tailBufs μ sp, q ∉ F := fun q hq =>
    hdis q (by unfold tailFree; exact List.mem_append_right _ hq)
  refine ⟨⟨H', T.hsp, ?_, ?_, ?_, ?_⟩, tf⟩
  · rw [e 456 (by omega), e 464 (by omega)]; exact ResultsOwn.keepG T.O hG hk
  · rw [e 456 (by omega), e 464 (by omega), e 448 (by omega), hr]
    exact T.b1.keepF hk fun hc => hb _ (by
      unfold tailBufs; exact List.mem_append_left _ (List.mem_append_left _ (optBuf_mem hc)))
  · rw [e 456 (by omega), e 464 (by omega), e 448 (by omega), e 128 (by omega), e 104 (by omega), hr]
    exact T.b2.keepF hk fun hc => hb _ (by
      unfold tailBufs; exact List.mem_append_left _ (List.mem_append_right _ (optBuf_mem hc)))
  · rw [e 456 (by omega), e 464 (by omega), e 448 (by omega), e 128 (by omega), e 104 (by omega),
      e 264 (by omega), e 272 (by omega), hr]
    exact T.b3.keepF hk fun hc => hb _ (by unfold tailBufs; exact List.mem_append_right _ (optBuf_mem hc))

/-- **Row 11 from 15028 (the instructions' drop, then the results write) implements
    `unless b (store (Key.results package item) (encodeResults rs))`** (GP v0.8.0 Appendix B, Ω_W;
    quirk Q4), as `row_eleven_core`, after the drop of the instructions' `IntoIter` at sp + 472 (33214,
    named hypothesis `DropInstrsH`). It ends in `R7Post` with `iterFree ++ tailFree` freed. On top of
    `row_eleven_core`'s hypotheses (against the state at 15028): `IterOwn` (the remaining instructions
    `is` owned by the `IntoIter`), `DropInstrsH`'s stack room (2³¹ + 4096 ≤ sp, S0 + 4096 ≤ sp), and the
    disjointness premises: `(iterFree ++ tailFree).Nodup`, and `ResultsAvoid` (the results' octets lie in
    chunks not in `iterFree`). -/
theorem row_eleven {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : AccEnv) {pb S0 S1 : Nat} (hE : ExtendH p P env pb S0 S1) (hO : OkEncH p P env pb S0 S1)
    (B : InstrRep) (hD : DropInstrsH B p P env.code pb S0 S1)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    (Ab : St Stream → Prop) (hAb1 : ∀ s : St Stream, s.i = 36528 → Ab s)
    (hAb2 : ∀ s : St Stream, s.i = 34070 → Ab s) (hAbX : ∀ s : St Stream, s.i = 40611 ∨ s.i = 40821 → Ab s)
    (s : St Stream) (st : State) (sp z item kc : Nat) (rs : List Spec.Result) (is : List Spec.Instr) (b : Bool)
    (hi : s.i = 15028) (h1 : s.ω[1] = UInt64.ofNat sp)
    (hspD : 2147483648 + 4096 ≤ sp) (hS0D : S0 + 4096 ≤ sp)
    (I : IterOwn B s.μ st (sp + 472) is)
    (T : TailHyp env.code pb S0 S1 s.μ st sp)
    (L : LoopHyp pb S0 S1 sp (rdN s.μ (sp + 456) 8) (rdN s.μ (sp + 464) 8) rs st s.μ) (hS1 : sp + 1632 ≤ S1)
    (hnd : (iterFree B s.μ (sp + 472) is.length ++ tailFree s.μ sp).Nodup)
    (hav : ResultsAvoid s.μ st (rdN s.μ (sp + 456) 8) rs (iterFree B s.μ (sp + 472) is.length))
    (mz : rdN s.μ (sp + 160) 8 = z) (hz : z % 2 = 1 ↔ b = true)
    (hitem : s.μ.readN (sp + 176) 2 = fixed 2 item)
    (mc : s.μ.readN 68696 8 = Num.encodeLE 8 kc) (hkc : 35 ≤ kc ∧ kc + 31 < 68719476736)
    (ht8 : rdN s.μ 69072 4 = 4294900408) (ht4 : rdN s.μ 69056 4 = 4294900402)
    (hro : ∀ a, 68680 ≤ a → a < 69076 → s.μ.readable a = true) (hvals : StoreFit s.c) :
    Impl p (accContractS env) env Ab
      (if b then pure () else store (.results (s.μ.readN (sp + 312) 32) item) (encodeResults rs))
      (fun _ => R7Post env.code pb S0 S1 sp s.ω[5] st s.μ
        (iterFree B s.μ (sp + 472) is.length ++ tailFree s.μ sp)) s := by
  obtain ⟨i, ω, μ, c0, f⟩ := s
  dsimp only at hi h1 I T L hnd hav mz hitem mc ht8 ht4 hro hvals ⊢
  subst hi
  have H := T.H
  have hT := H.hS1
  obtain ⟨hs1, hs2, hs3⟩ := T.hsp
  have hn := L.hn
  -- 15028 → 33214 → 15038
  obtain ⟨ω0, run0, w0, w1, w5, w6, w7⟩ :=
    r11_di0 (R := KeepCtx (accContractS env)) (P := P) (c0, f) ω μ sp h1 (by omega)
  obtain ⟨ω1, μ1, N1, run1, H1, K1, Fm1, e1, e5, -⟩ :=
    hD (KeepCtx (accContractS env)) (c0, f) ω0 μ st sp (sp + 472) 558 15038 is H I w0 (w1.trans h1) w7
      hspD hS0D (by omega) (by omega) (by decide) jte_278 bs_15038
  -- the frame
  have fr : ∀ a, sp ≤ a → a < 4294967296 → μ1.read a = μ.read a := fun a h1 h2 => Fm1.1 a h2 h1
  have e8 : ∀ o, o + 8 ≤ 1632 → rdN μ1 (sp + o) 8 = rdN μ (sp + o) 8 := fun o ho =>
    rdN_frame fun j hj => fr _ (by omega) (by omega)
  have hro1 : ∀ a, a < 196608 → μ1.read a = μ.read a := fun a ha =>
    Fm1.2.2.1 a (by unfold two32; omega) (H.ro a ha)
  have hdis : ∀ q ∈ tailFree μ sp, q ∉ iterFree B μ (sp + 472) is.length := by
    intro q hq hF
    exact (List.nodup_append.1 hnd).2.2 q hF q hq rfl
  have hk : ChunksKeptG (NotIn (iterFree B μ (sp + 472) is.length)) μ st μ1
      ((iterFree B μ (sp + 472) is.length).foldl free st) := fun d hd hu hn => K1 d hd hu hn
  have hI : ∀ k, k < 144 * rdN μ (sp + 464) 8 → ∀ d ∈ chunks st, d.used = true →
      InData d (rdN μ (sp + 456) 8 + k) → d.addr + 32 ∉ iterFree B μ (sp + 472) is.length := by
    intro k hk' d hd hu hin
    obtain ⟨d', ⟨hd', -, hn'⟩, hin'⟩ := hav.1 k (by rw [hn]; exact hk')
    rw [chunk_uniq H.wf hd hd' hin hin']; exact hn'
  obtain ⟨T1, tf⟩ := T.keepF H1 hk hdis hI fun a h1 h2 => fr a h1 (by omega)
  have L1 : LoopHyp pb S0 S1 sp (rdN μ1 (sp + 456) 8) (rdN μ1 (sp + 464) 8) rs
      ((iterFree B μ (sp + 472) is.length).foldl free st) μ1 := by
    rw [e8 456 (by omega), e8 464 (by omega)]
    exact { L with hR := (hav.keep K1).toAt }
  have core := row_eleven_core env hE hO cap hcap1 hcap Ab hAb1 hAb2 hAbX ⟨15038, ω1, μ1, c0, f⟩
    ((iterFree B μ (sp + 472) is.length).foldl free st) sp z item kc rs b rfl (e1.trans (w1.trans h1)) T1 L1 hS1
    (by rw [e8 160 (by omega)]; exact mz) hz
    (by rw [← hitem]; exact Memory.readN_congr fun j hj => fr _ (by omega) (by omega))
    (by rw [← mc]; exact Memory.readN_congr fun j hj => hro1 _ (by omega)) hkc
    (by rw [← ht8]; exact rdN_frame fun j hj => hro1 _ (by omega))
    (by rw [← ht4]; exact rdN_frame fun j hj => hro1 _ (by omega))
    (fun a h1 h2 => by rw [Fm1.2.2.2.1 a]; exact hro a h1 h2) hvals
  dsimp only at core
  have hq : μ1.readN (sp + 312) 32 = μ.readN (sp + 312) 32 :=
    Memory.readN_congr fun j hj => fr _ (by omega) (by omega)
  rw [hq] at core
  refine Impl.pre _ _ (s' := ⟨15038, ω1, μ1, c0, f⟩) ⟨_, run0.trans run1⟩ rfl ?_
  refine Impl.then ?_ _ _ core
  rintro _ s' ⟨hi', h1', h5', st', H', hk', stk', gl'⟩
  refine Impl.pure_of ⟨hi', h1', h5'.trans (e5.trans w5), st', H', fun d hd hu hn => ?_,
    fun a h1 h2 h3 => (stk' a h1 h2 h3).trans (fr a h2 h1), fun a ha => (gl' a ha).trans (Fm1.2.1 a ha)⟩
  have hn1 : d.addr + 32 ∉ iterFree B μ (sp + 472) is.length := fun h => hn (List.mem_append_left _ h)
  have hn2 : d.addr + 32 ∉ tailFree μ1 sp := fun h => hn (List.mem_append_right _ (tf ▸ h))
  obtain ⟨g1, g2⟩ := K1 d hd hu hn1
  obtain ⟨g3, g4⟩ := hk' d g1 hu hn2
  exact ⟨g3, fun a ha => (g4 a ha).trans (g2 a ha)⟩

end Services.Bootstrap.Acc.Handlers.RowEleven
