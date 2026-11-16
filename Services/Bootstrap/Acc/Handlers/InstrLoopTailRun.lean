import Services.Bootstrap.Acc.Handlers.InstrLoopOwn
import Services.Bootstrap.Acc.Handlers.InstrLoopPush
import Services.Bootstrap.Acc.Handlers.InstrLoopMid
import Services.Bootstrap.Acc.Handlers.RowElevenFront

/-!
# R5, the instruction loop: the tail's runs (14278 → 8540)

Spec `onWorkItem`'s `results := results ++ [r]` (GP v0.8.0 Appendix B, Ω_W; bootstrap's own loop). From
the shared tail 14278 the result's log line is formatted (`ResultLogH`) and logged (host call 100, only
ω₇ changes), the line's `String` freed, the result pushed onto the results `Vec` (growing it through
`PushH` when full), the instruction's `String` freed, and the run goes back to the head 8540. Logging is
frame-only (Adam's standing decision).

- `il_tail_log`: 14278 → 14420 (the log line and its `String`).
-/

namespace Services.Bootstrap.Acc.Handlers.InstrLoop

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.Alloc Services.Bootstrap.Acc Services.Bootstrap.Spec Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Acc.Handlers.Results

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem setR7_ne' (ω : Regs) (r : Nat) (j : Nat) (hj : j < 13) (h : j ≠ 7) : (setR7 ω r)[j] = ω[j] := by
  unfold setR7; rw [Vector.getElem_set]; simp [Ne.symm h]

/-- **14278 … 14420, the result's log line**: from the shared tail with the result r at sp + 1000 (in
    chunks C, allocated in st), the formatter word 678 at sp + 200 and the instruction's `String`'s
    octets readable, either the run reaches 14420 with ω₁ kept, the allocator's context for some st′
    keeping st's allocated chunks with their data, and from sp up only sp + 1144 … sp + 1168,
    sp + 1496 … sp + 1512 and sp + 1568 … sp + 1616 changed; or the line's allocation fails
    (`ExhaustsP`). -/
theorem il_tail_log {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : AccEnv)
    {pb S0 S1 : Nat} (hR : ResultLogH p env pb S0 S1) (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory)
    (st : State) (sp : Nat) (r : Spec.Result) (C : Chunk → Prop) (H : HeapCtxC env.code pb S0 S1 μ st)
    (h1 : ω[1] = UInt64.ofNat sp) (hs1 : 2147483648 + 4096 ≤ sp) (hs2 : S0 + 4096 ≤ sp)
    (hs3 : sp + 1632 ≤ S1)
    (hr : ResultAtP μ C (sp + 1000) r) (hC : ∀ d, C d → d ∈ chunks st ∧ d.used = true)
    (m200 : rdN μ (sp + 200) 8 = 678)
    (hstr : ∀ a, rdN μ (sp + 984) 8 ≤ a → a < rdN μ (sp + 984) 8 + rdN μ (sp + 992) 8 → μ.readable a = true) :
    (∃ (st' : State) (ω' : Regs) (μ' : Memory) (N : Nat),
      FreeStepsH p (KeepCtx (accContractS env)) 14278 ω μ (c, f) 14420 ω' μ' (c, f) N ∧
      HeapCtxC env.code pb S0 S1 μ' st' ∧ ω'[1] = ω[1] ∧
      (∀ d ∈ chunks st, d.used = true → d ∈ chunks st' ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < sp + 1144 ∨ sp + 1168 ≤ a) → (a < sp + 1496 ∨ sp + 1512 ≤ a) →
        (a < sp + 1568 ∨ sp + 1616 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a)) ∨
    ExhaustsP p env pb 14278 ω μ c f := by
  have hT := H.hS1
  have hSt := H.st
  have rd : ∀ a, S0 ≤ a → a < S1 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hSt a h1 h2)
  -- 14278 → 59375
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, n1, n2, n3, n4, n5, n6, n7, n8, fr1, rd1, wr1⟩ :=
    il_res_log_pre (R := KeepCtx (accContractS env)) (P := P) (c, f) ω μ sp (rdN μ (sp + 1000) 1) 678 h1
      ⟨by omega, by omega⟩ (ResultsDrop.rdN_lt1 _ _) (by decide) (KeyEnc.readN_enc μ _ 1)
      (by rw [← m200]; exact KeyEnc.readN_enc μ _ 8) (fun a h1 h2 => rd a (by omega) (by omega))
      (fun a h1 h2 => rd a (by omega) (by omega)) (fun a h1 h2 => hSt a (by omega) (by omega))
      (fun a h1 h2 => hSt a (by omega) (by omega))
  have f1 : ∀ a, a < 4294967296 → (a < sp + 1496 ∨ sp + 1512 ≤ a) → (a < sp + 1568 ∨ sp + 1616 ≤ a) →
      μ1.read a = μ.read a := fr1
  have H1 : HeapCtxC env.code pb S0 S1 μ1 st :=
    HeapKeep.keepHi H (fun a ha => f1 a (by omega) (.inl (by omega)) (.inl (by omega))) wr1
  have kHeap : ∀ d, C d → C d ∧ ∀ a, InData d a → μ1.read a = μ.read a := fun d hd => ⟨hd, fun a ha => by
    have := ResultsDrop.data_lt H (hC d hd).1 ha
    exact f1 a (by omega) (.inl (by omega)) (.inl (by omega))⟩
  have hr1 : ResultAt μ1 st (sp + 1000) r := ResultAtP.toAt' hC
    (ResultAtP.copy kHeap (fun o ho => f1 _ (by omega) (.inl (by omega)) (.inl (by omega))) hr)
  have e1000 : rdN μ1 (sp + 1000) 1 = rdN μ (sp + 1000) 1 :=
    rdN_frame fun j hj => f1 _ (by omega) (.inl (by omega)) (.inl (by omega))
  have e984 : rdN μ1 (sp + 984) 8 = rdN μ (sp + 984) 8 :=
    rdN_frame fun j hj => f1 _ (by omega) (.inl (by omega)) (.inl (by omega))
  have e992 : rdN μ1 (sp + 992) 8 = rdN μ (sp + 992) 8 :=
    rdN_frame fun j hj => f1 _ (by omega) (.inl (by omega)) (.inl (by omega))
  rcases hR c f ω1 μ1 st sp r H1 a0 (a1.trans h1) a7 a8 a9 hs2 hs3 hs1
    (DesignateAlloc.rd8 (by omega) n1) (DesignateAlloc.rd8 (by omega) n2)
    (DesignateAlloc.rd8 (by omega) n3) (DesignateAlloc.rd8 (by omega) n4)
    (DesignateAlloc.rd8 (by omega) n5) (DesignateAlloc.rd8 (by omega) n6)
    (fun a h1 h2 => by rw [rd1]; rw [e984, e992] at *; exact hstr a h1 h2) hr1
    (by rw [e1000]; exact DesignateAlloc.rd8 (by split <;> omega) n7)
    (by rw [e1000]; exact DesignateAlloc.rd8 (by split <;> omega) n8) with
    ⟨s', ω2, μ2, N2, kc, kp, run2, H2, b1, b5, b6, m2c, m2p, hfb, hkeep, fr2, gl2⟩ | hX
  rotate_left
  · exact .inr (ResStore.ExhaustsP.pre run1 hX)
  have hSt2 := H2.st
  -- 14376 → 14401
  have bc := ResultsDrop.rdN_lt8 μ2 (sp + 1144)
  have bp := ResultsDrop.rdN_lt8 μ2 (sp + 1152)
  rw [m2c] at bc; rw [m2p] at bp
  obtain ⟨ω3, run3, c1, c5, c6⟩ := il_tail_a (R := KeepCtx (accContractS env)) (P := P) (c, f) ω2 μ2 sp kc kp
    (rdN μ2 (sp + 1160) 8) (b1.trans (a1.trans h1)) ⟨by omega, by omega⟩ bc bp (ResultsDrop.rdN_lt8 _ _)
    (by rw [← m2c]; exact KeyEnc.readN_enc μ2 _ 8) (by rw [← m2p]; exact KeyEnc.readN_enc μ2 _ 8)
    (KeyEnc.readN_enc μ2 _ 8) (fun a h1 h2 => Memory.readable_of_writable (hSt2 a (by omega) (by omega)))
  have g1 : (setR7 ω3 Result.WHAT)[1] = ω[1] := by
    rw [setR7_ne' _ _ 1 (by decide) (by decide), c1, b1, a1]
  have g5 : (setR7 ω3 Result.WHAT)[5] = UInt64.ofNat kc := by rw [setR7_ne' _ _ 5 (by decide) (by decide), c5]
  have g6 : (setR7 ω3 Result.WHAT)[6] = UInt64.ofNat kp := by rw [setR7_ne' _ _ 6 (by decide) (by decide), c6]
  have frA : ∀ a, a < 4294967296 → sp ≤ a → (a < sp + 1144 ∨ sp + 1168 ≤ a) → (a < sp + 1496 ∨ sp + 1512 ≤ a) →
      (a < sp + 1568 ∨ sp + 1616 ≤ a) → μ2.read a = μ.read a := fun a h0 ha hb hc hd => by
    rw [fr2 a h0 ha hb, f1 a h0 hc hd]
  have kA : ∀ d ∈ chunks st, d.used = true → d ∈ chunks s' ∧ ∀ a, InData d a → μ2.read a = μ.read a :=
    fun d hd hu => by
      obtain ⟨hd2, hk⟩ := hkeep d hd hu
      refine ⟨hd2, fun a ha => ?_⟩
      have := ResultsDrop.data_lt H hd ha
      rw [hk a ha, f1 a (by omega) (.inl (by omega)) (.inl (by omega))]
  by_cases hc0 : kc = 0
  · -- no buffer: 14403 → 14420
    subst hc0
    obtain ⟨ω4, run4, d1⟩ := il_tail_b0 (R := KeepCtx (accContractS env)) (P := P) (c, f) (setR7 ω3 Result.WHAT)
      μ2 g5
    exact .inl ⟨s', ω4, μ2, _, run1.trans (run2.trans (run3.trans (FreeStepsH.logS env f (d_14401 (P := P)) run4))), H2,
      d1.trans g1, kA, frA, fun a ha => by
        have hg := ha; unfold Glob at hg
        rw [gl2 a ha, f1 a (by omega) (.inl (by omega)) (.inl (by omega))]⟩
  · -- 14403 → 40613 → 14420
    obtain ⟨ω4, run4, d0, d1, d5, d6, d7, d8, d9⟩ := il_tail_b1 (R := KeepCtx (accContractS env)) (P := P) (c, f)
      (setR7 ω3 Result.WHAT) μ2 kc kp g5 g6 bc hc0 bp
    obtain ⟨ch, hch, hcu, hca, hfr⟩ := hfb.resolve_left hc0
    obtain ⟨ω5, μ5, run5, H5, -, -, -, k5, gl5, kd5, e0, e1, -, -⟩ := Decode.DeallocCall.dealloc_callG (R := KeepCtx (accContractS env))
      (P := P) env.code pb S0 S1 (c, f) ω4 μ2 s' sp kp 536 14420 ch H2 hch hcu hca d0 (d1.trans (g1.trans h1)) d7
      (by decide) jte_267 bs_14420 (by omega) ⟨by omega, by omega⟩
    refine .inl ⟨free s' kp, ω5, μ5, _,
      run1.trans (run2.trans (run3.trans (FreeStepsH.logS env f (d_14401 (P := P)) (run4.trans run5)))), H5,
      e1.trans (d1.trans g1), fun d hd hu => ?_, fun a h0 ha hb hc hd => ?_, fun a ha => ?_⟩
    · obtain ⟨hd2, hk⟩ := kA d hd hu
      obtain ⟨hd5, hk5⟩ := kd5 d hd2 hu (hfr d hd hu)
      exact ⟨hd5, fun a ha => (hk5 a ha).trans (hk a ha)⟩
    · rw [k5 a h0 ha, frA a h0 ha hb hc hd]
    · have hg := ha; unfold Glob at hg
      rw [gl5 a ha, gl2 a ha, f1 a (by omega) (.inl (by omega)) (.inl (by omega))]

/-- An allocated chunk's data lies at or above 196608 (the read-only octets below are not writable). -/
theorem data_ge {code : ByteArray} {pb S0 S1 : Nat} {μ : Memory} {s : State}
    (H : HeapCtxC code pb S0 S1 μ s) {d : Chunk} (hd : d ∈ chunks s) (hu : d.used = true) {a : Nat}
    (ha : InData d a) : 196608 ≤ a := by
  refine Classical.byContradiction fun hlt => ?_
  have h1 := HeapKeep.writableData H hd hu ha
  rw [H.ro a (by omega)] at h1
  exact absurd h1 (by decide)

/-- A global (196616 … 196791) lies below every allocated chunk (the heap's base is 206864 or above). -/
theorem glob_lt {code : ByteArray} {pb S0 S1 : Nat} {μ : Memory} {s : State}
    (H : HeapCtxC code pb S0 S1 μ s) {d : Chunk} (hd : d ∈ chunks s) (hu : d.used = true) {a : Nat}
    (ha : Glob a) : a < d.addr := by
  have := (Services.Bootstrap.Decode.VecU8.chunk_in H.wf hd hu).1
  have := H.hb0
  unfold Glob at ha
  omega

/-- The new buffer d′ of the results `Vec` (data rp′, room for cp′ items) against st: allocated in st′,
    and every other allocated chunk of st (data address ≠ rp) is not d′ and is kept with its data. -/
def NewBuf (st st' : State) (μ μ' : Memory) (rp rp' cp' : Nat) : Prop :=
  ∃ d' ∈ chunks st', d'.used = true ∧ d'.addr + 32 = rp' ∧ rp' + 144 * cp' ≤ d'.addr + 32 * d'.size ∧
    ∀ d ∈ chunks st, d.used = true → d.addr + 32 ≠ rp → d ≠ d' ∧ d ∈ chunks st' ∧
      ∀ a, InData d a → μ'.read a = μ.read a

/-- **14420 … 14516, the push**: with the results `Vec` { cp, rp, n } at sp + 448 (n ≤ cp; a buffer
    chunk with room for cp items if cp ≠ 0), either the run reaches 14516 with ω₁ kept, ω₅ = n, the
    allocator's context for some st′, a `Vec` { cp′, rp′, n } with n < cp′ in a buffer `NewBuf`, the
    first n items kept, the result's 144 octets at sp + 1000 copied to item n, and from sp up only
    sp + 448 … sp + 464 changed, the globals kept; or the growth fails (`ExhaustsP`). -/
theorem il_tail_push {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : AccEnv)
    {pb S0 S1 : Nat} (hP : PushH p env pb S0 S1) (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory)
    (st : State) (sp cp rp n : Nat) (H : HeapCtxC env.code pb S0 S1 μ st)
    (h1 : ω[1] = UInt64.ofNat sp) (hs1 : 2147483648 + 4096 ≤ sp) (hs2 : S0 + 4096 ≤ sp)
    (hs3 : sp + 1632 ≤ S1) (hs8 : sp % 8 = 0)
    (mcp : rdN μ (sp + 448) 8 = cp) (mrp : rdN μ (sp + 456) 8 = rp) (mn : rdN μ (sp + 464) 8 = n)
    (hncp : n ≤ cp)
    (hbuf : cp ≠ 0 → ∃ d ∈ chunks st, d.used = true ∧ d.addr + 32 = rp ∧ rp + 144 * cp ≤ d.addr + 32 * d.size) :
    (∃ (st' : State) (ω' : Regs) (μ' : Memory) (N cp' rp' : Nat),
      FreeStepsH p (KeepCtx (accContractS env)) 14420 ω μ (c, f) 14516 ω' μ' (c, f) N ∧
      HeapCtxC env.code pb S0 S1 μ' st' ∧ ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat n ∧
      rdN μ' (sp + 448) 8 = cp' ∧ rdN μ' (sp + 456) 8 = rp' ∧ rdN μ' (sp + 464) 8 = n ∧ n < cp' ∧
      NewBuf st st' μ μ' rp rp' cp' ∧
      μ'.readN rp' (144 * n) = μ.readN rp (144 * n) ∧ μ'.readN (rp' + 144 * n) 144 = μ.readN (sp + 1000) 144 ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < sp + 448 ∨ sp + 464 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a)) ∨
    ExhaustsP p env pb 14420 ω μ c f := by
  have hT := H.hS1
  have hSt := H.st
  have rd : ∀ a, S0 ≤ a → a < S1 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hSt a h1 h2)
  have bcp := ResultsDrop.rdN_lt8 μ (sp + 448)
  have brp := ResultsDrop.rdN_lt8 μ (sp + 456)
  have bn := ResultsDrop.rdN_lt8 μ (sp + 464)
  rw [mcp] at bcp; rw [mrp] at brp; rw [mn] at bn
  have ecp : μ.readN (sp + 448) 8 = Num.encodeLE 8 cp := by rw [← mcp]; exact KeyEnc.readN_enc μ _ 8
  have erp : μ.readN (sp + 456) 8 = Num.encodeLE 8 rp := by rw [← mrp]; exact KeyEnc.readN_enc μ _ 8
  have en : μ.readN (sp + 464) 8 = Num.encodeLE 8 n := by rw [← mn]; exact KeyEnc.readN_enc μ _ 8
  /- The copy of the result into a buffer chunk d (data q, room for k items, n < k), from 14485's or
     14420's memcpy call: the memcpy and what it keeps. -/
  have copy : ∀ (ω₀ : Regs) (μ₀ : Memory) (s₀ : State) (q k : Nat) (d : Chunk),
      HeapCtxC env.code pb S0 S1 μ₀ s₀ → d ∈ chunks s₀ → d.used = true → d.addr + 32 = q →
      q + 144 * k ≤ d.addr + 32 * d.size → n < k →
      ω₀[0] = UInt64.ofNat 540 → ω₀[1] = UInt64.ofNat sp → ω₀[7] = UInt64.ofNat (q + 144 * n) →
      ω₀[8] = UInt64.ofNat (sp + 1000) → ω₀[9] = UInt64.ofNat 144 →
      ∃ ω' μ', FreeStepsH p (KeepCtx (accContractS env)) 68729 ω₀ μ₀ (c, f) 14516 ω' μ' (c, f) (7 * 144 + 320) ∧
        HeapCtxC env.code pb S0 S1 μ' s₀ ∧ ω'[1] = ω₀[1] ∧ ω'[5] = ω₀[5] ∧
        μ'.readN (q + 144 * n) 144 = μ₀.readN (sp + 1000) 144 ∧
        (∀ a, a < 4294967296 → (a < q + 144 * n ∨ q + 144 * n + 144 ≤ a) → (a < sp - 48 ∨ sp ≤ a) →
          μ'.read a = μ₀.read a) ∧
        (∀ e ∈ chunks s₀, e.used = true → e ≠ d → ∀ a, InData e a → μ'.read a = μ₀.read a) := by
    intro ω₀ μ₀ s₀ q k d H₀ hd hu hq hk hnk g0 g1 g7 g8 g9
    have hdlo := data_ge H₀ hd hu (a := q + 144 * n) ⟨by omega, by omega⟩
    have hdhi := ResultsDrop.data_lt H₀ hd (a := q + 144 * n + 143) ⟨by omega, by omega⟩
    have hSt0 := H₀.st
    obtain ⟨ω', μ', run, e0, e1, e5, e6, m, fr, rdd, wrr⟩ := memcpy_val (R := KeepCtx (accContractS env))
      (P := P) (c, f) ω₀ μ₀ 540 14516 sp (q + 144 * n) (sp + 1000) 144 g0 g1 g7 g8 g9 (by decide) jte_269 bs_14516
      ⟨by omega, by omega, hs8⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (.inl (by omega)) (.inr (by omega))
      (.inl (by omega)) (fun a h1 h2 => Memory.readable_of_writable (hSt0 a (by omega) (by omega)))
      (fun a h1 h2 => HeapKeep.writableData H₀ hd hu (a := a) ⟨by omega, by omega⟩)
      (fun a h1 h2 => hSt0 a (by omega) (by omega))
    refine ⟨ω', μ', run, HeapKeep.keepData H₀ hd (fun a ha ho => fr a (by omega) (by omega) (.inl (by omega)))
      wrr, e1, e5, m, fun a h0 ha hs => fr a h0 ha hs, fun e he heu hne a ha => ?_⟩
    · have hlt := ResultsDrop.data_lt H₀ he ha
      refine fr a (by omega) ?_ (.inl (by omega))
      refine Classical.byContradiction fun hin => ?_
      exact hne (RowEleven.chunk_uniq H₀.wf he hd ha ⟨by omega, by omega⟩)
  have hrd : ∀ a, sp + 448 ≤ a → a < sp + 472 → μ.readable a = true := fun a h1 h2 => rd a (by omega) (by omega)
  rcases Nat.lt_or_ge n cp with hlt | hge
  · -- room
    obtain ⟨d, hd, hu, hq, hk⟩ := hbuf (by omega)
    have hhi := ResultsDrop.data_lt H hd (a := rp + 144 * n) ⟨by omega, by omega⟩
    obtain ⟨ω1, run1, a0, a1, a5, a7, a8, a9⟩ := il_push (R := KeepCtx (accContractS env)) (P := P) (c, f) ω μ sp
      cp rp n h1 ⟨by omega, by omega⟩ bcp bn (by omega) (by omega) ecp erp en hrd
    obtain ⟨ω2, μ2, run2, H2, b1, b5, m2, fr2, ke2⟩ := copy ω1 μ st rp cp d H hd hu hq hk hlt a0 (a1.trans h1)
      a7 a8 a9
    have fhi : ∀ a, a < 4294967296 → sp ≤ a → μ2.read a = μ.read a := fun a h0 ha =>
      fr2 a h0 (.inr (by omega)) (.inr ha)
    refine .inl ⟨st, ω2, μ2, _, cp, rp, run1.trans run2, H2, b1.trans a1, b5.trans a5, ?_, ?_, ?_, hlt,
      ⟨d, hd, hu, hq, hk, fun e he heu hne => ⟨fun h => hne (by subst h; exact hq), he,
        ke2 e he heu (fun h => hne (by subst h; exact hq))⟩⟩,
      Memory.readN_congr fun j hj => fr2 _ (by omega) (.inl (by omega)) (.inl (by omega)), m2,
      fun a h0 ha _ => fhi a h0 ha, fun a ha => by
        have hg := ha; unfold Glob at hg
        have := glob_lt H hd hu ha
        exact fr2 a (by omega) (.inl (by omega)) (.inl (by omega))⟩
    · rw [rdN_frame fun j hj => fhi _ (by omega) (by omega)]; exact mcp
    · rw [rdN_frame fun j hj => fhi _ (by omega) (by omega)]; exact mrp
    · rw [rdN_frame fun j hj => fhi _ (by omega) (by omega)]; exact mn
  · -- full: 14420 → 14431 → `finish_grow` → 14485 → memcpy → 14516
    have hcn : cp = n := by omega
    subst hcn
    obtain ⟨ω1, run1, a1, a5, a6⟩ := il_full (R := KeepCtx (accContractS env)) (P := P) (c, f) ω μ sp cp h1
      ⟨by omega, by omega⟩ bcp ecp en hrd
    rcases hP c f ω1 μ st sp rp cp H (a1.trans h1) a5 hs2 hs3 hs1 mcp mrp mn (fun h => hbuf h) with
      ⟨st', ω2, μ2, N2, cp', rp', run2, H2, b1, b5, m2cp, hlt, m2rp, mv, ⟨d', hd', hu', hq', hk', hkeep⟩, fr2, gl2⟩ | hX
    rotate_left
    · exact .inr (ResStore.ExhaustsP.pre run1 hX)
    have hhi := ResultsDrop.data_lt H2 hd' (a := rp' + 144 * cp) ⟨by omega, by omega⟩
    have hrd2 : ∀ a, sp + 456 ≤ a → a < sp + 464 → μ2.readable a = true := fun a h1 h2 =>
      Memory.readable_of_writable (H2.st a (by omega) (by omega))
    obtain ⟨ω3, run3, c0, c1, c5, c7, c8, c9⟩ := il_push2 (R := KeepCtx (accContractS env)) (P := P) (c, f) ω2 μ2
      sp rp' cp (b1.trans (a1.trans h1)) (b5.trans a5) ⟨by omega, by omega⟩ (by omega)
      (by rw [← m2rp]; exact KeyEnc.readN_enc μ2 _ 8) hrd2
    obtain ⟨ω4, μ4, run4, H4, e1, e5, m4, fr4, ke4⟩ := copy ω3 μ2 st' rp' cp' d' H2 hd' hu' hq' hk' hlt c0
      (c1.trans (b1.trans (a1.trans h1))) c7 c8 c9
    have fhi : ∀ a, a < 4294967296 → sp ≤ a → μ4.read a = μ2.read a := fun a h0 ha =>
      fr4 a h0 (.inr (by omega)) (.inr ha)
    have fhi2 : ∀ a, a < 4294967296 → sp ≤ a → (a < sp + 448 ∨ sp + 464 ≤ a) → μ4.read a = μ.read a :=
      fun a h0 ha hb => (fhi a h0 ha).trans (fr2 a h0 ha hb)
    refine .inl ⟨st', ω4, μ4, _, cp', rp', run1.trans (run2.trans (run3.trans run4)), H4,
      e1.trans (c1.trans (b1.trans a1)), e5.trans (c5.trans (b5.trans a5)), ?_, ?_, ?_, hlt,
      ⟨d', hd', hu', hq', hk', fun e he heu hne => ?_⟩, ?_, ?_, fhi2, fun a ha => ?_⟩
    · rw [rdN_frame fun j hj => fhi _ (by omega) (by omega)]; exact m2cp
    · rw [rdN_frame fun j hj => fhi _ (by omega) (by omega)]; exact m2rp
    · rw [rdN_frame fun j hj => fhi2 _ (by omega) (by omega) (.inr (by omega))]; exact mn
    · obtain ⟨hne', he', hk2⟩ := hkeep e he heu hne
      exact ⟨hne', he', fun a ha => (ke4 e he' heu hne' a ha).trans (hk2 a ha)⟩
    · rw [← mv]; exact Memory.readN_congr fun j hj => fr4 _ (by omega) (.inl (by omega)) (.inl (by omega))
    · rw [m4]; exact Memory.readN_congr fun j hj => fr2 _ (by omega) (by omega) (.inr (by omega))
    · have hg := ha; unfold Glob at hg
      have := glob_lt H2 hd' hu' ha
      rw [fr4 a (by omega) (.inl (by omega)) (.inl (by omega)), gl2 a ha]

/-- **14516 … 8540, the loop's back edge**: with ω₅ = n, the instruction's `String` { kc, kp, _ } at
    sp + 976 (kp the data of an allocated chunk ch if kc ≠ 0): len := n + 1 at sp + 464, the `String`
    freed (state `(optBuf kc kp).foldl free st`), every other allocated chunk kept with its data, and
    from sp up only sp + 464 … sp + 472 changed, the globals kept. -/
theorem il_tail_post {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : AccEnv)
    {pb S0 S1 : Nat} (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory)
    (st : State) (sp n kc kp : Nat) (H : HeapCtxC env.code pb S0 S1 μ st)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat n) (hs1 : 2147483648 + 4096 ≤ sp)
    (hs2 : S0 + 4096 ≤ sp) (hs3 : sp + 1632 ≤ S1) (hn : n + 1 < 2 ^ 64)
    (mc : rdN μ (sp + 976) 8 = kc) (mq : rdN μ (sp + 984) 8 = kp)
    (hstr : kc ≠ 0 → ∃ ch ∈ chunks st, ch.used = true ∧ ch.addr + 32 = kp) :
    ∃ (ω' : Regs) (μ' : Memory) (N : Nat),
      FreeStepsH p (KeepCtx (accContractS env)) 14516 ω μ (c, f) 8540 ω' μ' (c, f) N ∧
      HeapCtxC env.code pb S0 S1 μ' ((InstrRep.optBuf kc kp).foldl free st) ∧ ω'[1] = ω[1] ∧
      rdN μ' (sp + 464) 8 = n + 1 ∧
      (∀ d ∈ chunks st, d.used = true → d.addr + 32 ∉ InstrRep.optBuf kc kp →
        d ∈ chunks ((InstrRep.optBuf kc kp).foldl free st) ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < sp + 464 ∨ sp + 472 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) := by
  have hT := H.hS1
  have hSt := H.st
  have bc := ResultsDrop.rdN_lt8 μ (sp + 976)
  have bq := ResultsDrop.rdN_lt8 μ (sp + 984)
  rw [mc] at bc; rw [mq] at bq
  have ec : μ.readN (sp + 976) 8 = Num.encodeLE 8 kc := by rw [← mc]; exact KeyEnc.readN_enc μ _ 8
  have eq : μ.readN (sp + 984) 8 = Num.encodeLE 8 kp := by rw [← mq]; exact KeyEnc.readN_enc μ _ 8
  by_cases hc0 : kc = 0
  · subst hc0
    rw [show InstrRep.optBuf 0 kp = [] from rfl, List.foldl_nil]
    obtain ⟨ω1, μ1, run1, a1, m1, fr1, rd1, wr1⟩ := il_post0 (R := KeepCtx (accContractS env)) (P := P) (c, f) ω μ
      sp n h1 h5 ⟨by omega, by omega⟩ hn ec (fun a h1 h2 => Memory.readable_of_writable (hSt a (by omega) (by omega)))
      (fun a h1 h2 => hSt a (by omega) (by omega))
    refine ⟨ω1, μ1, _, run1, HeapKeep.keepHi H (fun a ha => fr1 a (by omega) (.inl (by omega))) wr1, a1,
      DesignateAlloc.rd8 hn m1, fun d hd hu _ => ⟨hd, fun a ha => ?_⟩, fun a h0 _ hb => fr1 a h0 hb,
      fun a ha => by have hg := ha; unfold Glob at hg; exact fr1 a (by omega) (.inl (by omega))⟩
    have := ResultsDrop.data_lt H hd ha
    exact fr1 a (by omega) (.inl (by omega))
  · obtain ⟨ch, hch, hcu, hca⟩ := hstr hc0
    obtain ⟨ω1, μ1, run1, a0, a1, a7, a8, a9, m1, fr1, rd1, wr1⟩ := il_post1 (R := KeepCtx (accContractS env))
      (P := P) (c, f) ω μ sp n kc kp h1 h5 ⟨by omega, by omega⟩ hn bc hc0 bq ec eq
      (fun a h1 h2 => Memory.readable_of_writable (hSt a (by omega) (by omega)))
      (fun a h1 h2 => hSt a (by omega) (by omega))
    have H1 : HeapCtxC env.code pb S0 S1 μ1 st := HeapKeep.keepHi H (fun a ha => fr1 a (by omega) (.inl (by omega))) wr1
    obtain ⟨ω2, μ2, run2, H2, -, -, -, k2, gl2, kd2, e0, e1, -, -⟩ := Decode.DeallocCall.dealloc_callG
      (R := KeepCtx (accContractS env)) (P := P) env.code pb S0 S1 (c, f) ω1 μ1 st sp kp 542 14546 ch H1 hch hcu hca
      a0 (a1.trans h1) a7 (by decide) jte_270 bs_14546 (by omega) ⟨by omega, by omega⟩
    have ob : InstrRep.optBuf kc kp = [kp] := by unfold InstrRep.optBuf; simp [hc0]
    rw [ob, List.foldl_cons, List.foldl_nil]
    refine ⟨ω2, μ2, _, run1.trans (run2.trans (il_back (R := KeepCtx (accContractS env)) (P := P) (c, f) ω2 μ2)), H2,
      e1.trans a1, ?_, fun d hd hu hnot => ?_, fun a h0 ha hb => ?_, fun a ha => ?_⟩
    · rw [rdN_frame fun j hj => k2 _ (by omega) (by omega)]; exact DesignateAlloc.rd8 hn m1
    · have hne : d ≠ ch := fun h => hnot (by subst h; simp [hca])
      obtain ⟨hd2, hk2⟩ := kd2 d hd hu hne
      refine ⟨hd2, fun a ha => ?_⟩
      have := ResultsDrop.data_lt H hd ha
      rw [hk2 a ha, fr1 a (by omega) (.inl (by omega))]
    · rw [k2 a h0 ha, fr1 a h0 hb]
    · have hg := ha; unfold Glob at hg
      rw [gl2 a ha, fr1 a (by omega) (.inl (by omega))]

end Services.Bootstrap.Acc.Handlers.InstrLoop
