import Services.Bootstrap.Refine.ExportStep
import Services.Bootstrap.Refine.Lookup
import Services.Bootstrap.Refine.LookupRun

/-!
# The eager `Lookup` step: from the loop head to the wrapper's return

The first half of the step 5042 → 5042 for an eager `Lookup` (index 8, flag octet 44 set): the element is staged
(`Pass.pa`, `memcpy_any`), dispatched into the eager handler (`Lookup.ld`), the length query set up (`Lookup.la`), and
`foreign_historical_lookup` run (`LookupRun.lookup_wrap`) to 5372 with the result at M + 560 (`Done`), or an allocation
fails. GP v0.8.0 Appendix B.4 (Ψ_R running bootstrap's code) and B.6 (historical_lookup, Ω_H).
-/

namespace Services.Bootstrap.Refine.LookupStep

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeR
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Refine.PassLoop Services.Bootstrap.Refine.LookupRun Services.Bootstrap.Refine.LookupHost

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- i … 5288: the `Lookup` element at cur (D = 2^63 + 7, its octet 44, the eager flag, nonzero) is staged: cursor
    and `IntoIter` pointer advanced to cur + 232, D at M + 304, its octets 8 … 232 at M + 312 … M + 536; then into the
    eager handler. Memory changes as in `ExportStep.xhead`. -/
theorem lhead {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] {X : Type}
    {R : HostRel X} (x : X) (ω : Regs) (μ : Memory) (M cur en : Nat)
    (hM : 65536 + 48 ≤ M ∧ M + 632 < 4294967296 ∧ M % 8 = 0)
    (hcur : 65536 ≤ cur ∧ cur + 232 + 24 < 4294967296) (hcM : cur + 232 + 24 ≤ M - 48 ∨ M + 632 ≤ cur)
    (hne : cur ≠ en) (hen : en < 18446744073709551616) (h1 : ω[1] = UInt64.ofNat M) (i : Nat)
    (hi : (i = 5042 ∧ μ.readN (M + 144) 8 = Num.encodeLE 8 cur) ∨ (i = 5054 ∧ ω[5] = UInt64.ofNat cur))
    (s120 : μ.readN (M + 120) 8 = Num.encodeLE 8 en)
    (sD : μ.readN cur 8 = Num.encodeLE 8 (9223372036854775807 + 8))
    (hflag : rdN μ (cur + 44) 1 ≠ 0)
    (s128 : μ.readN (M + 128) 8 = Num.encodeLE 8 9223372036854775832)
    (s136 : μ.readN (M + 136) 8 = Num.encodeLE 8 9223372036854775809)
    (hrc : ∀ a, cur ≤ a → a < cur + 232 → μ.readable a = true)
    (hwM : ∀ a, M - 48 ≤ a → a < M + 632 → μ.writable a = true) :
    ∃ ω' μ' N, FreeStepsH p R i ω μ x 5288 ω' μ' x N ∧ ω'[1] = UInt64.ofNat M ∧
      ω'[5] = UInt64.ofNat cur ∧ ω'[6] = UInt64.ofNat (9223372036854775807 + 8) ∧
      μ'.readN (M + 144) 8 = Num.encodeLE 8 (cur + 232) ∧ μ'.readN (M + 280) 8 = Num.encodeLE 8 (cur + 232) ∧
      μ'.readN (M + 304) 8 = Num.encodeLE 8 (9223372036854775807 + 8) ∧
      μ'.readN (M + 312) 224 = μ.readN (cur + 8) 224 ∧
      (∀ a, a < 4294967296 → (a < M - 48 ∨ (M ≤ a ∧ a < M + 144) ∨ (M + 152 ≤ a ∧ a < M + 280) ∨
        (M + 288 ≤ a ∧ a < M + 304) ∨ M + 536 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hM0, hM1, hM8⟩ := hM
  have hr : ∀ a, M - 48 ≤ a → a < M + 632 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwM a h1 h2)
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, a144, a304, a280, afr, ard, awr⟩ := Pass.pa (p := p) (P := P)
    (R := R) x ω μ M cur en (9223372036854775807 + 8) (by omega) (by omega) (by omega) hne hen (by omega)
    (by omega) h1 i hi s120 sD (fun a h1 h2 => hr a (by omega) (by omega))
    (fun a h1 h2 => hrc a h1 (by omega)) (fun a h1 h2 => hwM a (by omega) (by omega))
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, bd, bfr, brd, bwr⟩ := memcpy_any (p := p) (P := P) (R := R) x ω1 μ1
    162 5095 M (M + 312) (cur + 8) 224 a0 a1 a7 a8 a9 ⟨by decide, by decide, by decide⟩ jte_80 bs_5095
    ⟨by omega, by omega, hM8⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega) (by omega)
    (fun a h1 h2 => by rw [ard]; exact hrc a (by omega) (by omega))
    (fun a h1 h2 => by rw [awr]; exact hwM a (by omega) (by omega))
    (fun a h1 h2 => by rw [awr]; exact hwM a (by omega) (by omega))
  have k2 : ∀ a, a < 4294967296 → (a < M - 48 ∨ (M ≤ a ∧ a < M + 144) ∨ (M + 152 ≤ a ∧ a < M + 280) ∨
      (M + 288 ≤ a ∧ a < M + 304) ∨ M + 536 ≤ a) → μ2.read a = μ.read a :=
    fun a h0 h1 => by rw [bfr a h0 (by omega) (by omega), afr a h0 (by omega)]
  -- the staged octets: those of the element, in μ
  have e1 : μ1.readN (cur + 8) 224 = μ.readN (cur + 8) 224 :=
    Memory.readN_congr (fun j hj => afr _ (by omega) (by omega))
  have bd' : μ2.readN (M + 312) 224 = μ.readN (cur + 8) 224 := by rw [bd, e1]
  have fl : rdN μ2 (M + 348) 1 ≠ 0 := by
    have h2 := Decode.Loop.readN_sub μ2 (M + 312) 224 36 1 _ bd' (by omega)
    have h0 := Decode.Loop.readN_sub μ (cur + 8) 224 36 1 _ rfl (by omega)
    rw [show M + 312 + 36 = M + 348 by omega] at h2
    rw [show cur + 8 + 36 = cur + 44 by omega] at h0
    unfold rdN at hflag ⊢
    rw [h2, ← h0]; exact hflag
  obtain ⟨ω3, run3, c1, c5, c6⟩ := Lookup.ld (p := p) (P := P) (R := R) x ω2 μ2 M fl (by omega) b1 (by rw [b6, a6])
    (by rw [Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega))]; exact s128)
    (by rw [Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega))]; exact s136)
    (fun a h1 h2 => by rw [brd, ard]; exact hr a (by omega) (by omega))
    (fun a h1 h2 => by rw [brd, ard]; exact hr a (by omega) (by omega))
  refine ⟨ω3, μ2, _, run1.trans (run2.trans run3), by rw [c1, b1], by rw [c5, b5, a5], by rw [c6, b6, a6],
    ?_, ?_, ?_, bd', k2, fun a => by rw [brd, ard], fun a => by rw [bwr, awr]⟩
  · rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega) (by omega))]; exact a144
  · rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega) (by omega))]; exact a280
  · rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega) (by omega))]; exact a304

/-- The historical lookup of the hash h in service svc's account (GP v0.8.0 eq. B.6, Ω_H's 𝐯). -/
def lookupOf (env : RefineHost.Env) (svc : Nat) (h : List UInt8) : Option (List UInt8) :=
  (env.accounts.get? svc).bind fun a => a.historicalLookup env.lookupSlot h

theorem lookupVal_of {env : RefineHost.Env} {ω : Regs} {μ : Memory} {svc : Nat} {h : List UInt8}
    (h7 : reg ω 7 = svc) (hh : μ.readN (reg ω 8) 32 = h) : lookupVal env ω μ = lookupOf env svc h := by
  unfold lookupVal lookupOf; rw [h7, hh]

/-- 32 octets as four words. -/
theorem readN32 (μ μ' : Memory) (a b : Nat) (h0 : μ'.readN a 8 = μ.readN b 8)
    (h8 : μ'.readN (a + 8) 8 = μ.readN (b + 8) 8) (h16 : μ'.readN (a + 16) 8 = μ.readN (b + 16) 8)
    (h24 : μ'.readN (a + 24) 8 = μ.readN (b + 24) 8) : μ'.readN a 32 = μ.readN b 32 := by
  rw [show (32 : Nat) = 8 + (8 + (8 + 8)) from rfl, Memory.readN_split, Memory.readN_split, Memory.readN_split,
    Memory.readN_split μ, Memory.readN_split μ, Memory.readN_split μ]
  rw [show a + 8 + 8 = a + 16 by omega, show a + 16 + 8 = a + 24 by omega, show b + 8 + 8 = b + 16 by omega,
    show b + 16 + 8 = b + 24 by omega, h0, h8, h16, h24]

/-- **The eager `Lookup`, i … 5372**: from `PInv k` at i, with element k a `Lookup` (D = 2^63 + 7) whose flag octet 44
    is set, service id svc (its octets 8 … 12) and hash h (its octets 12 … 44): the element is staged, the length query
    made and `foreign_historical_lookup` run, reaching 5372 with the result `lookupOf env svc h` at M + 560 (`ResAt`), the
    heap context for some s' (every allocated chunk of s kept with its data), ω₁ = M, ω₅ = the cursor, the cursor and
    the `IntoIter` pointer advanced, D staged at M + 304, and the frame from M up kept outside the words written.
    Internal hypotheses: the preimage is shorter than 2^63 octets (`hlen`, decision pending with Adam) and the cap
    covers the second Ω_H (`hgas`). Or an allocation fails. -/
theorem lmid {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P]
    (env : RefineHost.Env) (cap0 : Nat) (hcap1 : 134217728 ≤ cap0) (hcap0 : cap0 < 18446744073709551616)
    {pb S0 S1 : Nat} (x : RefineCtx) (ω : Regs) (μ μ0 : Memory) (s : State)
    {M E n capI : Nat} {ce : Chunk} {Kp : Chunk → Prop} {O : Nat → List UInt8 → Prop} {i : Nat}
    (L : LayP S0 S1 M E n ce) (k : Nat) (hk : k < n) (svc : Nat) (h : List UInt8)
    (sD0 : μ0.readN (E + 232 * k) 8 = Num.encodeLE 8 (9223372036854775807 + 8))
    (hflag : rdN μ0 (E + 232 * k + 44) 1 ≠ 0)
    (sv : μ0.readN (E + 232 * k + 8) 4 = Num.encodeLE 4 svc) (hsvc : svc < 4294967296)
    (sh : μ0.readN (E + 232 * k + 12) 32 = h)
    (hlen : ∀ d, lookupOf env svc h = some d → d.length < 9223372036854775808)
    (hgas : ∀ d, lookupOf env svc h = some d → Constants.CgasHconst + memGas Constants.CgasHlinear d.length ≤ cap0)
    (st : PInv env pb S0 S1 M E n ce capI μ0 Kp O i k ω μ s) :
    (∃ (ω' : Regs) (μ' : Memory) (s' : State) (N : Nat),
      FreeStepsH p (refineContractK cap0 env) i ω μ x 5372 ω' μ' x N ∧
      HeapCtx env pb S0 S1 μ' s' ∧ ω'[1] = UInt64.ofNat M ∧ ω'[5] = UInt64.ofNat (E + 232 * k) ∧
      ω'[6] = UInt64.ofNat (9223372036854775807 + 8) ∧
      μ'.readN (M + 144) 8 = Num.encodeLE 8 (E + 232 * k + 232) ∧
      μ'.readN (M + 280) 8 = Num.encodeLE 8 (E + 232 * k + 232) ∧
      μ'.readN (M + 304) 8 = Num.encodeLE 8 (9223372036854775807 + 8) ∧
      (∀ a, a < 4294967296 → M ≤ a → (a < M + 144 ∨ (M + 152 ≤ a ∧ a < M + 168) ∨ (M + 200 ≤ a ∧ a < M + 280) ∨
        (M + 288 ≤ a ∧ a < M + 304) ∨ (M + 536 ≤ a ∧ a < M + 560) ∨ M + 584 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ d ∈ chunks s, d.used = true → d ∈ chunks s' ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
      ResAt μ' (M + 560) (lookupOf env svc h) s s') ∨
    ∃ N, ExhaustsX env cap0 pb p i ω μ x N := by
  obtain ⟨hS0M, hMS1, hM2, hM8⟩ := L.hM
  have hn := L.hn
  obtain ⟨hE0, hE1⟩ := L.hE
  have hEtop := L.hEtop
  have hS1 := st.H.hS1
  have hbT := st.H.hbT
  have hb0 := st.H.hb0
  obtain ⟨hce0, -, hceT⟩ := Decode.VecU8.chunk_in st.H.wf st.hce.1 st.hce.2
  have inE : ∀ a, E ≤ a → a < E + 232 * n → InData ce a := fun a h1 h2 => ⟨by omega, by omega⟩
  have e0 : ∀ a l, E + 232 * k ≤ a → a + l ≤ E + 232 * k + 232 → μ.readN a l = μ0.readN a l :=
    fun a l h1 h2 => Memory.readN_congr (fun j hj => st.data _ (inE _ (by omega) (by omega)))
  have rE : ∀ a, E + 232 * k ≤ a → a < E + 232 * k + 232 → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (Decode.VecU8.heap_writable st.H st.hce.1 st.hce.2 (inE a (by omega) (by omega)))
  have wM : ∀ a, M - 48 ≤ a → a < M + 632 → μ.writable a = true := fun a h1 h2 => st.H.st a (by omega) (by omega)
  have fl : rdN μ (E + 232 * k + 44) 1 ≠ 0 := by
    unfold rdN at hflag ⊢; rw [e0 _ _ (by omega) (by omega)]; exact hflag
  obtain ⟨ω1, μ1, N1, run1, a1, a5, a6, a144, a280, a304, a312, afr, ard, awr⟩ := lhead (p := p) (P := P)
    (R := refineContractK cap0 env) x ω μ M (E + 232 * k) (E + 232 * n) ⟨by omega, by omega, hM8⟩
    ⟨by omega, by omega⟩ (Or.inl (by omega)) (by omega) (by omega) st.h1 i st.cur st.en
    (by rw [e0 _ _ (by omega) (by omega)]; exact sD0) fl st.c128 st.c136 rE wM
  -- the staged service id and hash
  have st312 : μ1.readN (M + 312) 4 = Num.encodeLE 4 svc := by
    have h2 := Decode.Loop.readN_sub μ1 (M + 312) 224 0 4 _ a312 (by omega)
    have h0 := Decode.Loop.readN_sub μ (E + 232 * k + 8) 224 0 4 _ rfl (by omega)
    simp only [Nat.add_zero] at h2 h0
    rw [h2, ← h0, e0 _ _ (by omega) (by omega)]; exact sv
  have hrd : ∀ a, M - 48 ≤ a → a < M + 632 → μ1.readable a = true := fun a h1 h2 => by
    rw [ard]; exact Memory.readable_of_writable (wM a h1 h2)
  obtain ⟨ω2, μ2, run2, b1, b5, b6, b7, b8, b9, b10, b11, b168, b176, b184, b192, bG0, bG8, bG16, bG24, bG32, bG40,
      bfr, brd, bwr⟩ := Lookup.la (p := p) (P := P) (R := refineContractK cap0 env) x ω1 μ1 M (E + 232 * k) svc
    ⟨by omega, by omega, hM8⟩ (by omega) (Or.inl (by omega)) hsvc a1 a5 st312
    (fun a h1 h2 => by rw [ard]; exact rE a (by omega) (by omega)) (fun a h1 h2 => hrd a (by omega) (by omega))
    (fun a h1 h2 => by rw [awr]; exact wM a (by omega) (by omega))
    (fun a h1 h2 => by rw [awr]; exact wM a (by omega) (by omega))
  have l1 : ∀ a l, a + l ≤ M - 48 → μ1.readN a l = μ.readN a l :=
    fun a l hl => Memory.readN_congr (fun j hj => afr _ (by omega) (Or.inl (by omega)))
  have H2 : HeapCtx env pb S0 S1 μ2 s := Decode.GrowOne.ctx_high (Decode.GrowOne.ctx_high st.H
    (fun a ha => afr a (by omega) (Or.inl (by omega))) awr) (fun a ha => bfr a (by omega) (Or.inl (by omega))
    (Or.inl (by omega))) bwr
  have hh : μ2.readN (M + 168) 32 = h := by
    rw [readN32 μ1 μ2 (M + 168) (E + 232 * k + 12) b168 (by rw [b176]) (by rw [b184]) (by rw [b192]), l1 _ _ (by omega),
      e0 _ _ (by omega) (by omega)]
    exact sh
  have hv : lookupVal env ω2 μ2 = lookupOf env svc h :=
    lookupVal_of (by rw [reg_of b7 (by omega)]) (by rw [reg_of b8 (by omega)]; exact hh)
  have pre : Pre env pb S0 S1 (M - 48) svc (M + 168) (M + 560) (E + 232 * k) (9223372036854775807 + 8) ω2 μ2 s :=
    { H := H2
      hG := ⟨by omega, by omega, by omega, by omega, by omega⟩
      hsvc := hsvc
      hr5 := by omega
      hr6 := by omega
      h1 := b1
      h7 := b7
      h8 := b8
      h9 := b9
      h10 := b10
      h11 := b11
      s0 := bG0
      s8 := bG8
      s16 := bG16
      s24 := by rw [bG24, a6]; simp
      s32 := bG32
      s40 := bG40 }
  rcases lookup_wrap (p := p) (P := P) env cap0 ⟨hcap1, hcap0⟩ x pre (by rw [hv]; exact hlen)
      (by rw [hv]; exact hgas) with
    ⟨ω3, μ3, s3, N3, run3, d1, d5, d6, H3, dkeep, dfr, dres⟩ | ⟨j, ω3, μ3, N3, run3, hx⟩
  rotate_left
  · exact Or.inr ⟨_, ω3, μ3, x, j, run1.trans (run2.trans run3), hx⟩
  rw [hv] at dres
  have k12 : ∀ a, a < 4294967296 → M ≤ a → (a < M + 144 ∨ (M + 152 ≤ a ∧ a < M + 168) ∨ (M + 200 ≤ a ∧ a < M + 280) ∨
      (M + 288 ≤ a ∧ a < M + 304) ∨ (M + 536 ≤ a ∧ a < M + 560) ∨ M + 584 ≤ a) → μ2.read a = μ.read a :=
    fun a h0 h1 h2 => by rw [bfr a h0 (Or.inr h1) (by omega), afr a h0 (by omega)]
  refine Or.inl ⟨ω3, μ3, s3, _, run1.trans (run2.trans run3), H3, by rw [d1]; congr 1; omega, d5, d6, ?_, ?_, ?_,
    fun a h0 h1 h2 => by rw [dfr a h0 (by omega) (by omega), k12 a h0 h1 h2], fun d hd hu => ?_, dres⟩
  · rw [show μ3.readN (M + 144) 8 = μ1.readN (M + 144) 8 from Memory.readN_congr (fun j hj => by
      rw [dfr _ (by omega) (by omega) (by omega), bfr _ (by omega) (Or.inr (by omega)) (by omega)])]; exact a144
  · rw [show μ3.readN (M + 280) 8 = μ1.readN (M + 280) 8 from Memory.readN_congr (fun j hj => by
      rw [dfr _ (by omega) (by omega) (by omega), bfr _ (by omega) (Or.inr (by omega)) (by omega)])]; exact a280
  · rw [show μ3.readN (M + 304) 8 = μ1.readN (M + 304) 8 from Memory.readN_congr (fun j hj => by
      rw [dfr _ (by omega) (by omega) (by omega), bfr _ (by omega) (Or.inr (by omega)) (by omega)])]; exact a304
  · obtain ⟨hd3, kd3⟩ := dkeep d hd hu
    refine ⟨hd3, fun a ha => ?_⟩
    have hal := data_lo st.H hd hu ha
    rw [kd3 a ha, bfr a (by omega) (Or.inl (by omega)) (Or.inl (by omega)), afr a (by omega) (Or.inl (by omega))]

end Services.Bootstrap.Refine.LookupStep
