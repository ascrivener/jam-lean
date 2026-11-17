import Services.Bootstrap.Refine.LookupStep
import Services.Bootstrap.Refine.LookupFmt
import Services.Bootstrap.Refine.PInvAdopt
import Services.Bootstrap.Refine.ExportElem

/-!
# The eager `Lookup` step: from the wrapper's return to the loop head

The second half of the step 5042 → 5042 for an eager `Lookup` (index 8): the result `Option<Vec<u8>>` at M + 560 is
formatted (5398 → 59375, the named hypothesis `LookupFmt.LookupFmtOk`), logged (host 100 at 5428) and the `String`
freed (5441); then `LookedUp(result)` is pushed into the output `Vec` (with room, or after `grow_one`), the staged
element dropped (4046, the table entry `Lookup.dropEntry8`) and the loop goes round. GP v0.8.0 Appendix B.4 (Ψ_R
running bootstrap's code) and B.6 (historical_lookup, Ω_H).
-/

namespace Services.Bootstrap.Refine.LookupStep2

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeR
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Refine.PassLoop Services.Bootstrap.Refine.LookupRun Services.Bootstrap.Refine.LookupHost
  Services.Bootstrap.Refine.LookupFmt Services.Bootstrap.Refine.HostSteps Services.Bootstrap.Refine.ExportSeg

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- The wrapper's result, as `format!` needs it: `ResAt` with the preimage shorter than 2^63 octets gives `OptVecAt`
    (`None`; or `Some(Vec)` with cap = len = |d|, its buffer the dangling 1 for `Some []` or a chunk's data). -/
theorem optVec_of_res {env : RefineHost.Env} {pb S0 S1 : Nat} {μ : Memory} {s s' : State} {out : Nat}
    {v : Option (List UInt8)} (H : HeapCtx env pb S0 S1 μ s') (hr : ResAt μ out v s s')
    (hlen : ∀ d, v = some d → d.length < 9223372036854775808) : OptVecAt μ out := by
  cases v with
  | none => exact Or.inl hr
  | some d =>
    obtain ⟨e0, e16, buf, e8, hb⟩ := hr
    have hl := hlen d rfl
    have hbT := H.hbT
    refine Or.inr ⟨d.length, buf, d.length, e0, e8, e16, Nat.le_refl _, hl, ?_, ?_⟩
    · rcases hb with ⟨rfl, rfl⟩ | ⟨c, hc, hcu, hca, hcs, -, -⟩
      · simp
      · obtain ⟨-, -, hT⟩ := Decode.VecU8.chunk_in H.wf hc hcu
        rw [hcs] at hT; omega
    · intro a h1 h2
      rcases hb with ⟨rfl, rfl⟩ | ⟨c, hc, hcu, hca, hcs, -, -⟩
      · simp at h2; omega
      · exact Memory.readable_of_writable (Decode.VecU8.heap_writable H hc hcu ⟨by omega, by rw [hcs]; omega⟩)

/-- `OptVecAt` depends only on its 24 octets and on access. -/
theorem OptVecAt.congr {μ μ' : Memory} {o : Nat} (h : OptVecAt μ o)
    (hk : ∀ a, o ≤ a → a < o + 24 → μ'.read a = μ.read a) (hr : ∀ a, μ'.readable a = μ.readable a) :
    OptVecAt μ' o := by
  have rk : ∀ a l, o ≤ a → a + l ≤ o + 24 → μ'.readN a l = μ.readN a l :=
    fun a l h1 h2 => Memory.readN_congr (fun j hj => hk _ (by omega) (by omega))
  rcases h with h | ⟨cap, ptr, len, e0, e8, e16, hl, hc, hp, hrd⟩
  · exact Or.inl (by rw [rk _ _ (by omega) (by omega)]; exact h)
  · exact Or.inr ⟨cap, ptr, len, by rw [rk _ _ (by omega) (by omega)]; exact e0,
      by rw [rk _ _ (by omega) (by omega)]; exact e8, by rw [rk _ _ (by omega) (by omega)]; exact e16, hl, hc, hp,
      fun a h1 h2 => by rw [hr]; exact hrd a h1 h2⟩

/-- `ResAt` carried along: its 24 octets kept, and the preimage's chunk (when there is one) kept with its data. -/
theorem ResAt.congr {μ μ' : Memory} {out : Nat} {v : Option (List UInt8)} {s s1 s2 : State}
    (h : ResAt μ out v s s1) (hk : ∀ a, out ≤ a → a < out + 24 → μ'.read a = μ.read a)
    (hc : ∀ c ∈ chunks s1, c.used = true → (∀ e ∈ chunks s, e.used = true → e ≠ c) →
      c ∈ chunks s2 ∧ ∀ a, InData c a → μ'.read a = μ.read a) :
    ResAt μ' out v s s2 := by
  have rk : ∀ a l, out ≤ a → a + l ≤ out + 24 → μ'.readN a l = μ.readN a l :=
    fun a l h1 h2 => Memory.readN_congr (fun j hj => hk _ (by omega) (by omega))
  cases v with
  | none => show μ'.readN out 8 = _; rw [rk _ _ (by omega) (by omega)]; exact h
  | some d =>
    obtain ⟨e0, e16, buf, e8, hb⟩ := h
    refine ⟨by rw [rk _ _ (by omega) (by omega)]; exact e0, by rw [rk _ _ (by omega) (by omega)]; exact e16, buf,
      by rw [rk _ _ (by omega) (by omega)]; exact e8, ?_⟩
    rcases hb with h | ⟨c, hcm, hcu, hca, hcs, hfr, hd⟩
    · exact Or.inl h
    · obtain ⟨hc2, kc⟩ := hc c hcm hcu hfr
      refine Or.inr ⟨c, hc2, hcu, hca, hcs, hfr, ?_⟩
      rw [Memory.readN_congr (fun j hj => kc _ ⟨by omega, by rw [hcs]; omega⟩)]; exact hd

/-- **The log line and the `String` freed** (5372 … 5448): `format!` of the result at M + 560 (`LookupFmtOk`), `log`
    (host 100 at 5428), and the `String` at M + 584 freed when its capacity is nonzero. The allocator's context holds
    for some s'; every allocated chunk of s keeps its data; the stack from M up is kept apart from the `format!`
    arguments (M + 536 … M + 552) and the `String` (M + 584 … M + 608). Or an allocation fails. -/
theorem lfmt {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (env : RefineHost.Env)
    (cap0 : Nat) (hcap1 : 134217728 ≤ cap0) (hcap0 : cap0 < 18446744073709551616) {pb S0 S1 : Nat}
    {ro : List UInt8} (fmt : LookupFmtOk p cap0 env pb S0 S1 ro) (x : RefineCtx) (ω : Regs) (μ : Memory) (s : State)
    (H : HeapCtx env pb S0 S1 μ s) (hro : RoData.RoIs ro μ) (M : Nat)
    (hM : S0 + 7560 ≤ M ∧ M + 632 ≤ S1 ∧ 2147484104 ≤ M ∧ M % 8 = 0) (h1 : ω[1] = UInt64.ofNat M)
    (s16 : μ.readN (M + 16) 8 = Num.encodeLE 8 66793) (s24 : μ.readN (M + 24) 8 = Num.encodeLE 8 66506)
    (s32 : μ.readN (M + 32) 8 = Num.encodeLE 8 668) (hopt : OptVecAt μ (M + 560)) :
    (∃ (ω' : Regs) (μ' : Memory) (s' : State) (N : Nat),
      FreeStepsH p (refineContractK cap0 env) 5372 ω μ x 5448 ω' μ' x N ∧ HeapCtx env pb S0 S1 μ' s' ∧
      ω'[1] = UInt64.ofNat M ∧
      (∀ a, a < 4294967296 → M ≤ a → (a < M + 536 ∨ M + 552 ≤ a) → (a < M + 584 ∨ M + 608 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ d ∈ chunks s, d.used = true → d ∈ chunks s' ∧ ∀ a, InData d a → μ'.read a = μ.read a)) ∨
    ∃ N, ExhaustsX env cap0 pb p 5372 ω μ x N := by
  obtain ⟨hS0M, hMS1, hM2, hM8⟩ := hM
  have hS1 := H.hS1
  have wst := H.st
  -- 1. the `format!` call's arguments
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, a536, a544, afr, ard, awr⟩ := Lookup.lf (p := p) (P := P)
    (R := refineContractK cap0 env) x ω μ M ⟨by omega, by omega, hM8⟩ h1 s24 s32
    (fun a h1 h2 => Memory.readable_of_writable (wst a (by omega) (by omega)))
    (fun a h1 h2 => wst a (by omega) (by omega))
  have H1 : HeapCtx env pb S0 S1 μ1 s :=
    Decode.GrowOne.ctx_high H (fun a ha => afr a (by omega) (Or.inl (by omega))) awr
  have r1 : ∀ a l, a + l ≤ 2147483648 → μ1.readN a l = μ.readN a l :=
    fun a l h => Memory.readN_congr (fun j hj => afr _ (by omega) (Or.inl (by omega)))
  have hw1 : ω1[1] = UInt64.ofNat M := a1.trans h1
  -- 2. the `format!` (a hypothesis)
  rcases fmt x ω1 μ1 s M H1 (hro.congr r1) hS0M (by omega) hM8 a0 hw1 a7 a8 a9 a536 a544
      (OptVecAt.congr hopt (fun a h1 h2 => afr a (by omega) (Or.inr (by omega))) ard) with
    ⟨ω2, μ2, s2, N2, cap, ptr, len, run2, H2, c1, c5, c6, cfr, ckeep, c584, c592, c600, hcapb, hptrb, hlen, hbuf⟩ |
      ⟨N2, hx⟩
  rotate_left
  · exact Or.inr ⟨_, ExhaustsX.pre run1 hx⟩
  have hS12 := H2.hS1
  have k2 : ∀ a, a < 4294967296 → M ≤ a → (a < M + 536 ∨ M + 552 ≤ a) → (a < M + 584 ∨ M + 608 ≤ a) →
      μ2.read a = μ.read a := fun a h0 h1 h2 h3 => by rw [cfr a h0 h1 h3, afr a h0 h2]
  have hw2 : ω2[1] = UInt64.ofNat M := c1.trans hw1
  -- 3. the `log` call's arguments, and `log`
  obtain ⟨ω3, run3, d1, d5, d6⟩ := Lookup.ll (p := p) (P := P) (R := refineContractK cap0 env) x ω2 μ2 M cap ptr len
    ⟨by omega, by omega, hM8⟩ (by omega) (by omega) (by omega) hw2
    (by rw [Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega) (by omega) (by omega))]; exact s16)
    c584 c592 c600 (fun a h1 h2 => Memory.readable_of_writable (H2.st a (by omega) (by omega)))
    (fun a h1 h2 => Memory.readable_of_writable (H2.st a (by omega) (by omega)))
  have e1 : (setR7 ω3 Result.WHAT)[1] = UInt64.ofNat M := by
    rw [setR7_getElem _ _ 1 (by decide) (by decide), d1, hw2]
  have e6 : (setR7 ω3 Result.WHAT)[6] = UInt64.ofNat cap := by rw [setR7_getElem _ _ 6 (by decide) (by decide), d6]
  have e5 : (setR7 ω3 Result.WHAT)[5] = UInt64.ofNat ptr := by rw [setR7_getElem _ _ 5 (by decide) (by decide), d5]
  have dk2 : ∀ d ∈ chunks s, d.used = true → d ∈ chunks s2 ∧ ∀ a, InData d a → μ2.read a = μ.read a :=
    fun d hd hu => by
      obtain ⟨hd2, hk2⟩ := ckeep d hd hu
      refine ⟨hd2, fun a ha => ?_⟩
      obtain ⟨-, -, hdT⟩ := Decode.VecU8.chunk_in H.wf hd hu
      have := H.hbT
      unfold InData at ha
      rw [hk2 a ⟨ha.1, ha.2⟩, afr a (by omega) (Or.inl (by omega))]
  -- 4. the `String` freed, or not
  by_cases hc0 : cap = 0
  · subst hc0
    obtain ⟨ω5, run5, f1⟩ := Lookup.lfz (p := p) (P := P) (R := refineContractK cap0 env) x (setR7 ω3 Result.WHAT)
      μ2 e6
    have run := run1.trans (run2.trans (run3.trans
      (FreeStepsH.logRef cap0 ⟨by omega, hcap0⟩ env (d_5428 (p := p) (P := P)) run5)))
    exact Or.inl ⟨ω5, μ2, s2, _, run, H2, by rw [f1, e1], k2, dk2⟩
  · rcases hbuf with h | ⟨c, hc, hcu, hca, hcf⟩
    · exact absurd h hc0
    obtain ⟨ω5, run5, f0, f1, f5, f6, f7⟩ := Lookup.lfr (p := p) (P := P) (R := refineContractK cap0 env) x
      (setR7 ω3 Result.WHAT) μ2 cap hc0 (by omega) e6
    have f7' : ω5[7] = UInt64.ofNat (c.addr + 32) := by rw [f7, e5, hca]
    obtain ⟨ω6, μ6, run6, H6, -, -, -, stk6, -, keep6, g0, g1, g5, g6⟩ := Decode.DeallocCall.dealloc_call
      (R := refineContractK cap0 env) (p := p) (P := P) env pb S0 S1 x ω5 μ2 s2 M
      (c.addr + 32) 174 5448 c H2 hc hcu rfl f0 (by rw [f1, e1]) f7' ⟨by decide, by decide, by decide⟩
      jte_86 bs_5448 (by omega) ⟨by omega, by omega⟩
    have run := run1.trans (run2.trans (run3.trans
      (FreeStepsH.logRef cap0 ⟨by omega, hcap0⟩ env (d_5428 (p := p) (P := P)) (run5.trans run6))))
    refine Or.inl ⟨ω6, μ6, _, _, run, H6, by rw [g1, f1, e1],
      fun a h0 h1 h2 h3 => by rw [stk6 a h0 h1, k2 a h0 h1 h2 h3], fun d hd hu => ?_⟩
    obtain ⟨hd2, hk2⟩ := dk2 d hd hu
    obtain ⟨hd6, hk6⟩ := keep6 d hd2 hu (hcf d hd hu)
    exact ⟨hd6, fun a ha => by rw [hk6 a ha, hk2 a ha]⟩

/-- **`LookedUp(result)` pushed** (5448 … 4046), with room or after growing the output: the result's three words
    {w0, w1, w2} at M + 560 go into slot k behind `LookedUp`'s discriminant word (from M + 8); the output
    `{cap, ptr, k}` becomes `{cap', ptr', k + 1}`, its buffer an allocated chunk none of the chunks of s other than the
    old buffer; slots j < k as they were and slot k satisfies `O k` (`hO`); every other allocated chunk keeps its
    data; the stack from M up is kept apart from M + 248 … M + 272 and M + 584 … M + 608; then into the drop of the
    staged element (4046, return address 178, ω₇ = M + 304). Or the heap is exhausted. -/
theorem lpush {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P]
    (env : RefineHost.Env) (cap0 : Nat) (hcap1 : 134217728 ≤ cap0) (hcap0 : cap0 < 18446744073709551616)
    (x : RefineCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) {pb S0 S1 M n : Nat}
    {O : Nat → List UInt8 → Prop} (k : Nat) (hkn : k < n) (hn : n ≤ 16777216)
    (hM : S0 + 7560 ≤ M ∧ M + 632 ≤ S1 ∧ 2147484104 ≤ M ∧ M % 8 = 0)
    (H : HeapCtx env pb S0 S1 μ s) (h1 : ω[1] = UInt64.ofNat M) (w0 w1 w2 : Nat)
    (hw0 : w0 < 18446744073709551616) (hw1 : w1 < 18446744073709551616) (hw2 : w2 < 18446744073709551616)
    (s560 : μ.readN (M + 560) 8 = Num.encodeLE 8 w0) (s568 : μ.readN (M + 568) 8 = Num.encodeLE 8 w1)
    (s576 : μ.readN (M + 576) 8 = Num.encodeLE 8 w2)
    (s8 : μ.readN (M + 8) 8 = Num.encodeLE 8 9223372036854775825)
    (cap ptr : Nat) (vc : μ.readN (M + 248) 8 = Num.encodeLE 8 cap) (vp : μ.readN (M + 256) 8 = Num.encodeLE 8 ptr)
    (vl : μ.readN (M + 264) 8 = Num.encodeLE 8 k) (hkc : k ≤ cap) (hcapn : cap ≤ 2 * n + 4)
    (hptr : ptr < 2147483648)
    (hold : (cap = 0 ∧ ptr = 8) ∨ ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true ∧ c.size = (232 * cap + 31) / 32 + 1)
    (hout : ∀ j, j < k → O j (μ.readN (ptr + 232 * j) 232))
    (hO : ∀ (μ' : Memory) (a : Nat), μ'.readN a 8 = Num.encodeLE 8 9223372036854775825 →
      μ'.readN (a + 8) 8 = Num.encodeLE 8 w0 → μ'.readN (a + 16) 8 = Num.encodeLE 8 w1 →
      μ'.readN (a + 24) 8 = Num.encodeLE 8 w2 → O k (μ'.readN a 232)) :
    (∃ (ω' : Regs) (μ' : Memory) (s' : State) (N cap' ptr' : Nat),
      FreeStepsH p (refineContractK cap0 env) 5448 ω μ x 4046 ω' μ' x N ∧
      HeapCtx env pb S0 S1 μ' s' ∧ ω'[0] = UInt64.ofNat 178 ∧ ω'[1] = UInt64.ofNat M ∧
      ω'[7] = UInt64.ofNat (M + 304) ∧
      μ'.readN (M + 248) 8 = Num.encodeLE 8 cap' ∧ μ'.readN (M + 256) 8 = Num.encodeLE 8 ptr' ∧
      μ'.readN (M + 264) 8 = Num.encodeLE 8 (k + 1) ∧ k + 1 ≤ cap' ∧ cap' ≤ 2 * n + 4 ∧ ptr' < 2147483648 ∧
      (∃ c ∈ chunks s', c.addr + 32 = ptr' ∧ c.used = true ∧ c.size = (232 * cap' + 31) / 32 + 1 ∧
        ∀ d ∈ chunks s, d.used = true → d.addr + 32 ≠ ptr → d ≠ c) ∧
      (∀ j, j < k + 1 → O j (μ'.readN (ptr' + 232 * j) 232)) ∧
      μ'.readN (ptr' + 232 * k) 8 = Num.encodeLE 8 9223372036854775825 ∧
      μ'.readN (ptr' + 232 * k + 8) 8 = Num.encodeLE 8 w0 ∧ μ'.readN (ptr' + 232 * k + 16) 8 = Num.encodeLE 8 w1 ∧
      μ'.readN (ptr' + 232 * k + 24) 8 = Num.encodeLE 8 w2 ∧
      (∀ d ∈ chunks s, d.used = true → d.addr + 32 ≠ ptr → d ∈ chunks s' ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → M ≤ a → (a < M + 248 ∨ M + 272 ≤ a) → (a < M + 584 ∨ M + 608 ≤ a) →
        μ'.read a = μ.read a)) ∨
    ∃ N, ExhaustsX env cap0 pb p 5448 ω μ x N := by
  obtain ⟨hS0M, hMS1, hM2, hM8⟩ := hM
  have hS1 := H.hS1
  have hb0 := H.hb0
  have hbT := H.hbT
  have wst := H.st
  have rst : ∀ a, M ≤ a → a < M + 632 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (wst a (by omega) (by omega))
  by_cases hroom : k = cap
  · subst hroom
    have hold' : k = 0 ∨ ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true ∧ c.size = (232 * k + 31) / 32 + 1 := by
      rcases hold with ⟨h0, _⟩ | h
      · exact Or.inl h0
      · exact Or.inr h
    obtain ⟨ω1, μ1, run1, a0, a1, a5, a7, a584, a592, a600, afr, ard, awr⟩ := Lookup.lpg (p := p) (P := P)
      (R := refineContractK cap0 env) x ω μ M k w0 w1 w2 ⟨by omega, by omega, hM8⟩ (by omega) hw0 hw1 hw2 h1
      s560 s568 s576 vc vl (fun a h1 h2 => rst a (by omega) (by omega)) (fun a h1 h2 => rst a (by omega) (by omega))
      (fun a h1 h2 => wst a (by omega) (by omega))
    have H1 : HeapCtx env pb S0 S1 μ1 s :=
      Decode.GrowOne.ctx_high H (fun a ha => afr a (by omega) (Or.inl (by omega))) awr
    have k1 : ∀ a l, (a + l ≤ M + 584 ∨ M + 608 ≤ a) → a + l ≤ 4294967296 → μ1.readN a l = μ.readN a l :=
      fun a l h h' => Memory.readN_congr (fun j hj => afr _ (by omega) (by omega))
    rcases Decode.GrowOne.grow_one_call (p := p) (P := P) (hb := hb) env cap0 hcap1 hcap0 x ω1 μ1 s M (M + 248) k ptr
        176 5493 k ω1[6].toNat pb S0 S1 H1 hold' (by omega) ⟨by omega, by omega⟩ ⟨by omega, hM8⟩ ⟨by omega, by omega⟩
        a0 (a1.trans h1) a5 UInt64.ofNat_toNat.symm a7 ⟨by decide, by decide, by decide⟩ jte_87 bs_5493 (by omega)
        (UInt64.toNat_lt _) (by omega) (by rw [k1 _ _ (by omega) (by omega)]; exact vc)
        (by rw [k1 _ _ (by omega) (by omega)]; exact vp) with
      ⟨q, s', ω2, μ2, run2, e0, e1, e5, e6, eV, eV8, hnew, emove, H2, keep, fresh, _, stk, _, _, ewr⟩ | hx
    rotate_left
    · exact Or.inr ⟨_, ExhaustsX.pre run1 (ExhaustsX.of (P := P) hx)⟩
    obtain ⟨hq0, -, hqT⟩ := Decode.VecU8.chunk_in H2.wf hnew rfl
    simp only at hq0 hqT
    have hb0' := H2.hb0
    have hbT' := H2.hbT
    have k2 : ∀ a l, M ≤ a → (a + l ≤ M + 248 ∨ M + 264 ≤ a) → a + l ≤ 4294967296 → μ2.readN a l = μ1.readN a l :=
      fun a l h0 h h' => Memory.readN_congr (fun j hj => stk _ (by omega) (by omega) (by omega))
    obtain ⟨ω3, μ3, run3, b0, b1, b7, bD, b8, b16, b24, b264, bfr, brd, bwr⟩ := Lookup.lps (p := p) (P := P)
      (R := refineContractK cap0 env) x ω2 μ2 M q k w0 w1 w2 ⟨by omega, by omega, hM8⟩ (by omega) (Or.inl (by omega))
      hw0 hw1 hw2 e1 e5
      (by rw [k2 _ _ (by omega) (by omega) (by omega), k1 _ _ (by omega) (by omega)]; exact s8) eV8
      (by rw [k2 _ _ (by omega) (by omega) (by omega)]; exact a584)
      (by rw [k2 _ _ (by omega) (by omega) (by omega)]; exact a592)
      (by rw [k2 _ _ (by omega) (by omega) (by omega)]; exact a600)
      (fun a h1 h2 => Memory.readable_of_writable (H2.st a (by omega) (by omega)))
      (fun a h1 h2 => Memory.readable_of_writable (H2.st a (by omega) (by omega)))
      (fun a h1 h2 => Memory.readable_of_writable (H2.st a (by omega) (by omega)))
      (fun a h1 h2 => Decode.VecU8.heap_writable H2 hnew rfl ⟨by simp; omega, by simp; omega⟩)
      (fun a h1 h2 => H2.st a (by omega) (by omega))
    have H3 : HeapCtx env pb S0 S1 μ3 s' := Decode.VecU8.ctx_congr_data H2 hnew
      (fun a ha h => bfr a (by omega) (by simp at h; omega) (Or.inl (by omega))) (fun a => by rw [bwr])
    refine Or.inl ⟨ω3, μ3, s', _, max (2 * k) 4, q, run1.trans (run2.trans run3), H3, b0, by rw [b1, e1],
      b7, ?_, ?_, b264, by omega, by omega, by omega,
      ⟨_, hnew, by simp; omega, rfl, rfl, fun d hd hu hne h => ?_⟩, fun j hj => ?_, bD, b8, b16, b24,
      fun c hc hu hne' => ?_,
      fun a h0 h1 h2 h3 => ?_⟩
    · rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (Or.inr (by omega)) (Or.inl (by omega)))]; exact eV
    · rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (Or.inr (by omega)) (Or.inl (by omega)))]; simpa using eV8
    · have := fresh d hd hu hne
      rw [h] at this; simp at this; omega
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · have e3 : μ3.readN (q + 232 * j) 232 = μ2.readN (q + 232 * j) 232 :=
          Memory.readN_congr (fun i hi => bfr _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)))
        have e2 : μ2.readN (q + 232 * j) 232 = μ.readN (ptr + 232 * j) 232 := by
          rw [PassLoop.slot_eq emove hj]
          rcases hold with ⟨h0, -⟩ | ⟨c, hc, hca, hcu, hcs⟩
          · omega
          · obtain ⟨hc0, -, hcT⟩ := Decode.VecU8.chunk_in H.wf hc hcu
            exact Memory.readN_congr (fun i hi => afr _ (by omega) (Or.inl (by omega)))
        rw [e3, e2]; exact hout j hj
      · exact hO μ3 _ bD b8 b16 b24
    · obtain ⟨hc', hd⟩ := keep c hc hu hne'
      refine ⟨hc', fun a ha => ?_⟩
      have hfa := fresh c hc hu hne'
      have hcq : c ≠ (⟨q - 32, (232 * max (2 * k) 4 + 31) / 32 + 1, true⟩ : Chunk) := by
        intro h; apply hfa; rw [h]; simp; omega
      have hdisj := Decode.VecU8.data_disj H2.wf hc' hnew hcq ha
      obtain ⟨hc0, -, hcT⟩ := Decode.VecU8.chunk_in H.wf hc hu
      unfold InData at ha
      simp only at hdisj
      rw [bfr a (by omega) (by omega) (Or.inl (by omega)), hd a ⟨ha.1, ha.2⟩, afr a (by omega) (Or.inl (by omega))]
    · rw [bfr a h0 (Or.inr (by omega)) (by omega), stk a h0 h1 (by omega), afr a h0 h3]
  · obtain ⟨c, hc, hca, hcu, hcs⟩ := hold.resolve_left (fun h => hroom (by omega))
    obtain ⟨hc0, -, hcT⟩ := Decode.VecU8.chunk_in H.wf hc hcu
    have hcs' : 232 * cap + 32 ≤ 32 * c.size := by rw [hcs]; omega
    obtain ⟨ω1, μ1, run1, a1, a5, a584, a592, a600, afr, ard, awr⟩ := Lookup.lp0 (p := p) (P := P)
      (R := refineContractK cap0 env) x ω μ M cap k w0 w1 w2 ⟨by omega, by omega, hM8⟩ hroom
      (by omega) (by omega) hw0 hw1 hw2 h1 s560 s568 s576 vc vl (fun a h1 h2 => rst a (by omega) (by omega))
      (fun a h1 h2 => rst a (by omega) (by omega)) (fun a h1 h2 => wst a (by omega) (by omega))
    have k1 : ∀ a l, (a + l ≤ M + 584 ∨ M + 608 ≤ a) → a + l ≤ 4294967296 → μ1.readN a l = μ.readN a l :=
      fun a l h h' => Memory.readN_congr (fun j hj => afr _ (by omega) (by omega))
    have H1 : HeapCtx env pb S0 S1 μ1 s :=
      Decode.GrowOne.ctx_high H (fun a ha => afr a (by omega) (Or.inl (by omega))) awr
    obtain ⟨ω3, μ3, run3, b0, b1, b7, bD, b8, b16, b24, b264, bfr, brd, bwr⟩ := Lookup.lps (p := p) (P := P)
      (R := refineContractK cap0 env) x ω1 μ1 M ptr k w0 w1 w2 ⟨by omega, by omega, hM8⟩ (by omega)
      (Or.inl (by omega)) hw0 hw1 hw2 (a1.trans h1) a5
      (by rw [k1 _ _ (by omega) (by omega)]; exact s8) (by rw [k1 _ _ (by omega) (by omega)]; exact vp)
      a584 a592 a600
      (fun a h1 h2 => by rw [ard]; exact rst a (by omega) (by omega))
      (fun a h1 h2 => by rw [ard]; exact rst a (by omega) (by omega))
      (fun a h1 h2 => by rw [ard]; exact rst a (by omega) (by omega))
      (fun a h1 h2 => by rw [awr]; exact Decode.VecU8.heap_writable H hc hcu ⟨by omega, by omega⟩)
      (fun a h1 h2 => by rw [awr]; exact wst a (by omega) (by omega))
    have H3 : HeapCtx env pb S0 S1 μ3 s := Decode.VecU8.ctx_congr_data H1 hc
      (fun a ha h => bfr a (by omega) (by omega) (Or.inl (by omega))) bwr
    refine Or.inl ⟨ω3, μ3, s, _, cap, ptr, run1.trans run3, H3, b0, by rw [b1, a1, h1], b7,
      by rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega) (Or.inl (by omega))), k1 _ _ (by omega)
        (by omega)]; exact vc,
      by rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega) (Or.inl (by omega))), k1 _ _ (by omega)
        (by omega)]; exact vp,
      b264, by omega, hcapn, hptr, ⟨c, hc, hca, hcu, hcs, fun d hd hu hne h => hne (by rw [h, hca])⟩,
      fun j hj => ?_, bD, b8, b16, b24, fun d hd hu hne => ⟨hd, fun a ha => ?_⟩, fun a h0 h1 h2 h3 => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Memory.readN_congr (fun i hi => bfr _ (by omega) (by omega) (Or.inl (by omega))), k1 _ _ (by omega)
          (by omega)]; exact hout j hj
      · exact hO μ3 _ bD b8 b16 b24
    · have hdc : d ≠ c := fun h => hne (by rw [h, hca])
      have hdj := Decode.VecU8.data_disj H.wf hd hc hdc ha
      obtain ⟨hd0, -, hdT⟩ := Decode.VecU8.chunk_in H.wf hd hu
      have ha' := ha; unfold InData at ha'
      rw [bfr a (by omega) (by omega) (Or.inl (by omega)), afr a (by omega) (Or.inl (by omega))]
    · rw [bfr a h0 (by omega) (by omega), afr a h0 h3]

/-- Output slot k at a holding `LookedUp(v)`: the discriminant word 2^63 + 17, then `None` (the niche word 2^64 − 1;
    the other two words unspecified) or `Some(Vec)` {|d|, buf, |d|}. -/
def LUSlot (μ : Memory) (a : Nat) (v : Option (List UInt8)) (buf : Nat) : Prop :=
  μ.readN a 8 = Num.encodeLE 8 9223372036854775825 ∧
  match v with
  | none => μ.readN (a + 8) 8 = Num.encodeLE 8 18446744073709551615
  | some d => μ.readN (a + 8) 8 = Num.encodeLE 8 d.length ∧ μ.readN (a + 16) 8 = Num.encodeLE 8 buf ∧
      μ.readN (a + 24) 8 = Num.encodeLE 8 d.length

/-- The slot holds `LookedUp(v)` when its words after the discriminant are the result's three words; its buffer word
    is the one at M + 568. -/
theorem luslot_of {μ4 μ' : Memory} {M a : Nat} {v : Option (List UInt8)} {s s' : State}
    (hr : ResAt μ4 (M + 560) v s s') (D : μ'.readN a 8 = Num.encodeLE 8 9223372036854775825)
    (W0 : μ'.readN (a + 8) 8 = Num.encodeLE 8 (rdN μ4 (M + 560) 8))
    (W1 : μ'.readN (a + 16) 8 = Num.encodeLE 8 (rdN μ4 (M + 568) 8))
    (W2 : μ'.readN (a + 24) 8 = Num.encodeLE 8 (rdN μ4 (M + 576) 8)) :
    LUSlot μ' a v (rdN μ4 (M + 568) 8) := by
  rw [encodeLE_rdN] at W0 W2
  cases v with
  | none => exact ⟨D, W0.trans hr⟩
  | some d =>
    obtain ⟨e0, e16, -, -, -⟩ := hr
    rw [show M + 560 + 16 = M + 576 by omega] at e16
    exact ⟨D, W0.trans e0, W1, W2.trans e16⟩

/-- What an eager `Lookup` step does to the loop's snapshot μ0 and chunks to keep `Kp`: for `None` and for `Some []`
    with the dangling buffer 1, nothing; otherwise the preimage's chunk ch (its data at buf) joins the chunks to keep
    and the snapshot is rebased on it (`snapWith`), so that it holds d at buf and is μ0 outside ch's data. -/
def LUOwn (μ0 μ0' : Memory) (Kp Kp' : Chunk → Prop) (v : Option (List UInt8)) (buf : Nat) : Prop :=
  match v with
  | none => μ0' = μ0 ∧ Kp' = Kp
  | some d => (d = [] ∧ buf = 1 ∧ μ0' = μ0 ∧ Kp' = Kp) ∨
      ∃ ch : Chunk, ch.addr + 32 = buf ∧ ch.size = (d.length + 31) / 32 + 1 ∧ ¬ Kp ch ∧
        Kp' = (fun c => Kp c ∨ c = ch) ∧ μ0'.readN buf d.length = d ∧
        ∀ a, a < 4294967296 → (a < ch.addr + 32 ∨ ch.addr + 32 * ch.size ≤ a) → μ0'.read a = μ0.read a

/-- **One eager `Lookup` instruction** (5042 … 5042), without adopting the preimage's chunk: instruction k is index 8
    with its flag octet 44 set, service id svc and hash h. `PInv k` becomes `PInv (k + 1)` with the same snapshot and
    chunks to keep: slot k holds `LookedUp(lookupOf env svc h)` (`LUSlot`, so `O k` by `hO`), and the result is still
    at M + 560 (`ResAt`, its buffer the slot's). The host context is unchanged. Named hypotheses: `LookupFmtOk` (the
    log line, Fmt) and the drop table's entry for index 8 (`htab`, part of `VendoredFactsC`). Internal hypotheses:
    `hlen` (preimages shorter than 2^63 octets; decision pending with Adam) and `hgas`. Or an allocation fails. -/
theorem lookup_step {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P]
    (env : RefineHost.Env) (cap0 : Nat) (hcap1 : 134217728 ≤ cap0) (hcap0 : cap0 < 18446744073709551616)
    {pb S0 S1 : Nat} {ro : List UInt8} (fmt : LookupFmtOk p cap0 env pb S0 S1 ro)
    (htab : (ro.drop 32).take 4 = Lookup.dropEntry8)
    (x : RefineCtx) (ω : Regs) (μ μ0 : Memory) {hb : Nat} (s : State) (hro : RoData.RoIs ro μ)
    (rtab : ∀ a, 65568 ≤ a → a < 65572 → μ.readable a = true)
    {M E n capI : Nat} {ce : Chunk} {Kp : Chunk → Prop} {O : Nat → List UInt8 → Prop} {i : Nat}
    (L : LayP S0 S1 M E n ce) (k : Nat) (hk : k < n) (svc : Nat) (h : List UInt8)
    (sD0 : μ0.readN (E + 232 * k) 8 = Num.encodeLE 8 (9223372036854775807 + 8))
    (hflag : rdN μ0 (E + 232 * k + 44) 1 ≠ 0)
    (sv : μ0.readN (E + 232 * k + 8) 4 = Num.encodeLE 4 svc) (hsvc : svc < 4294967296)
    (sh : μ0.readN (E + 232 * k + 12) 32 = h)
    (hlen : ∀ d, LookupStep.lookupOf env svc h = some d → d.length < 9223372036854775808)
    (hgas : ∀ d, LookupStep.lookupOf env svc h = some d →
      Constants.CgasHconst + memGas Constants.CgasHlinear d.length ≤ cap0)
    (hO : ∀ (μ' : Memory) (a buf : Nat), LUSlot μ' a (LookupStep.lookupOf env svc h) buf → O k (μ'.readN a 232))
    (st : PInv env pb S0 S1 M E n ce capI μ0 Kp O i k ω μ s) :
    (∃ (s' : State) (ω' : Regs) (μ' μ0' : Memory) (Kp' : Chunk → Prop) (N ptr' : Nat),
      FreeStepsH p (refineContractK cap0 env) i ω μ x 5042 ω' μ' x N ∧
      PInv env pb S0 S1 M E n ce capI μ0' Kp' O 5042 (k + 1) ω' μ' s' ∧
      μ'.readN (M + 256) 8 = Num.encodeLE 8 ptr' ∧
      LUSlot μ' (ptr' + 232 * k) (LookupStep.lookupOf env svc h) (rdN μ' (M + 568) 8) ∧
      LUOwn μ0 μ0' Kp Kp' (LookupStep.lookupOf env svc h) (rdN μ' (M + 568) 8)) ∨
    ∃ N, ExhaustsX env cap0 pb p i ω μ x N := by
  obtain ⟨hS0M, hMS1, hM2, hM8⟩ := L.hM
  have hn := L.hn
  have hS1 := st.H.hS1
  have hbT := st.H.hbT
  have hb0 := st.H.hb0
  -- 1. stage, query, `foreign_historical_lookup` (to 5372)
  rcases LookupStep.lmid (p := p) (P := P) env cap0 hcap1 hcap0 x ω μ μ0 s L k hk svc h sD0 hflag sv hsvc sh hlen
      hgas st with
    ⟨ω3, μ3, s3, N3, run3, H3, d1, -, -, c144, c280, c304, dfr, dkeep, dres⟩ | hx
  rotate_left
  · exact Or.inr hx
  have hro3 : RoData.RoIs ro μ3 := RoData.RoIs.keep st.H run3 hro
  have m3 : ∀ a l, M ≤ a → (a + l ≤ M + 144 ∨ (M + 200 ≤ a ∧ a + l ≤ M + 280) ∨ (M + 288 ≤ a ∧ a + l ≤ M + 304) ∨
      (M + 584 ≤ a ∧ a + l ≤ 4294967296)) → μ3.readN a l = μ.readN a l :=
    fun a l h0 h => Memory.readN_congr (fun j hj => dfr _ (by omega) (by omega) (by omega))
  -- 2. the log line, the `String` freed (to 5448)
  rcases lfmt (p := p) (P := P) env cap0 hcap1 hcap0 fmt x ω3 μ3 s3 H3 hro3 M ⟨hS0M, hMS1, hM2, hM8⟩ d1
      (by rw [m3 _ _ (by omega) (by omega)]; exact st.c16) (by rw [m3 _ _ (by omega) (by omega)]; exact st.c24)
      (by rw [m3 _ _ (by omega) (by omega)]; exact st.c32) (optVec_of_res H3 dres hlen) with
    ⟨ω4, μ4, s4, N4, run4, H4, e1, efr, ekeep⟩ | ⟨N4, hx⟩
  rotate_left
  · exact Or.inr ⟨_, ExhaustsX.pre run3 hx⟩
  have m4 : ∀ a l, M ≤ a → (a + l ≤ M + 536 ∨ (M + 552 ≤ a ∧ a + l ≤ M + 584) ∨ (M + 608 ≤ a ∧ a + l ≤ 4294967296)) →
      μ4.readN a l = μ3.readN a l :=
    fun a l h0 h => Memory.readN_congr (fun j hj => efr _ (by omega) (by omega) (by omega) (by omega))
  have dres4 : ResAt μ4 (M + 560) (LookupStep.lookupOf env svc h) s s4 :=
    ResAt.congr dres (fun a h1 h2 => efr a (by omega) (by omega) (by omega) (by omega)) (fun c hc hcu _ => ekeep c hc hcu)
  have k4 : ∀ d ∈ chunks s, d.used = true → d ∈ chunks s4 ∧ ∀ a, InData d a → μ4.read a = μ.read a :=
    fun d hd hu => by
      obtain ⟨h3, kk3⟩ := dkeep d hd hu
      obtain ⟨h4, kk4⟩ := ekeep d h3 hu
      exact ⟨h4, fun a ha => by rw [kk4 a ha, kk3 a ha]⟩
  obtain ⟨cap, ptr, vc, vp, vl, hkc, hcapn, hptr, hold, hout⟩ := st.out
  have mo : ∀ a l, M + 248 ≤ a → a + l ≤ M + 272 → μ4.readN a l = μ.readN a l := fun a l h0 h => by
    rw [m4 _ _ (by omega) (by omega), m3 _ _ (by omega) (by omega)]
  have hold4 : (cap = 0 ∧ ptr = 8) ∨
      ∃ c ∈ chunks s4, c.addr + 32 = ptr ∧ c.used = true ∧ c.size = (232 * cap + 31) / 32 + 1 := by
    rcases hold with h | ⟨c, hc, hca, hcu, hcs, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨c, (k4 c hc hcu).1, hca, hcu, hcs⟩
  have hout4 : ∀ j, j < k → O j (μ4.readN (ptr + 232 * j) 232) := fun j hj => by
    rcases hold with ⟨h0, -⟩ | ⟨c, hc, hca, hcu, hcs, -⟩
    · omega
    · have hcs' : 232 * cap + 32 ≤ 32 * c.size := by rw [hcs]; omega
      rw [Memory.readN_congr (fun i hi => (k4 c hc hcu).2 _ ⟨by omega, by omega⟩)]; exact hout j hj
  have hD : ∀ (μ' : Memory) (a : Nat), μ'.readN a 8 = Num.encodeLE 8 9223372036854775825 →
      μ'.readN (a + 8) 8 = Num.encodeLE 8 (rdN μ4 (M + 560) 8) →
      μ'.readN (a + 16) 8 = Num.encodeLE 8 (rdN μ4 (M + 568) 8) →
      μ'.readN (a + 24) 8 = Num.encodeLE 8 (rdN μ4 (M + 576) 8) → O k (μ'.readN a 232) := fun μ' a D W0 W1 W2 => by
    exact hO μ' a _ (luslot_of dres4 D W0 W1 W2)
  -- 3. `LookedUp(result)` pushed (to 4046)
  rcases lpush (p := p) (P := P) (hb := hb) env cap0 hcap1 hcap0 x ω4 μ4 s4 (O := O) k hk hn
      ⟨hS0M, hMS1, hM2, hM8⟩ H4 e1 (rdN μ4 (M + 560) 8) (rdN μ4 (M + 568) 8) (rdN μ4 (M + 576) 8)
      (rdN_lt64 _ _) (rdN_lt64 _ _) (rdN_lt64 _ _)
      (encodeLE_rdN _ _ _).symm (encodeLE_rdN _ _ _).symm (encodeLE_rdN _ _ _).symm
      (by rw [m4 _ _ (by omega) (by omega), m3 _ _ (by omega) (by omega)]; exact st.c8)
      cap ptr (by rw [mo _ _ (by omega) (by omega)]; exact vc) (by rw [mo _ _ (by omega) (by omega)]; exact vp)
      (by rw [mo _ _ (by omega) (by omega)]; exact vl) hkc hcapn hptr hold4 hout4 hD with
    ⟨ω5, μ5, s5, N5, cap', ptr', run5, H5, f0, f1, f7, vc5, vp5, vl5, hk5, hc5, hp5,
      ⟨c', hc', hca', hcu', hcs', hcd'⟩, hout5, sD5, sW0, sW1, sW2, keep5, fr5⟩ | ⟨N5, hx⟩
  rotate_left
  · exact Or.inr ⟨_, ExhaustsX.pre (run3.trans run4) hx⟩
  -- 4. the staged element dropped (to 5042)
  have hro5 : RoData.RoIs ro μ5 := RoData.RoIs.keep H4 run5 (RoData.RoIs.keep H3 run4 hro3)
  have tab5 : μ5.readN 65568 4 = Lookup.dropEntry8 := by
    have := hro5 32 4 (by decide); rw [htab] at this; exact this
  have rt5 : ∀ a, 65568 ≤ a → a < 65572 → μ5.readable a = true := fun a h1 h2 => by
    have e := (FreeStepsH.keepRO st.H.bd (run3.trans (run4.trans run5))).1 (a / pageSize)
      (Or.inl (by unfold pageSize; omega))
    have := rtab a h1 h2
    unfold Memory.readable at this ⊢; rw [e]; exact this
  obtain ⟨ω6, μ6, run6, g1, gfr, -, gwr⟩ := Lookup.ldrop (p := p) (P := P) (R := refineContractK cap0 env) x ω5 μ5 M
    ⟨by omega, by omega, hM8⟩ f0 f1 f7
    (by rw [Memory.readN_congr (fun j hj => fr5 _ (by omega) (by omega) (by omega) (by omega)),
      m4 _ _ (by omega) (by omega)]; exact c304)
    tab5 (fun a h1 h2 => Memory.readable_of_writable (H5.st a (by omega) (by omega))) rt5
    (fun a h1 h2 => H5.st a (by omega) (by omega))
  have H6 : HeapCtx env pb S0 S1 μ6 s5 :=
    Decode.GrowOne.ctx_high H5 (fun a ha => gfr a (by omega) (Or.inl (by omega))) gwr
  -- the frame, through to μ6
  have m65 : ∀ a l, M ≤ a → a + l ≤ 4294967296 → μ6.readN a l = μ5.readN a l :=
    fun a l h0 h1 => Memory.readN_congr (fun j hj => gfr _ (by omega) (Or.inr (by omega)))
  have m64 : ∀ a l, M ≤ a → (a + l ≤ M + 248 ∨ (M + 272 ≤ a ∧ a + l ≤ M + 584)) → μ6.readN a l = μ4.readN a l :=
    fun a l h0 h => by
      rw [m65 _ _ h0 (by omega)]
      exact Memory.readN_congr (fun j hj => fr5 _ (by omega) (by omega) (by omega) (by omega))
  have m6 : ∀ a l, M ≤ a → (a + l ≤ M + 144 ∨ (M + 200 ≤ a ∧ a + l ≤ M + 248) ∨ (M + 272 ≤ a ∧ a + l ≤ M + 280) ∨
      (M + 288 ≤ a ∧ a + l ≤ M + 304)) → μ6.readN a l = μ.readN a l := fun a l h0 h => by
    rw [m64 _ _ h0 (by omega), m4 _ _ h0 (by omega), m3 _ _ h0 (by omega)]
  -- the chunks of s other than the old output buffer, kept
  have nptr : ∀ d, Kp d → d.addr + 32 ≠ ptr := fun d hd => by
    obtain ⟨hds, hdu, -⟩ := st.kp d hd
    obtain ⟨hd0, -, -⟩ := Decode.VecU8.chunk_in st.H.wf hds hdu
    rcases hold with ⟨-, rfl⟩ | ⟨c, hc, hca, -, -, -, hck⟩
    · omega
    · rw [← hca]; exact ExportElem.addr_ne st.H.wf hds hc (fun h => hck (h ▸ hd))
  have hcep : ce.addr + 32 ≠ ptr := by
    obtain ⟨hce0, -, -⟩ := Decode.VecU8.chunk_in st.H.wf st.hce.1 st.hce.2
    rcases hold with ⟨-, rfl⟩ | ⟨c, hc, hca, -, -, hne, -⟩
    · omega
    · rw [← hca]; exact ExportElem.addr_ne st.H.wf st.hce.1 hc (fun h => hne h.symm)
  have ks : ∀ d ∈ chunks s, d.used = true → d.addr + 32 ≠ ptr → d ∈ chunks s5 ∧
      ∀ a, InData d a → μ6.read a = μ.read a := fun d hd hu hne => by
    obtain ⟨h4, kk4⟩ := k4 d hd hu
    obtain ⟨h5, kk5⟩ := keep5 d h4 hu hne
    refine ⟨h5, fun a ha => ?_⟩
    obtain ⟨-, -, hdT⟩ := Decode.VecU8.chunk_in st.H.wf hd hu
    have ha' := ha; unfold InData at ha'
    rw [gfr a (by omega) (Or.inl (by omega)), kk5 a ha, kk4 a ha]
  have hce5 := ks ce st.hce.1 st.hce.2 hcep
  have hcec : c' ≠ ce := fun h => hcd' ce (k4 ce st.hce.1 st.hce.2).1 st.hce.2 hcep h.symm
  have hcK : ¬ Kp c' := fun hK => by
    obtain ⟨hds, hdu, -⟩ := st.kp c' hK
    exact hcd' c' (k4 c' hds hdu).1 hdu (nptr c' hK) rfl
  obtain ⟨hq0, -, hqT⟩ := Decode.VecU8.chunk_in H5.wf hc' hcu'
  have hb5 := H5.hbT
  have hcs'' : 232 * cap' + 32 ≤ 32 * c'.size := by rw [hcs']; omega
  have sl6 : ∀ a l, ptr' ≤ a → a + l ≤ ptr' + 232 * cap' → μ6.readN a l = μ5.readN a l :=
    fun a l h0 h => Memory.readN_congr (fun j hj => gfr _ (by omega) (Or.inl (by omega)))
  have t0 : μ6.readN (ptr' + 232 * k) 8 = Num.encodeLE 8 9223372036854775825 := by
    rw [sl6 (ptr' + 232 * k) 8 (by omega) (by omega)]; exact sD5
  have t8 : μ6.readN (ptr' + 232 * k + 8) 8 = Num.encodeLE 8 (rdN μ4 (M + 560) 8) := by
    rw [sl6 (ptr' + 232 * k + 8) 8 (by omega) (by omega)]; exact sW0
  have t16 : μ6.readN (ptr' + 232 * k + 16) 8 = Num.encodeLE 8 (rdN μ4 (M + 568) 8) := by
    rw [sl6 (ptr' + 232 * k + 16) 8 (by omega) (by omega)]; exact sW1
  have t24 : μ6.readN (ptr' + 232 * k + 24) 8 = Num.encodeLE 8 (rdN μ4 (M + 576) 8) := by
    rw [sl6 (ptr' + 232 * k + 24) 8 (by omega) (by omega)]; exact sW2
  have e568 : rdN μ6 (M + 568) 8 = rdN μ4 (M + 568) 8 := by unfold rdN; rw [m64 _ _ (by omega) (by omega)]
  have hlu : LUSlot μ6 (ptr' + 232 * k) (LookupStep.lookupOf env svc h) (rdN μ6 (M + 568) 8) := by
    rw [e568]; exact luslot_of dres4 t0 t8 t16 t24
  have vp6 : μ6.readN (M + 256) 8 = Num.encodeLE 8 ptr' := by rw [m65 _ _ (by omega) (by omega)]; exact vp5
  have st6 : PInv env pb S0 S1 M E n ce capI μ0 Kp O 5042 (k + 1) ω6 μ6 s5 :=
    { h1 := g1.trans f1
      cur := Or.inl ⟨rfl, by
        rw [m64 _ _ (by omega) (by omega), m4 _ _ (by omega) (by omega), c144,
          show E + 232 * k + 232 = E + 232 * (k + 1) by omega]⟩
      en := by rw [m6 _ _ (by omega) (by omega)]; exact st.en
      c128 := by rw [m6 _ _ (by omega) (by omega)]; exact st.c128
      c136 := by rw [m6 _ _ (by omega) (by omega)]; exact st.c136
      c48 := by rw [m6 _ _ (by omega) (by omega)]; exact st.c48
      c40 := by rw [m6 _ _ (by omega) (by omega)]; exact st.c40
      c16 := by rw [m6 _ _ (by omega) (by omega)]; exact st.c16
      c24 := by rw [m6 _ _ (by omega) (by omega)]; exact st.c24
      c32 := by rw [m6 _ _ (by omega) (by omega)]; exact st.c32
      c8 := by rw [m6 _ _ (by omega) (by omega)]; exact st.c8
      i0 := by rw [m6 _ _ (by omega) (by omega)]; exact st.i0
      i8 := by
        rw [m64 _ _ (by omega) (by omega), m4 _ _ (by omega) (by omega), c280,
          show E + 232 * k + 232 = E + 232 * (k + 1) by omega]
      i16 := by rw [m6 _ _ (by omega) (by omega)]; exact st.i16
      i24 := by rw [m6 _ _ (by omega) (by omega)]; exact st.i24
      out := ⟨cap', ptr', by rw [m65 _ _ (by omega) (by omega)]; exact vc5, vp6,
        by rw [m65 _ _ (by omega) (by omega)]; exact vl5,
        hk5, hc5, hp5, Or.inr ⟨c', hc', hca', hcu', hcs', hcec, hcK⟩,
        fun j hj => by rw [sl6 _ _ (by omega) (by omega)]; exact hout5 j hj⟩
      H := H6
      hce := ⟨hce5.1, st.hce.2⟩
      data := fun a ha => by rw [hce5.2 a ha, st.data a ha]
      kp := fun d hd => by
        obtain ⟨hds, hdu, hdd⟩ := st.kp d hd
        obtain ⟨h5, kk5⟩ := ks d hds hdu (nptr d hd)
        exact ⟨h5, hdu, fun a ha => by rw [kk5 a ha, hdd a ha]⟩
      fr := fun a ha => by
        rw [gfr a (by omega) (Or.inr (by omega)), fr5 a (by omega) (by omega) (by omega) (by omega),
          efr a (by omega) (by omega) (by omega) (by omega), dfr a (by omega) (by omega) (by omega), st.fr a ha] }
  have run := run3.trans (run4.trans (run5.trans run6))
  generalize LookupStep.lookupOf env svc h = v at hlu dres4 ⊢
  cases v with
  | none => exact Or.inl ⟨s5, ω6, μ6, μ0, Kp, _, ptr', run, st6, vp6, hlu, rfl, rfl⟩
  | some d =>
    obtain ⟨-, -, b, e8, hb⟩ := dres4
    rw [show M + 560 + 8 = M + 568 by omega] at e8
    rcases hb with ⟨hd, rfl⟩ | ⟨c, hc, hcu, hca, hcs, hfr, hdat⟩
    · have h1 : rdN μ6 (M + 568) 8 = 1 := by rw [e568]; exact rd8 (by decide) e8
      exact Or.inl ⟨s5, ω6, μ6, μ0, Kp, _, ptr', run, st6, vp6, hlu, Or.inl ⟨hd, h1, rfl, rfl⟩⟩
    · have hc0 := Decode.VecU8.chunk_in H4.wf hc hcu
      have hb4 := H4.hb0
      have hb4T := H4.hbT
      have hrb : rdN μ6 (M + 568) 8 = c.addr + 32 := by rw [e568]; exact rd8 (by omega) (by rw [e8, hca])
      have hne : c.addr + 32 ≠ ptr := by
        rcases hold with ⟨-, rfl⟩ | ⟨co, hco, hca, hcou, -, -, -⟩
        · omega
        · rw [← hca]; exact ExportElem.addr_ne H4.wf hc (k4 co hco hcou).1 (fun h => hfr co hco hcou h.symm)
      obtain ⟨hc5, kk5⟩ := keep5 c hc hcu hne
      have hcc' : c ≠ c' := hcd' c hc hcu hne
      have hc6 : ∀ a, InData c a → μ6.read a = μ4.read a := fun a ha => by
        have ha' := ha; unfold InData at ha'
        rw [gfr a (by omega) (Or.inl (by omega)), kk5 a ha]
      have st7 := PInv.adopt st6 ⟨by omega, by omega⟩ c hc5 hcu (fun h => hfr ce st.hce.1 st.hce.2 h.symm)
        (fun d hd => hfr d (st.kp d hd).1 (st.kp d hd).2.1)
        (fun c0 h0 hc0' heq => by
          subst heq
          have e1 : c0.addr + 32 = ptr' := by
            have a1 := rd8 (by omega) h0; have a2 := rd8 (show ptr' < 2 ^ 64 by omega) vp6; omega
          exact ExportElem.addr_ne H5.wf hc5 hc' hcc' (by rw [e1, hca']))
      have hT : c.addr + 32 * c.size ≤ 2147483648 := by omega
      refine Or.inl ⟨s5, ω6, μ6, PassLoop.snapWith μ0 μ6 c, fun d => Kp d ∨ d = c, _, ptr', run, st7, vp6, hlu,
        Or.inr ⟨c, hrb.symm, hcs, fun hK => hfr c (st.kp c hK).1 (st.kp c hK).2.1 rfl, rfl, ?_, fun a ha hout =>
          PassLoop.snapWith_out hT (by rw [hcs]; omega) ha hout⟩⟩
      rw [hrb, hca]
      refine Eq.trans (Memory.readN_congr (fun j hj => ?_)) hdat
      have hj' : b + j < c.addr + 32 * c.size := by rw [hcs]; omega
      rw [PassLoop.snapWith_in hT ⟨by omega, hj'⟩, hc6 _ ⟨by omega, hj'⟩]

end Services.Bootstrap.Refine.LookupStep2
