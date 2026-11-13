import Services.Bootstrap.Refine.ExportSeg
import Services.Bootstrap.Decode.GrowOne

/-!
# Refine's `Export` handler: the push of `Exported(n)`

After the segment loop (5810), `Export` pushes `Exported(n)` onto the output `Vec<Instruction>` at M + 248:
with room (`push_room`) or after `RawVec::grow_one` (`push_grow`). GP v0.8.0 Appendix B.4 (Ψ_R running
bootstrap's code); `Spec.refineInstr`'s `.exportSegs ds => … pure (.exported ds.length)`.
-/

namespace Services.Bootstrap.Refine.ExportStep

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeR
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Refine.PassLoop Services.Bootstrap.Refine.Export

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **`Exported(n)` pushed, with room** (5810 … 5868 / 5909): slot len of the output `{cap, ptr, len}` (len ≠ cap)
    gets the first word 2^63 + 19 and the count n (from M + 56); len + 1 at M + 264. Memory changes only in the
    slot's first 16 octets and at M + 264. -/
theorem push_room {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] {X : Type}
    {R : HostRel X} (x : X) (ω : Regs) (μ : Memory) (M cap ptr len n : Nat)
    (hM : 2147483648 ≤ M ∧ M + 632 ≤ 4294967296 ∧ M % 8 = 0) (hne : len ≠ cap) (hcap : cap < 18446744073709551616)
    (hlen : len + 1 < 18446744073709551616) (hn : n < 18446744073709551616)
    (hd : ptr + 232 * len + 16 ≤ 2147483648)
    (h1 : ω[1] = UInt64.ofNat M)
    (sc : μ.readN (M + 248) 8 = Num.encodeLE 8 cap) (sp : μ.readN (M + 256) 8 = Num.encodeLE 8 ptr)
    (sl : μ.readN (M + 264) 8 = Num.encodeLE 8 len)
    (s136 : μ.readN (M + 136) 8 = Num.encodeLE 8 9223372036854775809) (s56 : μ.readN (M + 56) 8 = Num.encodeLE 8 n)
    (hrM : ∀ a, M + 56 ≤ a → a < M + 272 → μ.readable a = true)
    (hwd : ∀ a, ptr + 232 * len ≤ a → a < ptr + 232 * len + 16 → μ.writable a = true)
    (hw2 : ∀ a, M + 264 ≤ a → a < M + 272 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 5810 ω μ x (if n = 0 then 5909 else 5868) ω' μ' x 16 ∧ ω'[1] = ω[1] ∧
      μ'.readN (ptr + 232 * len) 8 = Num.encodeLE 8 (9223372036854775807 + 20) ∧
      μ'.readN (ptr + 232 * len + 8) 8 = Num.encodeLE 8 n ∧ μ'.readN (M + 264) 8 = Num.encodeLE 8 (len + 1) ∧
      (∀ a, a < 4294967296 → (a < ptr + 232 * len ∨ ptr + 232 * len + 16 ≤ a) → (a < M + 264 ∨ M + 272 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hM0, hM1, hM8⟩ := hM
  obtain ⟨ω1, run1, a1, a5⟩ := xp0 (p := p) (P := P) (R := R) x ω μ M cap len (by omega) hne hcap (by omega) h1 sc sl
    (fun a h1 h2 => hrM a (by omega) (by omega))
  obtain ⟨ω2, μ2, run2, b1, b0, b8, b264, bfr, brd, bwr⟩ := xps (p := p) (P := P) (R := R) x ω1 μ M ptr len n
    ⟨by omega, hM1, hM8⟩ (by omega) (Or.inl (by omega)) hlen hn (a1.trans h1) a5 sp s136 s56 hrM hwd hw2
  exact ⟨ω2, μ2, run1.trans run2, b1.trans a1, b0, b8, b264, bfr, brd, bwr⟩

/-- **`Exported(n)` pushed after growing the output** (5810 … 5868 / 5909, the output full: len = cap):
    `RawVec::grow_one` (32785) moves the len slots to a fresh buffer q, then slot len gets `Exported(n)` and
    len + 1 goes to M + 264. Or the heap is exhausted. -/
theorem push_grow {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P]
    (env : RefineHost.Env) (cap0 : Nat) (hcap1 : 134217728 ≤ cap0) (hcap0 : cap0 < 18446744073709551616)
    (x : RefineCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (M ptr len n pb S0 S1 : Nat)
    (H : HeapCtx env pb S0 S1 μ s)
    (hold : len = 0 ∨ ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true ∧ c.size = (232 * len + 31) / 32 + 1)
    (hlen : len ≤ 2097152) (hn : n < 18446744073709551616)
    (hM : S0 + 456 ≤ M ∧ M + 648 ≤ S1 ∧ 2147484104 ≤ M ∧ M % 8 = 0) (hptr : ptr < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat M)
    (sc : μ.readN (M + 248) 8 = Num.encodeLE 8 len) (sp : μ.readN (M + 256) 8 = Num.encodeLE 8 ptr)
    (sl : μ.readN (M + 264) 8 = Num.encodeLE 8 len)
    (s136 : μ.readN (M + 136) 8 = Num.encodeLE 8 9223372036854775809) (s56 : μ.readN (M + 56) 8 = Num.encodeLE 8 n) :
    (∃ q s' ω' μ', FreeStepsH p (refineContractK cap0 env) 5810 ω μ x (if n = 0 then 5909 else 5868) ω' μ' x
        (64 * ((232 * len + 31) / 32) + 1600) ∧
      ω'[1] = UInt64.ofNat M ∧
      μ'.readN (M + 248) 8 = Num.encodeLE 8 (max (2 * len) 4) ∧ μ'.readN (M + 256) 8 = Num.encodeLE 8 q ∧
      μ'.readN (M + 264) 8 = Num.encodeLE 8 (len + 1) ∧
      (⟨q - 32, (232 * max (2 * len) 4 + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      μ'.readN q (232 * len) = μ.readN ptr (232 * len) ∧
      μ'.readN (q + 232 * len) 8 = Num.encodeLE 8 (9223372036854775807 + 20) ∧
      μ'.readN (q + 232 * len + 8) 8 = Num.encodeLE 8 n ∧
      HeapCtx env pb S0 S1 μ' s' ∧
      (∀ c ∈ chunks s, c.used = true → c.addr + 32 ≠ ptr →
        c ∈ chunks s' ∧ ∀ a, InData c a → μ'.read a = μ.read a) ∧
      (∀ d ∈ chunks s, d.used = true → d.addr + 32 ≠ ptr → d.addr + 32 ≠ q) ∧
      (∀ a, a < 4294967296 → M ≤ a → (a < M + 248 ∨ M + 272 ≤ a) → μ'.read a = μ.read a)) ∨
    ExhaustsX env cap0 pb p 5810 ω μ x (64 * ((232 * len + 31) / 32) + 1600) := by
  obtain ⟨hS0M, hMS1, hM2, hM8⟩ := hM
  have hS1 := H.hS1
  obtain ⟨ω1, run1, a0, a1, a5, a6, a7⟩ := xpg (p := p) (P := P) (R := refineContractK cap0 env) x ω μ M len
    (by omega) (by omega) h1 sc sl (fun a h1 h2 => Memory.readable_of_writable (H.st a (by omega) (by omega)))
  rcases Decode.GrowOne.grow_one_call (p := p) (P := P) (hb := hb) env cap0 hcap1 hcap0 x ω1 μ s M (M + 248) len ptr
      188 5832 len ω1[6].toNat pb S0 S1 H hold hlen ⟨by omega, by omega⟩ ⟨by omega, hM8⟩ ⟨by omega, by omega⟩ a0
      (a1.trans h1) a5 UInt64.ofNat_toNat.symm a7 ⟨by decide, by decide, by decide⟩ jte_93 bs_5832 (by omega)
      (UInt64.toNat_lt _) hptr sc sp with
    ⟨q, s', ω2, μ2, run2, e0, e1, e5, e6, eV, eV8, hnew, emove, H2, keep, fresh, _, stk, _, _, ewr⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsX.of (P := P) (Exhausts.pre run1 hx)).mono (by omega))
  obtain ⟨hq0, -, hqT⟩ := Decode.VecU8.chunk_in H2.wf hnew rfl
  simp only at hq0 hqT
  have hb0 := H2.hb0
  have hbT := H2.hbT
  have hq32 : 32 ≤ q := by omega
  have hcapq : 232 * max (2 * len) 4 ≤ 32 * ((232 * max (2 * len) 4 + 31) / 32) := by omega
  have k2 : ∀ a l, M ≤ a → (a + l ≤ M + 248 ∨ M + 264 ≤ a) → a + l ≤ 4294967296 → μ2.readN a l = μ.readN a l :=
    fun a l h0 h h' => Memory.readN_congr (fun j hj => stk _ (by omega) (by omega) (by omega))
  obtain ⟨ω3, μ3, run3, b1, b0, b8, b264, bfr, brd, bwr⟩ := xps (p := p) (P := P) (R := refineContractK cap0 env)
    x ω2 μ2 M q len n ⟨by omega, by omega, hM8⟩ (by omega) (Or.inl (by omega)) (by omega) hn (e1) e5
    (by simpa using eV8) (by rw [k2 _ _ (by omega) (by omega) (by omega)]; exact s136)
    (by rw [k2 _ _ (by omega) (by omega) (by omega)]; exact s56)
    (fun a h1 h2 => Memory.readable_of_writable (H2.st a (by omega) (by omega)))
    (fun a h1 h2 => Decode.VecU8.heap_writable H2 hnew rfl ⟨by simp; omega, by simp; omega⟩)
    (fun a h1 h2 => H2.st a (by omega) (by omega))
  have H3 : HeapCtx env pb S0 S1 μ3 s' := by
    have H2' := Decode.VecU8.ctx_congr_data H2 hnew
      (fun a ha h => bfr a (by omega) (by simp at h; omega) (Or.inl (by omega))) (fun a => by rw [bwr])
    exact H2'
  refine Or.inl ⟨q, s', ω3, μ3, ((run1.trans run2).trans run3).mono (by omega), by rw [b1, e1], ?_, ?_, b264, hnew,
    ?_, b0, b8, H3, fun c hc hu hne' => ?_, fresh, fun a h0 h1 h2 => ?_⟩
  · rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (Or.inr (by omega)) (Or.inl (by omega)))]; exact eV
  · rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (Or.inr (by omega)) (Or.inl (by omega)))]; simpa using eV8
  · rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (Or.inl (by omega)) (Or.inl (by omega))), emove]
  · obtain ⟨hc', hd⟩ := keep c hc hu hne'
    refine ⟨hc', fun a ha => ?_⟩
    have hfa := fresh c hc hu hne'
    have hcq : c ≠ (⟨q - 32, (232 * max (2 * len) 4 + 31) / 32 + 1, true⟩ : Chunk) := by
      intro h; apply hfa; rw [h]; simp; omega
    have hdisj := Decode.VecU8.data_disj H2.wf hc' hnew hcq ha
    obtain ⟨hc0, -, hcT⟩ := Decode.VecU8.chunk_in H.wf hc hu
    have := H.hbT
    unfold InData at ha
    simp only at hdisj
    rw [bfr a (by omega) (by omega) (Or.inl (by omega)), hd a ⟨ha.1, ha.2⟩]
  · rw [bfr a h0 (Or.inr (by omega)) (by omega), stk a h0 h1 (by omega)]

/-- **`Export`'s frees and return** (5868 / 5909 … 5042): the n segments' buffers are freed (`ExportSeg.frees`),
    then the segments' `Vec` buffer co (capacity `capv` at M + 64, data `ptrv` at M + 104), then the handler
    returns to the loop head without dropping the staged element. The allocator's context holds; every other
    allocated chunk keeps its data; the stack from M up is kept. -/
theorem tail {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (env : RefineHost.Env)
    (cap0 : Nat) {pb S0 S1 : Nat} (x : RefineCtx) (ω : Regs) (μ : Memory) (s : State) (H : HeapCtx env pb S0 S1 μ s)
    (M ptrv capv n : Nat) (co : Chunk) (capf qf : Nat → Nat)
    (hM : S0 + 456 ≤ M ∧ M + 648 ≤ S1 ∧ 2147484104 ≤ M ∧ M % 8 = 0) (hp : ptrv + 24 * n + 8 ≤ 2147483648)
    (hcv : 24 * capv < 18446744073709551616) (hnc : n ≤ capv)
    (hco : capv ≠ 0 → co ∈ chunks s ∧ co.used = true ∧ co.addr + 32 = ptrv)
    (hcoD : ∀ a, ptrv ≤ a → a < ptrv + 24 * n → InData co a)
    (hq : ∀ i, i < n → capf i ≠ 0 → qf i ≠ co.addr + 32 ∧ ∀ j, j < n → j ≠ i → capf j ≠ 0 → qf j ≠ qf i)
    (hcap : ∀ i, i < n → capf i < 18446744073709551616) (hq64 : ∀ i, i < n → qf i < 18446744073709551616)
    (hcs : ∀ i, i < n → capf i ≠ 0 → ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 = qf i)
    (hw : ∀ i, i < n → μ.readN (ptrv + 24 * i) 8 = Num.encodeLE 8 (capf i) ∧
      μ.readN (ptrv + 24 * i + 8) 8 = Num.encodeLE 8 (qf i))
    (h1 : ω[1] = UInt64.ofNat M)
    (s104 : μ.readN (M + 104) 8 = Num.encodeLE 8 ptrv) (s96 : μ.readN (M + 96) 8 = Num.encodeLE 8 (24 * n))
    (s64 : μ.readN (M + 64) 8 = Num.encodeLE 8 capv) (s72 : μ.readN (M + 72) 8 = Num.encodeLE 8 10)
    (s40 : μ.readN (M + 40) 8 = Num.encodeLE 8 2098688) :
    ∃ (ω' : Regs) (μ' : Memory) (s' : State) (N : Nat),
      FreeStepsH p (refineContractK cap0 env) (if n = 0 then 5909 else 5868) ω μ x 5042 ω' μ' x N ∧
      HeapCtx env pb S0 S1 μ' s' ∧ ω'[1] = UInt64.ofNat M ∧ (∀ a, a < 4294967296 → M ≤ a → μ'.read a = μ.read a) ∧
      (∀ d ∈ chunks s, d.used = true → (capv ≠ 0 → d ≠ co) → (∀ i, i < n → capf i ≠ 0 → d.addr + 32 ≠ qf i) →
        d ∈ chunks s' ∧ ∀ a, InData d a → μ'.read a = μ.read a) := by
  obtain ⟨hS0M, hMS1, hM2, hM8⟩ := hM
  have hS1 := H.hS1
  have rM : ∀ a, S0 ≤ a → a < S1 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (H.st a h1 h2)
  -- from 5909 on: the `Vec`'s buffer freed, and the return
  have fin : ∀ (ω1 : Regs) (μ1 : Memory) (s1 : State), HeapCtx env pb S0 S1 μ1 s1 → ω1[1] = UInt64.ofNat M →
      (∀ a, a < 4294967296 → M ≤ a → μ1.read a = μ.read a) → (capv ≠ 0 → co ∈ chunks s1) →
      ∃ (ω' : Regs) (μ' : Memory) (s' : State) (N : Nat),
        FreeStepsH p (refineContractK cap0 env) 5909 ω1 μ1 x 5042 ω' μ' x N ∧ HeapCtx env pb S0 S1 μ' s' ∧
        ω'[1] = UInt64.ofNat M ∧ (∀ a, a < 4294967296 → M ≤ a → μ'.read a = μ1.read a) ∧
        (∀ d ∈ chunks s1, d.used = true → (capv ≠ 0 → d ≠ co) → d ∈ chunks s' ∧
          ∀ a, InData d a → μ'.read a = μ1.read a) := by
    intro ω1 μ1 s1 H1 e1 k1 hco1
    have r1 : ∀ a l, M ≤ a → a + l ≤ 4294967296 → μ1.readN a l = μ.readN a l :=
      fun a l h h' => Memory.readN_congr (fun j hj => k1 _ (by omega) (by omega))
    have rM1 : ∀ a, S0 ≤ a → a < S1 → μ1.readable a = true :=
      fun a h1 h2 => Memory.readable_of_writable (H1.st a h1 h2)
    have ret : ∀ (ω2 : Regs) (μ2 : Memory), ω2[1] = UInt64.ofNat M →
        (∀ a, a < 4294967296 → M ≤ a → μ2.read a = μ.read a) → (∀ a, S0 ≤ a → a < S1 → μ2.readable a = true) →
        ∃ ω3, FreeStepsH p (refineContractK cap0 env) 5938 ω2 μ2 x 5042 ω3 μ2 x 10 ∧ ω3[1] = UInt64.ofNat M :=
      fun ω2 μ2 f1 f2 f3 => by
        obtain ⟨ω3, run3, g1⟩ := xt1 (p := p) (P := P) (R := refineContractK cap0 env) x ω2 μ2 M (by omega) f1
          (by rw [Memory.readN_congr (fun j hj => f2 _ (by omega) (by omega))]; exact s72)
          (by rw [Memory.readN_congr (fun j hj => f2 _ (by omega) (by omega))]; exact s40)
          (fun a h1 h2 => f3 a (by omega) (by omega))
        exact ⟨ω3, run3, g1.trans f1⟩
    by_cases hc0 : capv = 0
    · subst hc0
      obtain ⟨ω2, run2, f1⟩ := xt0z (p := p) (P := P) (R := refineContractK cap0 env) x ω1 μ1 M (by omega) e1
        (by rw [r1 _ _ (by omega) (by omega)]; exact s64) (fun a h1 h2 => rM1 a (by omega) (by omega))
      obtain ⟨ω3, run3, g1⟩ := ret ω2 μ1 (f1.trans e1) k1 rM1
      exact ⟨ω3, μ1, s1, _, run2.trans run3, H1, g1, fun _ _ _ => rfl, fun d hd _ _ => ⟨hd, fun _ _ => rfl⟩⟩
    · obtain ⟨-, hcou, hcoa⟩ := hco hc0
      obtain ⟨ω2, run2, f0, f1, f5, f6, f7⟩ := xt0 (p := p) (P := P) (R := refineContractK cap0 env) x ω1 μ1 M capv
        ptrv (by omega) hc0 hcv (by omega) e1 (by rw [r1 _ _ (by omega) (by omega)]; exact s64)
        (by rw [r1 _ _ (by omega) (by omega)]; exact s104) (fun a h1 h2 => rM1 a (by omega) (by omega))
      obtain ⟨ω3, μ3, run3, H3, -, -, -, stk3, -, keep3, g0, g1, g5, g6⟩ := Decode.DeallocCall.dealloc_call
        (R := refineContractK cap0 env) (p := p) (P := P) env pb S0 S1 x ω2 μ1 s1 M ptrv 192 5938 co H1
        (hco1 hc0) hcou hcoa f0 (by rw [f1, e1]) f7 ⟨by decide, by decide, by decide⟩ jte_95 bs_5938 (by omega)
        ⟨by omega, by omega⟩
      obtain ⟨ω4, run4, h41⟩ := ret ω3 μ3 (by rw [g1, f1, e1]) (fun a h0 h => by rw [stk3 a h0 h, k1 a h0 h])
        (fun a h1 h2 => Memory.readable_of_writable (H3.st a h1 h2))
      exact ⟨ω4, μ3, _, _, run2.trans (run3.trans run4), H3, h41, stk3,
        fun d hd hu hne => keep3 d hd hu (hne hc0)⟩
  by_cases hn0 : n = 0
  · subst hn0
    simp only [↓reduceIte]
    obtain ⟨ω', μ', s', N, run, H', e1, k', keep'⟩ := fin ω μ s H h1 (fun _ _ _ => rfl) (fun h => (hco h).1)
    exact ⟨ω', μ', s', N, run, H', e1, k', fun d hd hu hne _ => keep' d hd hu hne⟩
  · have hn0' : ¬ n = 0 := hn0
    simp only [hn0', ↓reduceIte]
    have hcv0 : capv ≠ 0 := by omega
    obtain ⟨hcos, hcou, hcoa⟩ := hco hcv0
    obtain ⟨ω1, run1, a1, a5, a6⟩ := xr0 (p := p) (P := P) (R := refineContractK cap0 env) x ω μ M ptrv n (by omega)
      (by omega) h1 s104 s96 (fun a h1 h2 => rM a (by omega) (by omega))
    obtain ⟨ω2, μ2, s2, N2, run2, H2, b1, k2, hco2, keep2⟩ := ExportSeg.frees (p := p) (P := P) env cap0 x M ptrv n co
      capf qf ⟨hS0M, hMS1, hM2, hM8⟩ hp hcoD hq hcap hq64 n 0 ω1 μ s (by omega) (by omega) H hcos hcou
      (fun i _ hi hci => hcs i hi hci) hw (a1.trans h1) (by rw [a5]) (by rw [a6])
    obtain ⟨ω', μ', s', N, run, H', e1, k', keep'⟩ := fin ω2 μ2 s2 H2 b1 k2 (fun _ => hco2)
    refine ⟨ω', μ', s', _, run1.trans (run2.trans run), H', e1, fun a h0 h => by rw [k' a h0 h, k2 a h0 h],
      fun d hd hu hne hne' => ?_⟩
    obtain ⟨hd2, hk2⟩ := keep2 d hd hu (fun i _ hi hci => hne' i hi hci)
    obtain ⟨hd', hk'⟩ := keep' d hd2 hu hne
    exact ⟨hd', fun a ha => by rw [hk' a ha, hk2 a ha]⟩

/-- **`Export`'s head** (5042 … 5587): the element at `cur` (≠ end), of index 10 (`ExportSegs`), is staged at
    M + 304 and dispatched to the handler, with ω₅ = cur and the cursor advanced (M + 144, M + 280). Memory
    changes only in [M − 48, M), M + 144 … M + 152, M + 280 … M + 288 and M + 304 … M + 536. -/
theorem xhead {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] {X : Type}
    {R : HostRel X} (x : X) (ω : Regs) (μ : Memory) (M cur en : Nat)
    (hM : 65536 + 48 ≤ M ∧ M + 632 + 16 < 4294967296 ∧ M % 8 = 0)
    (hcur : 65536 ≤ cur ∧ cur + 232 + 24 < 4294967296) (hcM : cur + 232 + 24 ≤ M - 48 ∨ M + 632 ≤ cur)
    (hne : cur ≠ en) (hen : en < 18446744073709551616) (h1 : ω[1] = UInt64.ofNat M)
    (s144 : μ.readN (M + 144) 8 = Num.encodeLE 8 cur) (s120 : μ.readN (M + 120) 8 = Num.encodeLE 8 en)
    (sD : μ.readN cur 8 = Num.encodeLE 8 (9223372036854775807 + 10))
    (s128 : μ.readN (M + 128) 8 = Num.encodeLE 8 9223372036854775832)
    (s136 : μ.readN (M + 136) 8 = Num.encodeLE 8 9223372036854775809)
    (hrc : ∀ a, cur ≤ a → a < cur + 232 → μ.readable a = true)
    (hwM : ∀ a, M - 48 ≤ a → a < M + 632 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 5042 ω μ x 5587 ω' μ' x 2000 ∧ ω'[1] = UInt64.ofNat M ∧
      ω'[5] = UInt64.ofNat cur ∧ ω'[8] = UInt64.ofNat 10 ∧
      μ'.readN (M + 144) 8 = Num.encodeLE 8 (cur + 232) ∧ μ'.readN (M + 280) 8 = Num.encodeLE 8 (cur + 232) ∧
      (∀ a, a < 4294967296 → (a < M - 48 ∨ (M ≤ a ∧ a < M + 144) ∨ (M + 152 ≤ a ∧ a < M + 280) ∨
        (M + 288 ≤ a ∧ a < M + 304) ∨ M + 536 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hM0, hM1, hM8⟩ := hM
  have hr : ∀ a, M - 48 ≤ a → a < M + 632 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwM a h1 h2)
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, a144, a304, a280, afr, ard, awr⟩ := Pass.pa (p := p) (P := P)
    (R := R) x ω μ M cur en (9223372036854775807 + 10) (by omega) (by omega) (by omega) hne hen (by omega)
    (by omega) h1 s144 s120 sD (fun a h1 h2 => hr a (by omega) (by omega))
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
  obtain ⟨ω3, run3, c1, c5, c8⟩ := xd (p := p) (P := P) (R := R) x ω2 μ2 M (by omega) b1 (by rw [b6, a6])
    (by rw [Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega))]; exact s128)
    (by rw [Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega))]; exact s136)
    (fun a h1 h2 => by rw [brd, ard]; exact hr a (by omega) (by omega))
  refine ⟨ω3, μ2, (run1.trans (run2.trans run3)).mono (by omega), by rw [c1, b1], by rw [c5, b5, a5], c8,
    ?_, ?_, k2, fun a => by rw [brd, ard], fun a => by rw [bwr, awr]⟩
  · rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega) (by omega))]; exact a144
  · rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega) (by omega))]; exact a280

end Services.Bootstrap.Refine.ExportStep
