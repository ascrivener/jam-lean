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

end Services.Bootstrap.Refine.ExportStep
