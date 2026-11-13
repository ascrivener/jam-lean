import Services.Bootstrap.Refine.Pass
import Services.Bootstrap.Decode.GrowOne
import Services.Bootstrap.Decode.LoopAPass

/-!
# Refine's transform loop: an instruction passed through when the output is full

As `Pass.pass_elem`, for `len = cap`: before the copy the loop grows the output with
`RawVec::grow_one` (`Decode.GrowOne.grow_one_call`), to `max (2 len) 4` elements in a fresh chunk q holding
the old elements. Under refine's host contract (`refineContractK`), the step either reaches 5042 again
with the allocator's context kept (`HeapCtx`), or the heap is exhausted (`Exhausts`).
-/

namespace Services.Bootstrap.Refine.PassGrow

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeR
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Refine.Pass Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.HeapCtx

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **One instruction passed through, with the output full** (5042 … 5042, `len = cap`): the output grows
    to `max (2 len) 4` elements in a fresh chunk q (the old `len` elements moved there), the element's 232
    octets are copied unchanged to `q + 232 len`, and `cur + 232`, `len + 1` are stored; or the heap is
    exhausted. -/
theorem pass_elem_grow {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P]
    (env : RefineHost.Env) (cap0 : Nat) (hcap1 : 134217728 ≤ cap0) (hcap0 : cap0 < 18446744073709551616)
    (x : RefineCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (M cur en t len ptr pb S0 S1 : Nat)
    (H : HeapCtx env pb S0 S1 μ s) (ht : PassIdx t)
    (hold : len = 0 ∨ ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true ∧ c.size = (232 * len + 31) / 32 + 1)
    (hlen : len ≤ 2097152)
    (hM : S0 + 456 ≤ M ∧ M + 632 + 16 ≤ S1 ∧ 2147484104 ≤ M ∧ M % 8 = 0)
    (hcur : 65536 ≤ cur ∧ cur + 232 + 24 < 2147483648)
    (hne : cur ≠ en) (hen : en < 18446744073709551616) (hptr : ptr < 18446744073709551616)
    (hpl : ptr + 232 * len < 2147483648)
    (h1 : ω[1] = UInt64.ofNat M)
    (s144 : μ.readN (M + 144) 8 = Num.encodeLE 8 cur) (s120 : μ.readN (M + 120) 8 = Num.encodeLE 8 en)
    (sD : μ.readN cur 8 = Num.encodeLE 8 (9223372036854775807 + t))
    (s128 : μ.readN (M + 128) 8 = Num.encodeLE 8 9223372036854775832)
    (s136 : μ.readN (M + 136) 8 = Num.encodeLE 8 9223372036854775809)
    (sc : μ.readN (M + 248) 8 = Num.encodeLE 8 len) (sp : μ.readN (M + 256) 8 = Num.encodeLE 8 ptr)
    (sl : μ.readN (M + 264) 8 = Num.encodeLE 8 len)
    (hrc : ∀ a, cur ≤ a → a < cur + 232 → μ.readable a = true) :
    (∃ q s' ω' μ', FreeStepsH p (refineContractK cap0 env) 5042 ω μ x 5042 ω' μ' x
        (64 * ((232 * len + 31) / 32) + 6000) ∧
      ω'[1] = UInt64.ofNat M ∧
      μ'.readN (M + 144) 8 = Num.encodeLE 8 (cur + 232) ∧ μ'.readN (M + 264) 8 = Num.encodeLE 8 (len + 1) ∧
      μ'.readN (M + 248) 8 = Num.encodeLE 8 (max (2 * len) 4) ∧ μ'.readN (M + 256) 8 = Num.encodeLE 8 q ∧
      (⟨q - 32, (232 * max (2 * len) 4 + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      μ'.readN q (232 * len) = μ.readN ptr (232 * len) ∧
      μ'.readN (q + 232 * len) 232 = μ.readN cur 232 ∧
      μ'.readN (M + 120) 8 = Num.encodeLE 8 en ∧
      μ'.readN (M + 128) 8 = Num.encodeLE 8 9223372036854775832 ∧
      μ'.readN (M + 136) 8 = Num.encodeLE 8 9223372036854775809 ∧
      HeapCtx env pb S0 S1 μ' s' ∧
      (∀ c ∈ chunks s, c.used = true → c.addr + 32 ≠ ptr →
        c ∈ chunks s' ∧ ∀ a, InData c a → μ'.read a = μ.read a) ∧
      (∀ d ∈ chunks s, d.used = true → d.addr + 32 ≠ ptr → d.addr + 32 ≠ q) ∧
      μ'.readN (M + 280) 8 = Num.encodeLE 8 (cur + 232) ∧
      (∀ a, (M ≤ a ∧ a < M + 144) ∨ (M + 152 ≤ a ∧ a < M + 248) ∨ (M + 272 ≤ a ∧ a < M + 280) ∨
        (M + 288 ≤ a ∧ a < M + 304) → μ'.read a = μ.read a)) ∨
    Exhausts env cap0 pb p P 5042 ω μ x (64 * ((232 * len + 31) / 32) + 6000) := by
  obtain ⟨hS0M, hMS1, hM2, hM8⟩ := hM
  have hS1 := H.hS1
  have wM : ∀ a, M - 48 ≤ a → a < M + 632 → μ.writable a = true := fun a h1 h2 => H.st a (by omega) (by omega)
  have rM : ∀ a, M - 48 ≤ a → a < M + 632 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (wM a h1 h2)
  have hD : 9223372036854775807 + t < 18446744073709551616 := by unfold PassIdx at ht; omega
  -- the element staged at M + 304
  obtain ⟨ω1, μ1, run1, a0, a1, a6, a7, a8, a9, a144, a304, a280, afr, ard, awr⟩ := pa (p := p) (P := P)
    (R := refineContractK cap0 env) x ω μ M cur en (9223372036854775807 + t) (by omega) (by omega) (by omega)
    hne hen hD (by unfold PassIdx at ht; omega) h1 s144 s120 sD (fun a h1 h2 => rM a (by omega) (by omega))
    (fun a h1 h2 => hrc a h1 (by omega)) (fun a h1 h2 => wM a (by omega) (by omega))
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, bd, bfr, brd, bwr⟩ := memcpy_any (p := p) (P := P)
    (R := refineContractK cap0 env) x ω1 μ1 162 5095 M (M + 312) (cur + 8) 224 a0 a1 a7 a8 a9
    ⟨by decide, by decide, by decide⟩ jte_80 bs_5095 ⟨by omega, by omega, hM8⟩ ⟨by omega, by omega⟩
    ⟨by omega, by omega⟩ (by omega) (by omega) (by omega)
    (fun a h1 h2 => by rw [ard]; exact hrc a (by omega) (by omega))
    (fun a h1 h2 => by rw [awr]; exact wM a (by omega) (by omega))
    (fun a h1 h2 => by rw [awr]; exact wM a (by omega) (by omega))
  have k2 : ∀ a, a < 4294967296 → (a < M - 48 ∨ (M ≤ a ∧ a < M + 144) ∨ (M + 152 ≤ a ∧ a < M + 280) ∨
      M + 536 ≤ a) → μ2.read a = μ.read a :=
    fun a h0 h1 => by rw [bfr a h0 (by omega) (by omega), afr a h0 (by omega)]
  have H2 : HeapCtx env pb S0 S1 μ2 s := Decode.GrowOne.ctx_high H (fun a ha => k2 a (by omega) (by omega))
    (fun a => by rw [bwr, awr])
  have stage : μ2.readN (M + 304) 232 = μ.readN cur 232 := by
    rw [show (232 : Nat) = 8 + 224 from rfl, readN_add2, readN_add2, show M + 304 + 8 = M + 312 by omega, bd,
      Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega) (by omega)), a304, ← sD,
      Memory.readN_congr (fun j hj => afr _ (by omega) (by omega))]
  -- the dispatch, and the call of `grow_one`
  obtain ⟨ω3, run3, c1, c5⟩ := pd (p := p) (P := P) (R := refineContractK cap0 env) x ω2 μ2 M t ht (by omega) b1
    (by rw [b6, a6])
    (by rw [Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega))]; exact s128)
    (by rw [Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega))]; exact s136)
    (fun a h1 h2 => by rw [brd, ard]; exact rM a (by omega) (by omega))
  obtain ⟨ω4, run4, d0, d1, d5, d6, d7⟩ := pg (p := p) (P := P) (R := refineContractK cap0 env) x ω3 μ2 M len
    (by omega) (by omega) (c1.trans b1)
    (by rw [Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega))]; exact sc)
    (by rw [Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega))]; exact sl)
    (fun a h1 h2 => by rw [brd, ard]; exact rM a (by omega) (by omega))
  have pre := run1.trans (run2.trans (run3.trans run4))
  rcases Decode.GrowOne.grow_one_call (p := p) (P := P) (hb := hb) env cap0 hcap1 hcap0 x ω4 μ2 s M (M + 248) len ptr 180 5584 len
      ω4[6].toNat pb S0 S1 H2 hold hlen ⟨by omega, by omega⟩ ⟨by omega, hM8⟩ ⟨by omega, by omega⟩ d0 d1 d5
      UInt64.ofNat_toNat.symm d7 ⟨by decide, by decide, by decide⟩ jte_89 bs_5584 (by omega) (UInt64.toNat_lt _)
      hptr
      (by rw [Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega))]; exact sc)
      (by rw [Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega))]; exact sp) with
    ⟨q, s', ω5, μ5, run5, e0, e1, e5, e6, eV, eV8, hnew, emove, H5, keep, fresh, _, stk, _, _, ewr⟩ | hx
  rotate_left
  · exact Or.inr ((Exhausts.pre pre hx).mono (by omega))
  -- the copy into the grown output
  have hm4 : len + 1 ≤ max (2 * len) 4 := by omega
  obtain ⟨hq0, -, hqT⟩ := Decode.VecU8.chunk_in H5.wf hnew rfl
  simp only at hq0 hqT
  have hb0 := H5.hb0
  have hbT := H5.hbT
  have hq32 : 32 ≤ q := by omega
  have hcapq : 232 * max (2 * len) 4 ≤ 32 * ((232 * max (2 * len) 4 + 31) / 32) := by omega
  have k5 : ∀ a, a < 4294967296 → M ≤ a → (a < M + 248 ∨ M + 264 ≤ a) → μ5.read a = μ2.read a :=
    fun a h0 h1 h2 => stk a h0 h1 h2
  obtain ⟨ω6, run6, f0, f1, f5, f7, f8, f9⟩ := pc2 (p := p) (P := P) (R := refineContractK cap0 env) x ω5 μ5 M q len
    (by omega) (by omega) e1 e5 (by simpa using eV8)
    (fun a h1 h2 => by
      rw [← Memory.readable_of_writable (H5.st a (by omega) (by omega))])
  have wq : ∀ a, q + 232 * len ≤ a → a < q + 232 * len + 232 → μ5.writable a = true := fun a h1 h2 =>
    Decode.VecU8.heap_writable H5 hnew rfl ⟨by simp; omega, by simp; omega⟩
  obtain ⟨ω7, μ7, run7, g0, g1, g5, g6, gd, gfr, grd, gwr⟩ := memcpy_any (p := p) (P := P)
    (R := refineContractK cap0 env) x ω6 μ5 160 5034 M (q + 232 * len) (M + 304) 232 f0 f1 f7 f8 f9
    ⟨by decide, by decide, by decide⟩ jte_79 bs_5034 ⟨by omega, by omega, hM8⟩ ⟨by omega, by omega⟩
    ⟨by omega, by omega⟩ (by omega) (by omega) (by omega)
    (fun a h1 h2 => Memory.readable_of_writable (H5.st a (by omega) (by omega)))
    wq (fun a h1 h2 => H5.st a (by omega) (by omega))
  have H7 : HeapCtx env pb S0 S1 μ7 s' := Decode.VecU8.ctx_congr_data H5 hnew
    (fun a ha h => gfr a (by omega) (by simp at h; omega) (by omega)) gwr
  obtain ⟨ω8, μ8, run8, i1, i264, ifr, ird, iwr⟩ := pi (p := p) (P := P) (R := refineContractK cap0 env) x ω7 μ7 M
    len (by omega) (by omega) g1 (by rw [g5, f5])
    (fun a h1 h2 => by rw [gwr]; exact H5.st a (by omega) (by omega))
  have H8 : HeapCtx env pb S0 S1 μ8 s' := Decode.GrowOne.ctx_high H7 (fun a ha => ifr a (by omega) (by omega)) iwr
  -- μ8 against μ2 on the frame, away from the output's fields
  have k8 : ∀ a, a < 4294967296 → M ≤ a → (a < M + 248 ∨ M + 272 ≤ a) →
      (a < q + 232 * len ∨ q + 232 * len + 232 ≤ a) → μ8.read a = μ2.read a := fun a h0 h1 h2 h3 => by
    rw [ifr a h0 (by omega), gfr a h0 h3 (by omega), k5 a h0 h1 (by omega)]
  refine Or.inl ⟨q, s', ω8, μ8, (pre.trans (run5.trans (run6.trans (run7.trans run8)))).mono (by omega), i1,
    ?_, i264, ?_, ?_, hnew, ?_, ?_, ?_, ?_, ?_, H8, fun c hc hu hne' => ?_, fresh, ?_, fun a ha => ?_⟩
  · rw [Memory.readN_congr (fun j hj => k8 _ (by omega) (by omega) (by omega) (by omega)),
      Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega) (by omega))]; exact a144
  · rw [Memory.readN_congr (fun j hj => ifr _ (by omega) (by omega)),
      Memory.readN_congr (fun j hj => gfr _ (by omega) (by omega) (by omega))]; exact eV
  · rw [Memory.readN_congr (fun j hj => ifr _ (by omega) (by omega)),
      Memory.readN_congr (fun j hj => gfr _ (by omega) (by omega) (by omega))]; simpa using eV8
  · rw [Memory.readN_congr (fun j hj => ifr _ (by omega) (by omega)),
      Memory.readN_congr (fun j hj => gfr _ (by omega) (by omega) (by omega)), emove,
      Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega))]
  · rw [Memory.readN_congr (fun j hj => ifr _ (by omega) (by omega)), gd,
      Memory.readN_congr (fun j hj => k5 _ (by omega) (by omega) (by omega))]; exact stage
  · rw [Memory.readN_congr (fun j hj => k8 _ (by omega) (by omega) (by omega) (by omega)),
      Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega))]; exact s120
  · rw [Memory.readN_congr (fun j hj => k8 _ (by omega) (by omega) (by omega) (by omega)),
      Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega))]; exact s128
  · rw [Memory.readN_congr (fun j hj => k8 _ (by omega) (by omega) (by omega) (by omega)),
      Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega))]; exact s136
  · obtain ⟨hc', hd⟩ := keep c hc hu hne'
    refine ⟨hc', fun a ha => ?_⟩
    have hfa := fresh c hc hu hne'
    have hcq : c ≠ (⟨q - 32, (232 * max (2 * len) 4 + 31) / 32 + 1, true⟩ : Chunk) := by
      intro h; apply hfa; rw [h]; simp; omega
    have hdisj := Decode.VecU8.data_disj H5.wf hc' hnew hcq ha
    obtain ⟨hc0, -, hcT⟩ := Decode.VecU8.chunk_in H.wf hc hu
    have := H.hbT
    unfold InData at ha
    simp only at hdisj
    rw [ifr a (by omega) (by omega), gfr a (by omega) (by omega) (by omega), hd a ⟨ha.1, ha.2⟩,
      k2 a (by omega) (by omega)]
  · rw [Memory.readN_congr (fun j hj => k8 _ (by omega) (by omega) (by omega) (by omega)),
      Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega) (by omega))]; exact a280
  · have hqM : q + 232 * len + 232 ≤ M ∨ M + 632 ≤ q + 232 * len := by omega
    rw [k8 a (by omega) (by omega) (by omega) (by omega)]
    rcases ha with h | h | h | h
    · exact k2 a (by omega) (by omega)
    · exact k2 a (by omega) (by omega)
    · exact k2 a (by omega) (by omega)
    · rw [bfr a (by omega) (by omega) (by omega), afr a (by omega) (by omega)]

end Services.Bootstrap.Refine.PassGrow
