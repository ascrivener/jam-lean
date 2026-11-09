import Services.Bootstrap.Decode.VecU8Small
import Services.Bootstrap.Decode.LoopA
import Services.Bootstrap.Decode.VecU8Pass

/-!
# Reading 1 … 16384 octets into a fresh `Vec<u8>`, the payload in the heap

`vec_u8_heap` is `VecU8.vec_u8_small` in the decode loop's setting: the payload lies inside an
allocated chunk of the heap (below the stack), the allocator's context is `HeapCtx`, and the `alloc`
call is `HeapCtx.alloc_call`, under `refineContractK cap`. The payload survives the `alloc` because
`alloc` keeps every allocated chunk and writes only off their data (`HKeep`). Both outcomes of the
`alloc` are covered: the model's block, or null at the `alloc` wrapper's return (40611) when the
model's `alloc` fails.
-/

namespace Services.Bootstrap.Decode.VecU8

open PVM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc JAM
  Services.Bootstrap.Decode.AllocOk Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- The reader for n octets, 1 ≤ n ≤ 16384, from a source below the reader's frames (16 octets clear
    of them) and 24 octets clear of the buffer. -/
theorem read_low {p : ByteArray} {P : Program} [HasCode p P] {X : Type} {R : HostRel X} (x : X) (ω : Regs)
    (μ : Memory) (ret t sp rd buf ptr len n : Nat) (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp)
    (h7 : ω[7] = UInt64.ofNat rd) (h8 : ω[8] = UInt64.ofNat buf) (h9 : ω[9] = UInt64.ofNat n)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hsp : 65536 + 88 ≤ sp ∧ sp < 4294967296 ∧ sp % 8 = 0) (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296)
    (hbuf : 65536 ≤ buf ∧ buf + n + 24 ≤ sp - 88) (hptr : 65536 ≤ ptr ∧ ptr + n + 16 ≤ sp - 88)
    (hn : 1 ≤ n) (hnl : n ≤ len) (hlen : len < 4294967296)
    (hrf : sp ≤ rd) (hbp : buf + n + 24 ≤ ptr ∨ ptr + n + 24 ≤ buf)
    (hwf : ∀ a, sp - 88 ≤ a → a < sp → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hwb : ∀ a, buf ≤ a → a < buf + n → μ.writable a = true)
    (hra : ∀ a, ptr ≤ a → a < ptr + n → μ.readable a = true)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len) :
    ∃ ω' μ', FreeStepsH p R 58434 ω μ x t ω' μ' x (2 * n + 400) ∧ ReadOkBig ω ω' μ μ' sp rd buf ptr len n := by
  by_cases hs : n < 16
  · obtain ⟨ω', μ', run, ok⟩ := read_ok (p := p) (P := P) (R := R) x ω μ ret t sp rd buf ptr len n h0 h1 h7 h8 h9
      hret hjt hbt ⟨by omega, hsp.2.1⟩ hrd ⟨hbuf.1, by omega⟩ ⟨hptr.1, by omega⟩ hs hnl hlen (Or.inr hrf)
      (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (by omega) hwf hwr hwb hra hR0 hR8
    obtain ⟨o0, o1, -, -, -, o5, o6, -, o7, oR0, oR8, obuf, ofr, ord, owr⟩ := ok
    exact ⟨ω', μ', run.mono (by omega), o0, o1, o5, o6, o7, oR0, oR8, obuf, ofr, ord, owr⟩
  · exact read_big_sp (p := p) (P := P) (R := R) x ω μ ret t sp rd buf ptr len n h0 h1 h7 h8 h9 hret hjt hbt hsp
      hrd ⟨hbuf.1, by omega⟩ ⟨hptr.1, by omega⟩ (by omega) hnl hlen (Or.inr hrf) (Or.inl (by omega))
      (Or.inl (by omega)) (Or.inl (by omega)) hbp hwf hwr hwb hra hR0 hR8

/-- **Writes inside one allocated chunk's data, and above 2³¹, keep the allocator's context.** -/
theorem ctx_congr_data {env : RefineHost.Env} {pb S0 S1 : Nat} {μ μ' : Memory} {s : State}
    (H : HeapCtx env pb S0 S1 μ s) {c : Chunk} (hc : c ∈ chunks s)
    (wf : ∀ a, a < 2147483648 → (a < c.addr + 32 ∨ c.addr + 32 * c.size ≤ a) → μ'.read a = μ.read a)
    (ww : ∀ a, μ'.writable a = μ.writable a) : HeapCtx env pb S0 S1 μ' s := by
  obtain ⟨ph, h48, hhb, hp, hHTs, hHT⟩ := H.pages
  refine ⟨H.wf, HeapFrame.Rep.congr_data H.rep H.wf H.hb0 H.hbT hc (fun a h1 h2 => wf a h1 (by omega)),
    H.fo, ?_, H.hb0, H.hbT, H.hA, H.bd, ⟨ph, h48, hhb, HeapPages.of_eq hp ww, hHTs, hHT⟩, H.hSb, H.hS1,
    fun a h1 h2 => by rw [ww]; exact H.st a h1 h2, fun a ha => by rw [ww]; exact H.ro a ha⟩
  have ht := H.wf.2.2.2.1; unfold TilesOk at ht
  have hca := (ht.mem_lt c hc).1
  have := H.hb0
  rw [rdN_frame (fun j hj => wf _ (by omega) (Or.inl (by omega)))]; exact H.lock

/-- Data of distinct chunks of a well-formed heap does not overlap. -/
theorem data_disj {s : State} (hwf : WF s) {c d : Chunk} (hc : c ∈ chunks s) (hd : d ∈ chunks s) (hcd : c ≠ d)
    {a : Nat} (ha : InData c a) : a < d.addr ∨ d.addr + 32 * d.size ≤ a := by
  have ht := hwf.2.2.2.1; unfold TilesOk at ht
  unfold InData at ha
  rcases HeapFrame.Tiles.disjoint ht c hc d hd hcd with h | h <;> omega

/-- An allocated chunk's data is writable (`LoopA.heap_writable_data`, for any stack bounds). -/
theorem heap_writable {env : RefineHost.Env} {pb S0 S1 : Nat} {μ : Memory} {s : State}
    (H : HeapCtx env pb S0 S1 μ s) {c : Chunk} (hc : c ∈ chunks s) (hu : c.used = true) {a : Nat}
    (ha : InData c a) : μ.writable a = true := by
  obtain ⟨ph, h48, hhb, hp, hHTs, hHT⟩ := H.pages
  have hsp := H.wf.2.2.2.2.2.2.2
  unfold SpaceOk at hsp
  have h1 := (hsp c hc).1 hu
  have ht := H.wf.2.2.2.1
  unfold TilesOk at ht
  have hm := ht.mem_lt c hc
  have := H.hb0
  unfold InData at ha
  have hq := hp (a / 4096) (by omega) (by omega)
  unfold Memory.writable
  rw [show pageSize = 4096 from rfl, hq]
  simp only [decide_eq_true_eq]; omega

/-- **Reading 1 … 16384 octets into a fresh `Vec<u8>`, the payload in the heap** (3473): as
    `vec_u8_small`, with the allocator's context `HeapCtx` (under `refineContractK cap`, cap ≥ 2²⁷)
    and the n payload octets inside the data of an allocated chunk. Either the model's `alloc` of
    ⌈n/32⌉ units gives `(q, s')` and `read_vec` returns to t with the `Vec` `{cap n, ptr q, len n}`
    at O and the payload at q, the context kept for `s'`, every allocated chunk of `s` kept with its
    data, and the block a new allocated chunk; or the model's `alloc` fails and the run reaches the
    `alloc` wrapper's return (40611) with null. -/
theorem vec_u8_heap {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs) (μ : Memory)
    {hb : Nat} (s : State) (sp O rd ptr len n ret t v5 v6 pb S0 S1 : Nat)
    (H : HeapCtx env pb S0 S1 μ s)
    (hpay : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ptr ∧ ptr + n ≤ c.addr + 32 * c.size)
    (hS : S0 + 304 ≤ sp ∧ sp ≤ S1) (hsp : 2147483968 ≤ sp ∧ sp % 8 = 0)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat O) (h8 : ω[8] = UInt64.ofNat rd)
    (h9 : ω[9] = UInt64.ofNat n)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hn : 1 ≤ n ∧ n ≤ 16384) (hnl : n ≤ len) (hlen : len < 4294967296)
    (hrd : sp ≤ rd ∧ rd + 16 ≤ S1) (hO : sp ≤ O ∧ O + 24 ≤ S1) (hOr : O + 24 ≤ rd ∨ rd + 16 ≤ O)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len) :
    (∃ q s' ω' μ', alloc (growTo pb) hb 1 ((n + 31) / 32) s = some (q, s') ∧
      FreeStepsH p (refineContractK cap env) 3473 ω μ x t ω' μ' x (2 * n + 1200) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 n ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 q ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 n ∧ μ'.readN q n = μ.readN ptr n ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + n) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - n) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (⟨q - 32, (n + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ ⟨q - 32, (n + 31) / 32 + 1, true⟩) ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InData c a → μ'.read a = μ.read a) ∧
      PagesOut 48 pb μ μ' ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 24 ≤ a) → μ'.read a = μ.read a)) ∨
    (alloc (growTo pb) hb 1 ((n + 31) / 32) s = none ∧ ∃ ω' μ',
      FreeStepsH p (refineContractK cap env) 3473 ω μ x 40611 ω' μ' x (2 * n + 1200) ∧
      ω'[7] = UInt64.ofNat 0) := by
  obtain ⟨cp, hcpm, hcpu, hcp1, hcp2⟩ := hpay
  obtain ⟨hcpb, hcpT, hcpT'⟩ := chunk_in H.wf hcpm hcpu
  have hb0 := H.hb0
  have hbT := H.hbT
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst := H.st
  have hrd64 : rd < 18446744073709551616 := by omega
  have hO64 : O < 18446744073709551616 := by omega
  have hret64 : ret < 18446744073709551616 := by omega
  -- the frame and the call of finish_grow
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, a10, a11, a12, m8, m16, m24, m80, m88, m64, m96, fr1, rd1,
      wr1⟩ := v1 (p := p) (P := P) (R := refineContractK cap env) x ω μ sp O rd n len ret v5 v6 ⟨by omega, by omega⟩
    h0 h1 h5 h6 h7 h8 h9 hret64 hv5 hv6 hO64 hn hnl (by omega) (by omega) (Or.inr hrd.1) (rd8' (by omega) hR8)
    (fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)))
    (fun a h1 h2 => hst a (by omega) (by omega))
  obtain ⟨ω2, μ2, run2, b0, b1, b6, b7, b8, n32, n24, n16, n8, fr2, rd2, wr2⟩ :=
    g1 (p := p) (P := P) (R := refineContractK cap env) x ω1 μ1 (sp - 136) (sp - 48) n 88 0 n ⟨by omega, by omega⟩
      a0 (by rw [a1]; congr 1; omega) a5 a6 a7 a8 a10 a11 a12 (by decide) (by decide) (by omega) (by omega)
      ⟨hn.1, by omega⟩ (fun a h1 h2 => by rw [wr1]; exact hst a (by omega) (by omega))
  have hlow : ∀ a, a < 4294967296 → (a < sp - 136 ∨ sp ≤ a) → μ2.read a = μ.read a := fun a h0 h1 =>
    (fr2 a h0 (by omega)).trans (fr1 a h0 (by omega))
  have wr12 : ∀ a, μ2.writable a = μ.writable a := fun a => by rw [wr2, wr1]
  have H2 : HeapCtx env pb S0 S1 μ2 s :=
    ctx_congr_data H hcpm (fun a h1 _ => hlow a (by omega) (Or.inl (by omega))) wr12
  -- alloc
  rcases alloc_call (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω2 μ2 s (sp - 136) n 1 pb S0 S1 H2 b1 b7 b8
      (by decide) (by decide) (by omega) (by omega) ⟨by omega, by omega⟩ with
    ⟨q, s', ω3, μ3, ha, run3, H3, keep, hnew, hfresh, hk, e7, stk3, e0, e1, e5, e6⟩ |
    ⟨hna, ω3, μ3, run3, e7, -, -, -, -, -⟩
  rotate_left
  · exact Or.inr ⟨hna, ω3, μ3, (run1.trans (run2.trans run3)).mono (by omega), e7⟩
  have hcp' := keep cp hcpm hcpu
  have hcpne : cp ≠ ⟨q - 32, (n + 31) / 32 + 1, true⟩ := hfresh cp hcpm hcpu
  obtain ⟨hqb, hqT, hqT'⟩ := chunk_in H3.wf hnew rfl
  simp only at hqb hqT hqT'
  have hbase' : s'.base = s.base := alloc_base H.wf ha
  rw [hbase'] at hqb hqT hqT'
  -- the heap's data survives the alloc
  have kd : ∀ d ∈ chunks s, d.used = true → ∀ a, InData d a → μ3.read a = μ2.read a := fun d hd hu a ha =>
    hk.hkeep a (off_hdr_data H3.wf H3.hb0 H3.hbT (keep d hd hu) ha.1 ha.2)
  have run4 := alloc_ret (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (by rw [e0, b0])
  -- back in finish_grow
  have hF : ∀ a, sp - 136 ≤ a → a < 4294967296 → μ3.read a = μ2.read a := fun a h1 h2 => stk3 a h2 h1
  obtain ⟨ω5, μ5, run5, c0, c1, c5, c6, cres, cres8, cres16, fr5, rd5, wr5⟩ :=
    g2 (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (sp - 136) (sp - 48) n q 88 3600 0 n
      ⟨by omega, by omega⟩ (by omega) (Or.inr (by omega)) (by rw [e1, b1]) (by rw [e6, b6]) e7
      ⟨by omega, by omega⟩ (by omega) (by decide) (by omega)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n32)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n24)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n16)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n8)
      (by decide) jte_43 bs_3600
      (fun a h1 h2 => Memory.readable_of_writable (H3.st a (by omega) (by omega)))
      (fun a h1 h2 => H3.st a (by omega) (by omega))
  have hS5 : ∀ a, sp - 96 ≤ a → a < 4294967296 → (a < sp - 48 ∨ sp - 24 ≤ a) → μ5.read a = μ1.read a :=
    fun a h1 h2 h3 => (fr5 a h2 (by omega)).trans ((hF a (by omega) h2).trans (fr2 a h2 (by omega)))
  obtain ⟨ω6, μ6, run6, d0, d1, d5, d6, d7, d8, d9, dq, dn, fr6, rd6, wr6⟩ :=
    v2 (p := p) (P := P) (R := refineContractK cap env) x ω5 μ5 (sp - 96) rd q n ⟨by omega, by omega⟩
      (by rw [c1]; congr 1; omega) c5 c6 (by omega) (by omega) hrd64
      (by rw [show sp - 96 + 48 = sp - 48 by omega]; exact cres)
      (by rw [show sp - 96 + 56 = sp - 48 + 8 by omega]; exact cres8)
      (by rw [Memory.readN_congr (fun j hj => hS5 _ (by omega) (by omega) (by omega))]; exact m96)
      (by rw [show sp - 96 + 16 = sp - 80 by omega, Memory.readN_congr (fun j hj => hS5 _ (by omega) (by omega) (by omega))]; exact m80)
      (fun a h1 h2 => by rw [wr5]; exact H3.st a (by omega) (by omega))
  -- the read
  have hhigh : ∀ a, a < 4294967296 → sp ≤ a → μ6.read a = μ.read a := fun a h0 h1 =>
    (fr6 a h0 (by omega) (by omega)).trans ((fr5 a h0 (by omega)).trans ((hF a (by omega) h0).trans (hlow a h0 (Or.inr h1))))
  have h63 : ∀ a, a < 2147483648 → μ6.read a = μ3.read a := fun a h0 =>
    (fr6 a (by omega) (by omega) (by omega)).trans (fr5 a (by omega) (Or.inl (by omega)))
  have hpay6 : ∀ a, InData cp a → μ6.read a = μ.read a := fun a ha =>
    (h63 a (by unfold InData at ha; omega)).trans ((kd cp hcpm hcpu a ha).trans (hlow a (by unfold InData at ha; omega) (Or.inl (by unfold InData at ha; omega))))
  have wr36 : ∀ a, μ6.writable a = μ3.writable a := fun a => by rw [wr6, wr5]
  have hwq : ∀ a, q ≤ a → a < q + n → μ6.writable a = true := fun a h1 h2 => by
    rw [wr36]; exact heap_writable H3 hnew rfl ⟨by simp only; omega, by simp only; omega⟩
  have hdq : q + n + 24 ≤ ptr ∨ ptr + n + 24 ≤ q := by
    have ht := H3.wf.2.2.2.1; unfold TilesOk at ht
    rcases HeapFrame.Tiles.disjoint ht cp hcp' _ hnew hcpne with h' | h' <;> simp only at h' <;> omega
  obtain ⟨ω7, μ7, run7, r0, r1, r5, r6, r7, rR0, rR8, rbuf, fr7, rd7, wr7⟩ :=
    read_low (p := p) (P := P) (R := refineContractK cap env) x ω6 μ6 90 3635 (sp - 96) rd q ptr len n d0 d1 d7 d8
      d9 (by decide) jte_44 bs_3635 ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ hn.1 hnl hlen (by omega) hdq
      (fun a h1 h2 => by rw [wr36]; exact H3.st a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr36]; exact H3.st a (by omega) (by omega)) hwq
      (fun a h1 h2 => by
        exact Memory.readable_of_writable (by rw [wr36]; exact heap_writable H3 hcp' hcpu ⟨by omega, by omega⟩))
      (by rw [Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))]; exact hR8)
  -- the return
  have hS7 : ∀ a, sp - 96 ≤ a → a < sp → μ7.read a = μ6.read a := fun a h1 h2 =>
    fr7 a (by omega) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
  have hS61 : ∀ a, sp - 96 ≤ a → a < sp → (a < sp - 72 ∨ sp - 64 ≤ a) → (a < sp - 56 ∨ sp - 48 ≤ a) →
      (a < sp - 48 ∨ sp - 24 ≤ a) → μ7.read a = μ1.read a := fun a h1 h2 h3 h3' h4 =>
    (hS7 a h1 h2).trans ((fr6 a (by omega) (by omega) (by omega)).trans (hS5 a h1 (by omega) h4))
  obtain ⟨ω8, μ8, run8, z0, z1, z5, z6, zO, zO8, zO16, fr8, rd8, wr8⟩ :=
    v3 (p := p) (P := P) (R := refineContractK cap env) x ω7 μ7 (sp - 96) O q n ret t v5 v6 ⟨by omega, by omega⟩
      (by omega) (Or.inr (by omega)) (by rw [r1, d1]) (by rw [r5, d5]) (by rw [r6, d6]) r7 (by omega) (by omega)
      hv5 hv6
      (by rw [show sp - 96 + 32 = sp - 64 by omega, Memory.readN_congr (fun j hj => hS61 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact m64)
      (by rw [Memory.readN_congr (fun j hj => hS7 _ (by omega) (by omega))]; exact dn)
      (by rw [Memory.readN_congr (fun j hj => hS7 _ (by omega) (by omega))]; exact dq)
      (by rw [show sp - 96 + 8 = sp - 88 by omega, Memory.readN_congr (fun j hj => hS61 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact m88)
      (by rw [show sp - 96 + 88 = sp - 8 by omega, Memory.readN_congr (fun j hj => hS61 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact m8)
      (by rw [show sp - 96 + 80 = sp - 16 by omega, Memory.readN_congr (fun j hj => hS61 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact m16)
      (by rw [show sp - 96 + 72 = sp - 24 by omega, Memory.readN_congr (fun j hj => hS61 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact m24)
      hret hjt hbt
      (fun a h1 h2 => by rw [rd7]; exact Memory.readable_of_writable (by rw [wr36]; exact H3.st a (by omega) (by omega)))
      (fun a h1 h2 => by rw [wr7, wr36]; exact H3.st a (by omega) (by omega))
  -- the heap after the read and the return
  have hlowh : ∀ a, a < 2147483648 → (a < q ∨ q + n ≤ a) → μ8.read a = μ3.read a := fun a h1 h3 =>
    (fr8 a (by omega) (by omega)).trans ((fr7 a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) h3).trans
      (h63 a h1))
  have run18 := run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans run8))))))
  have wr8' : ∀ a, μ8.writable a = μ3.writable a := fun a => by rw [wr8, wr7, wr36]
  refine Or.inl ⟨q, s', ω8, μ8, ha, run18.mono (by omega), z0, by rw [z1]; congr 1; omega, z5, z6, zO, zO8, zO16,
    ?_, ?_, ?_, ctx_congr_data H3 hnew (fun a h1 h2 => hlowh a h1 (by simp only at h2; omega)) wr8', keep, hnew,
    hfresh, ?_, FreeStepsH.pagesOut H.bd run18, ?_⟩
  · rw [Memory.readN_congr (fun j hj => fr8 _ (by omega) (by omega)), rbuf]
    exact Memory.readN_congr (fun j hj => hpay6 _ ⟨by omega, by omega⟩)
  · rw [Memory.readN_congr (fun j hj => fr8 _ (by omega) (by omega))]; exact rR0
  · rw [Memory.readN_congr (fun j hj => fr8 _ (by omega) (by omega))]; exact rR8
  · intro d hd hu a ha
    have hdis := data_disj H3.wf (keep d hd hu) hnew (hfresh d hd hu) ha
    simp only at hdis
    have hca := ha
    unfold InData at hca
    have := (chunk_in H.wf hd hu).2.2
    rw [hlowh a (by omega) (by omega), kd d hd hu a ha]
    exact hlow a (by omega) (Or.inl (by omega))
  · intro a h0 h1 h2 h3
    rw [fr8 a h0 h3, fr7 a h0 (Or.inr (by omega)) h2 (Or.inr (by omega))]; exact hhigh a h0 h1

end Services.Bootstrap.Decode.VecU8
