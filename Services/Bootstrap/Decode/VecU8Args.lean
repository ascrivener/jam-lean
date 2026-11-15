import Services.Bootstrap.Decode.VecU8Heap

/-!
# Reading 1 … 16384 octets into a fresh `Vec<u8>`, the payload in the argument zone

`vec_u8_args` is `vec_u8_heap` with the payload read from above the stack instead of from an
allocated chunk of the heap: the source [ptr, ptr + n) lies at or above the stack's top S1 (and 16
octets clear of 2³²) and is readable, as the argument blob is (≥ 4278124544 > S1 = 4278059008).
The source survives every step before the copy because the frame, the `alloc` call and the return
to `finish_grow` keep memory from sp up (`alloc_call`'s stack clause), and its readability survives
because a run under the heap contract changes no page from pb up (`FreeStepsH.keepRO`). The
conclusions are `vec_u8_heap`'s, word for word.
-/

namespace Services.Bootstrap.Decode.VecU8

open PVM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc JAM
  Services.Bootstrap.Decode.AllocOk Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **Writes only at or above 2³¹ keep the allocator's context** (as `Fmt.ctx_hi`, which this file
    does not import): through `ctx_congr_data` on any chunk of the well-formed heap. -/
theorem ctx_congr_hi {env : RefineHost.Env} {pb S0 S1 : Nat} {μ μ' : Memory} {s : State}
    (H : HeapCtx env pb S0 S1 μ s) (hk : ∀ a, a < 2147483648 → μ'.read a = μ.read a)
    (ww : ∀ a, μ'.writable a = μ.writable a) : HeapCtx env pb S0 S1 μ' s := by
  have ht := H.wf.2.2.2.1
  unfold TilesOk at ht
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  obtain ⟨c, hc⟩ : ∃ c, c ∈ chunks s := by
    cases h : chunks s with
    | nil => rw [h] at ht; simp only [Tiles] at ht; omega
    | cons c cs => exact ⟨c, List.mem_cons_self⟩
  exact ctx_congr_data H hc (fun a ha _ => hk a ha) ww

/-- A run under the heap contract keeps the access of every octet from page pb up. -/
theorem readable_hi {p : ByteArray} {env : RefineHost.Env} {cap pb : Nat}
    (hbd : heapBounds env.code = (48, pb)) {i i' n : Nat} {ω ω' : Regs} {μ μ' : Memory} {x x' : RefineCtx}
    (run : FreeStepsH p (refineContractK cap env) i ω μ x i' ω' μ' x' n) {a : Nat} (ha : 4096 * pb ≤ a) :
    μ'.readable a = μ.readable a := by
  obtain ⟨kp, -⟩ := FreeStepsH.keepRO hbd run
  unfold Memory.readable
  rw [kp _ (Or.inr (by unfold pageSize; omega))]

/-- The reader for n octets, n ≥ 1, from a source at or above sp (16 octets clear of 2³²), into a
    buffer 24 octets below the reader's frames (`read_low` with the source above). -/
theorem read_hi {p : ByteArray} {P : Program} [HasCode p P] {X : Type} {R : HostRel X} (x : X) (ω : Regs)
    (μ : Memory) (ret t sp rd buf ptr len n : Nat) (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp)
    (h7 : ω[7] = UInt64.ofNat rd) (h8 : ω[8] = UInt64.ofNat buf) (h9 : ω[9] = UInt64.ofNat n)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hsp : 65536 + 88 ≤ sp ∧ sp < 4294967296 ∧ sp % 8 = 0) (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296)
    (hbuf : 65536 ≤ buf ∧ buf + n + 24 ≤ sp - 88) (hptr : sp ≤ ptr ∧ ptr + n + 16 < 4294967296)
    (hn : 1 ≤ n) (hnl : n ≤ len) (hlen : len < 4294967296) (hrf : sp ≤ rd)
    (hwf : ∀ a, sp - 88 ≤ a → a < sp → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hwb : ∀ a, buf ≤ a → a < buf + n → μ.writable a = true)
    (hra : ∀ a, ptr ≤ a → a < ptr + n → μ.readable a = true)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len) :
    ∃ ω' μ', FreeStepsH p R 58434 ω μ x t ω' μ' x (2 * n + 400) ∧ ReadOkBig ω ω' μ μ' sp rd buf ptr len n := by
  by_cases hs : n < 16
  · obtain ⟨ω', μ', run, ok⟩ := read_ok (p := p) (P := P) (R := R) x ω μ ret t sp rd buf ptr len n h0 h1 h7 h8 h9
      hret hjt hbt ⟨by omega, hsp.2.1⟩ hrd ⟨hbuf.1, by omega⟩ ⟨by omega, by omega⟩ hs hnl hlen (Or.inr hrf)
      (Or.inl (by omega)) (Or.inr hptr.1) (Or.inl (by omega)) (Or.inl (by omega)) hwf hwr hwb hra hR0 hR8
    obtain ⟨o0, o1, -, -, -, o5, o6, -, o7, oR0, oR8, obuf, ofr, ord, owr⟩ := ok
    exact ⟨ω', μ', run.mono (by omega), o0, o1, o5, o6, o7, oR0, oR8, obuf, ofr, ord, owr⟩
  · exact read_big_sp (p := p) (P := P) (R := R) x ω μ ret t sp rd buf ptr len n h0 h1 h7 h8 h9 hret hjt hbt hsp
      hrd ⟨hbuf.1, by omega⟩ ⟨by omega, hptr.2⟩ (by omega) hnl hlen (Or.inr hrf) (Or.inl (by omega))
      (Or.inr hptr.1) (Or.inl (by omega)) (Or.inl (by omega)) hwf hwr hwb hra hR0 hR8

/-- **Reading 1 … 16384 octets into a fresh `Vec<u8>`, the payload in the argument zone** (3473): as
    `vec_u8_heap`, with the n payload octets at or above the stack's top S1 (and 16 octets clear of
    2³²), readable, instead of inside an allocated chunk. The conclusions are `vec_u8_heap`'s. -/
theorem vec_u8_args {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs) (μ : Memory)
    {hb : Nat} (s : State) (sp O rd ptr len n ret t v5 v6 pb S0 S1 : Nat)
    (H : HeapCtx env pb S0 S1 μ s)
    (hsrc : S1 ≤ ptr ∧ ptr + n + 16 < 4294967296)
    (hra : ∀ a, ptr ≤ a → a < ptr + n → μ.readable a = true)
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
      (∀ a, a < 4294967296 → sp ≤ a → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) ∧ (∀ a, S0 ≤ a → μ'.writable a = μ.writable a)) ∨
    (alloc (growTo pb) hb 1 ((n + 31) / 32) s = none ∧ ∃ ω' μ',
      FreeStepsH p (refineContractK cap env) 3473 ω μ x 40611 ω' μ' x (2 * n + 1200) ∧
      ω'[7] = UInt64.ofNat 0) := by
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
    ctx_congr_hi H (fun a h1 => hlow a (by omega) (Or.inl (by omega))) wr12
  -- alloc
  rcases alloc_call (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω2 μ2 s (sp - 136) n 1 pb S0 S1 H2 b1 b7 b8
      (by decide) (by decide) (by omega) (by omega) ⟨by omega, by omega⟩ with
    ⟨q, s', ω3, μ3, ha, run3, H3, keep, hnew, hfresh, hk, e7, stk3, e0, e1, e5, e6⟩ |
    ⟨hna, ω3, μ3, run3, e7, -, -, -, -, -⟩
  rotate_left
  · exact Or.inr ⟨hna, ω3, μ3, (run1.trans (run2.trans run3)).mono (by omega), e7⟩
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
  have run16 := run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))
  have wr36 : ∀ a, μ6.writable a = μ3.writable a := fun a => by rw [wr6, wr5]
  have hwq : ∀ a, q ≤ a → a < q + n → μ6.writable a = true := fun a h1 h2 => by
    rw [wr36]; exact heap_writable H3 hnew rfl ⟨by simp only; omega, by simp only; omega⟩
  obtain ⟨ω7, μ7, run7, r0, r1, r5, r6, r7, rR0, rR8, rbuf, fr7, rd7, wr7⟩ :=
    read_hi (p := p) (P := P) (R := refineContractK cap env) x ω6 μ6 90 3635 (sp - 96) rd q ptr len n d0 d1 d7 d8
      d9 (by decide) jte_44 bs_3635 ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, hsrc.2⟩ hn.1 hnl hlen (by omega)
      (fun a h1 h2 => by rw [wr36]; exact H3.st a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr36]; exact H3.st a (by omega) (by omega)) hwq
      (fun a h1 h2 => by rw [readable_hi H.bd run16 (by omega)]; exact hra a h1 h2)
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
    hfresh, ?_, FreeStepsH.pagesOut H.bd run18, ?_, ?_, ?_, ?_⟩
  · rw [Memory.readN_congr (fun j hj => fr8 _ (by omega) (by omega)), rbuf]
    exact Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))
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
  · intro a ha'
    obtain ⟨kp, kr⟩ := FreeStepsH.keepRO H.bd run18
    refine ⟨kr a (by unfold two32; omega) (Or.inl (by unfold pageSize; omega)) (H.ro a ha'), ?_⟩
    unfold Memory.readable
    rw [kp _ (Or.inl (by unfold pageSize; omega))]
  · intro a ha'
    have hg := ha'
    unfold Glob at hg
    have ht3 := H3.wf.2.2.2.1
    unfold TilesOk at ht3
    have hb3 := H3.hb0
    rw [hlowh a (by omega) (Or.inl (by omega)),
      hk.glob (fun b ⟨c, hc, e⟩ => Or.inr (by have := (ht3.mem_lt c hc).1; omega)) a ha']
    exact hlow a (by omega) (Or.inl (by omega))
  · intro a ha'
    obtain ⟨kp, -⟩ := FreeStepsH.keepRO H.bd run18
    have := H.hSb
    unfold Memory.writable
    rw [kp _ (Or.inr (by unfold pageSize; omega))]

end Services.Bootstrap.Decode.VecU8
