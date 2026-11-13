import Services.Bootstrap.Decode.ProvideInline
import Services.Bootstrap.Decode.VecU8Heap

/-!
# `Instruction::decode` of `Provide { Inline(bytes) }`, the payload in the heap

`provide_inline_heap`: `provide_inline_small` in the decode loop's setting, through
`VecU8.vec_u8_heap` (the encoding inside an allocated chunk, `HeapCtx`, the `alloc` failing an
outcome).
-/

namespace Services.Bootstrap.Decode.Provide

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Decode.Tag
  Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.VecU8
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA Services.Bootstrap.Decode.U32Hash

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **`Provide { service, preimage: Inline(bytes) }`, 1 ≤ n = |bytes| ≤ 16384, the payload in the heap**:
    as `provide_inline_small`, in the decode loop's setting (`VecU8.vec_u8_heap`): the encoding lies
    inside an allocated chunk of the allocator's state `s` (context `HeapCtx`, under
    `refineContractK cap`). Either the model's `alloc` of ⌈n/32⌉ units gives `(q, s')` and
    `Instruction::decode` returns the variant in O (the `Vec` `{cap n, ptr q, len n}` at O + 16, the n
    octets at q), the context kept for `s'`, every allocated chunk of `s` kept with its data; or the
    model's `alloc` fails and the run reaches the `alloc` wrapper's return (40611) with null. -/
theorem provide_inline_heap {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    (x : RefineCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s : State)
    (A O ret t v5 v6 rd ptr len n pb S0 S1 : Nat) (F : Frame P A O ret t v5 v6 ω μ)
    (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (tag : μ.read A = 17) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (H : HeapCtx env pb S0 S1 μ s) (hS : S0 + 456 ≤ A ∧ A + 56 ≤ S1)
    (hA8 : 2147484120 ≤ A ∧ A % 8 = 0) (hn : 1 ≤ n ∧ n ≤ 16384)
    (hlen : 5 + (Blob.encodeNat n).length + n ≤ len ∧ len < 4294967296)
    (hrd : A + 56 ≤ rd ∧ rd + 16 ≤ S1) (hO : A + 56 ≤ O ∧ O + 52 ≤ S1) (hOr : O + 52 ≤ rd ∨ rd + 16 ≤ O)
    (hpay : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ptr ∧
      ptr + 5 + (Blob.encodeNat n).length + n ≤ c.addr + 32 * c.size)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hinl : μ.read (ptr + 4) = 1) (henc : μ.readN (ptr + 5) (Blob.encodeNat n).length = Blob.encodeNat n) :
    (∃ q s' ω' μ', alloc (growTo pb) hb 1 ((n + 31) / 32) s = some (q, s') ∧
      FreeStepsH p (refineContractK cap env) 20626 ω μ x t ω' μ' x (2 * n + 2300) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775824 ∧ μ'.read (O + 8) = 1 ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 n ∧ μ'.readN (O + 24) 8 = Num.encodeLE 8 q ∧
      μ'.readN (O + 32) 8 = Num.encodeLE 8 n ∧ μ'.readN (O + 48) 4 = μ.readN ptr 4 ∧
      μ'.readN q n = μ.readN (ptr + 5 + (Blob.encodeNat n).length) n ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 5 + (Blob.encodeNat n).length + n) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 5 - (Blob.encodeNat n).length - n) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (⟨q - 32, (n + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ ⟨q - 32, (n + 31) / 32 + 1, true⟩) ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InData c a → μ'.read a = μ.read a) ∧
      PagesOut 48 pb μ μ' ∧
      (∀ a, a < 4294967296 → A ≤ a → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 52 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) ∧ (∀ a, S0 ≤ a → μ'.writable a = μ.writable a)) ∨
    (alloc (growTo pb) hb 1 ((n + 31) / 32) s = none ∧ ∃ ω' μ',
      FreeStepsH p (refineContractK cap env) 20626 ω μ x 40611 ω' μ' x (2 * n + 2300) ∧
      ω'[7] = UInt64.ofNat 0) := by
  have hA2 := F.hA
  have hS1' := H.hS1
  have hO64 : O < 18446744073709551616 := by omega
  have hw1 : 1 ≤ (Blob.encodeNat n).length := by
    unfold Blob.encodeNat; split
    · simp
    · split <;> simp
  have hst := H.st
  have hS1 := H.hS1
  obtain ⟨cp, hcpm, hcpu, hcp1, hcp2⟩ := hpay
  obtain ⟨hcpb, hcpT, hcpT'⟩ := chunk_in H.wf hcpm hcpu
  have hb0 := H.hb0
  have hbT := H.hbT
  have hra : ∀ a, ptr ≤ a → a < ptr + 5 + (Blob.encodeNat n).length + n → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (heap_writable H hcpm hcpu ⟨by omega, by omega⟩)
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, atag, apark, a982, aO, ard, aR0, aR8, afr, ard', awr⟩ :=
    pi_pre (p := p) (P := P) (R := refineContractK cap env) x ω μ A O ret t v5 v6 rd ptr len n F ⟨by omega, hA8.2⟩
      h6 h7 tag tab hrt ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) ⟨by omega, hlen.2⟩ hinl henc hR0 hR8
      (Or.inr hrd.1) (Or.inl (by omega)) (by omega) hO64 (fun a h1 h2 => hst a (by omega) (by omega))
      (fun a h1 h2 => hst a (by omega) (by omega)) (fun a h1 h2 => hra a h1 (by omega))
  obtain ⟨w, hW⟩ : ∃ w, (Blob.encodeNat n).length = w := ⟨_, rfl⟩
  simp only [hW] at hlen henc hcp2 hra hw1 aR0 aR8 ⊢
  have b1 : ∀ a, a < 2147483648 → μ1.read a = μ.read a := fun a h0 => afr a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  have H1 : HeapCtx env pb S0 S1 μ1 s := ctx_congr_data H hcpm (fun a h1 _ => b1 a h1) awr
  rcases vec_u8_heap (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω1 μ1 s (A - 152) (A - 152 + 80) rd
      (ptr + 5 + w) (len - 5 - w) n 1168 25153 O rd pb S0 S1 H1 ⟨cp, hcpm, hcpu, by omega, by omega⟩
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ a0 a1 a5 a6 a7 a8 a9 (by decide) jte_583 bs_25153 hO64 (by omega) hn
      (by omega) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) aR0 aR8 with
    ⟨q, s', ω2, μ2, ha, run2, v0, v1, v5', v6', vc, vp, vl, vdata, vR0, vR8, H2, keep, cm2, hfresh, kd2, pg2, vfr, -, vgl, -⟩ |
    ⟨hna, ω2, μ2, run2, f7⟩
  rotate_left
  · exact Or.inr ⟨hna, ω2, μ2, (run1.trans run2).mono (by omega), f7⟩
  have hst2 := H2.st
  have hqT : q + n < 2147483648 := by
    have := chunk_in H2.wf cm2 rfl; simp only at this; rw [alloc_base H.wf ha] at this; omega
  have hS2 : ∀ a, A - 152 ≤ a → a < 4294967296 → (a < A - 152 + 80 ∨ A - 152 + 104 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
      μ2.read a = μ1.read a := fun a h1 h2 h3 h4 => vfr a h2 h1 h4 (by omega)
  obtain ⟨ω3, μ3, run3, z0, z1, z5, z6, zO, zO8, zO16, zO24, zO32, zO48, zfr, zrd, zwr⟩ :=
    pi_post (p := p) (P := P) (R := refineContractK cap env) x ω2 μ2 A O ret t v5 v6 n q n (rdN μ1 (A - 152 + 8) 8) rd
      ⟨by omega, by omega⟩ (by omega) (by omega) v1 v5' (by omega) (by omega) (by omega) (rdN_lt64 _ _) (by omega)
      vc (by rw [show A - 152 + 88 = A - 152 + 80 + 8 by omega]; exact vp)
      (by rw [show A - 152 + 96 = A - 152 + 80 + 16 by omega]; exact vl)
      (by rw [Memory.readN_congr (fun j hj => hS2 _ (by omega) (by omega) (by omega) (by omega))]; exact atag)
      (by rw [Memory.readN_congr (fun j hj => hS2 _ (by omega) (by omega) (by omega) (by omega))]
          exact (encodeLE_rdN _ _ _).symm)
      (by rw [Memory.readN_congr (fun j hj => hS2 _ (by omega) (by omega) (by omega) (by omega))]; exact a982)
      (by rw [Memory.readN_congr (fun j hj => hS2 _ (by omega) (by omega) (by omega) (by omega))]; exact aO)
      (by rw [Memory.readN_congr (fun j hj => hS2 _ (by omega) (by omega) (by omega) (by omega))]; exact ard)
      (by rw [Memory.readN_congr (fun j hj => (hS2 _ (by omega) (by omega) (by omega) (by omega)).trans
            (afr _ (by omega) (by omega) (by omega)))]; exact F.s0)
      (by rw [Memory.readN_congr (fun j hj => (hS2 _ (by omega) (by omega) (by omega) (by omega)).trans
            (afr _ (by omega) (by omega) (by omega)))]; exact F.s5)
      (by rw [Memory.readN_congr (fun j hj => (hS2 _ (by omega) (by omega) (by omega) (by omega)).trans
            (afr _ (by omega) (by omega) (by omega)))]; exact F.s6)
      F.hret F.hjt F.hbt F.hv5 F.hv6
      (fun a h1 h2 => hst2 a (by omega) (by omega)) (fun a h1 h2 => hst2 a (by omega) (by omega))
      (fun a h1 h2 => Memory.readable_of_writable (hst2 a (by omega) (by omega)))
  have hlow : ∀ a, a < 2147483648 → μ3.read a = μ2.read a := fun a h0 => zfr a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  have run := run1.trans (run2.trans run3)
  have wr3 : ∀ a, μ3.writable a = μ2.writable a := zwr
  refine Or.inl ⟨q, s', ω3, μ3, ha, run.mono (by omega), z0, z1, z5, z6, zO, zO8, zO16, zO24, zO32, ?_, ?_, ?_, ?_,
    ctx_congr_data H2 cm2 (fun a h1 _ => hlow a h1) wr3, keep, cm2, hfresh,
    fun c hc hu a hia => by
      have := (chunk_in H.wf hc hu).2.2
      unfold InData at hia
      rw [hlow a (by omega), kd2 c hc hu a ⟨hia.1, hia.2⟩]
      exact b1 a (by omega),
    FreeStepsH.pagesOut H.bd run, ?_, ?_, ?_, ?_⟩
  · rw [zO48, ← take_encodeLE, encodeLE_rdN]; exact apark
  · rw [Memory.readN_congr (fun j hj => hlow _ (by omega)), vdata]
    exact Memory.readN_congr (fun j hj => afr _ (by omega) (by omega) (by omega))
  · rw [Memory.readN_congr (fun j hj => zfr _ (by omega) (by omega) (by omega))]; exact vR0
  · rw [Memory.readN_congr (fun j hj => zfr _ (by omega) (by omega) (by omega))]; exact vR8
  · intro a h0 h1 h2 h3
    rw [zfr a h0 (by omega) h3, vfr a h0 (by omega) h2 (by omega)]; exact afr a h0 (Or.inr h1) h2
  · intro a ha'
    obtain ⟨kp, kr⟩ := FreeStepsH.keepRO H.bd run
    refine ⟨kr a (by unfold two32; omega) (Or.inl (by unfold pageSize; omega)) (H.ro a ha'), ?_⟩
    unfold Memory.readable
    rw [kp _ (Or.inl (by unfold pageSize; omega))]
  · intro a ha'
    have hg := ha'
    unfold Glob at hg
    rw [hlow a (by omega), vgl a ha']
    exact b1 a (by omega)
  · intro a ha'
    obtain ⟨kp, -⟩ := FreeStepsH.keepRO H.bd run
    have := H.hSb
    unfold Memory.writable
    rw [kp _ (Or.inr (by unfold pageSize; omega))]

end Services.Bootstrap.Decode.Provide
