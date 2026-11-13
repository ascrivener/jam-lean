import Services.Bootstrap.Acc.Inputs.Glue
import Services.Bootstrap.Acc.Inputs.GlueFree
import Services.Bootstrap.Acc.DecodeU32A

/-!
# The inputs' decode, 44495 → 44674

In 6630's frame (sp): the fetched octets ℰ(↕**i**) (GP v0.8.0 §12: the accumulation inputs, a
length-prefixed sequence) at `ptr` in an allocated chunk F; their count n (1 … 89, one octet of
GP (C)'s compact form) by `decodeU32A`; the n items by `lp_call` into a fresh buffer; the fetched
buffer freed (`g_free`); `Vec { n, q, n }` stored at the output (the pointer at sp + 8); the return.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **The inputs' decode, 44495 → 44674** (n = |rest| items, 0 < n ≤ 89): the fetched octets
    `[n] ++ encs rest` at `ptr`, the data of the allocated chunk F (the fetched `Vec`'s capacity
    fc ≠ 0 at sp + 56, ptr at + 64, its length at + 72). Either `Vec { n, q, n }` is stored at the output
    o (the pointer at sp + 8), its buffer a fresh chunk whose slot j satisfies item j's `Rep` for any
    memory agreeing on the final state's allocated data, F freed, the context holding for the final
    state, every other allocated chunk and its data kept, the caller's stack above sp + 144 kept off
    the output, and ω₀, ω₅, ω₆ restored from the frame at the return; or the allocator is exhausted
    (the trap 45975, or 45642 when `finish_grow` fails). -/
theorem g_call {X : Type} (env : HeapHost X) (cap pb N : Nat) (hcap1 : 134217728 ≤ cap)
    (hcap : cap < 18446744073709551616) {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P]
    (x : X) (ω : Regs) (μ : Memory) {hb : Nat} (s0 : State) (sp o fc ptr len S0 S1 : Nat) (F : Chunk)
    (rest : List (List UInt8 × (List UInt8 → Memory → Prop)))
    (hok : ∀ e ∈ rest, ItemOk env cap pb p P N e.1 e.2) (hn : 0 < rest.length ∧ rest.length ≤ 89)
    (H : HeapCtxC env.code pb S0 S1 μ s0) (h1 : ω[1] = UInt64.ofNat sp)
    (m8 : rdN μ (sp + 8) 8 = o) (m56 : rdN μ (sp + 56) 8 = fc) (m64 : rdN μ (sp + 64) 8 = ptr)
    (m72 : rdN μ (sp + 72) 8 = len) (hfc : 0 < fc ∧ fc ≠ 18446744073709551615)
    (hF : F ∈ chunks s0) (hFu : F.used = true) (hFa : F.addr + 32 = ptr)
    (hFe : ptr + 1 + (encs rest).length ≤ F.addr + 32 * F.size)
    (hlen : 1 + (encs rest).length ≤ len ∧ len < 4294967296)
    (henc : μ.readN ptr (1 + (encs rest).length) = [UInt8.ofNat rest.length] ++ encs rest)
    (hsp : 2147483960 + 424 + 480 ≤ sp ∧ sp % 8 = 0) (hSTk : S0 + 864 + 480 ≤ sp)
    (ho : sp + 144 ≤ o ∧ o + 24 ≤ S1) :
    (∃ q st' ω' μ', FreeStepsH p (env.rel cap) 44495 ω μ x 44674 ω' μ' x ((N + 2100) * rest.length + 1900) ∧
      ω'[0] = UInt64.ofNat (rdN μ (sp + 136) 8) ∧ ω'[1] = UInt64.ofNat (sp + 144) ∧
      ω'[5] = UInt64.ofNat (rdN μ (sp + 128) 8) ∧ ω'[6] = UInt64.ofNat (rdN μ (sp + 120) 8) ∧
      rdN μ' o 8 = rest.length ∧ rdN μ' (o + 8) 8 = q ∧ rdN μ' (o + 16) 8 = rest.length ∧
      HeapCtxC env.code pb S0 S1 μ' st' ∧
      (∀ c ∈ chunks s0, c.used = true → c ≠ F → c ∈ chunks st' ∧ ∀ a, InDataA c a → μ'.read a = μ.read a) ∧
      (⟨q - 32, (rest.length * 184 + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks st' ∧
      (∀ d ∈ chunks s0, d.used = true → d ≠ ⟨q - 32, (rest.length * 184 + 31) / 32 + 1, true⟩) ∧
      (∀ (j : Nat) (e : List UInt8 × (List UInt8 → Memory → Prop)), rest[j]? = some e →
        ∀ μ'' : Memory, (∀ c ∈ chunks st', c.used = true → ∀ a, InDataA c a → μ''.read a = μ'.read a) →
          e.2 (μ''.readN (q + 184 * j) 184) μ'') ∧
      (∀ a, a < 4294967296 → sp + 144 ≤ a → (a < o ∨ o + 24 ≤ a) → μ'.read a = μ.read a)) ∨
    (∃ j ω' μ', (j = 45975 ∨ j = 45642) ∧
      FreeStepsH p (env.rel cap) 44495 ω μ x j ω' μ' x ((N + 2100) * rest.length + 1900)) := by
  have hbT := H.hbT
  have hb0 := H.hb0
  have hS1 := H.hS1
  have hst := H.st
  obtain ⟨Fb1, Fb2, Fb3⟩ := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hF hFu
  obtain ⟨hA, hB⟩ := readN_app μ ptr [UInt8.ofNat rest.length] (encs rest) (by simpa [Nat.add_comm] using henc)
  have hp0 : μ.read ptr = UInt8.ofNat rest.length := by simpa [Memory.readN] using hA
  -- 44495 → 39710
  obtain ⟨ω1, μ1, r1, a0, a1, a5, a6, a7, s0', R0, R8, fr1, rd1, wr1⟩ :=
    g_pre (p := p) (P := P) (R := env.rel cap) x ω μ sp fc ptr len h1 m56 m64 m72 hfc.2 ⟨by omega, by omega⟩
      (fun a h1 h2 => hst a (by omega) (by omega))
  have lo1 : ∀ a, a < 2147483648 → μ1.read a = μ.read a := fun a ha =>
    fr1 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  have H1 : HeapCtxC env.code pb S0 S1 μ1 s0 := HeapCtxC.keep_hi H lo1 wr1
  -- 39710 → 44527, the count
  obtain ⟨ω2, μ2, r2, b0, b1, -, -, -, b5, b6, -, b7, b8, R0', R8', fr2, rd2, wr2⟩ :=
    decodeU32A_len1 (p := p) (P := P) (R := env.rel cap) x ω1 μ1 2024 44527 sp (sp + 104) ptr len a0 a1 a7
      ⟨by decide, by decide, by decide⟩ (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_1011]) bs_44527
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, hlen.2⟩ (Or.inr (by omega))
      (Or.inl (by omega)) (Or.inl (by omega)) (fun a h1 h2 => by rw [wr1]; exact hst a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr1]; exact hst a (by omega) (by omega))
      (fun a h1 h2 => Memory.readable_of_writable (heapC_writable_data H1 hF hFu ⟨by omega, by omega⟩))
      R0 R8 rest.length ⟨hn.1, by omega⟩ (by rw [lo1 ptr (by omega)]; exact hp0)
  have lo2 : ∀ a, a < 2147483648 → μ2.read a = μ1.read a := fun a ha =>
    fr2 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  have H2 : HeapCtxC env.code pb S0 S1 μ2 s0 := HeapCtxC.keep_hi H1 lo2 wr2
  -- 44527 → 44916
  obtain ⟨ω3, r3, c0, c1, c5, c6, c7, c8, c9⟩ :=
    g_mid (p := p) (P := P) (R := env.rel cap) x ω2 μ2 sp rest.length (by rw [b1, a1]) b7 b8 (by omega)
      ⟨by omega, by omega⟩
  -- 44916 → 45613, the items
  rcases lp_call (hb := hb) env cap pb N hcap1 hcap x ω3 μ2 s0 sp (sp + 80) (sp + 104) (ptr + 1) (len - 1) S0 S1 F
      rest hok hn H2 c1 c7 c8 c9 hsp hSTk ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (Or.inl (by omega)) hF hFu
      (by omega) (by omega) R0' R8' (by omega) (by omega)
      (by
        rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => by rw [lo2 _ (by omega), lo1 _ (by omega)])]
        exact hB) with
    ⟨q, s2, ω4, μ4, r4, d0, d1, d5, d6, v0, v8, v16, H4, keep4, keepd4, hnew, hfresh, reps, -, -, fr4⟩ |
    ⟨j, ω4, μ4, hj, r4⟩
  · have hst4 := H4.st
    -- the stack above sp, from μ to μ4, off out (sp + 80 … + 104), the reader (… + 120), and sp itself
    have k4 : ∀ a, a < 4294967296 → sp ≤ a → (a < sp + 80 ∨ sp + 120 ≤ a) → (a < sp ∨ sp + 8 ≤ a) →
        μ4.read a = μ.read a := fun a h0 ha h2 h3 => by
      rw [fr4 a h0 ha (by omega) (by omega), fr2 a h0 (Or.inr ha) (by omega),
        fr1 a h0 h3 (by omega)]
    have kw : ∀ o', sp + 8 ≤ o' → o' + 8 ≤ sp + 80 ∨ sp + 120 ≤ o' → o' + 8 ≤ 4294967296 →
        rdN μ4 o' 8 = rdN μ o' 8 := fun o' h1 h2 h3 =>
      rdN_frame fun j hj => k4 _ (by omega) (by omega) (by omega) (Or.inr (by omega))
    have hsp4 : rdN μ4 sp 8 = ptr := by
      rw [rdN_frame fun j hj => fr4 _ (by omega) (by omega) (by omega) (by omega),
        rdN_frame fun j hj => fr2 _ (by omega) (Or.inr (by omega)) (by omega)]
      exact s0'
    have r5 := g_ret (p := p) (P := P) (R := env.rel cap) x ω4 μ4 (by rw [d0, c0])
    -- 44552 → 44591
    obtain ⟨ω6, μ6, r6, e1, e5, e6, e7, e8, p16, p24, fr6, rd6, wr6⟩ :=
      g_post (p := p) (P := P) (R := env.rel cap) x ω4 μ4 sp fc rest.length q rest.length (by rw [d1])
        (by rw [d6, c6, b6, a6]) v0 v8 v16 (by omega) ⟨hfc.1, by rw [← m56]; exact rdN_lt64 _ _⟩ ⟨by omega, by omega⟩
        (fun a h1 h2 => hst4 a (by omega) (by omega))
    have lo6 : ∀ a, a < 2147483648 → μ6.read a = μ4.read a := fun a ha => fr6 a (by omega) (Or.inl (by omega))
    have H6 : HeapCtxC env.code pb S0 S1 μ6 s2 := HeapCtxC.keep_hi H4 lo6 wr6
    -- 44591 → 44641, F freed
    obtain ⟨ω7, μ7, r7, H7, -, wr7, stk7, kd7, f1, f5, f6⟩ :=
      g_free (p := p) (P := P) (R := env.rel cap) env.code pb S0 S1 x ω6 μ6 s2 sp ptr F H6 (keep4 F hF hFu) hFu hFa
        e1 e6 e7 e8 (by rw [rdN_frame fun j hj => fr6 _ (by omega) (Or.inl (by omega))]; exact hsp4) (by omega)
        ⟨by omega, by omega⟩
    have hst7 := H7.st
    -- 44641 → 44674
    obtain ⟨ω8, μ8, r8, z0, z1, z5, z6, o0, o8, o16, fr8, rd8, wr8⟩ :=
      g_end (p := p) (P := P) (R := env.rel cap) x ω7 μ7 sp o rest.length q rest.length f1 (by rw [f5, e5])
        (by
          rw [rdN_frame fun j hj => stk7 _ (by omega) (by omega),
            rdN_frame fun j hj => fr6 _ (by omega) (Or.inl (by omega)), kw _ (by omega) (Or.inl (by omega)) (by omega)]
          exact m8)
        (by rw [rdN_frame fun j hj => stk7 _ (by omega) (by omega)]; exact p16)
        (by rw [rdN_frame fun j hj => stk7 _ (by omega) (by omega)]; exact p24) (by omega)
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (Or.inr ho.1)
        (fun a h1 h2 => Memory.readable_of_writable (hst7 a (by omega) (by omega)))
        (fun a h1 h2 => hst7 a (by omega) (by omega))
    have lo8 : ∀ a, a < 2147483648 → μ8.read a = μ7.read a := fun a ha => fr8 a (by omega) (Or.inl (by omega))
    -- the stack from sp + 120 on, μ7 to μ
    have k7 : ∀ a, a < 4294967296 → sp + 120 ≤ a → μ7.read a = μ.read a := fun a h0 ha => by
      rw [stk7 a h0 (by omega), fr6 a h0 (Or.inr (by omega)), k4 a h0 (by omega) (Or.inr ha) (Or.inr (by omega))]
    have rr : ∀ o', sp + 120 ≤ o' → o' + 8 ≤ sp + 144 → rdN μ7 o' 8 = rdN μ o' 8 := fun o' h1 h2 =>
      rdN_frame fun j hj => k7 _ (by omega) (by omega)
    -- the allocated data of s2 other than F, μ8 to μ4
    have kd8 : ∀ c ∈ chunks s2, c.used = true → c ≠ F → ∀ a, InDataA c a → μ8.read a = μ4.read a := by
      intro c hc hu hcF a ha
      have := Services.Bootstrap.Decode.VecU8.chunk_in H4.wf hc hu
      have hb4 := H4.hbT
      unfold InDataA at ha
      rw [lo8 a (by omega), (kd7 c hc hu hcF).2 a ha.1 ha.2, lo6 a (by omega)]
    have hNF : (⟨q - 32, (rest.length * 184 + 31) / 32 + 1, true⟩ : Chunk) ≠ F := Ne.symm (hfresh F hF hFu)
    refine Or.inl ⟨q, free s2 ptr, ω8, μ8,
      (((((((r1.trans r2).trans r3).trans r4).trans r5).trans r6).trans r7).trans r8).mono (by omega),
      by rw [z0, rr _ (by omega) (by omega)], by rw [z1], by rw [z5, rr _ (by omega) (by omega)],
      by rw [z6, rr _ (by omega) (by omega)], o0, o8, o16, HeapCtxC.keep_hi H7 lo8 wr8,
      fun c hc hu hcF => ⟨(kd7 c (keep4 c hc hu) hu hcF).1, fun a ha => ?_⟩,
      (kd7 _ hnew rfl hNF).1, hfresh, fun j e hj μ'' hag => reps j e hj μ'' fun c hc hu hcF a ha => ?_,
      fun a h0 ha ho' => ?_⟩
    · have := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hc hu
      rw [kd8 c (keep4 c hc hu) hu hcF a ha, keepd4 c hc hu a ha]
      unfold InDataA at ha
      rw [lo2 a (by omega), lo1 a (by omega)]
    · rw [hag c (kd7 c hc hu hcF).1 hu a ha, kd8 c hc hu hcF a ha]
    · rw [fr8 a h0 ho', k7 a h0 (by omega)]
  · exact Or.inr ⟨j, ω4, μ4, hj, ((((r1.trans r2).trans r3).trans r4).mono (by omega))⟩

end Services.Bootstrap.Acc
