import Services.Bootstrap.Refine.Exit
import Services.Bootstrap.Refine.PassLoop
import Services.Bootstrap.Encode.Loop
import Services.Bootstrap.Decode.LoopA
import Services.Bootstrap.Alloc.ReallocFallbackTail

/-!
# Refine's exit: the output handed to the encoder

After the `Debug` line (6159 … 6209), refine moves its output `Vec<Instruction>` `{cap, ptr, n}` from M + 248
to M + 168, puts the work item's index (the low 16 bits of the word at M + 80) after it at M + 192, opens the
encoder's frame at M − 80 (`BootstrapWorkOutput::encode`, inlined: the output `Vec<u8>` goes to M + 272, the
value at M + 168, the return address 204) and calls `alloc(232 n + 6, 1)` (40494), which returns into the
encoder at 30073 (return address 1414). This is the `encode()` of `Service::refine`'s result, GP v0.8.0
Appendix B.4 (Ψ_R running bootstrap's code).
-/

namespace Services.Bootstrap.Refine.ExitEnc

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Encode.Loop Services.Bootstrap.Encode.Enc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 6209 … 6291: the output moved to M + 168, the work item's index to M + 192, the encoder's frame at
    M − 80 (M + 272, M + 168 and n at M − 80, M − 72, M − 64; return address 204 and ω₅, ω₆ at M − 8,
    M − 16, M − 24), and the call `alloc(232 n + 6, 1)` with return address 1414. Memory changes only in
    [M − 80, M) and [M + 168, M + 194). -/
theorem en1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (M cap ptr n w : Nat)
    (hM : 65536 + 80 ≤ M ∧ M + 304 ≤ 4294967296 ∧ M % 8 = 0) (hcap : cap < 18446744073709551616)
    (hptr : ptr < 18446744073709551616) (hn : 232 * n + 6 < 18446744073709551616)
    (hw64 : w < 18446744073709551616) (h1 : ω[1] = UInt64.ofNat M)
    (s248 : μ.readN (M + 248) 8 = Num.encodeLE 8 cap) (s256 : μ.readN (M + 256) 8 = Num.encodeLE 8 ptr)
    (s264 : μ.readN (M + 264) 8 = Num.encodeLE 8 n) (s80 : μ.readN (M + 80) 8 = Num.encodeLE 8 w)
    (hr : ∀ a, M + 80 ≤ a → a < M + 88 → μ.readable a = true)
    (hr2 : ∀ a, M + 248 ≤ a → a < M + 272 → μ.readable a = true)
    (hw : ∀ a, M - 80 ≤ a → a < M → μ.writable a = true)
    (hw2 : ∀ a, M + 168 ≤ a → a < M + 194 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 6209 ω μ x 40494 ω' μ' x 40 ∧
      ω'[0] = UInt64.ofNat 1414 ∧ ω'[1] = UInt64.ofNat (M - 80) ∧ ω'[5] = UInt64.ofNat (232 * n + 6) ∧
      ω'[6] = UInt64.ofNat (232 * n) ∧ ω'[7] = UInt64.ofNat (232 * n + 6) ∧ ω'[8] = UInt64.ofNat 1 ∧
      μ'.readN (M + 168) 8 = Num.encodeLE 8 cap ∧ μ'.readN (M + 176) 8 = Num.encodeLE 8 ptr ∧
      μ'.readN (M + 184) 8 = Num.encodeLE 8 n ∧ μ'.readN (M + 192) 2 = Num.encodeLE 2 (w % 65536) ∧
      μ'.readN (M - 80) 8 = Num.encodeLE 8 (M + 272) ∧ μ'.readN (M - 80 + 8) 8 = Num.encodeLE 8 (M + 168) ∧
      μ'.readN (M - 80 + 16) 8 = Num.encodeLE 8 n ∧ μ'.readN (M - 80 + 72) 8 = Num.encodeLE 8 204 ∧
      μ'.readN (M - 80 + 64) 8 = Num.encodeLE 8 ω[5].toNat ∧ μ'.readN (M - 80 + 56) 8 = Num.encodeLE 8 ω[6].toNat ∧
      (∀ a, a < 4294967296 → (a < M - 80 ∨ M ≤ a) → (a < M + 168 ∨ M + 194 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hM0, hM1, hM8⟩ := hM
  have rc := rd8 hcap s248
  have rp := rd8 hptr s256
  have rn := rd8 (by omega) s264
  have rw := rd8 hw64 s80
  have hr3 : ∀ a, M - 80 ≤ a → a < M → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hr4 : ∀ a, M + 168 ≤ a → a < M + 194 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw2 a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hM0, hM1, hM8, hr, hr2, hr3, hr4, hw, hw2, rc, rp, rn, rw, Exit.rdN_writeN_enc8,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_,
      fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]
    post_simp

/-- 40611: `alloc`'s return into the encoder (return address 1414, the jump-table entry 30073). -/
theorem alloc_ret {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (h0 : ω[0] = UInt64.ofNat 1414) : FreeStepsH p R 40611 ω μ x 30073 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0]

/-- Encodings of at most 232 octets each add up to at most 232 a slot. -/
theorem off_le_232 (enc : Nat → List UInt8) (n : Nat) (h : ∀ j, j < n → (enc j).length ≤ 232) :
    off enc n ≤ 232 * n := by
  induction n with
  | zero => simp [off]
  | succ n ih =>
    rw [off_succ]
    have := ih (fun j hj => h j (by omega))
    have := h n (by omega)
    omega

/-- **The output encoded** (6209 … 6295): from the allocator's context, with the output `Vec<Instruction>`
    `{cap, E, n}` at M + 248 (0 < n < 128, its n slots inside the used chunk c, each slot j satisfying
    `rep j` and encoding by `EncOk` to `enc j` of at most 232 octets) and the work item's index w at
    M + 80, refine allocates a buffer `buf` of 232 n + 6 octets and encodes into it
    ℰ(`BootstrapWorkOutput`) = ↕ the n encodings ⌢ ℰ₂(w): `{cap', buf, |ℰ| }` at M + 272, the octets
    `n :: out enc n ++ ℰ₂(w mod 2^16)`. Memory changes only below M (the frames), at M + 168 … M + 194 and
    M + 272 … M + 296, in the new buffer and in the allocator's headers: every other used chunk keeps its
    data. Or the allocation fails (`ExhaustsX`). -/
theorem enc_run {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env) (cap0 : Nat)
    (hcap1 : 134217728 ≤ cap0) (hcap0 : cap0 < 18446744073709551616) (x : RefineCtx) (ω : Regs) (μ : Memory)
    {hb : Nat} (s : State) {pb S0 S1 : Nat} (H : HeapCtx env pb S0 S1 μ s) (M cap E n w : Nat) (c : Chunk)
    (enc : Nat → List UInt8) (rep : Nat → List UInt8 → Prop)
    (hM : S0 + 456 ≤ M ∧ M + 648 ≤ S1 ∧ 2147484104 ≤ M ∧ M % 8 = 0) (hn : 0 < n ∧ n < 128)
    (hcap : cap < 18446744073709551616) (hw64 : w < 18446744073709551616)
    (hc : c ∈ chunks s ∧ c.used = true ∧ c.addr + 32 ≤ E ∧ E + 232 * n ≤ c.addr + 32 * c.size)
    (h1 : ω[1] = UInt64.ofNat M)
    (s248 : μ.readN (M + 248) 8 = Num.encodeLE 8 cap) (s256 : μ.readN (M + 256) 8 = Num.encodeLE 8 E)
    (s264 : μ.readN (M + 264) 8 = Num.encodeLE 8 n) (s80 : μ.readN (M + 80) 8 = Num.encodeLE 8 w)
    (hok : ∀ j, j < n → EncOk p P (enc j) (rep j)) (hlen : ∀ j, j < n → (enc j).length ≤ 232)
    (hrep : ∀ j, j < n → rep j (μ.readN (E + 232 * j) 232))
    (tab : μ.readN 67376 100 = table) (rtab : ∀ a, 67376 ≤ a → a < 67476 → μ.readable a = true) :
    (∃ s' ω' μ' cap' buf, FreeStepsH p (refineContractK cap0 env) 6209 ω μ x 6295 ω' μ' x
        (4100 * n + 7 * off enc n + 2000) ∧ HeapCtx env pb S0 S1 μ' s' ∧
      ω'[1] = UInt64.ofNat M ∧
      μ'.readN (M + 272) 8 = Num.encodeLE 8 cap' ∧ μ'.readN (M + 280) 8 = Num.encodeLE 8 buf ∧
      μ'.readN (M + 288) 8 = Num.encodeLE 8 (off enc n + 3) ∧
      μ'.readN buf (off enc n + 3) = UInt8.ofNat n :: (out enc n ++ Num.encodeLE 2 (w % 65536)) ∧
      cap' = 232 * n + 6 ∧ (⟨buf - 32, (232 * n + 6 + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ a, a < 4294967296 → M ≤ a → (a < M + 168 ∨ M + 194 ≤ a) → (a < M + 272 ∨ M + 296 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ d ∈ chunks s, d.used = true → d ∈ chunks s' ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ ⟨buf - 32, (232 * n + 6 + 31) / 32 + 1, true⟩) ∧
      μ'.readN (M + 168) 8 = Num.encodeLE 8 cap ∧ μ'.readN (M + 176) 8 = Num.encodeLE 8 E ∧
      μ'.readN (M + 184) 8 = Num.encodeLE 8 n) ∨
    PassLoop.ExhaustsX env cap0 pb p 6209 ω μ x (4100 * n + 7 * off enc n + 2000) := by
  obtain ⟨hS0M, hMS1, hM2, hM8⟩ := hM
  obtain ⟨hcs, hcu, hcE0, hcE1⟩ := hc
  have hS1 := H.hS1
  have hbT := H.hbT
  have hb0 := H.hb0
  obtain ⟨hc0, -, hcT⟩ := Decode.VecU8.chunk_in H.wf hcs hcu
  have hoff := off_le_232 enc n hlen
  have wst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a168, a176, a184, a192, a80, a72, a64, a8', a16, a24, afr, ard,
      awr⟩ := en1 (p := p) (P := P) (R := refineContractK cap0 env) x ω μ M cap E n w ⟨by omega, by omega, hM8⟩
    hcap (by omega) (by omega) hw64 h1 s248 s256 s264 s80
    (fun a h1 h2 => Memory.readable_of_writable (wst a (by omega) (by omega)))
    (fun a h1 h2 => Memory.readable_of_writable (wst a (by omega) (by omega)))
    (fun a h1 h2 => wst a (by omega) (by omega)) (fun a h1 h2 => wst a (by omega) (by omega))
  have H1 : HeapCtx env pb S0 S1 μ1 s :=
    Decode.GrowOne.ctx_high H (fun a ha => afr a (by omega) (by omega) (by omega)) awr
  rcases alloc_call (p := p) (P := P) (hb := hb) env cap0 hcap1 hcap0 x ω1 μ1 s (M - 80) (232 * n + 6) 1 pb S0 S1
      H1 a1 a7 a8 (by decide) (by decide) (by omega) (by omega) ⟨by omega, by omega⟩ with
    ⟨buf, s2, ω2, μ2, ha, run2, H2, keep2, hnew, fresh2, hk2, b7, stk2, b0, b1, b5, b6⟩ | ⟨hna, ω2, μ2, run2, b7, -⟩
  rotate_left
  · exact Or.inr ⟨ω2, μ2, x, 40611, (run1.trans run2).mono (by omega), b7,
      Or.inl ⟨rfl, s, hb, (232 * n + 6 + 31) / 32, hna⟩⟩
  -- `alloc`'s return into the encoder
  have run3 := alloc_ret (p := p) (P := P) (R := refineContractK cap0 env) x ω2 μ2 (b0.trans a0)
  obtain ⟨hq0, -, hqT⟩ := Decode.VecU8.chunk_in H2.wf hnew rfl
  simp only at hq0 hqT
  have hb0' := H2.hb0
  have hbT' := H2.hbT
  have hcs2 := keep2 c hcs hcu
  have hcne := fresh2 c hcs hcu
  have hap := PassLoop.chunk_apart H2.wf hcs2 hnew hcne
  simp only at hap
  have hsz : 232 * n + 6 + 32 ≤ 32 * ((232 * n + 6 + 31) / 32 + 1) := by omega
  -- what the runs so far keep
  obtain ⟨kp, kr⟩ := FreeStepsH.keepRO H.bd (run1.trans run2)
  have dat : ∀ d ∈ chunks s, d.used = true → ∀ a, InData d a → μ2.read a = μ.read a := fun d hd hu a ha => by
    obtain ⟨hd0, -, hdT⟩ := Decode.VecU8.chunk_in H.wf hd hu
    have hd2 := keep2 d hd hu
    unfold InData at ha
    rw [hk2.hkeep a (Alloc.off_hdr_data H2.wf H2.hb0 H2.hbT hd2 ha.1 ha.2),
      afr a (by omega) (by omega) (by omega)]
  have stk : ∀ a, a < 4294967296 → M - 80 ≤ a → μ2.read a = μ1.read a := fun a h0 h1 => stk2 a h0 h1
  have L : LayL P p (M - 80) E n buf (232 * n + 6) enc rep μ2 :=
    { hM := ⟨by omega, by omega, by omega⟩
      hE := ⟨by omega, by omega⟩
      hEM := Or.inl (by omega)
      hbuf := ⟨by omega, by omega⟩
      hbM := Or.inl (by omega)
      hbE := by rcases hap with h | h
                · exact Or.inr (by omega)
                · exact Or.inl (by omega)
      hcap := ⟨by omega, by omega⟩
      ok := hok
      rep0 := fun j hj => by
        rw [Memory.readN_congr (fun i hi => dat c hcs hcu _ ⟨by omega, by omega⟩)]; exact hrep j hj
      tab := by
        rw [Memory.readN_congr (fun i hi => kr _ (by unfold two32; omega) (Or.inl (by unfold pageSize; omega))
          (H.ro _ (by omega)))]; exact tab
      rtab := fun a h1 h2 => by
        unfold Memory.readable; rw [kp _ (Or.inl (by unfold pageSize; omega))]; exact rtab a h1 h2
      rE := fun a h1 h2 => Memory.readable_of_writable
        (Decode.VecU8.heap_writable H2 hcs2 hcu ⟨by omega, by omega⟩)
      rM := fun a h1 h2 => Memory.readable_of_writable (H2.st a (by omega) (by omega))
      wM := fun a h1 h2 => H2.st a (by omega) (by omega)
      wbuf := fun a h1 h2 => Decode.VecU8.heap_writable H2 hnew rfl ⟨by simp; omega, by simp; omega⟩ }
  obtain ⟨ω4, μ4, run4, d0, d1, d5, d6, dO, dO8, dO16, dbuf, dfr, drd, dwr⟩ := encode_ok (p := p) (P := P)
    (R := refineContractK cap0 env) x ω2 μ2 L (M + 272) 204 6295 ω[5].toNat ω[6].toNat hn
    (by rw [b1, a1]) (by rw [b5, a5]) (by rw [b6, a6]) b7
    (by rw [Memory.readN_congr (fun i hi => stk _ (by omega) (by omega))]; exact a80)
    (by rw [Memory.readN_congr (fun i hi => stk _ (by omega) (by omega))]; exact a72)
    (by rw [Memory.readN_congr (fun i hi => stk _ (by omega) (by omega))]; exact a64)
    (by rw [show M + 168 + 8 = M + 176 by omega,
      Memory.readN_congr (fun i hi => stk _ (by omega) (by omega))]; exact a176)
    (by rw [Memory.readN_congr (fun i hi => stk _ (by omega) (by omega))]; exact a8')
    (by rw [Memory.readN_congr (fun i hi => stk _ (by omega) (by omega))]; exact a16)
    (by rw [Memory.readN_congr (fun i hi => stk _ (by omega) (by omega))]; exact a24)
    (UInt64.toNat_lt _) (UInt64.toNat_lt _) ⟨by decide, by decide, by decide⟩ jte_101 bs_6295
    (Or.inr (by omega)) (by omega) (Or.inr (by omega))
    (fun a h1 h2 => Memory.readable_of_writable (H2.st a (by omega) (by omega))) (by omega) (Or.inr (by omega))
    (Or.inr (by omega)) (fun a h1 h2 => H2.st a (by omega) (by omega))
  have H4 : HeapCtx env pb S0 S1 μ4 s2 := Decode.VecU8.ctx_congr_data H2 hnew
    (fun a ha h => dfr a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (by simp at h; omega)) dwr
  refine Or.inl ⟨s2, ω4, μ4, 232 * n + 6, buf,
    ((run1.trans run2).trans (run3.trans run4)).mono (by omega), H4, by rw [d1]; congr 1; omega, dO, dO8, dO16,
    ?_, rfl, hnew, fun a h0 h1 h2 h3 => ?_, fun d hd hu => ⟨keep2 d hd hu, fun a ha => ?_⟩, fresh2, ?_, ?_, ?_⟩
  · rw [dbuf, show M + 168 + 24 = M + 192 by omega,
      Memory.readN_congr (fun i hi => stk _ (by omega) (by omega)), a192]
  · rw [dfr a h0 (Or.inr (by omega)) (by omega) (Or.inr (by omega)), stk a h0 (by omega),
      afr a h0 (Or.inr h1) h2]
  · obtain ⟨hd0, -, hdT⟩ := Decode.VecU8.chunk_in H.wf hd hu
    have hdj := Decode.VecU8.data_disj H2.wf (keep2 d hd hu) hnew (fresh2 d hd hu) ha
    simp only at hdj
    unfold InData at ha
    rw [dfr a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (by omega), dat d hd hu a ⟨ha.1, ha.2⟩]
  · rw [show μ4.readN (M + 168) 8 = μ1.readN (M + 168) 8 from Memory.readN_congr (fun i hi => by
      rw [dfr _ (by omega) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inr (by omega)), stk _ (by omega) (by omega)])]
    exact a168
  · rw [show μ4.readN (M + 176) 8 = μ1.readN (M + 176) 8 from Memory.readN_congr (fun i hi => by
      rw [dfr _ (by omega) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inr (by omega)), stk _ (by omega) (by omega)])]
    exact a176
  · rw [show μ4.readN (M + 184) 8 = μ1.readN (M + 184) 8 from Memory.readN_congr (fun i hi => by
      rw [dfr _ (by omega) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inr (by omega)), stk _ (by omega) (by omega)])]
    exact a184

end Services.Bootstrap.Refine.ExitEnc
