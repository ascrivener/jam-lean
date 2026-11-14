import Services.Bootstrap.Refine.PassLoop
import Services.Bootstrap.Refine.ExitEnc
import Services.Bootstrap.Refine.Fin

/-!
# Refine's exit, whole: from the transform loop's end to refine's return

From the loop's state at 5042 after all n ≥ 1 instructions (`PInv n`), refine:
- leaves the loop (`Exit.ex0`);
- drops the input's `IntoIter` (`Exit.drop`);
- writes the `Debug` line of its output (6130 … 6209, `Exit.ex1` and then `DebugLineOk`, a hypothesis
  "discharged by the fmt summaries");
- encodes its output (`ExitEnc.enc_run`);
- drops it and returns (`Fin.fin_run`).
Each output slot satisfies `O`, from which the encoder's `rep`, the `Debug` line's `DR` and a variant whose
drop does nothing (`DropOut.NoDrop`) follow. GP v0.8.0 Appendix B.4 (Ψ_R running bootstrap's code).
-/

namespace Services.Bootstrap.Refine.ExitRun

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Encode.Loop Services.Bootstrap.Encode.Enc Services.Bootstrap.Refine.PassLoop

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **The `Debug` line of the output** (59375 … 6209), as a hypothesis: `format!("Returning {:?} into
    accumulate", out)` (template 66099, the output `Vec<Instruction>` at M + 248 with its `Debug` function
    1382), the `log` (6187) and the `String`'s `dealloc` (6202), from refine's frame at M with the allocator's
    context: the run reaches 6209 with the host context and ω₁ kept, the allocator's context for some heap s',
    every allocated chunk of s still allocated with its data, and the stack from M up kept apart from the
    `String` at M + 168 … M + 192; or an allocation fails. `DR j bs μ` is what the `Debug` arms need of slot j; the n
    slots at E lie in an allocated chunk. To be discharged by the fmt
    summaries (`Services/Bootstrap/Fmt`). -/
def DebugLineOk (p : ByteArray) (cap0 : Nat) (env : RefineHost.Env) (pb S0 S1 : Nat)
    (DR : Nat → List UInt8 → Memory → Prop) : Prop :=
  ∀ (x : RefineCtx) (ω : Regs) (μ : Memory) (s : State) (M c E n : Nat),
    HeapCtx env pb S0 S1 μ s → S0 + 456 ≤ M → M + 632 ≤ S1 → M % 8 = 0 →
    ω[0] = UInt64.ofNat 200 → ω[1] = UInt64.ofNat M → ω[7] = UInt64.ofNat (M + 168) →
    ω[8] = UInt64.ofNat 66099 → ω[9] = UInt64.ofNat (M + 272) →
    μ.readN (M + 272) 8 = Num.encodeLE 8 (M + 248) → μ.readN (M + 280) 8 = Num.encodeLE 8 1382 →
    μ.readN (M + 248) 8 = Num.encodeLE 8 c → μ.readN (M + 256) 8 = Num.encodeLE 8 E →
    μ.readN (M + 264) 8 = Num.encodeLE 8 n → (∀ j, j < n → DR j (μ.readN (E + 232 * j) 232) μ) →
    (n = 0 ∨ ∃ c ∈ chunks s, c.used = true ∧ ∀ k, k < 232 * n → InData c (E + k)) →
    (∃ (ω' : Regs) (μ' : Memory) (s' : State) (N : Nat),
      FreeStepsH p (refineContractK cap0 env) 59375 ω μ x 6209 ω' μ' x N ∧ HeapCtx env pb S0 S1 μ' s' ∧
      ω'[1] = ω[1] ∧ (∀ a, a < 4294967296 → M ≤ a → (a < M + 168 ∨ M + 192 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ d ∈ chunks s, d.used = true → d ∈ chunks s' ∧ ∀ a, InData d a → μ'.read a = μ.read a)) ∨
    ∃ N, ExhaustsX env cap0 pb p 59375 ω μ x N

/-- A refine run keeps the read-only data (below 65536 + 𝖹 …, pages under 48), values and access. -/
theorem ro_keep {p : ByteArray} {cap0 : Nat} {env : RefineHost.Env} {pb S0 S1 : Nat} {μ μ' : Memory} {s : State}
    {i i' n : Nat} {ω ω' : Regs} {x x' : RefineCtx} (H : HeapCtx env pb S0 S1 μ s)
    (run : FreeStepsH p (refineContractK cap0 env) i ω μ x i' ω' μ' x' n) {a l : Nat} (hal : a + l ≤ 196608) :
    μ'.readN a l = μ.readN a l ∧ ∀ b, a ≤ b → b < a + l → μ'.readable b = μ.readable b := by
  obtain ⟨kp, kr⟩ := FreeStepsH.keepRO H.bd run
  refine ⟨Memory.readN_congr (fun j hj => kr _ (by unfold two32; omega) (Or.inl (by unfold pageSize; omega))
    (H.ro _ (by omega))), fun b h1 h2 => ?_⟩
  unfold Memory.readable; rw [kp _ (Or.inl (by unfold pageSize; omega))]

/-- **Refine's exit** (5042 … t): from the loop's state after all n instructions (`PInv n`, 1 ≤ n < 128),
    where each output slot j satisfies `O j` (so `rep j` for the encoder, `DR j` for the `Debug` line and a
    variant whose drop does nothing), refine returns to the return address `ret` saved at M + 624 (→ t) with
    ω₇ = buf and ω₈ = len, where the len octets at buf are
    ℰ(`BootstrapWorkOutput`) = n :: (the n encodings) ⌢ ℰ₂(w mod 2^16), w the work item's index word at
    M + 80; the host context x is kept and the allocator's context holds. Or an allocation fails. The payload's `Vec<u8>` at
    M + 88 / M + 112 (capacity c', buffer cq, kept by the loop) is freed on the way. -/
theorem exit_run {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env) (cap0 : Nat)
    (hcap1 : 134217728 ≤ cap0) (hcap0 : cap0 < 18446744073709551616) {hb : Nat}
    {pb S0 S1 M E n capI : Nat} {ce : Chunk} {μ0 : Memory} {Kp : Chunk → Prop} {O : Nat → List UInt8 → Prop}
    (DR : Nat → List UInt8 → Memory → Prop) (enc : Nat → List UInt8) (rep : Nat → List UInt8 → Prop)
    (dbg : DebugLineOk p cap0 env pb S0 S1 DR)
    (x : RefineCtx) (ω : Regs) (μ : Memory) (s : State) (L : LayP S0 S1 M E n ce) (hn : 0 < n)
    (st : PInv env pb S0 S1 M E n ce capI μ0 Kp O 5042 n ω μ s) (hcapI : 232 * capI < 18446744073709551616)
    (hOD : ∀ j bs μ, j < n → O j bs → DR j bs μ) (hOR : ∀ j bs, j < n → O j bs → rep j bs)
    (hON : ∀ j bs, j < n → O j bs → ∃ t, DropOut.NoDrop t ∧ bs.take 8 = Num.encodeLE 8 (9223372036854775807 + t))
    (hok : ∀ j, j < n → EncOk p P (enc j) (rep j)) (hlen : ∀ j, j < n → (enc j).length ≤ 232)
    (w c' q ret r5 r6 t : Nat) (cq : Chunk) (hw64 : w < 18446744073709551616)
    (s80 : μ0.readN (M + 80) 8 = Num.encodeLE 8 w)
    (s88 : μ0.readN (M + 88) 8 = Num.encodeLE 8 c') (s112 : μ0.readN (M + 112) 8 = Num.encodeLE 8 q)
    (s624 : μ0.readN (M + 624) 8 = Num.encodeLE 8 ret) (s616 : μ0.readN (M + 616) 8 = Num.encodeLE 8 r5)
    (s608 : μ0.readN (M + 608) 8 = Num.encodeLE 8 r6)
    (hq' : c' < 18446744073709551616) (hcq : c' ≠ 0 → Kp cq ∧ cq.addr + 32 = q ∧ cq ≠ ce)
    (hret : Fin.RetTo P ret t) (hr5 : r5 < 18446744073709551616)
    (hr6 : r6 < 18446744073709551616)
    (tab : μ.readN 67376 100 = table) (rtab : ∀ a, 67376 ≤ a → a < 67476 → μ.readable a = true)
    (dtab : μ.readN 67760 96 = DropOut.dtable) (rdtab : ∀ a, 67760 ≤ a → a < 67856 → μ.readable a = true) :
    (∃ (ω' : Regs) (μ' : Memory) (s' : State) (N buf : Nat),
      FreeStepsH p (refineContractK cap0 env) 5042 ω μ x t ω' μ' x N ∧ HeapCtx env pb S0 S1 μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (M + 632) ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 ∧ ω'[7] = UInt64.ofNat buf ∧ ω'[8] = UInt64.ofNat (off enc n + 3) ∧
      μ'.readN buf (off enc n + 3) = UInt8.ofNat n :: (out enc n ++ Num.encodeLE 2 (w % 65536)) ∧
      (∀ a, buf ≤ a → a < buf + (off enc n + 3) → μ'.readable a = true)) ∨
    ∃ N, ExhaustsX env cap0 pb p 5042 ω μ x N := by
  obtain ⟨hS0M, hMS1, hM2, hM8⟩ := L.hM
  have hn' := L.hn
  obtain ⟨hE0, hE1⟩ := L.hE
  have hEtop := L.hEtop
  have hS1 := st.H.hS1
  have hbT := st.H.hbT
  have hb0 := st.H.hb0
  obtain ⟨cap, ptr, vc, vp, vl, hkc, hcapn, hptr, hold, hout⟩ := st.out
  obtain ⟨co, hco, hcoa, hcou, hcos, hcoe, hcok⟩ := hold.resolve_left (fun h => by omega)
  obtain ⟨hco0, -, hcoT⟩ := Decode.VecU8.chunk_in st.H.wf hco hcou
  obtain ⟨hce0, -, hceT⟩ := Decode.VecU8.chunk_in st.H.wf st.hce.1 st.hce.2
  have hcs : 232 * cap + 32 ≤ 32 * co.size := by rw [hcos]; omega
  -- 1. the loop's end
  obtain ⟨ω1, run1, a1, -, -⟩ := Exit.ex0 (p := p) (P := P) (R := refineContractK cap0 env) x ω μ M (E + 232 * n)
    (by omega) (by omega) st.h1 st.cur42 st.en
    (fun a h1 h2 => Memory.readable_of_writable (st.H.st a (by omega) (by omega)))
  -- 2. the input's `IntoIter` dropped
  obtain ⟨ω2, μ2, s2, run2, H2, -, -, b1, -, -, bfr, bkeep⟩ := Exit.drop (p := p) (P := P)
    (R := refineContractK cap0 env) env x ω1 μ s M (ce.addr + 32) (E + 232 * n) capI ce st.H
    ⟨by omega, by omega, by omega, hM8⟩ (by omega) (by omega) hcapI (fun _ => ⟨st.hce.1, st.hce.2, rfl⟩)
    (a1.trans st.h1) st.i0 st.i8 st.i16 st.i24
  have co2 := bkeep co hco hcou (fun _ => hcoe)
  -- 3. the `Debug` line's setup
  obtain ⟨ω3, μ3, run3, c0, c1, -, -, c7, c8, c9, c272, c280, cfr, crd, cwr⟩ := Exit.ex1 (p := p) (P := P)
    (R := refineContractK cap0 env) x ω2 μ2 M ⟨by omega, by omega, hM8⟩ b1
    (fun a h1 h2 => H2.st a (by omega) (by omega))
  have H3 : HeapCtx env pb S0 S1 μ3 s2 := Decode.GrowOne.ctx_high H2 (fun a ha => cfr a (by omega) (by omega)) cwr
  -- reads from M up, through the first three pieces
  have k3 : ∀ a, a < 4294967296 → M ≤ a → (a < M + 272 ∨ M + 288 ≤ a) → μ3.read a = μ.read a :=
    fun a h0 h1 h2 => by rw [cfr a h0 h2, bfr a h0 h1]
  -- the output's slots, through the first three pieces
  have sl3 : ∀ a, InData co a → μ3.read a = μ.read a := fun a ha => by
    unfold InData at ha
    rw [cfr a (by omega) (by omega), co2.2 a ha]
  have pre3 := run1.trans (run2.trans run3)
  -- 4. the `Debug` line
  rcases dbg x ω3 μ3 s2 M cap ptr n H3 (by omega) (by omega) hM8 c0 c1 c7 c8 c9 c272 c280
      (by rw [Memory.readN_congr (fun j hj => k3 _ (by omega) (by omega) (by omega))]; exact vc)
      (by rw [Memory.readN_congr (fun j hj => k3 _ (by omega) (by omega) (by omega))]; exact vp)
      (by rw [Memory.readN_congr (fun j hj => k3 _ (by omega) (by omega) (by omega))]; exact vl)
      (fun j hj => hOD j _ μ3 hj (by
        rw [Memory.readN_congr (fun i hi => sl3 _ ⟨by omega, by omega⟩)]; exact hout j hj))
      (Or.inr ⟨co, co2.1, hcou, fun k hk => ⟨by omega, by omega⟩⟩) with
    ⟨ω4, μ4, s4, N4, run4, H4, d1, dfr, dkeep⟩ | ⟨N4, hx⟩
  rotate_left
  · exact Or.inr ⟨_, ExhaustsX.pre pre3 hx⟩
  have co4 := dkeep co co2.1 hcou
  have k4 : ∀ a, a < 4294967296 → M ≤ a → (a < M + 168 ∨ M + 192 ≤ a) → (a < M + 272 ∨ M + 288 ≤ a) →
      μ4.read a = μ.read a := fun a h0 h1 h2 h3 => by rw [dfr a h0 h1 h2, k3 a h0 h1 h3]
  have sl4 : ∀ a, InData co a → μ4.read a = μ.read a := fun a ha => by rw [co4.2 a ha, sl3 a ha]
  have pre4 := pre3.trans run4
  -- the read-only tables, kept
  obtain ⟨tab4, rtab4⟩ := ro_keep st.H pre4 (a := 67376) (l := 100) (by omega)
  -- 5. the output encoded
  rcases ExitEnc.enc_run (p := p) (P := P) (hb := hb) env cap0 hcap1 hcap0 x ω4 μ4 s4 H4 M cap ptr n w co enc rep
      ⟨by omega, by omega, by omega, hM8⟩ ⟨hn, hn'⟩ (by omega) hw64
      ⟨co4.1, hcou, by omega, by omega⟩ (d1.trans c1)
      (by rw [Memory.readN_congr (fun j hj => k4 _ (by omega) (by omega) (by omega) (by omega))]; exact vc)
      (by rw [Memory.readN_congr (fun j hj => k4 _ (by omega) (by omega) (by omega) (by omega))]; exact vp)
      (by rw [Memory.readN_congr (fun j hj => k4 _ (by omega) (by omega) (by omega) (by omega))]; exact vl)
      (by rw [show μ4.readN (M + 80) 8 = μ0.readN (M + 80) 8 from Memory.readN_congr (fun j hj => by
        rw [k4 _ (by omega) (by omega) (by omega) (by omega), st.fr _ (by omega)])]; exact s80)
      hok hlen
      (fun j hj => hOR j _ hj (by rw [Memory.readN_congr (fun i hi => sl4 _ ⟨by omega, by omega⟩)]; exact hout j hj))
      (by rw [tab4]; exact tab) (fun a h1 h2 => by rw [rtab4 a h1 h2]; exact rtab a h1 h2) with
    ⟨s5, ω5, μ5, cap5, buf, run5, H5, e1, e272, e280, e288, ebuf, -, hnew, efr, ekeep, efresh, e168, e176, e184⟩ | hx
  rotate_left
  · exact Or.inr ⟨_, ExhaustsX.pre pre4 hx⟩
  have co5 := ekeep co co4.1 hcou
  have k5 : ∀ a, a < 4294967296 → M ≤ a → (a < M + 168 ∨ M + 194 ≤ a) → (a < M + 272 ∨ M + 296 ≤ a) →
      μ5.read a = μ.read a := fun a h0 h1 h2 h3 => by
    rw [efr a h0 h1 h2 h3, k4 a h0 h1 (by omega) (by omega)]
  have f5 : ∀ a l, (M + 80 ≤ a ∧ a + l ≤ M + 96) ∨ (M + 112 ≤ a ∧ a + l ≤ M + 120) ∨
      (M + 608 ≤ a ∧ a + l ≤ M + 632) →
      μ5.readN a l = μ0.readN a l := fun a l h => Memory.readN_congr (fun j hj => by
    rw [k5 _ (by omega) (by omega) (by omega) (by omega), st.fr _ (by omega)])
  have pre5 := pre4.trans run5
  have hoff := ExitEnc.off_le_232 enc n hlen
  have hbT5 := H5.hbT
  have hb05 := H5.hb0
  obtain ⟨dtab5, rdtab5⟩ := ro_keep st.H pre5 (a := 67760) (l := 96) (by omega)
  obtain ⟨hq0, -, hqT⟩ := Decode.VecU8.chunk_in H5.wf hnew rfl
  simp only at hq0 hqT
  -- 6. the epilogue
  obtain ⟨ω6, μ6, s6, run6, H6, f0, f1, f5', f6, f7, f8, ffr, fkeep⟩ := Fin.fin_run (p := p) (P := P)
    (R := refineContractK cap0 env) env x ω5 μ5 s5 H5 M cap ptr n c' q buf (off enc n + 3) ret r5 r6 t co cq
    ⟨by omega, by omega, by omega, hM8⟩ hn hkc ⟨co5.1, hcou, by omega, by omega⟩ (by omega)
    (fun h => by
      obtain ⟨hK, hqa, hqce⟩ := hcq h
      obtain ⟨hq, hqu, -⟩ := st.kp cq hK
      have q2 := bkeep cq hq hqu (fun _ => hqce)
      have q4 := dkeep cq q2.1 hqu
      exact ⟨(ekeep cq q4.1 hqu).1, hqu, hqa, fun e => hcok (e ▸ hK)⟩)
    hq' (by omega) (by omega) e1
    e168 e176 e184 (by rw [f5 _ _ (by omega)]; exact s88) (by rw [f5 _ _ (by omega)]; exact s112) e280 e288
    (by rw [f5 _ _ (by omega)]; exact s624) (by rw [f5 _ _ (by omega)]; exact s616)
    (by rw [f5 _ _ (by omega)]; exact s608) hret hr5 hr6
    (fun j hj => by
      obtain ⟨tj, htj, hD⟩ := hON j _ hj (hout j hj)
      refine ⟨tj, htj, ?_⟩
      have e := Decode.Loop.readN_sub μ (ptr + 232 * j) 232 0 8 _ rfl (by omega)
      simp only [Nat.add_zero, List.drop_zero] at e
      rw [show μ5.readN (ptr + 232 * j) 8 = μ.readN (ptr + 232 * j) 8 from Memory.readN_congr (fun i hi => by
        rw [co5.2 _ ⟨by omega, by omega⟩, sl4 _ ⟨by omega, by omega⟩]), e, hD])
    (by rw [dtab5]; exact dtab) (fun a h1 h2 => by rw [rdtab5 a h1 h2]; exact rdtab a h1 h2)
  -- the encoded output, kept by the epilogue
  have hnco : (⟨buf - 32, (232 * n + 6 + 31) / 32 + 1, true⟩ : Chunk) ≠ co := fun e => efresh co co4.1 hcou e.symm
  have hncq : c' ≠ 0 → (⟨buf - 32, (232 * n + 6 + 31) / 32 + 1, true⟩ : Chunk) ≠ cq := fun h e => by
    obtain ⟨hK, -, hqce⟩ := hcq h
    obtain ⟨hq, hqu, -⟩ := st.kp cq hK
    have q2 := bkeep cq hq hqu (fun _ => hqce)
    exact efresh cq (dkeep cq q2.1 hqu).1 hqu e.symm
  obtain ⟨nm, nk⟩ := fkeep _ hnew rfl hnco hncq
  refine Or.inl ⟨ω6, μ6, s6, _, buf, pre5.trans run6, H6, f0, f1, f5', f6, f7, f8, ?_, fun a h1 h2 =>
    Memory.readable_of_writable (Decode.VecU8.heap_writable H6 nm rfl ⟨by simp; omega, by simp; omega⟩)⟩
  rw [Memory.readN_congr (fun i hi => nk _ ⟨by simp; omega, by simp; omega⟩)]
  exact ebuf

end Services.Bootstrap.Refine.ExitRun
