import Services.Bootstrap.Refine.Entry
import Services.Bootstrap.Refine.ExitRun

/-!
# Refine's body, from the decoded instructions to its return

`body` composes `Entry.entry` (4842 … 5054), `LoopAll.loop_all` (the transform loop) and `ExitRun.exit_run`
(the loop's end … refine's return): from the decode's `Vec<Instruction>` at M + 168, each instruction passed
through or exported, refine returns ℰ(`BootstrapWorkOutput`) with the host context the instructions' exports
in order, or an allocation fails. The instructions' facts are stated on the memory at 4842; `PassOk.congr`
and `ExportOk.congr` carry them to any memory agreeing below 2³¹ (the heap). GP v0.8.0 Appendix B.4 (Ψ_R
running bootstrap's code); `Spec.refine`.
-/

namespace Services.Bootstrap.Refine.Body

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeR
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA Services.Bootstrap.Refine.Pass
  Services.Bootstrap.Refine.PassLoop Services.Bootstrap.Refine.LoopAll Services.Bootstrap.Encode.Writer
  Services.Bootstrap.Encode.Loop Services.Bootstrap.Encode.Enc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem PassOk.congr {μ μ' : Memory} {E k : Nat} {Kp Kp' : Chunk → Prop} {O : Nat → List UInt8 → Prop}
    {x x' : RefineCtx} (hk : E + 232 * k + 232 ≤ 2147483648) (h : ∀ a, a < 2147483648 → μ'.read a = μ.read a)
    (ok : PassOk μ E k Kp Kp' O x x') : PassOk μ' E k Kp Kp' O x x' := by
  obtain ⟨t, ht, sD, hO, hK, hx⟩ := ok
  have r : ∀ a l, a + l ≤ 2147483648 → μ'.readN a l = μ.readN a l :=
    fun a l hl => Memory.readN_congr (fun j hj => h _ (by omega))
  refine ⟨t, ?_, by rw [r _ _ (by omega)]; exact sD, by rw [r _ _ (by omega)]; exact hO, hK, hx⟩
  unfold rdN; rw [r _ _ (by omega)]; exact ht

theorem ExportOk.congr {env : RefineHost.Env} {μ μ' : Memory} {E k : Nat} {ce : Chunk} {Kp Kp' : Chunk → Prop}
    {O : Nat → List UInt8 → Prop} {x x' : RefineCtx} (hk : E + 232 * k + 232 ≤ 2147483648)
    (h : ∀ a, a < 2147483648 → μ'.read a = μ.read a)
    (ok : ExportOk env μ E k ce Kp Kp' O x x') : ExportOk env μ' E k ce Kp Kp' O x x' := by
  obtain ⟨capv, ptrv, ns, co, capf, qf, lf, sD0, sv8, sv16, sv24, hcv, hnc, hp, hco, hcoD, hw0, hcap, hql, hq,
    hcs, hsd, hoff, hK', hO, hx⟩ := ok
  have r : ∀ a l, a + l ≤ 2147483648 → μ'.readN a l = μ.readN a l :=
    fun a l hl => Memory.readN_congr (fun j hj => h _ (by omega))
  have rq : ∀ j, j < ns → rdN μ (ptrv + 24 * j + 8) 8 = qf j ∧ rdN μ (ptrv + 24 * j + 16) 8 = lf j :=
    fun j hj => ⟨rd8 (by have := hql j hj; omega) (hw0 j hj).2.1, rd8 (by have := hql j hj; omega) (hw0 j hj).2.2⟩
  refine ⟨capv, ptrv, ns, co, capf, qf, lf, by rw [r _ _ (by omega)]; exact sD0, by rw [r _ _ (by omega)]; exact sv8,
    by rw [r _ _ (by omega)]; exact sv16, by rw [r _ _ (by omega)]; exact sv24, hcv, hnc, hp, hco, hcoD,
    fun i hi => ⟨by rw [r _ _ (by omega)]; exact (hw0 i hi).1, by rw [r _ _ (by omega)]; exact (hw0 i hi).2.1,
      by rw [r _ _ (by omega)]; exact (hw0 i hi).2.2⟩, hcap, hql, hq, hcs, hsd, hoff, hK', hO, ?_⟩
  rw [hx, ExportElem.expUpTo_congr ns (fun a ha => h a (by
    rcases ha with ⟨-, h2⟩ | ⟨j, hj, -, h2⟩
    · omega
    · rw [(rq j hj).1, (rq j hj).2] at h2; have := hql j hj; omega))]

/-- **Refine's body** (4842 … t): from the decode's `Vec<Instruction>` `{cap, E, n}` at M + 168 (1 ≤ n < 128,
    E = ce.addr + 32 in the allocated chunk ce) and the allocator's context, with each instruction k passed
    through (`PassOk`) or exported (`ExportOk`), the chunks to keep `Kp k` and the host context `ctx k` per
    instruction, and each output slot satisfying `O` (whence `rep` for the encoder, `DR` for the `Debug` line
    and a variant whose drop does nothing), refine returns to `ret` (→ t) with ω₇ = buf and ω₈ the length of
    ℰ(`BootstrapWorkOutput`) = n :: (the encodings) ⌢ ℰ₂(w mod 2^16) at buf, the host context `ctx n`. Or an
    allocation fails. Hypotheses: `ExportFmtOk` and `DebugLineOk` (the fmt summaries). -/
theorem body {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P]
    (env : RefineHost.Env) (cap0 : Nat) (hcap1 : 134217728 ≤ cap0) (hcap0 : cap0 < 18446744073709551616)
    {hb : Nat} {pb S0 S1 : Nat} (fmt : ExportSeg.ExportFmtOk p cap0 env pb S0 S1)
    (DR : Nat → List UInt8 → Memory → Prop) (enc : Nat → List UInt8) (rep : Nat → List UInt8 → Prop)
    (dbg : ExitRun.DebugLineOk p cap0 env pb S0 S1 DR)
    (ω : Regs) (μ : Memory) (s : State) (H : HeapCtx env pb S0 S1 μ s) (M cap n : Nat) (ce : Chunk)
    (Kp : Nat → Chunk → Prop) (O : Nat → List UInt8 → Prop) (ctx : Nat → RefineCtx)
    (hM : S0 + 456 ≤ M ∧ M + 648 ≤ S1 ∧ 2147484104 ≤ M ∧ M % 8 = 0) (hn : 0 < n) (hn128 : n < 128)
    (hcap : 232 * cap < 18446744073709551616) (hce : cap ≠ 18446744073709551615)
    (hceC : ce ∈ chunks s ∧ ce.used = true) (hE : ce.addr + 32 + 232 * n ≤ ce.addr + 32 * ce.size)
    (hEtop : ce.addr + 32 + 232 * n < 2147483648)
    (hkp : ∀ d, Kp 0 d → d ∈ chunks s ∧ d.used = true) (h1 : ω[1] = UInt64.ofNat M)
    (s168 : μ.readN (M + 168) 8 = Num.encodeLE 8 cap) (s176 : μ.readN (M + 176) 8 = Num.encodeLE 8 (ce.addr + 32))
    (s184 : μ.readN (M + 184) 8 = Num.encodeLE 8 n)
    (elem : ∀ k, k < n → PassOk μ (ce.addr + 32) k (Kp k) (Kp (k + 1)) O (ctx k) (ctx (k + 1)) ∨
      ExportOk env μ (ce.addr + 32) k ce (Kp k) (Kp (k + 1)) O (ctx k) (ctx (k + 1)))
    (hOD : ∀ j bs μ, j < n → O j bs → DR j bs μ) (hOR : ∀ j bs, j < n → O j bs → rep j bs)
    (hON : ∀ j bs, j < n → O j bs → ∃ t, DropOut.NoDrop t ∧ bs.take 8 = Num.encodeLE 8 (9223372036854775807 + t))
    (hok : ∀ j, j < n → EncOk p P (enc j) (rep j)) (hlen : ∀ j, j < n → (enc j).length ≤ 232)
    (w c' q ret r5 r6 t : Nat) (cq : Chunk) (hw64 : w < 18446744073709551616)
    (s80 : μ.readN (M + 80) 8 = Num.encodeLE 8 w)
    (s88 : μ.readN (M + 88) 8 = Num.encodeLE 8 c') (s112 : μ.readN (M + 112) 8 = Num.encodeLE 8 q)
    (s624 : μ.readN (M + 624) 8 = Num.encodeLE 8 ret) (s616 : μ.readN (M + 616) 8 = Num.encodeLE 8 r5)
    (s608 : μ.readN (M + 608) 8 = Num.encodeLE 8 r6)
    (hq' : c' < 18446744073709551616) (hcq : c' ≠ 0 → Kp n cq ∧ cq.addr + 32 = q ∧ cq ≠ ce)
    (hret : Fin.RetTo P ret t) (hr5 : r5 < 18446744073709551616)
    (hr6 : r6 < 18446744073709551616)
    (tab : μ.readN 67376 100 = table) (rtab : ∀ a, 67376 ≤ a → a < 67476 → μ.readable a = true)
    (dtab : μ.readN 67760 96 = DropOut.dtable) (rdtab : ∀ a, 67760 ≤ a → a < 67856 → μ.readable a = true) :
    (∃ (ω' : Regs) (μ' : Memory) (s' : State) (N buf : Nat),
      FreeStepsH p (refineContractK cap0 env) 4842 ω μ (ctx 0) t ω' μ' (ctx n) N ∧ HeapCtx env pb S0 S1 μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (M + 632) ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 ∧ ω'[7] = UInt64.ofNat buf ∧ ω'[8] = UInt64.ofNat (off enc n + 3) ∧
      μ'.readN buf (off enc n + 3) = UInt8.ofNat n :: (out enc n ++ Num.encodeLE 2 (w % 65536))) ∨
    ∃ N, ExhaustsX env cap0 pb p 4842 ω μ (ctx 0) N := by
  obtain ⟨hS0M, hMS1, hM2, hM8⟩ := hM
  have hS1 := H.hS1
  obtain ⟨ω1, μ1, run1, L, st, efr⟩ := Entry.entry (p := p) (P := P) (R := refineContractK cap0 env) env (ctx 0)
    ω μ s M cap n ce (Kp 0) O H ⟨hS0M, hMS1, hM2, hM8⟩ hn hn128 (by omega) hce hceC hE hEtop hkp h1 s168 s176 s184
  have lo : ∀ a, a < 2147483648 → μ1.read a = μ.read a := fun a h => efr a (by omega) (Or.inl (by omega))
  have elem1 : ∀ k, k < n → PassOk μ1 (ce.addr + 32) k (Kp k) (Kp (k + 1)) O (ctx k) (ctx (k + 1)) ∨
      ExportOk env μ1 (ce.addr + 32) k ce (Kp k) (Kp (k + 1)) O (ctx k) (ctx (k + 1)) := fun k hk =>
    (elem k hk).imp (PassOk.congr (by omega) lo) (ExportOk.congr (by omega) lo)
  rcases loop_all (p := p) (P := P) (hb := hb) env cap0 hcap1 hcap0 fmt μ1 Kp O ctx L elem1 5054 (Or.inr hn)
      ω1 μ1 s st with ⟨s2, ω2, μ2, N2, run2, st2⟩ | ⟨N, hx⟩
  rotate_left
  · exact Or.inr ⟨_, ExhaustsX.pre run1 hx⟩
  have pre := run1.trans run2
  obtain ⟨tab2, rtab2⟩ := ExitRun.ro_keep H pre (a := 67376) (l := 100) (by omega)
  obtain ⟨dtab2, rdtab2⟩ := ExitRun.ro_keep H pre (a := 67760) (l := 96) (by omega)
  have m1 : ∀ a l, (M + 56 ≤ a ∧ a + l ≤ M + 120) ∨ (M + 304 ≤ a ∧ a + l ≤ 4294967296) →
      μ1.readN a l = μ.readN a l := fun a l h => Memory.readN_congr (fun j hj => efr _ (by omega) (by omega))
  rcases ExitRun.exit_run (p := p) (P := P) (hb := hb) env cap0 hcap1 hcap0 DR enc rep dbg (ctx n) ω2 μ2 s2 L hn
      st2 hcap hOD hOR hON hok hlen w c' q ret r5 r6 t cq hw64
      (by rw [m1 _ _ (by omega)]; exact s80) (by rw [m1 _ _ (by omega)]; exact s88)
      (by rw [m1 _ _ (by omega)]; exact s112) (by rw [m1 _ _ (by omega)]; exact s624)
      (by rw [m1 _ _ (by omega)]; exact s616) (by rw [m1 _ _ (by omega)]; exact s608)
      hq' hcq hret hr5 hr6 (by rw [tab2]; exact tab) (fun a h1 h2 => by rw [rtab2 a h1 h2]; exact rtab a h1 h2)
      (by rw [dtab2]; exact dtab) (fun a h1 h2 => by rw [rdtab2 a h1 h2]; exact rdtab a h1 h2) with
    ⟨ω3, μ3, s3, N3, buf, run3, H3, f0, f1, f5, f6, f7, f8, fo⟩ | ⟨N, hx⟩
  · exact Or.inl ⟨ω3, μ3, s3, _, buf, pre.trans run3, H3, f0, f1, f5, f6, f7, f8, fo⟩
  · exact Or.inr ⟨_, ExhaustsX.pre pre hx⟩

end Services.Bootstrap.Refine.Body
