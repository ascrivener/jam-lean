import Services.Bootstrap.Refine.Kinds
import Services.Bootstrap.Refine.Decode

/-!
# Refine from the payload to its return, for fixed-width instructions passed through (interim)

`run_fixed` composes `Decode.decode_one` (4792 … 4842: `Instructions::decode`) and `Body.body` (4842 … refine's
return) for a payload ℰ(`Instructions { is, salt }`) whose 1 ≤ n ≤ 70 instructions are all passed through
(`Kinds.FixedKind`: the milestone's fixed-width kinds, `Kinds.kind_of`): refine returns ℰ(`BootstrapWorkOutput`)
= n :: (ℰ(is₀) … ℰ(isₙ₋₁)) ⌢ ℰ₂(w mod 2^16), the host context unchanged; or an allocation fails. Interim:
n ≤ 70 (one reserve batch); `Export` comes with its decode's chunk facts. GP v0.8.0 Appendix B.4 (Ψ_R
running bootstrap's code); `Spec.refine`.
-/

namespace Services.Bootstrap.Refine.RunFixed

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeR
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.Loop Services.Bootstrap.Alloc Services.Bootstrap.Refine.Pass
  Services.Bootstrap.Refine.PassLoop Services.Bootstrap.Refine.LoopAll Services.Bootstrap.Refine.Kinds
  Services.Bootstrap.Encode.Loop Services.Bootstrap.Encode.Enc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- The instruction j's encoding (`Spec.Instr.encode`), `Panic`'s past the end. -/
def encAt (is : List Spec.Instr) (j : Nat) : List UInt8 := (is.getD j .panic).encode

theorem run_fixed {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P]
    (env : RefineHost.Env) (cap0 : Nat) (hcap1 : 134217728 ≤ cap0) (hcap0 : cap0 < 18446744073709551616)
    {hb pb : Nat} (gl : Nat → UInt8)
    (is : List Spec.Instr) (Rs : Nat → List UInt8 → Prop) (ts : Nat → Nat)
    (hk : ∀ j, j < is.length → FixedKind p P (encAt is j) (Rs j) (ts j))
    {ro : List UInt8} (fmt : ExportSeg.ExportFmtOk p cap0 env pb S0 S1 ro)
    (dbg : ExitRun.DebugLineOk p cap0 env pb S0 S1 ro (fun j bs _ => Rs j bs))
    (x : RefineCtx) (ω : Regs) (μ : Memory) (s : State) (H : HeapCtx env pb S0 S1 μ s) (hro : RoData.RoIs ro μ)
    (M q Ly r5 : Nat) (salt : List UInt8) (cp : Chunk)
    (hn : 1 ≤ is.length ∧ is.length ≤ 70) (hM : S0 + 7560 ≤ M ∧ M + 632 ≤ S1 ∧ M % 8 = 0)
    (hr5 : r5 < 18446744073709551616)
    (hcp : cp ∈ chunks s ∧ cp.used = true ∧ cp.addr = s.base) (hcpq : cp.addr + 32 = q)
    (hcpd : ∀ a, q ≤ a → a < q + Ly → InData cp a)
    (hLy : 1 + (is.map Spec.Instr.encode).flatten.length + 32 ≤ Ly ∧ Ly < 4294967296)
    (hg : ∀ a, Glob a → μ.read a = gl a)
    (h1 : ω[1] = UInt64.ofNat M) (h5 : ω[5] = UInt64.ofNat r5) (h6 : ω[6] = UInt64.ofNat Ly)
    (s112 : μ.readN (M + 112) 8 = Num.encodeLE 8 q) (sb : μ.read q = UInt8.ofNat is.length)
    (pay : μ.readN (q + 1) (is.map Spec.Instr.encode).flatten.length = (is.map Spec.Instr.encode).flatten)
    (ssalt : μ.readN (q + 1 + (is.map Spec.Instr.encode).flatten.length) 32 = salt)
    (w c' ret r5' r6' t : Nat) (hw64 : w < 18446744073709551616)
    (s80 : μ.readN (M + 80) 8 = Num.encodeLE 8 w) (s88 : μ.readN (M + 88) 8 = Num.encodeLE 8 c')
    (s624 : μ.readN (M + 624) 8 = Num.encodeLE 8 ret) (s616 : μ.readN (M + 616) 8 = Num.encodeLE 8 r5')
    (s608 : μ.readN (M + 608) 8 = Num.encodeLE 8 r6')
    (hc' : c' < 18446744073709551616)
    (hret : Fin.RetTo P ret t) (hr5' : r5' < 18446744073709551616)
    (hr6' : r6' < 18446744073709551616)
    (tab : μ.readN 67476 100 = Decode.Tag.table) (rt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (tab2 : μ.readN 67376 100 = table) (rtab2 : ∀ a, 67376 ≤ a → a < 67476 → μ.readable a = true)
    (dtab : μ.readN 67760 96 = DropOut.dtable) (rdtab : ∀ a, 67760 ≤ a → a < 67856 → μ.readable a = true) :
    (∃ (ω' : Regs) (μ' : Memory) (s' : State) (N buf : Nat),
      FreeStepsH p (refineContractK cap0 env) 4792 ω μ x t ω' μ' x N ∧ HeapCtx env pb S0 S1 μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (M + 632) ∧ ω'[5] = UInt64.ofNat r5' ∧
      ω'[6] = UInt64.ofNat r6' ∧ ω'[7] = UInt64.ofNat buf ∧ ω'[8] = UInt64.ofNat (off (encAt is) is.length + 3) ∧
      μ'.readN buf (off (encAt is) is.length + 3) =
        UInt8.ofNat is.length :: (out (encAt is) is.length ++ Num.encodeLE 2 (w % 65536)) ∧
      ((∀ a, buf ≤ a → a < buf + (off (encAt is) is.length + 3) → μ'.readable a = true) ∧ buf + (off (encAt is) is.length + 3) < 2147483648)) ∨
    ∃ N, ExhaustsX env cap0 pb p 4792 ω μ x N := by
  obtain ⟨hM0, hM1, hM8⟩ := hM
  have hS0d : S0 = 4278050816 := rfl
  have hS1d : S1 = 4278059008 := rfl
  have hes : ∀ j (hj : j < (is.map Spec.Instr.encode).length), (is.map Spec.Instr.encode)[j] = encAt is j :=
    fun j hj => by
      simp only [List.length_map] at hj
      simp [encAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  have hL : Lay (M - 744) (M + 272) := ⟨by omega, by omega, by omega, by omega⟩
  rcases Decode.decode_one (p := p) (P := P) (hb := hb) env cap0 hcap1 hcap0 gl x ω μ s H M q Ly r5
      (is.map Spec.Instr.encode) salt (fun j bs _ => Rs j bs) cp (fun _ => 4000)
      (fun j hj => by rw [hes j hj]; exact ElemOkAF.of_elemOkF hL ((hk j (by simpa using hj)).dec _ _ hL))
      hg (by simpa using hn) (fun j hj => by rw [hes j hj]; exact (hk j (by simpa using hj)).ne)
      ⟨by omega, by omega, hM8⟩ hr5 hcp hcpd hLy h1 h5 h6 s112 (by simpa using sb) pay ssalt tab rt with
    ⟨ω1, μ1, s1, E, N1, run1, b1, -, -, b168, b176, b184, -, -, -, H1, hcb, hcbd, hel1, keep1, fresh1, hi1, -⟩ | ⟨N, hx⟩
  rotate_left
  · exact Or.inr ⟨_, ExhaustsX.of hx⟩
  simp only [List.length_map] at b168 b176 b184 hcb hcbd hel1 fresh1
  obtain ⟨n, hN⟩ : ∃ n, is.length = n := ⟨_, rfl⟩
  rw [hN] at hn b168 b184 hcb hcbd hel1 fresh1 ⊢
  have hb1 := H1.hb0
  have hbT1 := H1.hbT
  obtain ⟨hE0, -, hET⟩ := Decode.VecU8.chunk_in H1.wf hcb rfl
  simp only at hE0 hET
  have hE32 : E - 32 + 32 = E := by omega
  have m1 : ∀ a l, M ≤ a → a + l ≤ 4294967296 → (a + l ≤ M + 168 ∨ M + 224 ≤ a) → (a + l ≤ M + 272 ∨ M + 288 ≤ a) →
      μ1.readN a l = μ.readN a l :=
    fun a l h0 h1 h2 h3 => Memory.readN_congr (fun j hj => hi1 _ (by omega) (by omega) (by omega) (by omega))
  obtain ⟨tab1, rtab1⟩ := ExitRun.ro_keep H run1 (a := 67376) (l := 100) (by omega)
  obtain ⟨dtab1, rdtab1⟩ := ExitRun.ro_keep H run1 (a := 67760) (l := 96) (by omega)
  -- the decoded slots
  have slot : ∀ j, j < n → Rs j (μ1.readN (E + 232 * j) 232) := fun j hj => by
    obtain ⟨cs, -, hr⟩ := hel1 j hj
    exact hr μ1 (fun _ _ _ _ => rfl)
  have rsub : ∀ j o l, o + l ≤ 232 → μ1.readN (E + 232 * j + o) l = ((μ1.readN (E + 232 * j) 232).drop o).take l :=
    fun j o l h => Decode.Loop.readN_sub μ1 _ 232 o l _ rfl h
  rcases Body.body (p := p) (P := P) (hb := hb) env cap0 hcap1 hcap0 fmt (fun j bs _ => Rs j bs) (encAt is) Rs dbg
      ω1 μ1 s1 H1 (RoData.RoIs.keep H run1 hro) M n n ⟨E - 32, (232 * n + 31) / 32 + 1, true⟩ (fun _ d => d = cp) Rs (fun _ => x)
      ⟨by omega, hM1, by omega, hM8⟩ (by omega) (by omega) (by omega) (by omega) ⟨hcb, rfl⟩
      (by simp only; omega) (by simp only; omega)
      (fun d hd => by rw [hd]; exact ⟨(keep1 cp hcp.1 hcp.2.1).1, hcp.2.1⟩) b1
      b168 (by simp only [hE32]; exact b176) b184
      (fun k hk' => Or.inl ⟨ts k, by
          have := (hk k (by omega)).pass _ (slot k hk')
          simp only [hE32]; unfold rdN; rw [rsub k 44 1 (by omega)]; exact this,
        by simp only [hE32]; rw [show E + 232 * k = E + 232 * k + 0 from rfl, rsub k 0 8 (by omega)]
           simpa using (hk k (by omega)).tag _ (slot k hk'),
        by simp only [hE32]; exact slot k hk', fun d h => h, rfl⟩)
      (fun j bs μ hj h => h) (fun j bs hj h => h)
      (fun j bs hj h => ⟨ts j, (hk j (by omega)).nd, (hk j (by omega)).tag bs h⟩)
      (fun j hj => (hk j (by omega)).enc) (fun j hj => (hk j (by omega)).len)
      w c' q ret r5' r6' t cp hw64
      (by rw [m1 _ _ (by omega) (by omega) (by omega) (by omega)]; exact s80)
      (by rw [m1 _ _ (by omega) (by omega) (by omega) (by omega)]; exact s88)
      (by rw [m1 _ _ (by omega) (by omega) (by omega) (by omega)]; exact s112)
      (by rw [m1 _ _ (by omega) (by omega) (by omega) (by omega)]; exact s624)
      (by rw [m1 _ _ (by omega) (by omega) (by omega) (by omega)]; exact s616)
      (by rw [m1 _ _ (by omega) (by omega) (by omega) (by omega)]; exact s608)
      hc' (fun _ => ⟨rfl, hcpq, fun e => fresh1 cp hcp.1 hcp.2.1 e⟩) hret hr5' hr6'
      (by rw [tab1]; exact tab2) (fun a h1 h2 => by rw [rtab1 a h1 h2]; exact rtab2 a h1 h2)
      (by rw [dtab1]; exact dtab) (fun a h1 h2 => by rw [rdtab1 a h1 h2]; exact rdtab a h1 h2) with
    ⟨ω2, μ2, s2, N2, buf, run2, H2, e0, e1, e5, e6, e7, e8, eo, erd⟩ | ⟨N, hx⟩
  · exact Or.inl ⟨ω2, μ2, s2, _, buf, run1.trans run2, H2, e0, e1, e5, e6, e7, e8, eo, erd⟩
  · exact Or.inr ⟨_, ExhaustsX.pre run1 hx⟩

end Services.Bootstrap.Refine.RunFixed
