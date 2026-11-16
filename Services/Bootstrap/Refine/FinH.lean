import Services.Bootstrap.Refine.Fin
import Services.Bootstrap.Refine.DropVecH

/-!
# Refine's exit: the epilogue, with heap elements

`Fin.fin_run` with `DropVecH.drop_vecH` for the output's drop: an output element may be a `DeleteItems` or `Imported`
whose `Vec<Vec<u8>>` (the chunks `own j`) is freed by the drop. GP v0.8.0 Appendix B.4 (Ψ_R running bootstrap's code).
-/

namespace Services.Bootstrap.Refine.FinH

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeR
  Services.Bootstrap.CodeT1B Services.Bootstrap.Encode.Writer
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA Services.Bootstrap.Refine.Fin
  Services.Bootstrap.Refine.DropVecH

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **Refine's epilogue, with heap elements** (6295 … t): `Fin.fin_run` where each output element is of a variant whose
    drop does nothing or a heap element (`HeapEl`, owning `own j`; the owned chunks are disjoint between elements and are
    neither the output buffer `co` nor the payload buffer `cq`). The owned chunks are freed too; every allocated chunk
    owned by no element, other than `co` and `cq`, keeps its data. -/
theorem fin_runH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P]
    (env : RefineHost.Env) {pb S0 S1 : Nat} (x : X)
    (ω : Regs) (μ : Memory) (s : State) (H : HeapCtx env pb S0 S1 μ s) (M c E n c' q buf len ret r5 r6 t : Nat)
    (co cq : Chunk) (own : Nat → Chunk → Prop)
    (hM : S0 + 7560 ≤ M ∧ M + 632 ≤ S1 ∧ 2147484104 ≤ M ∧ M % 8 = 0) (hn : 0 < n) (hnc : n ≤ c)
    (hc : co ∈ chunks s ∧ co.used = true ∧ co.addr + 32 = E ∧ E + 232 * n ≤ co.addr + 32 * co.size)
    (hc'' : 232 * c < 18446744073709551616)
    (hq : c' ≠ 0 → cq ∈ chunks s ∧ cq.used = true ∧ cq.addr + 32 = q ∧ cq ≠ co) (hq' : c' < 18446744073709551616)
    (hown : ∀ j j' d, j < n → j' < n → j ≠ j' → own j d → own j' d → False)
    (hoco : ∀ j, j < n → ¬ own j co) (hocq : c' ≠ 0 → ∀ j, j < n → ¬ own j cq)
    (hbuf : buf < 18446744073709551616) (hlen : len < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat M)
    (s168 : μ.readN (M + 168) 8 = Num.encodeLE 8 c) (s176 : μ.readN (M + 176) 8 = Num.encodeLE 8 E)
    (s184 : μ.readN (M + 184) 8 = Num.encodeLE 8 n)
    (s88 : μ.readN (M + 88) 8 = Num.encodeLE 8 c') (s112 : μ.readN (M + 112) 8 = Num.encodeLE 8 q)
    (s280 : μ.readN (M + 280) 8 = Num.encodeLE 8 buf) (s288 : μ.readN (M + 288) 8 = Num.encodeLE 8 len)
    (s624 : μ.readN (M + 624) 8 = Num.encodeLE 8 ret) (s616 : μ.readN (M + 616) 8 = Num.encodeLE 8 r5)
    (s608 : μ.readN (M + 608) 8 = Num.encodeLE 8 r6)
    (hret : RetTo P ret t) (hr5 : r5 < 18446744073709551616)
    (hr6 : r6 < 18446744073709551616)
    (kinds : ∀ j, j < n → (∃ t, DropOut.NoDrop t ∧ μ.readN (E + 232 * j) 8 = Num.encodeLE 8 (9223372036854775807 + t)) ∨
      HeapEl μ s (E + 232 * j) (own j))
    (tab : μ.readN 67760 96 = DropOut.dtable) (hrt : ∀ a, 67760 ≤ a → a < 67856 → μ.readable a = true) :
    ∃ ω' μ' s' N, FreeStepsH p R 6295 ω μ x t ω' μ' x N ∧ HeapCtx env pb S0 S1 μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (M + 632) ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 ∧ ω'[7] = UInt64.ofNat buf ∧ ω'[8] = UInt64.ofNat len ∧
      (∀ a, a < 4294967296 → M ≤ a → μ'.read a = μ.read a) ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ co → (c' ≠ 0 → d ≠ cq) → (∀ j, j < n → ¬ own j d) → d ∈ chunks s' ∧
        ∀ a, InData d a → μ'.read a = μ.read a) := by
  obtain ⟨hS0M, hMS1, hM2, hM8⟩ := hM
  have hS1 := H.hS1
  have hbT := H.hbT
  have hb0 := H.hb0
  obtain ⟨hco, hcou, hcoa, hcoE⟩ := hc
  obtain ⟨hco0, -, hcoT⟩ := Decode.VecU8.chunk_in H.wf hco hcou
  have rM : ∀ a, S0 ≤ a → a < S1 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (H.st a h1 h2)
  -- the drop
  obtain ⟨ω1, run1, a0, a1, a5, a6, a7⟩ := f1 (p := p) (P := P) (R := R) x ω μ M (by omega) h1
  obtain ⟨ω2, μ2, s2, N2, run2, b0, b1, b5, b6, H2, bfr, bkp, -, -, -⟩ := drop_vecH (p := p) (P := P) (R := R)
    env pb S0 S1 x ω1 μ s M (M + 168) E n 206 6305 co own ⟨by omega, by omega, by omega, hM8⟩ (by omega)
    (Or.inr (by omega)) hn H hco hcou (fun a h1 h2 => ⟨by omega, by omega⟩) hown hoco a0 (a1.trans h1) a7 s176 s184
    kinds tab hrt (fun a h1 h2 => rM a (by omega) (by omega)) ⟨by decide, by decide, by decide⟩ jte_102 bs_6305
  have k2 : ∀ a, a < 4294967296 → M ≤ a → μ2.read a = μ.read a := fun a h0 h => bfr a h0 h
  have r2 : ∀ a l, M ≤ a → a + l ≤ 4294967296 → μ2.readN a l = μ.readN a l :=
    fun a l h h' => Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega))
  obtain ⟨hco2, -⟩ := bkp co hco hcou hoco
  -- the output buffer's free
  obtain ⟨ω3, run3, c0, c1, c5, c6, c7⟩ := f2 (p := p) (P := P) (R := R) x ω2 μ2 M c E (by omega) (by omega) hc''
    (by omega) b1 (by rw [r2 _ _ (by omega) (by omega)]; exact s168)
    (by rw [r2 _ _ (by omega) (by omega)]; exact s176)
    (fun a h1 h2 => Memory.readable_of_writable (H2.st a (by omega) (by omega)))
  obtain ⟨ω4, μ4, run4, H4, k4, keep4, d1, d5, d6⟩ := free_opt (p := p) (P := P) (R := R) env x ω3 μ2 s2 M 208 6330
    co H2 hco2 hcou c0 (c1.trans b1) (by rw [c7, hcoa]) ⟨by decide, by decide, by decide⟩
    jte_103 bs_6330 ⟨by omega, by omega, by omega⟩
  have r4 : ∀ a l, M ≤ a → a + l ≤ 4294967296 → μ4.readN a l = μ.readN a l :=
    fun a l h h' => Memory.readN_congr (fun j hj => by rw [k4 _ (by omega) (by omega), k2 _ (by omega) (by omega)])
  have h1' : ω4[1] = UInt64.ofNat M := by rw [d1, c1, b1]
  -- the `Vec<u8>`'s free, then the return
  have fin : ∀ (ω5 : Regs) (μ5 : Memory) (s5 : State) (n5 : Nat), HeapCtx env pb S0 S1 μ5 s5 →
      FreeStepsH p R 6295 ω μ x 6349 ω5 μ5 x n5 → ω5[1] = UInt64.ofNat M →
      (∀ a, a < 4294967296 → M ≤ a → μ5.read a = μ.read a) →
      ∃ ω' μ', FreeStepsH p R 6295 ω μ x t ω' μ' x (n5 + 8) ∧
        ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (M + 632) ∧ ω'[5] = UInt64.ofNat r5 ∧
        ω'[6] = UInt64.ofNat r6 ∧ ω'[7] = UInt64.ofNat buf ∧ ω'[8] = UInt64.ofNat len ∧ μ' = μ5 := by
    intro ω5 μ5 s5 n5 H5 run5 e1 k5
    have r5' : ∀ a l, M ≤ a → a + l ≤ 4294967296 → μ5.readN a l = μ.readN a l :=
      fun a l h h' => Memory.readN_congr (fun j hj => k5 _ (by omega) (by omega))
    obtain ⟨ω6, run6, g0, g1, g5, g6, g7, g8⟩ := f4 (p := p) (P := P) (R := R) x ω5 μ5 M buf len ret r5 r6 t
      (by omega) hbuf hlen e1 (by rw [r5' _ _ (by omega) (by omega)]; exact s280)
      (by rw [r5' _ _ (by omega) (by omega)]; exact s288) (by rw [r5' _ _ (by omega) (by omega)]; exact s624)
      (by rw [r5' _ _ (by omega) (by omega)]; exact s616) (by rw [r5' _ _ (by omega) (by omega)]; exact s608)
      hret hr5 hr6 (fun a h1 h2 => Memory.readable_of_writable (H5.st a (by omega) (by omega)))
      (fun a h1 h2 => Memory.readable_of_writable (H5.st a (by omega) (by omega)))
    exact ⟨ω6, μ5, run5.trans run6, g0, g1, g5, g6, g7, g8, rfl⟩
  have pre := run1.trans (run2.trans (run3.trans run4))
  have kd2 : ∀ d ∈ chunks s, d.used = true → d ≠ co → (∀ j, j < n → ¬ own j d) →
      d ∈ chunks (free s2 (co.addr + 32)) ∧ ∀ a, InData d a → μ4.read a = μ.read a := fun d hd hu hne hno => by
    obtain ⟨hd2, hk2⟩ := bkp d hd hu hno
    obtain ⟨hd4, hk4⟩ := keep4 d hd2 hu hne
    exact ⟨hd4, fun a ha => by rw [hk4 a ha, hk2 a ha]⟩
  by_cases hq0 : c' = 0
  · subst hq0
    obtain ⟨ω5, run5, e1, -, -⟩ := f3z (p := p) (P := P) (R := R) x ω4 μ4 M (by omega) h1'
      (by rw [r4 _ _ (by omega) (by omega)]; exact s88)
      (fun a h1 h2 => Memory.readable_of_writable (H4.st a (by omega) (by omega)))
    obtain ⟨ω', μ', run', g0, g1, g5, g6, g7, g8, e⟩ := fin ω5 μ4 _ _ H4 (pre.trans run5)
      (e1.trans h1') (fun a h0 h => by rw [k4 a h0 h, k2 a h0 h])
    subst e
    exact ⟨ω', μ', _, _, run', H4, g0, g1, g5, g6, g7, g8, fun a h0 h => by rw [k4 a h0 h, k2 a h0 h],
      fun d hd hu hne _ hno => kd2 d hd hu hne hno⟩
  · obtain ⟨hcq, hcqu, hcqa, hcqo⟩ := hq hq0
    obtain ⟨-, -, hcqT⟩ := Decode.VecU8.chunk_in H.wf hcq hcqu
    obtain ⟨ω5, run5, e0, e1, e5, e6, e7⟩ := f3 (p := p) (P := P) (R := R) x ω4 μ4 M c' q (by omega) hq0 hq'
      (by omega) h1' (by rw [r4 _ _ (by omega) (by omega)]; exact s88)
      (by rw [r4 _ _ (by omega) (by omega)]; exact s112)
      (fun a h1 h2 => Memory.readable_of_writable (H4.st a (by omega) (by omega)))
    obtain ⟨hcq4, -⟩ := kd2 cq hcq hcqu hcqo (hocq hq0)
    obtain ⟨ω6, μ6, run6, H6, k6, keep6, f1', -, -⟩ := free_opt (p := p) (P := P) (R := R) env x ω5 μ4
      (free s2 (co.addr + 32)) M 210 6349 cq H4 hcq4 hcqu e0 (e1.trans h1') (by rw [e7, hcqa])
      ⟨by decide, by decide, by decide⟩ jte_104 bs_6349 ⟨by omega, by omega, by omega⟩
    obtain ⟨ω', μ', run', g0, g1, g5, g6, g7, g8, e⟩ := fin ω6 μ6 _ _ H6 ((pre.trans run5).trans run6)
      (f1'.trans (e1.trans h1')) (fun a h0 h => by rw [k6 a h0 h, k4 a h0 h, k2 a h0 h])
    subst e
    refine ⟨ω', μ', _, _, run', H6, g0, g1, g5, g6, g7, g8, fun a h0 h => by rw [k6 a h0 h, k4 a h0 h, k2 a h0 h],
      fun d hd hu hne hne' hno => ?_⟩
    obtain ⟨hd4, hk4⟩ := kd2 d hd hu hne hno
    obtain ⟨hd6, hk6⟩ := keep6 d hd4 hu (hne' hq0)
    exact ⟨hd6, fun a ha => by rw [hk6 a ha, hk4 a ha]⟩

end Services.Bootstrap.Refine.FinH
