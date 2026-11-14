import Services.Bootstrap.AccLog.ItemLog

/-!
# The `Imported` handler's log line (9116 … 9165), frame-only

In the instruction loop's `Imported` arm (9047), `format!` at 9116 (`format_inner`, 59375; template
at 66312: "Imported data " and one argument, its pair at sp + 1496, formatter 37897) writes a
`String` at sp + 1568; `log` (100, level 2) at 9144 sends it (the message unspecified), and the
`String` is freed at 9159 (40613). As `ItemLog.lean`, at this site's addresses; the formatting of
the argument is the hypothesis `hA`, discharged by `ArgOk` of 37897.
-/

namespace Services.Bootstrap.AccLog

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.CodeF
  Services.Bootstrap.Acc Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Fmt

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 9123 … 9142: `log`'s arguments: level 2 (ω₇), the target at 66793 (ω₈, 4 octets, ω₉), the
    message at the `String`'s buffer (ω₁₀ = ω₅ = the word at sp + 1576) and length (ω₁₁, at
    sp + 1584). -/
theorem iml_a {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp : Nat) (hsp : sp + 1592 < 4294967296) (h1 : ω[1] = UInt64.ofNat sp)
    (hr : ∀ a, sp + 1568 ≤ a → a < sp + 1592 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 9123 ω μ x 9144 ω' μ x 6 ∧
      ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat (rdN μ (sp + 1576) 8) ∧ ω'[6] = ω[6] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hsp, hr, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_⟩
    all_goals post_simp [h1, Nat.mod_eq_of_lt (rdN_lt64 μ (sp + 1576))]

/-- 9146 … 9159, the `String`'s capacity (at sp + 1568) nonzero: `dealloc(ω₅, 1)` (40613), returning
    to 9165 (316). -/
theorem iml_b {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp q : Nat) (hsp : sp + 1592 < 4294967296) (hq : q < 18446744073709551616) (h1 : ω[1] = UInt64.ofNat sp)
    (h5 : ω[5] = UInt64.ofNat q)
    (hcap : rdN μ (sp + 1568) 8 ≠ 0) (hr : ∀ a, sp + 1568 ≤ a → a < sp + 1576 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 9146 ω μ x 40613 ω' μ x 6 ∧
      ω'[0] = UInt64.ofNat 316 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat q := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, hsp, hcap, hr, Nat.mod_eq_of_lt (rdN_lt64 μ (sp + 1568)), ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, h5, Nat.mod_eq_of_lt hq]

/-- 9146 … 9151, capacity 0: on to 9165. -/
theorem iml_b0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp : Nat) (hsp : sp + 1592 < 4294967296) (h1 : ω[1] = UInt64.ofNat sp)
    (hcap : rdN μ (sp + 1568) 8 = 0) (hr : ∀ a, sp + 1568 ≤ a → a < sp + 1576 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 9146 ω μ x 9165 ω' μ x 3 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hsp, hcap, hr, Nat.mod_eq_of_lt (rdN_lt64 μ (sp + 1568)), ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1]

theorem imported_log_post {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (cap : Nat)
    (hcap : 1000 ≤ cap ∧ cap < 2 ^ 64) (env : AccEnv) (envH : RefineHost.Env) (pb S0 S1 : Nat)
    (x : AccCtx) (ω : Regs) (μ : Memory) (s₀ s : State) (sp : Nat)
    (H : HeapCtx envH pb S0 S1 μ s) (hso : StrOut s₀ s μ (sp + 1568)) (h1 : ω[1] = UInt64.ofNat sp)
    (hsp : 2147483716 ≤ sp ∧ S0 + 40 ≤ sp ∧ sp + 1592 ≤ S1) :
    ∃ ω' μ' s', FreeStepsH p (accContractK cap env) 9123 ω μ x 9165 ω' μ' x 300 ∧
      HeapCtx envH pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Outside pb sp (fun _ => False) μ μ' ∧
      (∀ d ∈ chunks s₀, d.used = true → d ∈ chunks s' ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
      ω'[1] = ω[1] ∧ ω'[6] = ω[6] := by
  have hS1 := H.hS1
  have hst := H.st
  obtain ⟨scap, slen, hs⟩ := hso
  have hr : ∀ a, sp + 1568 ≤ a → a < sp + 1592 → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (hst a (by omega) (by omega))
  obtain ⟨ω1, run1, a1, a5, a6⟩ := iml_a (p := p) (P := P) (R := accContractK cap env) x ω μ sp (by omega) h1 hr
  -- the log call
  have refl : ∀ d ∈ chunks s₀, d.used = true → d ∈ chunks s ∧ ∀ a, InData d a → μ.read a = μ.read a :=
    fun d hd hu => ⟨hs.base d hd hu, fun _ _ => rfl⟩
  have outR : Outside pb sp (fun _ => False) μ μ :=
    ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ => rfl⟩
  have w1 : (setR7 ω1 Result.WHAT)[1] = UInt64.ofNat sp := by
    simp only [setR7, Vector.getElem_set]; simp [a1, h1]
  have w5 : (setR7 ω1 Result.WHAT)[5] = UInt64.ofNat (rdN μ (sp + 1576) 8) := by
    simp only [setR7, Vector.getElem_set]; simp [a5]
  have w6 : (setR7 ω1 Result.WHAT)[6] = ω[6] := by simp only [setR7, Vector.getElem_set]; simp [a6]
  by_cases hc0 : scap = 0
  · subst hc0
    obtain ⟨ω2, run2, b0, b1, b5, b6⟩ := iml_b0 (p := p) (P := P) (R := accContractK cap env) x
      (setR7 ω1 Result.WHAT) μ sp (by omega) w1 hs.rc (fun a h1 h2 => hr a h1 (by omega))
    refine ⟨ω2, μ, s, run1.trans (FreeStepsH.logAcc cap hcap env (d_9144 (p := p) (P := P)) run2) |>.mono (by omega), H, rfl, outR,
      refl, b1.trans (w1.trans h1.symm), b6.trans w6⟩
  · obtain ⟨c, hc, hcu, hca, -, hcf⟩ := hs.buf.resolve_left hc0
    obtain ⟨ω2, run2, b0, b1, b5, b6, b7⟩ := iml_b (p := p) (P := P) (R := accContractK cap env) x
      (setR7 ω1 Result.WHAT) μ sp (rdN μ (sp + 1568 + 8) 8) (by omega) (rdN_lt64 μ _) w1 w5
      (by rw [hs.rc]; exact hc0) (fun a h1 h2 => hr a h1 (by omega))
    obtain ⟨ω3, μ3, run3, H3, hb3, hpg, hro, stk, hgl, keep3, c0, c1, c5, c6⟩ :=
      Decode.DeallocCall.dealloc_call (R := accContractK cap env) (p := p) (P := P) envH pb S0 S1 x ω2 μ s sp
        (rdN μ (sp + 1568 + 8) 8) 316 9165 c H hc hcu hca b0 (b1.trans w1) b7 (by decide) jte_157 bs_9165 hsp.1
        ⟨hsp.2.1, by omega⟩
    have out3 : Outside pb sp (fun _ => False) μ μ3 :=
      ⟨fun b _ => ⟨by unfold Memory.readable; rw [hpg], by unfold Memory.writable; rw [hpg]⟩,
        fun b hb _ hw => hro b hb hw, fun a ha hb _ => stk a hb ha, hgl⟩
    refine ⟨ω3, μ3, free s (rdN μ (sp + 1568 + 8) 8),
      (run1.trans (FreeStepsH.logAcc cap hcap env (d_9144 (p := p) (P := P)) (run2.trans run3))).mono (by omega),
      H3, hb3, out3, fun d hd hu => ?_, c1.trans (b1.trans (w1.trans h1.symm)),
      c6.trans (b6.trans w6)⟩
    have hd' := hs.base d hd hu
    have hne : d ≠ c := fun e => hcf d hd hu (by rw [e])
    exact keep3 d hd' hu hne

/-- The template at 66312: 14 octets of literal ("Imported data "), then `{}`. -/
def importedTmpl : List TItem := [.lit 14, .arg]

/-- The template's 17 octets in the blob's read-only data. -/
def importedTmplBytes : List UInt8 := [14, 73, 109, 112, 111, 114, 116, 101, 100, 32, 100, 97, 116, 97, 32, 192, 0]

/-- **The template at 66312 is `importedTmpl`**, from its octets. -/
theorem tmpl_imported {μ : Memory} (h : μ.readN 66312 17 = importedTmplBytes)
    (hr : ∀ a, 66312 ≤ a → a < 66329 → μ.readable a = true) : Tmpl μ 66312 importedTmpl := by
  have r := fun j hj => rd1_of_readN h j hj
  simp only [importedTmpl, Tmpl]
  refine ⟨by decide, by decide, (r 0 (by decide)).trans (by decide), fun b h1 h2 => hr b (by omega) (by omega), ?_⟩
  refine ⟨(r 15 (by decide)).trans (by decide), hr _ (by omega) (by omega), ?_⟩
  exact ⟨(r 16 (by decide)).trans (by decide), hr _ (by omega) (by omega)⟩

variable {X : Type} {R : HostRel X} in
/-- 9116: the call of `format_inner` (59375), returning to 9123 (314). -/
theorem imported_site_call {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory) :
    ∃ ω', FreeStepsH p R 9116 ω μ x 59375 ω' μ x 1 ∧ ω'[0] = UInt64.ofNat 314 ∧ ω'[1] = ω[1] ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧ ω'[9] = ω[9] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go []
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [rdN_lit8]

theorem imported_fmt_site {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] [HasCodeA p P] (cap : Nat)
    (hcap : 1000 ≤ cap ∧ cap < 2 ^ 64) (env : AccEnv) (envH : RefineHost.Env) (pb S0 S1 : Nat)
    (HA : AllocOk p (accContractK cap env) envH pb S0 S1)
    (HR : ReallocOk p (accContractK cap env) envH pb S0 S1)
    (x : AccCtx) (ω : Regs) (μ : Memory) (s : State) (S : Nat)
    (H : HeapCtx envH pb S0 S1 μ s) (hba : s.base % 8 = 0)
    (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat (S + 1568)) (h8 : ω[8] = UInt64.ofNat 66312)
    (h9 : ω[9] = UInt64.ofNat (S + 1496))
    (hS : S0 + 800 ≤ S ∧ S % 8 = 0 ∧ 2147484500 ≤ S ∧ S + 1700 ≤ S1)
    (hro : RoW μ) (htm : μ.readN 66312 17 = importedTmplBytes)
    (hrt : ∀ a, 66312 ≤ a → a < 66329 → μ.readable a = true)
    (c d : Nat) (hc : c < 1048576) (hA : ArgsAt p P (accContractK cap env) envH pb S0 S1 600 μ s S (S + 1496) 0 importedTmpl c d) :
    (∃ ω' μ' x' s', FreeStepsH p (accContractK cap env) 9116 ω μ x 9165 ω' μ' x'
        (1 + fmtCost c d importedTmpl + 300) ∧
      HeapCtx envH pb S0 S1 μ' s' ∧ s'.base = s.base ∧
      Keeps pb S (fun a => S + 1568 ≤ a ∧ a < S + 1568 + 24) s μ μ' s' ∧ ω'[1] = ω[1] ∧ ω'[6] = ω[6]) ∨
    Exhausts p (accContractK cap env) pb 9116 ω μ x (1 + fmtCost c d importedTmpl) := by
  have hst := H.st
  have hS1 := H.hS1
  have hSb := H.hSb
  have hrd : ∀ a, S0 ≤ a → a < S1 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hst a h1 h2)
  obtain ⟨ω1, run1, a0, a1, a5, a6, a7, a8, a9⟩ := imported_site_call (p := p) (P := P) (R := accContractK cap env) x ω μ
  rcases format_inner (p := p) (P := P) (R := accContractK cap env) envH pb S0 S1 600 (Nat.le_refl _) HA HR S (S + 1568) 66312
      (S + 1496) 314 9123 c d importedTmpl x ω1 μ s H hba a0 (a1.trans h1) (a7.trans h7) (a8.trans h8)
      (a9.trans h9) (by decide) jte_156 bs_9123 ⟨by omega, hS.2.1, by omega, by omega⟩ ⟨by omega, by omega⟩
      hro (tmpl_imported htm hrt) (by simp [importedTmpl, tsize]) ⟨by omega, by omega⟩ hA (by simp [importedTmpl, nargs])
      (by simp [importedTmpl, tlen]; omega) with
    ⟨ω2, μ2, x2, s2, run2, H2, hb2, K2, hso, b0, b1, b5, b6⟩ | hx
  · obtain ⟨ω3, μ3, s3, run3, H3, hb3, out3, keep3, c1, c6⟩ := imported_log_post (p := p) (P := P) cap hcap env envH pb S0 S1
      x2 ω2 μ2 s s2 S H2 hso (b1.trans (a1.trans h1)) ⟨by omega, by omega, by omega⟩
    have K3 : Keeps pb S (fun a => S + 1568 ≤ a ∧ a < S + 1568 + 24) s μ2 μ3 s3 :=
      ⟨⟨out3.access, out3.ro, fun a ha hb _ => out3.hi a ha hb (fun h => h), out3.glob⟩,
        fun d hd hu => (keep3 d hd hu).1, fun d hd hu a ha => (keep3 d hd hu).2 a ha⟩
    have K := K2.trans' K3
    rw [Nat.max_self] at K
    exact Or.inl ⟨ω3, μ3, x2, s3, (run1.trans (run2.trans run3)).mono (by omega), H3, hb3.trans hb2, K,
      c1.trans (b1.trans a1), c6.trans (b6.trans a6)⟩
  · exact Or.inr (Exhausts.pre run1 hx)

end Services.Bootstrap.AccLog
