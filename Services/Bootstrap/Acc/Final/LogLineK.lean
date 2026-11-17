import Services.Bootstrap.Acc.Final.KeepK
import Services.Bootstrap.Fmt.AccFmt

/-!
# Accumulate's first log line under the context-keeping contract

Copies of `Fmt.info_self`, `Fmt.log_site`, `Fmt.acc_fmt_site` and `Fmt.acc_log_line` (6501 … 6630) under
`accKeepK cap env` (`accContractK` steps that keep the context) in place of `accContractK cap env`:
the same proofs, with the `info` and `log` steps from `FreeStepsH.infoSelfK` / `FreeStepsH.logKeepK`
and the allocator's contracts from `allocOk_keepK` / `reallocOk_keepK`. A run under `accKeepK` keeps the
context and lifts to `KeepCtx (accContractS env)` (`FreeStepsH.keepS`), which T2's `Impl` needs.
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.CodeF Services.Bootstrap.Acc Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **`info` of the accumulating service, frame-only** (49454, called at 6501 with the destination
    D in ω₇): under `accKeepK cap env` (𝖬_I ≤ cap), when the service's own account a is in the
    context's accounts and its `info` record is shorter than 2⁶⁴ − 9 octets, the call returns to t
    (the address ω₀ resolves to) with ω₀, ω₁, ω₅, ω₆ as they were and the context unchanged. Memory
    changes only in S − 488 … S (its frames) and the 96 octets at D (the decoded record, not
    stated). -/
theorem info_selfK {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (cap : Nat)
    (hcap : 703 ≤ cap ∧ cap < 2 ^ 64) (env : AccEnv) (x : AccCtx) (a : ServiceAccount)
    (ha : x.1.state.accounts.get? x.1.id = some a) (hlen : (infoValue a).length < 18446744073709551607)
    (ω : Regs) (μ : Memory) (S D ret t : Nat)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat D)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hS : 65536 + 600 ≤ S ∧ S % 8 = 0) (hD : S + 8 ≤ D ∧ D + 96 + 16 < 4294967296)
    (hwS : ∀ a, S - 488 ≤ a → a < S → μ.writable a = true)
    (hwD : ∀ a, D ≤ a → a < D + 96 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (accKeepK cap env) 49454 ω μ x t ω' μ' x 8000 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      (∀ b, b < 4294967296 → (b < S - 488 ∨ S ≤ b) → (b < D ∨ D + 96 ≤ b) → μ'.read b = μ.read b) ∧
      (∀ b, μ'.readable b = μ.readable b) ∧ (∀ b, μ'.writable b = μ.writable b) := by
  have hv5 := UInt64.toNat_lt ω[5]
  have hv6 := UInt64.toNat_lt ω[6]
  have hw : ∀ b, S - 488 ≤ b → b < S → μ.writable b = true := hwS
  -- the frames
  obtain ⟨ω1, μ1, run1, a0, a1, a6, a7, a8, a9, m112, m104, m256, m248, m240, m56, fr1, rd1, wr1⟩ :=
    io_entry (p := p) (P := P) (R := accKeepK cap env) x ω μ S D ret ω[5].toNat ω[6].toNat ⟨by omega, by omega⟩ h0 h1
      UInt64.ofNat_toNat.symm UInt64.ofNat_toNat.symm h7 ⟨by omega, hv5, hv6, by omega⟩
      (fun b h1 h2 => hw b (by omega) h2)
  -- memset of the buffer
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, -, fr2, rd2, wr2⟩ := Memzero.memzero (p := p) (P := P) (R := accKeepK cap env) x ω1 μ1
    (S - 384 + 64) 96 2158 48534 (by omega) ⟨by omega, by omega⟩ (by omega) a0 a7 a8 a9 (by decide) jte_1078
    bs_48534 (fun b h1 h2 => by rw [wr1]; exact hw b (by omega) (by omega))
  obtain ⟨ω3, run3, c1, c7, c8, c9, c10⟩ := io_a1 (p := p) (P := P) (R := accKeepK cap env) x ω2 μ2 (S - 384) ⟨by omega, by omega⟩
    (b1.trans a1) (b6.trans a6)
  -- after the host call
  obtain ⟨L, hL⟩ : ∃ L, (infoValue a).length = L := ⟨_, rfl⟩
  rw [hL] at hlen
  obtain ⟨μ4, hμ4⟩ : ∃ m, m = μ2.writeN (S - 384 + 64) ((infoValue a).take (min 96 L)) := ⟨_, rfl⟩
  have fr4 : ∀ b, b < 4294967296 → (b < S - 384 + 64 ∨ S - 384 + 160 ≤ b) → μ4.read b = μ2.read b := fun b hb h => by
    rw [hμ4, Memory.read_writeN_disjoint _ _ _ _ (by simp only [List.length_take]; omega)
      (by simp only [List.length_take, two32]; omega) (by simp only [two32]; omega)]
  have wr4 : ∀ b, μ4.writable b = μ2.writable b := fun b => by rw [hμ4, Memory.writable_writeN]
  have rd4 : ∀ b, μ4.readable b = μ2.readable b := fun b => by rw [hμ4, Memory.readable_writeN]
  have k14 : ∀ b, b < 4294967296 → (b < S - 384 + 64 ∨ S - 384 + 160 ≤ b) → μ4.read b = μ1.read b := fun b hb h => by
    rw [fr4 b hb h, fr2 b hb h]
  have wr14 : ∀ b, μ4.writable b = μ1.writable b := fun b => by rw [wr4, wr2]
  have hw4 : ∀ b, S - 488 ≤ b → b < S → μ4.writable b = true := fun b h1 h2 => by
    rw [wr14, wr1]; exact hw b h1 h2
  obtain ⟨ω4, hω4⟩ : ∃ w, w = setR7 ω3 L := ⟨_, rfl⟩
  have d1 : ω4[1] = UInt64.ofNat (S - 384) := by rw [hω4, setR7_getElem _ _ _ (by decide) (by decide), c1]
  have d7 : ω4[7] = UInt64.ofNat L := by rw [hω4, setR7_getElem7]
  obtain ⟨ω5, μ5, run5, e0, e1, e7, e8, e9, rp5, rl5, fr5, rd5, wr5⟩ := io_a2 (p := p) (P := P) (R := accKeepK cap env) x ω4 μ4
    (S - 384) L ⟨by omega, by omega⟩ hlen d1 d7 (fun b h1 h2 => hw4 b (by omega) (by omega))
  have k15 : ∀ b, b < 4294967296 → (b < S - 384 + 64 ∨ (S - 384 + 240 ≤ b)) → μ5.read b = μ1.read b :=
    fun b hb h => by rw [fr5 b hb (by omega), k14 b hb (by omega)]
  have st5 : ISt μ5 (S - 384) (S - 120) D ω[6].toNat 0 :=
    ⟨by rw [rdN_frame (fun j hj => k15 _ (by omega) (by omega))]; exact m56,
     by rw [rdN_frame (fun j hj => k15 _ (by omega) (by omega))]; exact m256,
     by rw [rdN_frame (fun j hj => k15 _ (by omega) (by omega))]; exact m248,
     by rw [rdN_frame (fun j hj => k15 _ (by omega) (by omega))]; exact m240,
     by rw [rp5], by rw [rl5]⟩
  have hw5 : ∀ b, S - 384 - 104 ≤ b → b < S - 384 + 264 → μ5.writable b = true := fun b h1 h2 => by
    rw [wr5]; exact hw4 b (by omega) (by omega)
  obtain ⟨ω6, μ6, run6, f1, f7, st6, fr6, rd6, wr6⟩ := info_reads (p := p) (P := P) (R := accKeepK cap env) x ω5 μ5 (S - 384)
    (S - 120) D ω[6].toNat ⟨by omega, by omega, by omega⟩ st5 e0 e1 e7 e8 e9 hw5
  -- the record's write-back, the copy to D and the return
  have hw6 : ∀ b, S - 488 ≤ b → b < S → μ6.writable b = true := fun b h1 h2 => by
    rw [wr6, wr5]; exact hw4 b h1 h2
  obtain ⟨ω7, μ7, run7, g1, g5, g6, gt, fr7, rd7, wr7⟩ := io_l (p := p) (P := P) (R := accKeepK cap env) x ω6 μ6 (S - 384) D
    ω[6].toNat ⟨by omega, by omega⟩ f1 f7 (by rw [st6.res]; omega) st6.s0 st6.s5 st6.s6
    (fun b h1 h2 => Memory.readable_of_writable (hw6 b (by omega) (by omega)))
    (fun b h1 h2 => hw6 b (by omega) (by omega))
  obtain ⟨ω8, run8, h80, h81, h85, h86, h87, h88, h89⟩ := io_b (p := p) (P := P) (R := accKeepK cap env) x ω7 μ7 (S - 120) D
    ⟨by omega, by omega⟩ (by omega) (by rw [g1]; congr 1; omega) g5 (by rw [show S - 120 = S - 384 + 264 by omega]; exact gt)
    (fun b h1 h2 => by rw [rd7]; exact Memory.readable_of_writable (hw6 b (by omega) (by omega)))
  obtain ⟨ω9, μ9, run9, i0, i1, i5, i6, fr9, rd9, wr9⟩ := memcpy_frame (p := p) (P := P) (R := accKeepK cap env) x ω8 μ7 2194 49529
    (S - 120) D (S - 120 + 8) 96 h80 h81 h87 h88 h89 (by decide) jte_1096 bs_49529 ⟨by omega, by omega, by omega⟩
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
    (fun b h1 h2 => by rw [rd7]; exact Memory.readable_of_writable (hw6 b (by omega) (by omega)))
    (fun b h1 h2 => by rw [wr7, wr6, wr5, wr14, wr1]; exact hwD b h1 h2)
    (fun b h1 h2 => by rw [wr7]; exact hw6 b (by omega) (by omega))
  -- the outer frame's words, kept since io_entry
  have kO : ∀ b, S - 120 + 104 ≤ b → b < S → μ9.read b = μ1.read b := fun b h1 h2 => by
    rw [fr9 b (by omega) (Or.inl (by omega)) (Or.inr (by omega)), fr7 b (by omega) (Or.inr (by omega)),
      fr6 b (by omega) (Or.inr (Or.inr (by omega))), k15 b (by omega) (Or.inr (by omega))]
  obtain ⟨ω10, run10, j0, j1, j5, j6⟩ := io_c (p := p) (P := P) (R := accKeepK cap env) x ω9 μ9 (S - 120) ret t ω[5].toNat
    ⟨by omega, by omega⟩ (i1.trans h81)
    (by rw [rdN_frame (fun j hj => kO _ (by omega) (by omega))]; exact m112)
    (by rw [rdN_frame (fun j hj => kO _ (by omega) (by omega))]; exact m104) hret hjt hbt
    (fun b h1 h2 => by rw [rd9, rd7, rd6, rd5, rd4, rd2, rd1]; exact Memory.readable_of_writable (hw b (by omega) (by omega)))
  -- the run: the host step after io_a1
  have rest : FreeStepsH p (accKeepK cap env) 48549 ω4 μ4 x t ω10 μ9 x
      (15 + 5000 + 40 + 6 + (7 * 96 + 320) + 5) :=
    (((((run5.trans run6).trans run7).trans run8).trans run9).trans run10)
  have run4 := FreeStepsH.infoSelfK cap hcap env (P := P) (i := 48547) (n := 48549) d_48547 ha c7 c8 c9 c10
    (by omega) (fun b h1 h2 => by rw [wr2, wr1]; exact hw b (by omega) (by omega))
    (by rw [hL, ← hω4, ← hμ4]; exact rest)
  refine ⟨ω10, μ9, (((run1.trans run2).trans run3).trans run4).mono (by omega), j0.trans h0.symm,
    by rw [j1, h1, show S - 120 + 120 = S by omega], ?_, ?_, fun b hb h h' => ?_, fun b => ?_, fun b => ?_⟩
  · rw [j5, UInt64.ofNat_toNat]
  · rw [j6, i6, h86, g6, UInt64.ofNat_toNat]
  · rw [fr9 b hb h' (by omega), fr7 b hb (by omega), fr6 b hb (by omega), fr5 b hb (by omega), fr4 b hb (by omega),
      fr2 b hb (by omega), fr1 b hb (by omega)]
  · rw [rd9, rd7, rd6, rd5, rd4, rd2, rd1]
  · rw [wr9, wr7, wr6, wr5, wr4, wr2, wr1]


theorem log_siteK {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (cap : Nat)
    (hcap : 1000 ≤ cap ∧ cap < 2 ^ 64) (env : AccEnv) (envH : RefineHost.Env) (pb S0 S1 : Nat)
    (x : AccCtx) (ω : Regs) (μ : Memory) (s₀ s : State) (sp : Nat)
    (H : HeapCtx envH pb S0 S1 μ s) (hso : StrOut s₀ s μ (sp + 744)) (h1 : ω[1] = UInt64.ofNat sp)
    (hsp : 2147483716 ≤ sp ∧ S0 + 40 ≤ sp ∧ sp + 768 ≤ S1) :
    ∃ ω' μ' s', FreeStepsH p (accKeepK cap env) 6587 ω μ x 6630 ω' μ' x 300 ∧
      HeapCtx envH pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Outside pb sp (fun _ => False) μ μ' ∧
      (∀ d ∈ chunks s₀, d.used = true → d ∈ chunks s' ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
      ω'[1] = ω[1] ∧ ω'[6] = ω[6] := by
  have hS1 := H.hS1
  have hst := H.st
  obtain ⟨scap, slen, hs⟩ := hso
  have hr : ∀ a, sp + 744 ≤ a → a < sp + 768 → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (hst a (by omega) (by omega))
  obtain ⟨ω1, run1, a0, a1, a5, a6⟩ := ls_a (p := p) (P := P) (R := accKeepK cap env) x ω μ sp (by omega) h1 hr
  -- the log call
  have refl : ∀ d ∈ chunks s₀, d.used = true → d ∈ chunks s ∧ ∀ a, InData d a → μ.read a = μ.read a :=
    fun d hd hu => ⟨hs.base d hd hu, fun _ _ => rfl⟩
  have outR : Outside pb sp (fun _ => False) μ μ :=
    ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ => rfl⟩
  have w1 : (setR7 ω1 Result.WHAT)[1] = UInt64.ofNat sp := by
    simp only [setR7, Vector.getElem_set]; simp [a1, h1]
  have w5 : (setR7 ω1 Result.WHAT)[5] = UInt64.ofNat (rdN μ (sp + 752) 8) := by
    simp only [setR7, Vector.getElem_set]; simp [a5]
  have w0 : (setR7 ω1 Result.WHAT)[0] = ω[0] := by simp only [setR7, Vector.getElem_set]; simp [a0]
  have w6 : (setR7 ω1 Result.WHAT)[6] = ω[6] := by simp only [setR7, Vector.getElem_set]; simp [a6]
  by_cases hc0 : scap = 0
  · subst hc0
    obtain ⟨ω2, run2, b0, b1, b5, b6⟩ := ls_b0 (p := p) (P := P) (R := accKeepK cap env) x
      (setR7 ω1 Result.WHAT) μ sp (by omega) w1 hs.rc (fun a h1 h2 => hr a h1 (by omega))
    refine ⟨ω2, μ, s, run1.trans (FreeStepsH.logKeepK cap hcap env (d_6608 (p := p) (P := P)) run2) |>.mono (by omega), H, rfl, outR,
      refl, b1.trans (w1.trans h1.symm), b6.trans w6⟩
  · obtain ⟨c, hc, hcu, hca, -, hcf⟩ := hs.buf.resolve_left hc0
    obtain ⟨ω2, run2, b0, b1, b5, b6, b7⟩ := ls_b (p := p) (P := P) (R := accKeepK cap env) x
      (setR7 ω1 Result.WHAT) μ sp (rdN μ (sp + 744 + 8) 8) (by omega) (rdN_lt64 μ _) w1 w5
      (by rw [hs.rc]; exact hc0) (fun a h1 h2 => hr a h1 (by omega))
    obtain ⟨ω3, μ3, run3, H3, hb3, hpg, hro, stk, hgl, keep3, c0, c1, c5, c6⟩ :=
      Decode.DeallocCall.dealloc_call (R := accKeepK cap env) (p := p) (P := P) envH pb S0 S1 x ω2 μ s sp
        (rdN μ (sp + 744 + 8) 8) 224 6630 c H hc hcu hca b0 (b1.trans w1) b7 (by decide) jte_111 bs_6630 hsp.1
        ⟨hsp.2.1, by omega⟩
    have out3 : Outside pb sp (fun _ => False) μ μ3 :=
      ⟨fun b _ => ⟨by unfold Memory.readable; rw [hpg], by unfold Memory.writable; rw [hpg]⟩,
        fun b hb _ hw => hro b hb hw, fun a ha hb _ => stk a hb ha, hgl⟩
    refine ⟨ω3, μ3, free s (rdN μ (sp + 744 + 8) 8),
      (run1.trans (FreeStepsH.logKeepK cap hcap env (d_6608 (p := p) (P := P)) (run2.trans run3))).mono (by omega),
      H3, hb3, out3, fun d hd hu => ?_, c1.trans (b1.trans (w1.trans h1.symm)),
      c6.trans (b6.trans w6)⟩
    have hd' := hs.base d hd hu
    have hne : d ≠ c := fun e => hcf d hd hu (by rw [e])
    exact keep3 d hd' hu hne


/-- **Accumulate's first log line from the call of `format!` to after the `String`'s `dealloc`**
    (6580 … 6630), frame-only, under `accKeepK cap env` (1000 ≤ cap) and its `AllocOk` and
    `ReallocOk`. From sp = S, with the template at 66464 (`accTmplBytes`), the `String` vtable's
    words (`RoW`) and the argument pairs `Acc.fmt_setup` stores at S + 1144 … S + 1192, it either
    reaches 6630 with the allocator's context kept (same base), ω₁ and ω₆ as they were, and from S
    up only the `String`'s 24 octets at S + 744 changed (`Keeps`); or a failed allocator call. -/
theorem acc_fmt_siteK {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] [HasCodeA p P] (cap : Nat)
    (hcap : 1000 ≤ cap ∧ cap < 2 ^ 64) (env : AccEnv) (envH : RefineHost.Env) (pb S0 S1 : Nat)
    (HA : AllocOk p (accKeepK cap env) envH pb S0 S1)
    (HR : ReallocOk p (accKeepK cap env) envH pb S0 S1)
    (x : AccCtx) (ω : Regs) (μ : Memory) (s : State) (S : Nat)
    (H : HeapCtx envH pb S0 S1 μ s) (hba : s.base % 8 = 0)
    (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat (S + 744)) (h8 : ω[8] = UInt64.ofNat 66464)
    (h9 : ω[9] = UInt64.ofNat (S + 1144))
    (hS : S0 + 800 ≤ S ∧ S % 8 = 0 ∧ 2147484500 ≤ S ∧ S + 1700 ≤ S1)
    (hro : RoW μ) (htm : μ.readN 66464 42 = accTmplBytes)
    (hrt : ∀ a, 66464 ≤ a → a < 66506 → μ.readable a = true)
    (p0 : rdN μ (S + 1144) 8 = S + 260) (p1 : rdN μ (S + 1144 + 8) 8 = 2616)
    (p2 : rdN μ (S + 1144 + 16) 8 = S + 256) (p3 : rdN μ (S + 1144 + 24) 8 = 2800)
    (p4 : rdN μ (S + 1144 + 32) 8 = S + 1600) (p5 : rdN μ (S + 1144 + 40) 8 = 2804) :
    (∃ ω' μ' x' s', FreeStepsH p (accKeepK cap env) 6580 ω μ x 6630 ω' μ' x'
        (1 + fmtCost 20 2900 accTmpl + 300) ∧
      HeapCtx envH pb S0 S1 μ' s' ∧ s'.base = s.base ∧
      Keeps pb S (fun a => S + 744 ≤ a ∧ a < S + 744 + 24) s μ μ' s' ∧ ω'[1] = ω[1] ∧ ω'[6] = ω[6]) ∨
    Exhausts p (accKeepK cap env) pb 6580 ω μ x (1 + fmtCost 20 2900 accTmpl) := by
  have hst := H.st
  have hS1 := H.hS1
  have hSb := H.hSb
  have hrd : ∀ a, S0 ≤ a → a < S1 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hst a h1 h2)
  obtain ⟨ω1, run1, a0, a1, a5, a6, a7, a8, a9⟩ := site_call (p := p) (P := P) (R := accKeepK cap env) x ω μ
  -- the arguments
  have hA : ArgsAt p P (accKeepK cap env) envH pb S0 S1 600 μ s S (S + 1144) 0 accTmpl 20 2900 := by
    intro j hj
    simp only [accTmpl, nargs] at hj
    have hr16 : ∀ j, j < 3 → ∀ a, S + 1144 + 16 * (0 + j) ≤ a → a < S + 1144 + 16 * (0 + j) + 16 →
        μ.readable a = true := fun j hj a h1 h2 => hrd a (by omega) (by omega)
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
    · refine ⟨S + 260, 2616, 60525, by omega, by omega, hr16 0 (by omega), by simpa using p0,
        by simpa using p1, by decide, jte_1307, bs_60525, ?_⟩
      exact (hex32_ok (p := p) (P := P) envH pb S0 S1 600 (Nat.le_refl _) HA HR μ s S (S + 260) (by omega) ⟨by omega, by omega⟩
        (fun a h1 h2 => hrd a (by omega) (by omega))).mono (by omega) (by omega)
    · refine ⟨S + 256, 2800, 68146, by omega, by omega, hr16 1 (by omega), by simpa using p2,
        by simpa using p3, by decide, jte_1399, bs_68146, ?_⟩
      exact (dec32_ok (p := p) (P := P) envH pb S0 S1 600 (Nat.le_refl _) HA HR μ s S (S + 256) (by omega) ⟨by omega, by omega⟩
        (fun a h1 h2 => hrd a (by omega) (by omega))).mono (by omega) (by omega)
    · refine ⟨S + 1600, 2804, 68449, by omega, by omega, hr16 2 (by omega), by simpa using p4,
        by simpa using p5, by decide, jte_1401, bs_68449, ?_⟩
      exact (dec64_ok (p := p) (P := P) envH pb S0 S1 600 (Nat.le_refl _) HA HR μ s S (S + 1600) (by omega) ⟨by omega, by omega⟩
        (fun a h1 h2 => hrd a (by omega) (by omega))).mono (by omega) (by omega)
  rcases format_inner (p := p) (P := P) (R := accKeepK cap env) envH pb S0 S1 600 (Nat.le_refl _) HA HR S (S + 744) 66464
      (S + 1144) 222 6587 20 2900 accTmpl x ω1 μ s H hba a0 (a1.trans h1) (a7.trans h7) (a8.trans h8)
      (a9.trans h9) (by decide) jte_110 bs_6587 ⟨by omega, hS.2.1, by omega, by omega⟩ ⟨by omega, by omega⟩
      hro (tmpl_acc htm hrt) (by simp [accTmpl, tsize]) ⟨by omega, by omega⟩ hA (by simp [accTmpl, nargs])
      (by simp [accTmpl, tlen]) with
    ⟨ω2, μ2, x2, s2, run2, H2, hb2, K2, hso, b0, b1, b5, b6⟩ | hx
  · obtain ⟨ω3, μ3, s3, run3, H3, hb3, out3, keep3, c1, c6⟩ := log_siteK (p := p) (P := P) cap hcap env envH pb S0 S1
      x2 ω2 μ2 s s2 S H2 hso (b1.trans (a1.trans h1)) ⟨by omega, by omega, by omega⟩
    have K3 : Keeps pb S (fun a => S + 744 ≤ a ∧ a < S + 744 + 24) s μ2 μ3 s3 :=
      ⟨⟨out3.access, out3.ro, fun a ha hb _ => out3.hi a ha hb (fun h => h), out3.glob⟩,
        fun d hd hu => (keep3 d hd hu).1, fun d hd hu a ha => (keep3 d hd hu).2 a ha⟩
    have K := K2.trans' K3
    rw [Nat.max_self] at K
    exact Or.inl ⟨ω3, μ3, x2, s3, (run1.trans (run2.trans run3)).mono (by omega), H3, hb3.trans hb2, K,
      c1.trans (b1.trans a1), c6.trans (b6.trans a6)⟩
  · exact Or.inr (Exhausts.pre run1 hx)

/-- (`Acc.fmt_setup`, also stating the spills at sp + 136 and sp + 208.) 6508 … 6576: after `info`, the arguments of the first log line's `format!`: the fmt::Arguments
    pairs (value address, formatter) at sp + 1144 … sp + 1191 for s (sp + 260, 2616), t (sp + 256,
    2800) and the info record (sp + 1600, 2804), spills at sp + 80, sp + 136 and sp + 208; then ω₇ =
    sp + 744 (the `String`), ω₈ = 66464 (the pieces) and ω₉ = sp + 1144 for the call at 6580. -/
theorem fmt_setup2 {X : Type} {R : HostRel X} {p : ByteArray} {P : Program} [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (h1 : ω[1] = UInt64.ofNat 4278057152)
    (hw1 : ∀ a, 4278057232 ≤ a → a < 4278057240 → μ.writable a = true)
    (hw2 : ∀ a, 4278057288 ≤ a → a < 4278057296 → μ.writable a = true)
    (hw3 : ∀ a, 4278057360 ≤ a → a < 4278057368 → μ.writable a = true)
    (hw4 : ∀ a, 4278058296 ≤ a → a < 4278058344 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 6508 ω μ x 6580 ω' μ' x 18 ∧
      ω'[1] = UInt64.ofNat 4278057152 ∧ ω'[7] = UInt64.ofNat 4278057896 ∧ ω'[8] = UInt64.ofNat 66464 ∧
      ω'[9] = UInt64.ofNat 4278058296 ∧
      ω'[0] = ω[0] ∧ ω'[2] = ω[2] ∧ ω'[3] = ω[3] ∧ ω'[4] = ω[4] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      μ'.readN 4278058296 8 = Num.encodeLE 8 4278057412 ∧ μ'.readN 4278058304 8 = Num.encodeLE 8 2616 ∧
      μ'.readN 4278058312 8 = Num.encodeLE 8 4278057408 ∧ μ'.readN 4278058320 8 = Num.encodeLE 8 2800 ∧
      μ'.readN 4278058328 8 = Num.encodeLE 8 4278058752 ∧ μ'.readN 4278058336 8 = Num.encodeLE 8 2804 ∧
      μ'.readN 4278057288 8 = Num.encodeLE 8 2804 ∧ μ'.readN 4278057360 8 = Num.encodeLE 8 2800 ∧
      (∀ a, a < 4294967296 → (a < 4278057232 ∨ 4278057240 ≤ a) → (a < 4278057288 ∨ 4278057296 ≤ a) →
        (a < 4278057360 ∨ 4278057368 ≤ a) → (a < 4278058296 ∨ 4278058344 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr1 := fun a h1 h2 => Memory.readable_of_writable (hw1 a h1 h2)
  have hr2 := fun a h1 h2 => Memory.readable_of_writable (hw2 a h1 h2)
  have hr3 := fun a h1 h2 => Memory.readable_of_writable (hw3 a h1 h2)
  have hr4 := fun a h1 h2 => Memory.readable_of_writable (hw4 a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, hw1, hw2, hw3, hw4, hr1, hr2, hr3, hr4]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1]
    all_goals try rfl
    all_goals try (simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_same, PVM.Memory.readN_writeN_disjoint,
      PVM.Num.length_encodeLE, List.length_cons, List.length_nil, PVM.two32]; done)
    all_goals try (intro a; simp only [PVM.Memory.readable_writeN, PVM.Memory.writable_writeN]; done)
    all_goals try (intro a ha h1 h2 h3 h4
                   simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint, PVM.Num.length_encodeLE,
                     List.length_cons, List.length_nil, PVM.two32])


/-- **Accumulate's first log line, frame-only** (6501 … 6630, sp = 4278057152): `info` of the
    service itself (`info_selfK`), the `format!` arguments (`Acc.fmt_setup`), `format!`, `log` (the
    message unspecified) and the `String`'s `dealloc`. Under `accKeepK cap env`
    (1000 ≤ cap) and its `AllocOk`/`ReallocOk`, given the service's own account a in the context
    with an `info` record shorter than 2⁶⁴ − 9 octets, the template's octets at 66464 and the
    `String` vtable's words (`RoW`), it either reaches 6630 with the allocator's context kept (same
    base), ω₁ kept, and from sp up only `logE` changed (`Keeps`); or a failed allocator call. -/
theorem acc_log_lineK {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] [HasCodeA p P] (cap : Nat)
    (hcap : 1000 ≤ cap ∧ cap < 2 ^ 64) (env : AccEnv) (envH : RefineHost.Env) (pb S0 S1 : Nat)
    (HA : AllocOk p (accKeepK cap env) envH pb S0 S1)
    (HR : ReallocOk p (accKeepK cap env) envH pb S0 S1)
    (x : AccCtx) (a : ServiceAccount) (ha : x.1.state.accounts.get? x.1.id = some a)
    (hlen : (infoValue a).length < 18446744073709551607)
    (ω : Regs) (μ : Memory) (s : State)
    (H : HeapCtx envH pb S0 S1 μ s) (hba : s.base % 8 = 0)
    (h1 : ω[1] = UInt64.ofNat 4278057152) (h7 : ω[7] = UInt64.ofNat (4278057152 + 1568))
    (hS : S0 + 800 ≤ 4278057152 - 488 ∧ 4278057152 + 1700 ≤ S1)
    (hro : RoW μ) (htm : μ.readN 66464 42 = accTmplBytes)
    (hrt : ∀ a, 66464 ≤ a → a < 66506 → μ.readable a = true) :
    (∃ ω' μ' x' s', FreeStepsH p (accKeepK cap env) 6501 ω μ x 6630 ω' μ' x'
        (8020 + (1 + fmtCost 20 2900 accTmpl + 300)) ∧
      HeapCtx envH pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Keeps pb 4278057152 (logE 4278057152) s μ μ' s' ∧
      ω'[1] = ω[1] ∧ rdN μ' (4278057152 + 136) 8 = 2804 ∧ rdN μ' (4278057152 + 208) 8 = 2800) ∨
    Exhausts p (accKeepK cap env) pb 6501 ω μ x (8020 + (1 + fmtCost 20 2900 accTmpl)) := by
  have hst := H.st
  have hS1 := H.hS1
  have hSb := H.hSb
  have hro0 := H.ro
  obtain ⟨ω1, run1, a0, a1, a5, a6, a7⟩ := site_info (p := p) (P := P) (R := accKeepK cap env) x ω μ
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, fr2, rd2, wr2⟩ := info_selfK (p := p) (P := P) cap ⟨by omega, hcap.2⟩
    env x a ha hlen ω1 μ 4278057152 (4278057152 + 1568) 220 6508 a0 (a1.trans h1) (a7.trans h7) (by decide)
    jte_109 bs_6508 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (fun b h1 h2 => hst b (by omega) (by omega))
    (fun b h1 h2 => hst b (by omega) (by omega))
  obtain ⟨ω3, μ3, run3, c1, c7, c8, c9, -, -, -, -, -, -, m0, m1, m2, m3, m4, m5, n136, n208, fr3, rd3, wr3⟩ :=
    fmt_setup2 (p := p) (P := P) (R := accKeepK cap env) x ω2 μ2 (b1.trans (a1.trans h1))
      (fun b h1 h2 => by rw [wr2]; exact hst b (by omega) (by omega))
      (fun b h1 h2 => by rw [wr2]; exact hst b (by omega) (by omega))
      (fun b h1 h2 => by rw [wr2]; exact hst b (by omega) (by omega))
      (fun b h1 h2 => by rw [wr2]; exact hst b (by omega) (by omega))
  -- the frame of info and the set-up
  have k3 : ∀ b, b < 4294967296 → ¬ ((4278057152 - 488 ≤ b ∧ b < 4278057152) ∨ logE 4278057152 b) →
      μ3.read b = μ.read b := fun b hb hn => by
    unfold logE at hn
    rw [fr3 b hb (by omega) (by omega) (by omega) (by omega), fr2 b hb (by omega) (by omega)]
  have wr13 : ∀ b, μ3.writable b = μ.writable b := fun b => by rw [wr3, wr2]
  have rd13 : ∀ b, μ3.readable b = μ.readable b := fun b => by rw [rd3, rd2]
  have K1 : Keeps pb 4278057152 (logE 4278057152) s μ μ3 s :=
    Keeps.of_frame (Z := fun b => (4278057152 - 488 ≤ b ∧ b < 4278057152) ∨ logE 4278057152 b) (fun _ h _ => h)
      k3 rd13 wr13 (fun b hz => by unfold logE at hz; exact hst b (by omega) (by omega))
      (fun b hz hb => by rcases hz with hz | hz; · omega
                         · exact hz)
      (fun b hz hg => by unfold Glob at hg; unfold logE at hz; omega)
      (fun d hd hu b hb => by
        have := chunk_bounds H.wf hd
        have := H.hbT
        unfold InData at hb; unfold logE; omega)
  have H3 : HeapCtx envH pb S0 S1 μ3 s := ctx_hi H (fun b hb => k3 b (by omega) (by unfold logE; omega)) wr13
  have klow : ∀ b, b < 196608 → μ3.read b = μ.read b ∧ μ3.readable b = μ.readable b := fun b hb =>
    ⟨k3 b (by omega) (by unfold logE; omega), rd13 b⟩
  have hp : ∀ (v : Nat) (o : Nat), μ3.readN o 8 = Num.encodeLE 8 v → v < 18446744073709551616 → rdN μ3 o 8 = v :=
    fun v o h hv => rdN_of_readN h hv
  rcases acc_fmt_siteK (p := p) (P := P) cap hcap env envH pb S0 S1 HA HR x ω3 μ3 s 4278057152 H3 hba
      c1 c7 c8 c9 ⟨by omega, by decide, by decide, by omega⟩
      (hro.congr (fun b h1 h2 => klow b h2))
      (by rw [readN_congr2 (b := 66464) (fun j hj => (klow _ (by omega)).1)]; exact htm)
      (fun b h1 h2 => by rw [(klow b (by omega)).2]; exact hrt b h1 h2)
      (hp _ _ m0 (by decide)) (hp _ _ m1 (by decide)) (hp _ _ m2 (by decide)) (hp _ _ m3 (by decide))
      (hp _ _ m4 (by decide)) (hp _ _ m5 (by decide)) with
    ⟨ω4, μ4, x4, s4, run4, H4, hb4, K4, d1, -⟩ | hx
  · have K := K1.trans' (K4.mono (Nat.le_refl _) (fun b hb => by unfold logE; omega))
    rw [Nat.max_self] at K
    have k4 : ∀ o, (o = 4278057152 + 136 ∨ o = 4278057152 + 208) → rdN μ4 o 8 = rdN μ3 o 8 := fun o ho =>
      rdN_frame fun j hj => K4.hi _ (by omega) (by omega) (by omega)
    exact Or.inl ⟨ω4, μ4, x4, s4, ((run1.trans run2).trans (run3.trans run4)).mono (by omega), H4, hb4, K,
      d1.trans (c1.trans h1.symm), by rw [k4 _ (.inl rfl)]; exact hp _ _ n136 (by decide),
      by rw [k4 _ (.inr rfl)]; exact hp _ _ n208 (by decide)⟩
  · exact Or.inr ((Exhausts.pre ((run1.trans run2).trans run3) hx).mono (by omega))

end Services.Bootstrap.Fmt
