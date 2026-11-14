import Services.Bootstrap.Fmt.LogSite
import Services.Bootstrap.Fmt.Info
import Services.Bootstrap.Acc.Args

/-!
# Accumulate's first log line: `format!` at 6580 and what follows, frame-only

The template at 66464 is `"Bootstrap Service Accumulate, " {s:x} "h @" {t} " $" {balance}`: three
literals and three default-option arguments (`accTmpl`, read off the blob's read-only data). Its
arguments, set up by `Acc.fmt_setup` at sp + 1144, are the u32 at sp + 260 (`{:x}`, 2616 → 60525),
the u32 at sp + 256 (`{}`, 2800 → 68146) and the u64 at sp + 1600 (`{}`, 2804 → 68449).

`acc_fmt_site`: from 6580 to 6630, `format!` (`format_inner`), `log` (the message unspecified) and
the `String`'s `dealloc`; the context is kept, and from sp up only the `String`'s 24 octets at
sp + 744 change. Or a failed allocator call.
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.CodeF Services.Bootstrap.Acc Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- The template at 66464: 30 octets of literal, `{:x}`, 3 octets, `{}`, 2 octets, `{}`. -/
def accTmpl : List TItem := [.lit 30, .arg, .lit 3, .arg, .lit 2, .arg]

/-- The template's 42 octets in the blob's read-only data. -/
def accTmplBytes : List UInt8 := [30, 66, 111, 111, 116, 115, 116, 114, 97, 112, 32, 83, 101, 114, 118, 105, 99,
  101, 32, 65, 99, 99, 117, 109, 117, 108, 97, 116, 101, 44, 32, 192, 3, 104, 32, 64, 192, 2, 32, 36, 192, 0]

theorem rd1_of_readN {μ : Memory} {a n : Nat} {l : List UInt8} (h : μ.readN a n = l) (j : Nat) (hj : j < n) :
    rdN μ (a + j) 1 = (l.getD j 0).toNat := by
  have e := Memory.read_of_readN h j hj
  simp only [rdN, Memory.readN, List.range_one, List.map_cons, List.map_nil, Nat.add_zero, e, Num.decodeLE]
  simp

/-- **The template at 66464 is `accTmpl`**, from its octets. -/
theorem tmpl_acc {μ : Memory} (h : μ.readN 66464 42 = accTmplBytes)
    (hr : ∀ a, 66464 ≤ a → a < 66506 → μ.readable a = true) : Tmpl μ 66464 accTmpl := by
  have r := fun j hj => rd1_of_readN h j hj
  simp only [accTmpl, Tmpl]
  refine ⟨by decide, by decide, (r 0 (by decide)).trans (by decide), fun b h1 h2 => hr b (by omega) (by omega), ?_⟩
  refine ⟨(r 31 (by decide)).trans (by decide), hr _ (by omega) (by omega), ?_⟩
  refine ⟨by decide, by decide, (r 32 (by decide)).trans (by decide), fun b h1 h2 => hr b (by omega) (by omega), ?_⟩
  refine ⟨(r 36 (by decide)).trans (by decide), hr _ (by omega) (by omega), ?_⟩
  refine ⟨by decide, by decide, (r 37 (by decide)).trans (by decide), fun b h1 h2 => hr b (by omega) (by omega), ?_⟩
  refine ⟨(r 40 (by decide)).trans (by decide), hr _ (by omega) (by omega), ?_⟩
  exact ⟨(r 41 (by decide)).trans (by decide), hr _ (by omega) (by omega)⟩

variable {X : Type} {R : HostRel X}

/-- 6580: the call of `format_inner` (59375), returning to 6587 (222). -/
theorem site_call {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory) :
    ∃ ω', FreeStepsH p R 6580 ω μ x 59375 ω' μ x 1 ∧ ω'[0] = UInt64.ofNat 222 ∧ ω'[1] = ω[1] ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧ ω'[9] = ω[9] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go []
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [rdN_lit8]

/-- **Accumulate's first log line from the call of `format!` to after the `String`'s `dealloc`**
    (6580 … 6630), frame-only, under `accContractK cap env` (1000 ≤ cap) and its `AllocOk` and
    `ReallocOk`. From sp = S, with the template at 66464 (`accTmplBytes`), the `String` vtable's
    words (`RoW`) and the argument pairs `Acc.fmt_setup` stores at S + 1144 … S + 1192, it either
    reaches 6630 with the allocator's context kept (same base), ω₁ and ω₆ as they were, and from S
    up only the `String`'s 24 octets at S + 744 changed (`Keeps`); or a failed allocator call. -/
theorem acc_fmt_site {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] [HasCodeA p P] (cap : Nat)
    (hcap : 1000 ≤ cap ∧ cap < 2 ^ 64) (env : AccEnv) (envH : RefineHost.Env) (pb S0 S1 : Nat)
    (HA : AllocOk p (accContractK cap env) envH pb S0 S1)
    (HR : ReallocOk p (accContractK cap env) envH pb S0 S1)
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
    (∃ ω' μ' x' s', FreeStepsH p (accContractK cap env) 6580 ω μ x 6630 ω' μ' x'
        (1 + fmtCost 20 2900 accTmpl + 300) ∧
      HeapCtx envH pb S0 S1 μ' s' ∧ s'.base = s.base ∧
      Keeps pb S (fun a => S + 744 ≤ a ∧ a < S + 744 + 24) s μ μ' s' ∧ ω'[1] = ω[1] ∧ ω'[6] = ω[6]) ∨
    Exhausts p (accContractK cap env) pb 6580 ω μ x (1 + fmtCost 20 2900 accTmpl) := by
  have hst := H.st
  have hS1 := H.hS1
  have hSb := H.hSb
  have hrd : ∀ a, S0 ≤ a → a < S1 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hst a h1 h2)
  obtain ⟨ω1, run1, a0, a1, a5, a6, a7, a8, a9⟩ := site_call (p := p) (P := P) (R := accContractK cap env) x ω μ
  -- the arguments
  have hA : ArgsAt p P (accContractK cap env) envH pb S0 S1 600 μ s S (S + 1144) 0 accTmpl 20 2900 := by
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
  rcases format_inner (p := p) (P := P) (R := accContractK cap env) envH pb S0 S1 600 (Nat.le_refl _) HA HR S (S + 744) 66464
      (S + 1144) 222 6587 20 2900 accTmpl x ω1 μ s H hba a0 (a1.trans h1) (a7.trans h7) (a8.trans h8)
      (a9.trans h9) (by decide) jte_110 bs_6587 ⟨by omega, hS.2.1, by omega, by omega⟩ ⟨by omega, by omega⟩
      hro (tmpl_acc htm hrt) (by simp [accTmpl, tsize]) ⟨by omega, by omega⟩ hA (by simp [accTmpl, nargs])
      (by simp [accTmpl, tlen]) with
    ⟨ω2, μ2, x2, s2, run2, H2, hb2, K2, hso, b0, b1, b5, b6⟩ | hx
  · obtain ⟨ω3, μ3, s3, run3, H3, hb3, out3, keep3, c1, c6⟩ := log_site (p := p) (P := P) cap hcap env envH pb S0 S1
      x2 ω2 μ2 s s2 S H2 hso (b1.trans (a1.trans h1)) ⟨by omega, by omega, by omega⟩
    have K3 : Keeps pb S (fun a => S + 744 ≤ a ∧ a < S + 744 + 24) s μ2 μ3 s3 :=
      ⟨⟨out3.access, out3.ro, fun a ha hb _ => out3.hi a ha hb (fun h => h), out3.glob⟩,
        fun d hd hu => (keep3 d hd hu).1, fun d hd hu a ha => (keep3 d hd hu).2 a ha⟩
    have K := K2.trans' K3
    rw [Nat.max_self] at K
    exact Or.inl ⟨ω3, μ3, x2, s3, (run1.trans (run2.trans run3)).mono (by omega), H3, hb3.trans hb2, K,
      c1.trans (b1.trans a1), c6.trans (b6.trans a6)⟩
  · exact Or.inr (Exhausts.pre run1 hx)

/-- 6501: the call of `info`'s wrapper (49454), returning to 6508 (220). -/
theorem site_info {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory) :
    ∃ ω', FreeStepsH p R 6501 ω μ x 49454 ω' μ x 1 ∧ ω'[0] = UInt64.ofNat 220 ∧ ω'[1] = ω[1] ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = ω[7] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go []
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [rdN_lit8]

/-- The octets accumulate's first log line changes from sp = S up: the fields `Acc.fmt_setup` spills
    (S + 80, S + 136, S + 208, the argument pairs at S + 1144 … S + 1192), the `String` at
    S + 744 … S + 768, and the `info` record at S + 1568 … S + 1664. -/
def logE (S a : Nat) : Prop :=
  (S + 80 ≤ a ∧ a < S + 88) ∨ (S + 136 ≤ a ∧ a < S + 144) ∨ (S + 208 ≤ a ∧ a < S + 216) ∨
  (S + 744 ≤ a ∧ a < S + 768) ∨ (S + 1144 ≤ a ∧ a < S + 1192) ∨ (S + 1568 ≤ a ∧ a < S + 1664)

/-- **Accumulate's first log line, frame-only** (6501 … 6630, sp = 4278057152): `info` of the
    service itself (`info_self`), the `format!` arguments (`Acc.fmt_setup`), `format!`, `log` (the
    message unspecified) and the `String`'s `dealloc`. Under `accContractK cap env`
    (1000 ≤ cap) and its `AllocOk`/`ReallocOk`, given the service's own account a in the context
    with an `info` record shorter than 2⁶⁴ − 9 octets, the template's octets at 66464 and the
    `String` vtable's words (`RoW`), it either reaches 6630 with the allocator's context kept (same
    base), ω₁ kept, and from sp up only `logE` changed (`Keeps`); or a failed allocator call. -/
theorem acc_log_line {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] [HasCodeA p P] (cap : Nat)
    (hcap : 1000 ≤ cap ∧ cap < 2 ^ 64) (env : AccEnv) (envH : RefineHost.Env) (pb S0 S1 : Nat)
    (HA : AllocOk p (accContractK cap env) envH pb S0 S1)
    (HR : ReallocOk p (accContractK cap env) envH pb S0 S1)
    (x : AccCtx) (a : ServiceAccount) (ha : x.1.state.accounts.get? x.1.id = some a)
    (hlen : (infoValue a).length < 18446744073709551607)
    (ω : Regs) (μ : Memory) (s : State)
    (H : HeapCtx envH pb S0 S1 μ s) (hba : s.base % 8 = 0)
    (h1 : ω[1] = UInt64.ofNat 4278057152) (h7 : ω[7] = UInt64.ofNat (4278057152 + 1568))
    (hS : S0 + 800 ≤ 4278057152 - 488 ∧ 4278057152 + 1700 ≤ S1)
    (hro : RoW μ) (htm : μ.readN 66464 42 = accTmplBytes)
    (hrt : ∀ a, 66464 ≤ a → a < 66506 → μ.readable a = true) :
    (∃ ω' μ' x' s', FreeStepsH p (accContractK cap env) 6501 ω μ x 6630 ω' μ' x'
        (8020 + (1 + fmtCost 20 2900 accTmpl + 300)) ∧
      HeapCtx envH pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Keeps pb 4278057152 (logE 4278057152) s μ μ' s' ∧
      ω'[1] = ω[1]) ∨
    Exhausts p (accContractK cap env) pb 6501 ω μ x (8020 + (1 + fmtCost 20 2900 accTmpl)) := by
  have hst := H.st
  have hS1 := H.hS1
  have hSb := H.hSb
  have hro0 := H.ro
  obtain ⟨ω1, run1, a0, a1, a5, a6, a7⟩ := site_info (p := p) (P := P) (R := accContractK cap env) x ω μ
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, fr2, rd2, wr2⟩ := info_self (p := p) (P := P) cap ⟨by omega, hcap.2⟩
    env x a ha hlen ω1 μ 4278057152 (4278057152 + 1568) 220 6508 a0 (a1.trans h1) (a7.trans h7) (by decide)
    jte_109 bs_6508 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (fun b h1 h2 => hst b (by omega) (by omega))
    (fun b h1 h2 => hst b (by omega) (by omega))
  obtain ⟨ω3, μ3, run3, c1, c7, c8, c9, -, -, -, -, -, -, m0, m1, m2, m3, m4, m5, fr3, rd3, wr3⟩ :=
    Acc.fmt_setup (p := p) (P := P) (R := accContractK cap env) x ω2 μ2 (b1.trans (a1.trans h1))
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
  rcases acc_fmt_site (p := p) (P := P) cap hcap env envH pb S0 S1 HA HR x ω3 μ3 s 4278057152 H3 hba
      c1 c7 c8 c9 ⟨by omega, by decide, by decide, by omega⟩
      (hro.congr (fun b h1 h2 => klow b h2))
      (by rw [readN_congr2 (b := 66464) (fun j hj => (klow _ (by omega)).1)]; exact htm)
      (fun b h1 h2 => by rw [(klow b (by omega)).2]; exact hrt b h1 h2)
      (hp _ _ m0 (by decide)) (hp _ _ m1 (by decide)) (hp _ _ m2 (by decide)) (hp _ _ m3 (by decide))
      (hp _ _ m4 (by decide)) (hp _ _ m5 (by decide)) with
    ⟨ω4, μ4, x4, s4, run4, H4, hb4, K4, d1, -⟩ | hx
  · have K := K1.trans' (K4.mono (Nat.le_refl _) (fun b hb => by unfold logE; omega))
    rw [Nat.max_self] at K
    exact Or.inl ⟨ω4, μ4, x4, s4, ((run1.trans run2).trans (run3.trans run4)).mono (by omega), H4, hb4, K,
      d1.trans (c1.trans h1.symm)⟩
  · exact Or.inr ((Exhausts.pre ((run1.trans run2).trans run3) hx).mono (by omega))

end Services.Bootstrap.Fmt
