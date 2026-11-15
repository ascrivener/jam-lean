import Services.Bootstrap.Decode.AllocZeroedCall

/-!
# One call of `alloc_impl` with a huge request, the lock held

A caller that sizes its request with a 32-bit add (`add_32`, GP v0.8.0 Appendix A, whose result is
sign-extended to 64 bits, X₄) may pass `alloc_impl` (41177) a unit request req ≥ 2³¹: the
sign-extension of a 32-bit sum with its top bit set, so req ≥ 2⁶⁴ − 2³¹. `alloc_impl` sizes the
request in 32-bit arithmetic as well: 41221 sets ω₄ = X₄((req + 1) mod 2³²) and 41228 ω₁₂ the same
sum (alignment one unit), then

* 41224: ω₄ = 0 (req mod 2³² = 2³² − 1) branches to 41401, which sets ω₁₁ = 0;
* 41231 … 41237: otherwise ω₁₁ = 0, ω₁₂ = ω₄ (so 41233's `branch_lt_u` is not taken) and
  ω₁₂ > 2²⁵ (`MAX_ALLOCATION_SIZE`) branches to 41404,

so in both cases the failure tail 41404 … 41423 returns ω₁₁ = 0: null, with only the frame
(sp − 152 … sp) written and no growth attempted. All that is needed of req is that its low 32 bits
are at least 2²⁵; for a sign-extended req ≥ 2⁶⁴ − 2³¹ they are at least 2³¹.
-/

namespace Services.Bootstrap.Decode.AllocHuge

open PVM Picoalloc Services.Bootstrap.Code Services.Bootstrap.Alloc JAM
open Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.DeallocCall
open Services.Bootstrap.Decode.AllocZeroedCall

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **41221 … 41404, req mod 2³² = 2³² − 1**: the 32-bit sum req + 1 is 0, so 41224 branches to
    41401, which sets ω₁₁ = 0. -/
theorem al_huge_wrap {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (req : Nat) (h9 : ω[9] = UInt64.ofNat req)
    (hrq : req < 18446744073709551616) (hr : req % 4294967296 = 4294967295) :
    ∃ ω', FreeStepsH p R 41221 ω μ x 41404 ω' μ x 6 ∧ ω'[11] = UInt64.ofNat 0 ∧
      ∀ j : Fin 13, j.val ∉ [4, 11, 12] → ω'[j] = ω[j] := by
  have e : (req + 1) % 4294967296 = 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h9, Nat.mod_eq_of_lt hrq, e]
  case post => exact ⟨by reg_val, by reg_frame⟩

/-- **41221 … 41404, 2²⁵ ≤ req mod 2³² < 2³² − 1**: the 32-bit sum v = (req + 1) mod 2³² is not 0
    and its sign-extension is above 2²⁵, so 41237 branches to 41404 with ω₁₁ = 0. -/
theorem al_huge_big {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (req : Nat) (h9 : ω[9] = UInt64.ofNat req) (h8 : ω[8] = UInt64.ofNat 1)
    (hrq : req < 18446744073709551616) (hr : 33554432 ≤ req % 4294967296)
    (hr1 : req % 4294967296 < 4294967295) :
    ∃ ω', FreeStepsH p R 41221 ω μ x 41404 ω' μ x 6 ∧ ω'[11] = UInt64.ofNat 0 ∧
      ∀ j : Fin 13, j.val ∉ [4, 11, 12] → ω'[j] = ω[j] := by
  obtain ⟨v, e⟩ : ∃ v, (req + 1) % 4294967296 = v := ⟨_, rfl⟩
  have e' : (1 + req) % 4294967296 = v := by rw [Nat.add_comm]; exact e
  have hv0 : 33554432 < v := by omega
  have hv1 : v < 4294967296 := by omega
  rw [show ω = regsNF ω [] from rfl]
  by_cases hs : v < 2147483648
  · have d : v / 2147483648 = 0 := by omega
    refine ⟨?ω', ?run, ?post⟩
    case run => pvm_go [h9, h8, Nat.mod_eq_of_lt hrq, e, e', d,
      Nat.mod_eq_of_lt (show v < 18446744073709551616 by omega), show v ≠ 0 by omega,
      show ¬ v ≤ 33554432 by omega]
    case post => exact ⟨by reg_val, by reg_frame⟩
  · have d : v / 2147483648 = 1 := by omega
    obtain ⟨w, hw⟩ : ∃ w, v + 18446744069414584320 = w := ⟨_, rfl⟩
    have hw0 : 33554432 < w := by omega
    have hw1 : w < 18446744073709551616 := by omega
    refine ⟨regsNF ω [(4, UInt64.ofNat w), (11, UInt64.ofNat 0), (12, UInt64.ofNat w)], ?run, ?post⟩
    case run => pvm_go [h9, h8, Nat.mod_eq_of_lt hrq, e, e', d, hw, Nat.mod_eq_of_lt hw1,
      show w ≠ 0 by omega, show ¬ w ≤ 33554432 by omega, hw0]
    case post => exact ⟨by reg_val, by reg_frame⟩

/-- **41221 … 41404, a huge request**: req's low 32 bits at least 2²⁵; ω₁₁ = 0 for the failure tail. -/
theorem al_huge {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (req : Nat) (h9 : ω[9] = UInt64.ofNat req) (h8 : ω[8] = UInt64.ofNat 1)
    (hrq : req < 18446744073709551616) (hr : 33554432 ≤ req % 4294967296) :
    ∃ ω', FreeStepsH p R 41221 ω μ x 41404 ω' μ x 6 ∧ ω'[11] = UInt64.ofNat 0 ∧
      ∀ j : Fin 13, j.val ∉ [4, 11, 12] → ω'[j] = ω[j] := by
  by_cases he : req % 4294967296 = 4294967295
  · exact al_huge_wrap (p := p) (P := P) x ω μ req h9 hrq he
  · exact al_huge_big (p := p) (P := P) x ω μ req h9 h8 hrq hr (by omega)

/-- **41177 … 41423, a huge request**: null returned, only the frame written. -/
theorem alloc_fail_huge {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp req base : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792)
    (h8 : ω[8] = UInt64.ofNat 1) (h9 : ω[9] = UInt64.ofNat req) (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb : rdN μ 206520 8 = base) (hb0 : base ≠ 0) (hrq : req < 18446744073709551616)
    (hr : 33554432 ≤ req % 4294967296)
    {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hSTk : S0 + 152 ≤ sp ∧ sp ≤ S1) (hwr : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 41177 ω μ x 41423 ω' μ' x 30 ∧ ω'[7] = UInt64.ofNat 0 ∧
      ω'[0] = ω[0] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[1] = ω[1] ∧
      (∀ a, μ'.writable a = μ.writable a) ∧
      (∀ a, a < 4294967296 → (a < sp - 152 ∨ sp ≤ a) → μ'.read a = μ.read a) := by
  have hb64 : base < 18446744073709551616 := by rw [← hb]; exact rdN_lt64 μ _
  obtain ⟨ω1, μ1, r1, a1, a11, -, st0, st5, st6, -, -, sf1, ww1, g1⟩ :=
    al_pro (p := p) (P := P) (R := R) x ω μ sp 0 base h1 h7 (by rw [h8]) (by decide) hsp hsp1 hb (by omega) hSTk hwr
  have r2 := al_br_used (p := p) (P := P) (R := R) x ω1 μ1 base a11 hb0 hb64
  obtain ⟨ω2, r3, b11, g3⟩ := al_huge (p := p) (P := P) (R := R) x ω1 μ1 req
    (by rw [fget g1 9 (by decide) (by decide)]; exact h9) (by rw [fget g1 8 (by decide) (by decide)]; exact h8) hrq hr
  obtain ⟨ω3, r4, d7, d0, d5, d6, d1, -⟩ := an_ret (p := p) (P := P) (R := R) x ω2 μ1 (sp - 152)
    (by rw [fget g3 1 (by decide) (by decide)]; exact a1) (by omega) hHTs ⟨by omega, by omega⟩ (hwr.of_eq ww1).rd
  refine ⟨ω3, μ1, (((r1.trans r2).trans r3).trans r4).mono (by omega), by rw [d7, b11], ?_, ?_, ?_, ?_, ww1, sf1⟩
  · rw [d0, show sp - 152 + 144 = sp - 8 by omega]; exact rd_restore st0
  · rw [d5, show sp - 152 + 136 = sp - 16 by omega]; exact rd_restore st5
  · rw [d6, show sp - 152 + 128 = sp - 24 by omega]; exact rd_restore st6
  · rw [d1, h1]; congr 1; omega

set_option linter.unusedVariables false in
/-- **One call of `alloc_impl` (41177) with a huge request, the lock held**, under `HeapHost`'s
    relation (any cap): with ω₇ = 196792 (the allocator), ω₈ = 1 (alignment one unit),
    ω₉ = req ≥ 2³¹ units whose low 32 bits are at least 2²⁵ (`hlo`; so for every sign-extended
    32-bit value req ≥ 2⁶⁴ − 2³¹), any zero flag ω₁₀ = z, and a return address ω₀ that **j**
    (GP v0.8.0 Appendix A, the dynamic jump) resolves to tg, the call returns null (ω₇ = 0) at tg in
    31 steps without a host call: the state is unchanged (s' = s) and the context, lock held, kept,
    the allocated chunks' data, the stack from sp up and the access kept, and ω₀, ω₁, ω₅, ω₆
    restored. The cap bounds, the zero flag and req ≥ 2³¹ are not needed by the proof (no host call is
    made and the flag is never read on this path); they are kept so the call matches
    `alloc_implZ_callG`'s shape. -/
theorem alloc_impl_huge_callG {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    (x : X) (ω : Regs) (μ : Memory) (s : State) (sp req z ret tg pb S0 S1 : Nat)
    (H : HeapCtxL env.code pb S0 S1 μ s)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat 1)
    (h9 : ω[9] = UInt64.ofNat req) (h10 : ω[10] = UInt64.ofNat z) (hz : z < 18446744073709551616)
    (h0 : ω[0] = UInt64.ofNat ret) (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = tg) (hbt : P.isBlockStart tg = true)
    (hreq : 2147483648 ≤ req) (hrq : req < 18446744073709551616) (hlo : 33554432 ≤ req % 4294967296)
    (hsp : 2147483800 ≤ sp) (hSTk : S0 + 152 ≤ sp ∧ sp ≤ S1) :
    ∃ s' ω' μ', FreeStepsH p (env.rel cap) 41177 ω μ x tg ω' μ' x 31 ∧ ω'[7] = UInt64.ofNat 0 ∧
      HeapCtxL env.code pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (∀ d ∈ chunks s, d.used = true → ∀ a, d.addr + 32 ≤ a → a < d.addr + 32 * d.size → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧ μ'.writable 206848 = true ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  obtain ⟨μ₀, H₀, hag, hwa⟩ := H
  obtain ⟨ph, h48, hhb, hp0, hHTs, hHT⟩ := H₀.pages
  have hp : HeapPages μ 48 pb ph := HeapPages.of_eq hp0 hwa
  have hsp1 : sp < 4294967296 := by have := H₀.hS1; omega
  have rep : Rep μ s := H₀.rep.congr_lock H₀.wf H₀.hb0 H₀.hbT fun a ha1 ha2 ha3 => hag a (by omega) (Or.inr (by
    unfold A0 at ha1; omega)) ha3
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := fun a h1 h2 => by rw [hwa]; exact H₀.st a h1 h2
  have hro : ∀ a, a < 196608 → μ.writable a = false := fun a ha => by rw [hwa]; exact H₀.ro a ha
  have hbase : rdN μ 206520 8 = s.base := by have := rep.base; unfold A0 at this; exact this
  obtain ⟨ω', μ', run, e7, e0, e5, e6, e1, ww, fr⟩ := alloc_fail_huge (p := p) (P := P) (R := env.rel cap)
    x ω μ sp req s.base h1 h7 h8 h9 hsp hsp1 hbase H₀.wf.1 hrq hlo hHTs hSTk (HeapPages.wrAt hp hhb hst)
  have ht := H₀.wf.2.2.2.1
  unfold TilesOk at ht
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hst' : ∀ a, S0 ≤ a → a < S1 → μ'.writable a = true := fun a h1 h2 => by rw [ww]; exact hst a h1 h2
  have hp' : HeapPages μ' 48 pb ph := HeapPages.of_eq hp ww
  refine ⟨s, ω', μ', (run.trans (ai_ret (R := env.rel cap) (p := p) (P := P) x ω' μ' ret tg (e0.trans h0) hret
      hjt hbt)).mono (by omega), e7,
    heldOf H₀ H₀.wf (rep.congr_lock H₀.wf H₀.hb0 H₀.hbT fun a _ ha2 _ => fr a (by omega) (Or.inl (by omega)))
      H₀.fo H₀.hb0 H₀.hbT H₀.hA ⟨ph, h48, hhb, hp', hHTs, hHT⟩ hst'
      (fun a ha => by rw [ww]; exact hro a ha),
    fun c hc _ => hc, fun d hd _ a _ h2 => ?_, fun a ha h' => fr a ha (Or.inr h'), hst',
    (HeapPages.wrAt hp' hhb hst') 206848 (Or.inl ⟨by omega, by omega⟩), e0, e1, e5, e6⟩
  have := ht.mem_lt d hd
  have := H₀.hbT
  exact fr a (by omega) (Or.inl (by omega))

end Services.Bootstrap.Decode.AllocHuge
