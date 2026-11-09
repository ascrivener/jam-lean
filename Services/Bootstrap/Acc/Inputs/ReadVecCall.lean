import Services.Bootstrap.Acc.Inputs.ReadVec
import Services.Bootstrap.Acc.Inputs.FinishGrowCall
import Services.Bootstrap.Alloc.ReallocFallbackTail

/-!
# One call of accumulate's `Vec<u8>` reader (45643) for 1 … 16384 octets, on the allocator's context

`rv_call`: the reader's `len` octets, inside an allocated chunk, are copied into a fresh block, and
`Vec { cap: len, ptr, len }` is written at `out`. The context `HeapCtxC` is kept for the model's
new state, every allocated chunk keeps its data, and the reader is advanced by `len`. Or the
model's `alloc` fails and the run reaches the trap at 45975 (`handle_error`): heap exhaustion.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- An allocated chunk's data. -/
def InDataA (c : Chunk) (a : Nat) : Prop := c.addr + 32 ≤ a ∧ a < c.addr + 32 * c.size

/-- **An allocated chunk's data is writable** (`LoopA.heap_writable_data` on `HeapCtxC`). -/
theorem heapC_writable_data {code : ByteArray} {pb S0 S1 : Nat} {μ : Memory} {s : State}
    (H : HeapCtxC code pb S0 S1 μ s) {c : Chunk} (hc : c ∈ chunks s) (hu : c.used = true) {a : Nat}
    (ha : InDataA c a) : μ.writable a = true := by
  obtain ⟨ph, h48, hhb, hp, hHTs, hHT⟩ := H.pages
  have hsp := H.wf.2.2.2.2.2.2.2
  unfold SpaceOk at hsp
  have h1 := (hsp c hc).1 hu
  have ht := H.wf.2.2.2.1
  unfold TilesOk at ht
  have hm := ht.mem_lt c hc
  have := H.hb0
  unfold InDataA at ha
  have hq := hp (a / 4096) (by omega) (by omega)
  unfold Memory.writable
  rw [show pageSize = 4096 from rfl, hq]
  simp only [decide_eq_true_eq]; omega

/-- **41175 … 45975**, `finish_grow` wrote `Err` (tag 1 at b + 48): the return to 45773 and the
    branch to the trap at 45975 (`handle_error`). -/
theorem rv_fail {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (b : Nat) (h0 : ω[0] = UInt64.ofNat 2058) (h1 : ω[1] = UInt64.ofNat b)
    (m48 : rdN μ (b + 48) 8 = 1) (hb : b + 96 < 4294967296)
    (hrb : ∀ a, b ≤ a → a < b + 96 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 41175 ω μ x 45975 ω' μ x 5 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run⟩
  case run => pvm_go [h0, h1, m48, hrb, ↓rdN_fold, ↓loadI_fold]


/-- **One call of the `Vec<u8>` reader for 1 … 16384 octets** on `HeapCtxC` (see the module doc).
    The reader `rd` (pointer ip, length rlen) and `out` lie in the caller's frame (from sp up); the
    octets ip … ip + len lie in an allocated chunk's data. -/
theorem rv_call {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : HeapHost X)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    (x : X) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (sp out rd ip rlen len pb S0 S1 : Nat)
    (H : HeapCtxC env.code pb S0 S1 μ s)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat out) (h8 : ω[8] = UInt64.ofNat rd)
    (h9 : ω[9] = UInt64.ofNat len)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ip) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 rlen)
    (hlen : 0 < len ∧ len ≤ 16384) (hrl : len ≤ rlen) (hrl32 : rlen < 4294967296)
    (hsrc : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ip ∧ ip + len ≤ c.addr + 32 * c.size)
    (hsp : 2147483936 ≤ sp ∧ sp % 8 = 0) (hSTk : S0 + 288 ≤ sp)
    (hout : sp ≤ out ∧ out + 24 ≤ S1) (hrd : sp ≤ rd ∧ rd + 16 ≤ S1)
    (dor : out + 24 ≤ rd ∨ rd + 16 ≤ out) :
    (∃ ptr s' ω' μ', alloc (growTo pb) hb 1 ((len + 31) / 32) s = some (ptr, s') ∧
      FreeStepsH p (env.rel cap) 45643 ω μ x 45950 ω' μ' x (7 * len + 1200) ∧
      HeapCtxC env.code pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (⟨ptr - 32, (len + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ ⟨ptr - 32, (len + 31) / 32 + 1, true⟩) ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InDataA c a → μ'.read a = μ.read a) ∧
      rdN μ' out 8 = len ∧ rdN μ' (out + 8) 8 = ptr ∧ rdN μ' (out + 16) 8 = len ∧
      μ'.readN ptr len = μ.readN ip len ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ip + len) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (rlen - len) ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < out ∨ out + 24 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
        μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6]) ∨
    (alloc (growTo pb) hb 1 ((len + 31) / 32) s = none ∧ ∃ ω' μ',
      FreeStepsH p (env.rel cap) 45643 ω μ x 45975 ω' μ' x (7 * len + 1200)) := by
  obtain ⟨ph, h48, hhb, hp, hHTs, hHT⟩ := H.pages
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst := H.st
  have rdN_of : ∀ (μ0 : Memory) (a v : Nat), μ0.readN a 8 = Num.encodeLE 8 v → v < 18446744073709551616 →
      rdN μ0 a 8 = v := fun μ0 a v h hv => by
    unfold rdN; rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (by simpa using hv)]
  -- 1. the entry
  obtain ⟨ω1, μ1, r1, a1, a7, a8, a9, a10, a11, a12, a0, a5, a6, sl0, sl40, s8, s16, s24, s88, s80,
      fr1, rd1, wr1⟩ :=
    rv_entry (p := p) (P := P) (R := env.rel cap) x ω μ sp out rd rlen len h1 h7 h8 h9
      (rdN_of μ _ _ hR8 (by omega)) hlen hrl (by omega) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega))) (Or.inr hrd.1)
      (fun a h1 h2 => hst a (by omega) (by omega))
  have H1 : HeapCtxC env.code pb S0 S1 μ1 s :=
    ⟨H.wf, H.rep.congr_lock H.wf H.hb0 H.hbT fun a _ ha2 _ => fr1 a (by omega) (Or.inl (by omega)), H.fo,
      by rw [rdN_frame fun j hj => fr1 _ (by omega) (Or.inl (by omega))]; exact H.lock, H.hb0, H.hbT, H.hA,
      H.bd, ⟨ph, h48, hhb, HeapPages.of_eq hp wr1, hHTs, hHT⟩, hSb, hS1,
      fun a h1 h2 => by rw [wr1]; exact hst a h1 h2, fun a ha => by rw [wr1]; exact H.ro a ha⟩
  -- 2. `finish_grow` for `len` octets, no current block
  have e1 : len * 1 = len := Nat.mul_one len
  rcases fg_new_call (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω1 μ1 s (sp - 96) (sp - 96 + 48) len 1 1
      pb S0 S1 H1 a1 (by rw [a7]; congr 1; omega) a8 a10 a11 a12 ⟨Nat.le_refl _, by decide⟩ (by omega) (by omega)
      (by omega) (by omega) ⟨by omega, by omega⟩ with
    ⟨ptr, s', ω2, μ2, ha, r2, H2, keep, hnew, hfresh, hk, o0, o8, o16, fr2, e0, e1', e5, e6⟩ |
    ⟨ha, ω2, μ2, r2, H2, o0, o8, o16, fr2, e0, e1', e5, e6⟩
  · sorry
  · right
    rw [e1] at ha
    refine ⟨ha, ?_⟩
    obtain ⟨ω3, r3⟩ := rv_fail (p := p) (P := P) (R := env.rel cap) x ω2 μ2 (sp - 96) (by rw [e0, a0])
      (by rw [e1', a1]) (by rw [show sp - 96 + 48 = sp - 48 by omega] at o0; rw [show sp - 96 + 48 = sp - 48 by omega]; exact o0)
      (by omega) (fun a h1 h2 => by
        have := H2.st a (by omega) (by omega)
        exact Memory.readable_of_writable this)
    exact ⟨ω3, μ2, ((r1.trans r2).trans r3).mono (by omega)⟩

end Services.Bootstrap.Acc
