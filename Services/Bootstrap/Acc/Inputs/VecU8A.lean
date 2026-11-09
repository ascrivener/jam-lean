import Services.Bootstrap.Acc.Inputs.ReadVecCall
import Services.Bootstrap.Acc.DecodeU32A

/-!
# Accumulate's length-prefixed `Vec<u8>` decoder (39634)

39634 decodes ↕**v** (GP v0.8.0 (C)): the length n by the `u32` decoder (39710,
`decodeU32A`), then n octets by the `Vec<u8>` reader (45643, `rv_call` / `rv_empty`), into a
`Vec<u8>` at `out`; a failed length decode writes −1 at `out`. Here n ≤ 16384, one chunk: a
**temporary** bound, lifted once the realloc impl lemmas take any return address.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **39634 … 39710**: the 24-octet frame (ω₀, ω₅, ω₆ at sp − 8, − 16, − 24), `out` kept in ω₅
    and the reader in ω₆, and the call of the `u32` decoder on the reader (return address 1958). -/
theorem vv_pre {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp out rd : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat out) (h8 : ω[8] = UInt64.ofNat rd)
    (hsp : 65536 + 24 ≤ sp ∧ sp < 4294967296) (hout : out < 18446744073709551616)
    (hrd : rd < 18446744073709551616)
    (hwf : ∀ a, sp - 24 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 39634 ω μ x 39710 ω' μ' x 10 ∧
      ω'[0] = UInt64.ofNat 1958 ∧ ω'[1] = UInt64.ofNat (sp - 24) ∧ ω'[5] = UInt64.ofNat out ∧
      ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat rd ∧
      rdN μ' (sp - 8) 8 = ω[0].toNat ∧ rdN μ' (sp - 16) 8 = ω[5].toNat ∧ rdN μ' (sp - 24) 8 = ω[6].toNat ∧
      (∀ a, a < 4294967296 → (a < sp - 24 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 24 ≤ a → a < sp → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h7, h8, hwf, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h7, h8]
    all_goals try with_reducible rfl
    all_goals try simp only [show sp - 24 + 16 = sp - 8 from by omega, show sp - 24 + 8 = sp - 16 from by omega,
      show sp - 24 + 0 = sp - 24 from by omega]
    all_goals try first
      | (rd_simp []; done)
      | rd_simp []
    all_goals try first
      | with_reducible rfl
      | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)
    all_goals first
      | (congr 1; omega)
      | rfl
      | rw [Nat.mod_eq_of_lt (by omega)]

/-- **39656 … 45643**, the length decoded (ω₇ = 0, ω₈ = n < 2³²): the call of the `Vec<u8>` reader
    with ω₇ = out, ω₈ = rd, ω₉ = n (return address 1960). -/
theorem vv_mid {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (out rd n : Nat) (h5 : ω[5] = UInt64.ofNat out) (h6 : ω[6] = UInt64.ofNat rd)
    (h7 : ω[7] = UInt64.ofNat 0) (h8 : ω[8] = UInt64.ofNat n) (hn : n < 4294967296)
    (hout : out < 18446744073709551616) (hrd : rd < 18446744073709551616) :
    ∃ ω', FreeStepsH p R 39656 ω μ x 45643 ω' μ x 10 ∧
      ω'[0] = UInt64.ofNat 1960 ∧ ω'[7] = UInt64.ofNat out ∧ ω'[8] = UInt64.ofNat rd ∧
      ω'[9] = UInt64.ofNat n ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h5, h6, h7, h8]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h5, h6, h8]
    all_goals try with_reducible rfl
    all_goals first
      | rfl
      | (congr 1; omega)
      | (congr 1; rw [Nat.mod_eq_of_lt (by omega)])
      | (congr 1; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)])

/-- **45950 … 39708**: the reader's return through entry 979 (1960) to 39697, ω₀, ω₅, ω₆ restored
    from the 24-octet frame and the frame popped, at the return's `jumpInd`. -/
theorem vv_post {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp r0 r5 r6 : Nat) (h0 : ω[0] = UInt64.ofNat 1960) (h1 : ω[1] = UInt64.ofNat sp)
    (m0 : rdN μ sp 8 = r6) (m8 : rdN μ (sp + 8) 8 = r5) (m16 : rdN μ (sp + 16) 8 = r0)
    (hsp : 65536 ≤ sp ∧ sp + 24 < 4294967296) (hr0 : r0 < 18446744073709551616)
    (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hrf : ∀ a, sp ≤ a → a < sp + 24 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 45950 ω μ x 39708 ω' μ x 10 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (sp + 24) ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 ∧ ω'[7] = ω[7] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h0, h1, m0, m8, m16, hrf, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1]
    all_goals first
      | with_reducible rfl
      | rfl
      | (congr 1; omega)


/-- **One call of the length-prefixed `Vec<u8>` decoder for 1 … 16384 octets** on `HeapCtxC`
    (39634 → 39708): the reader (`rd`, at ip with rlen octets left) holds ℰ(n) and then n octets, all
    inside an allocated chunk's data; n ≤ 16384 is the **temporary** one-chunk bound. Either the n
    octets are in a fresh block with `Vec { cap: n, ptr, len: n }` written at `out`, the context
    kept for the model's new state, every allocated chunk's data kept and the reader advanced past
    ℰ(n) and the octets; or the model's `alloc` fails and the run reaches the trap at 45975. -/
theorem vv_call {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : HeapHost X)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    (x : X) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (sp out rd ip rlen n pb S0 S1 : Nat)
    (H : HeapCtxC env.code pb S0 S1 μ s)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat out) (h8 : ω[8] = UInt64.ofNat rd)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ip) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 rlen)
    (hn : 0 < n ∧ n ≤ 16384) (hrl : (Blob.encodeNat n).length + n ≤ rlen) (hrl32 : rlen < 4294967296)
    (henc : μ.readN ip (Blob.encodeNat n).length = Blob.encodeNat n)
    (hsrc : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ip ∧
      ip + (Blob.encodeNat n).length + n + 32 ≤ c.addr + 32 * c.size)
    (hsp : 2147483960 ≤ sp ∧ sp % 8 = 0) (hSTk : S0 + 440 ≤ sp)
    (hout : sp ≤ out ∧ out + 24 ≤ S1) (hrd : sp ≤ rd ∧ rd + 16 ≤ S1)
    (dor : out + 24 ≤ rd ∨ rd + 16 ≤ out) :
    (∃ ptr s' ω' μ', alloc (growTo pb) hb 1 ((n + 31) / 32) s = some (ptr, s') ∧
      FreeStepsH p (env.rel cap) 39634 ω μ x 39708 ω' μ' x (7 * n + 1800) ∧
      HeapCtxC env.code pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (⟨ptr - 32, (n + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ ⟨ptr - 32, (n + 31) / 32 + 1, true⟩) ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InDataA c a → μ'.read a = μ.read a) ∧
      rdN μ' out 8 = n ∧ rdN μ' (out + 8) 8 = ptr ∧ rdN μ' (out + 16) 8 = n ∧
      μ'.readN ptr n = μ.readN (ip + (Blob.encodeNat n).length) n ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ip + (Blob.encodeNat n).length + n) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (rlen - (Blob.encodeNat n).length - n) ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < out ∨ out + 24 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
        μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6]) ∨
    (alloc (growTo pb) hb 1 ((n + 31) / 32) s = none ∧ ∃ ω' μ',
      FreeStepsH p (env.rel cap) 39634 ω μ x 45975 ω' μ' x (7 * n + 1800)) := by
  obtain ⟨ph, h48, hhb, hp, hHTs, hHT⟩ := H.pages
  have hst := H.st
  obtain ⟨c, hcm, hcu, hci1, hci2⟩ := hsrc
  have hcs := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hcm hcu
  have hbT := H.hbT
  have hb0 := H.hb0
  obtain ⟨w, hw⟩ : ∃ w, (Blob.encodeNat n).length = w := ⟨_, rfl⟩
  rw [hw] at hrl hci2
  -- 1. the frame
  obtain ⟨ω1, μ1, r1, a0, a1, a5, a6, a7, s8, s16, s24, fr1, rd1, wr1⟩ :=
    vv_pre (p := p) (P := P) (R := env.rel cap) x ω μ sp out rd h1 h7 h8 ⟨by omega, by have := H.hS1; omega⟩
      (by have := H.hS1; omega) (by have := H.hS1; omega) (fun a h1 h2 => hst a (by omega) (by omega))
  have m1 : ∀ a, a < 4294967296 → (a < sp - 24 ∨ sp ≤ a) → μ1.read a = μ.read a := fr1
  -- 2. the length
  obtain ⟨ω2, μ2, r2, d0, d1, -, -, -, d5, d6, -, d7, d8, q0, q8, dfr, drd, dwr⟩ :=
    decodeU32A (p := p) (P := P) (R := env.rel cap) x ω1 μ1 1958 39656 (sp - 24) rd ip rlen a0 a1 a7
      (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_978]) bs_39656
      ⟨by omega, by have := H.hS1; omega⟩ ⟨by omega, by have := H.hS1; omega⟩ ⟨by omega, by omega⟩
      (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
      (fun a h1 h2 => by rw [wr1]; exact hst a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr1]; exact hst a (by omega) (by omega))
      (by rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => m1 _ (by have := H.hS1; omega) (by omega))]; exact hR0)
      (by rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => m1 _ (by have := H.hS1; omega) (by omega))]; exact hR8)
      n (by omega) ⟨by omega, hrl32⟩
      (fun a h1 h2 => Memory.readable_of_writable (by
        rw [wr1]; exact heapC_writable_data H hcm hcu ⟨by omega, by omega⟩))
      (by rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => m1 _ (by omega) (Or.inl (by omega)))]; exact henc)
  rw [hw] at q0 q8
  sorry

end Services.Bootstrap.Acc
