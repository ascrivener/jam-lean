import Services.Bootstrap.Acc.Transfer.OrPanic
import Services.Bootstrap.Acc.Transfer.Trap
import Services.Bootstrap.Acc.Transfer.Tail
import Services.Bootstrap.Acc.Transfer.Read
import Services.Bootstrap.Acc.Impl.ROKeepS

/-!
# `on_transfer`, the counter's write as `Impl` (7326 → 7399)

Spec `onTransfer`'s second line (GP v0.8.0 §B.7, Ω_W; quirk Q14):
`orPanic (.write "transfer-count" (fixed 4 ((n + 1) % 2 ^ 32)))`, with n = `trCount` of the value read.

`tr_w1` composes, from the state `tr_read` reaches at 7326 (ω₆ = `sxw 4 n`):
- `tr_sk_pre_sx`: n at sp + 1496, (n + 1) mod 2³² at sp + 1568, the helper's frame, 7326 → 40494;
- `sk_call`: `set` of the copied key "transfer-count" with the 4 octets at sp + 1568 (Ω_W on x);
  or `alloc` returned null and the run reaches the trap at 4002 (the `heap` abort);
- `tr_chk_full` (FULL, ω₇ = 3) → 15361 (☇, as `orPanic` of the spec's `error`), or `tr_chk_ok` → 7399.

The state at 7399 is described by `W1Post`.
-/

namespace Services.Bootstrap.Acc
open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Picoalloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Spec
open JAM.Codec (fixed)
open Services.Bootstrap.ASem (argBase outBase writeAcct)
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem sxw4_lt (v : Nat) : sxw 4 v < 18446744073709551616 := by
  simp only [sxw, Exec.u64, Num.unsigned, Num.signed, Nat.reduceMul, Nat.reducePow, Nat.reduceSub]
  split <;> omega

theorem sxw4_succ_mod (n : Nat) (hn : n < 4294967296) :
    (sxw 4 n + 1) % 4294967296 = (n + 1) % 4294967296 := by
  have := sxw_mod 4 n (.inr rfl) (by simpa using hn)
  simp only [Nat.reducePow] at this
  omega

/-- **The state at 7399 after the counter's write**, from s at 7326 with memory μ and registers ω
    (counter n, allocator state s₀, context c, stream f): the context with the counter written, stream f;
    sp in ω₁, ω₅ and ω₆ (= (sxw 4 n + 1) mod 2⁶⁴) as the helper
    restores them; the allocator's context for some state keeping every allocated chunk of s₀ and its
    data; n at sp + 1496 and (n + 1) mod 2³² at sp + 1568 (u32); from sp up nothing else changed; below
    the read-write data (196608) the memory reads and is readable as before; the statics 196616 … 196791
    (`Glob`) kept. -/
def W1Post (env : AccEnv) (pb S0 S1 sp : Nat) (s₀ : State) (μ : Memory) (ω : Regs) (c : AccCtx)
    (f : Stream) (n : Nat) (s' : St Stream) : Prop :=
  s'.i = 7399 ∧ s'.c = (c.1.setSelf (writeAcct c.1.self trKey (fixed 4 ((n + 1) % 2 ^ 32))), c.2) ∧
  s'.q = f ∧ s'.ω[1] = UInt64.ofNat sp ∧ s'.ω[5] = UInt64.ofNat ω[5].toNat ∧
  s'.ω[6] = UInt64.ofNat ((sxw 4 n + 1) % 18446744073709551616) ∧
  (∃ st, HeapCtxC env.code pb S0 S1 s'.μ st ∧
    ∀ d ∈ chunks s₀, d.used = true → d ∈ chunks st ∧ ∀ a, InDataA d a → s'.μ.read a = μ.read a) ∧
  rdN s'.μ (sp + 1496) 4 = n ∧ rdN s'.μ (sp + 1568) 4 = (n + 1) % 4294967296 ∧
  (∀ a, a < 4294967296 → sp ≤ a → (a < sp + 1496 ∨ sp + 1500 ≤ a) → (a < sp + 1568 ∨ sp + 1572 ≤ a) →
    s'.μ.read a = μ.read a) ∧
  (∀ a, a < 196608 → s'.μ.read a = μ.read a ∧ s'.μ.readable a = μ.readable a) ∧
  (∀ a, Glob a → s'.μ.read a = μ.read a)

/-- **`on_transfer`'s counter write implements `orPanic (.write "transfer-count" (fixed 4 ((n+1) % 2³²)))`**
    from 7326, with ω₆ = `sxw 4 n` (n = `trCount` of the stored value, as `tr_read` leaves it).
    The early ☇ is the trap at 4002 (`alloc` of the key's copy returned null), allowed by any `Ab`
    holding at `HeapFailT` states. Premises beyond `tr_read`'s: the key "transfer-count" at 65956 and
    the error table at 69056 … 69076 (read-only data of the blob, see `accRoBytes`). -/
theorem tr_w1 (env : AccEnv) (cap pb : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] {Ab : St Stream → Prop}
    (hAb : ∀ s : St Stream, HeapFailT s → Ab s)
    (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory) (s₀ : State) (sp S0 S1 : Nat)
    (H : HeapCtxC env.code pb S0 S1 μ s₀)
    (h1 : ω[1] = UInt64.ofNat sp)
    (h6 : ω[6] = UInt64.ofNat (sxw 4 (trCount (c.1.self.storage.get? trKey))))
    (hsp : 2147483800 + 128 + 64 ≤ sp ∧ sp % 8 = 0) (hSTk : S0 + 400 ≤ sp ∧ sp + 1856 ≤ S1)
    (hkey : μ.readN 65956 14 = trKey) (hkr : ∀ a, 65956 ≤ a → a < 65970 → μ.readable a = true)
    (ht8 : rdN μ 69072 4 = 4294900408) (ht4 : rdN μ 69056 4 = 4294900402)
    (htr : ∀ a, 69056 ≤ a → a < 69076 → μ.readable a = true)
    (hfit : ∀ w, c.1.self.storage.get? trKey = some w → w.length < 9223372036854775808)
    (Q : Unit → St Stream → Prop)
    (hQ : ∀ s', W1Post env pb S0 S1 sp s₀ μ ω c f (trCount (c.1.self.storage.get? trKey)) s' → Q () s') :
    Impl p (accContractS env) env Ab
      (orPanic (.write trKey (fixed 4 ((trCount (c.1.self.storage.get? trKey) + 1) % 2 ^ 32)))) Q
      ⟨7326, ω, μ, c, f⟩ := by
  generalize hn : trCount (c.1.self.storage.get? trKey) = n at h6 hQ ⊢
  have hn32 : n < 4294967296 := hn ▸ trCount_lt _
  have hst := H.st
  have hS1 := H.hS1
  have hro := H.ro
  -- 7326 → 40494
  obtain ⟨ω1, μ1, run1, a0, a1, a7, a8, a5, a6, r1496, r1568, m0, m8, m56, m48, m40, fr1, rd1, wr1⟩ :=
    tr_sk_pre_sx (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω μ sp (sxw 4 n) h1 h6
      (sxw4_lt n) ⟨by omega, by omega⟩ (fun a h1 h2 => hst a (by omega) (by omega))
  have fr1' : ∀ a, a < sp - 64 → μ1.read a = μ.read a := fun a ha =>
    fr1 a (by omega) (.inl ha) (.inl (by omega)) (.inl (by omega))
  have H1 : HeapCtxC env.code pb S0 S1 μ1 s₀ :=
    HeapCtxC.keep_hi H (fun a ha => fr1' a (by omega)) wr1
  have hmod : (sxw 4 n + 1) % 4294967296 = (n + 1) % 4294967296 := sxw4_succ_mod n hn32
  have hval : μ1.readN (sp + 1568) 4 = fixed 4 ((n + 1) % 2 ^ 32) := by
    rw [readN_of_rdN r1568, hmod]; rfl
  have hkey1 : μ1.readN 65956 14 = trKey := by
    rw [Memory.readN_congr fun j hj => fr1' _ (by omega)]; exact hkey
  have hkr1 : ∀ a, 65956 ≤ a → a < 65970 → μ1.readable a = true := fun a h1 h2 => by rw [rd1]; exact hkr a h1 h2
  have ht81 : rdN μ1 69072 4 = 4294900408 := by
    rw [← ht8]; unfold rdN; congr 1; exact Memory.readN_congr fun j hj => fr1' _ (by omega)
  have ht41 : rdN μ1 69056 4 = 4294900402 := by
    rw [← ht4]; unfold rdN; congr 1; exact Memory.readN_congr fun j hj => fr1' _ (by omega)
  have htr1 : ∀ a, 69056 ≤ a → a < 69076 → μ1.readable a = true := fun a h1 h2 => by rw [rd1]; exact htr a h1 h2
  have hold : ∀ v, c.1.self.storage.get? trKey = some v → v.length < 2 ^ 63 := fun v h => by
    have := hfit v h; simpa using this
  have hsk := sk_call env cap pb hcap1 hcap (p := p) (P := P) (hb := 0) c f ω1 μ1 s₀ (sp - 64) (sp + 1568)
    ω[5].toNat ((sxw 4 n + 1) % 18446744073709551616) S0 S1 trKey (fixed 4 ((n + 1) % 2 ^ 32)) H1
    a0 a1 a7 a8 a5 a6 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    (readN_of_rdN m0) (readN_of_rdN m8) (readN_of_rdN m56) (readN_of_rdN m48) (readN_of_rdN m40)
    (UInt64.toNat_lt _) (Nat.mod_lt _ (by decide)) hkey1 hkr1 hval ht81 ht41 htr1 hold
  -- the operation's step
  have hk : argBase + trKey.length + (fixed 4 ((n + 1) % 2 ^ 32)).length ≤ outBase := by
    rw [show (fixed 4 ((n + 1) % 2 ^ 32)).length = 4 from Num.length_encodeLE _ _,
      show trKey.length = 14 by rw [← hkey]; exact Memory.length_readN _ _ _]; unfold argBase outBase; omega
  have estep := ASem.step_write env trKey (fixed 4 ((n + 1) % 2 ^ 32)) c hk hold
  have h1R : Reaches p (KeepCtx (accContractS env)) ⟨7326, ω, μ, c, f⟩ ⟨40494, ω1, μ1, c, f⟩ := ⟨18, run1⟩
  -- the null allocation: the trap at 4002
  have hnull : ∀ b, (∃ ω' μ' n, FreeStepsH p (KeepCtx (accContractS env)) 40494 ω1 μ1 (c, f) 3896 ω' μ' (c, f) n ∧
      ω'[7] = UInt64.ofNat 0 ∧
      FreeStepsH p (KeepCtx (accContractS env)) 3896 ω' μ' (c, f) 4002 ω' μ' (c, f) 1) →
      Aborts p (YIn (accContractS env) c.2 b) Ab ⟨40494, ω1, μ1, c, f⟩ c := by
    rintro b ⟨ω', μ', n', r1, -, r2⟩
    exact ⟨⟨4002, ω', μ', c, f⟩, ⟨n' + 1, (r1.trans r2).keepY c.2 b rfl⟩, hAb _ (.inl (.inr (.inl rfl))),
      ⟨ω', μ', f, heapTrapT_run (P := P) (.inr (.inl rfl)) _ ω' μ'⟩⟩
  -- read-only data below 196608 through the set call
  have roK : ∀ {ω' : Regs} {μ' : Memory} {x' : AccCtx × Stream} {i' n' : Nat} (b : Implications),
      FreeStepsH p (YIn (accContractS env) c.2 b) 40494 ω1 μ1 (c, f) i' ω' μ' x' n' →
      ∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a := by
    intro ω' μ' x' i' n' b run a ha
    have k := FreeStepsH.keepRO_of (yIn_keepsRO env H.bd c.2 b) run
    refine ⟨?_, ?_⟩
    · rw [k.2 a (by unfold two32; omega) (.inl (by unfold pageSize; omega)) (by rw [wr1]; exact hro a ha),
        fr1' a (by omega)]
    · have hp := k.1 (a / pageSize) (.inl (by unfold pageSize; omega))
      rw [← rd1 a]; unfold Memory.readable; rw [hp]
  by_cases hF : (writeAcct c.1.self trKey (fixed 4 ((n + 1) % 2 ^ 32))).minBalance >
      (writeAcct c.1.self trKey (fixed 4 ((n + 1) % 2 ^ 32))).balance
  · -- FULL: `orPanic` panics, the binary traps at 15361
    rw [if_pos hF] at estep
    refine impl_orPanic _ Q ⟨7326, ω, μ, c, f⟩ ⟨40494, ω1, μ1, c, f⟩ h1R rfl estep ?_
    rcases hsk with ⟨s', ω2, μ2, n2, run2, e7, -⟩ | hn0
    · have hR7 : writeR7 c.1.self trKey (fixed 4 ((n + 1) % 2 ^ 32)) = Result.FULL := by
        unfold writeR7; rw [if_pos hF]
      rw [hR7, if_pos rfl] at e7
      have hS : writeSelf c.1.self trKey (fixed 4 ((n + 1) % 2 ^ 32)) = c.1.self := by
        unfold writeSelf; rw [if_pos hF]
      rw [hS] at run2
      refine .inr ⟨⟨7386, ω2, μ2, (c.1.setSelf c.1.self, c.2), f⟩, ⟨n2, run2⟩, rfl, ?_⟩
      obtain ⟨ω3, run3⟩ := tr_chk_full (p := p) (P := P) (R := KeepCtx (accContractS env))
        ((c.1.setSelf c.1.self, c.2), f) ω2 μ2 e7
      exact ends_of_15361 (P := P) ⟨7386, ω2, μ2, (c.1.setSelf c.1.self, c.2), f⟩ run3
    · exact .inl (hnull _ hn0)
  · -- the write succeeded
    rw [if_neg hF] at estep
    refine impl_orPanic _ Q ⟨7326, ω, μ, c, f⟩ ⟨40494, ω1, μ1, c, f⟩ h1R rfl estep ?_
    rcases hsk with ⟨s', ω2, μ2, n2, run2, e7, e1, e5, e6, H2, kch, kdat, khi, kgl⟩ | hn0
    · have hR7 : writeR7 c.1.self trKey (fixed 4 ((n + 1) % 2 ^ 32)) ≠ Result.FULL := by
        unfold writeR7; rw [if_neg hF]
        cases hv : c.1.self.storage.get? trKey with
        | none => simp only [Option.map_none, Option.getD_none]; unfold Result.NONE Result.FULL; omega
        | some w =>
          have := hold w hv
          simp only [Option.map_some, Option.getD_some]; unfold Result.FULL; omega
      rw [if_neg hR7] at e7
      have hS : writeSelf c.1.self trKey (fixed 4 ((n + 1) % 2 ^ 32)) =
          writeAcct c.1.self trKey (fixed 4 ((n + 1) % 2 ^ 32)) := by
        unfold writeSelf; rw [if_neg hF]
      rw [hS] at run2
      have roK2 := roK c.2 run2
      refine .inr ⟨⟨7386, ω2, μ2, _, f⟩, ⟨n2, run2⟩, rfl, ?_⟩
      obtain ⟨ω3, run3, j3⟩ := tr_chk_ok (p := p) (P := P) (R := KeepCtx (accContractS env))
        ((c.1.setSelf (writeAcct c.1.self trKey (fixed 4 ((n + 1) % 2 ^ 32))), c.2), f) ω2 μ2 e7
      refine .inr ⟨⟨7399, ω3, μ2, _, f⟩, ⟨2, run3⟩, rfl, hQ _ ?_⟩
      -- the frame from sp up
      have kSp : ∀ a, a < 4294967296 → sp ≤ a → (a < sp + 1496 ∨ sp + 1500 ≤ a) →
          (a < sp + 1568 ∨ sp + 1572 ≤ a) → μ2.read a = μ.read a := fun a h0 ha hb hc => by
        rw [khi a h0 (by omega), fr1 a h0 (.inr ha) hb hc]
      have k2 : ∀ a, sp ≤ a → a < 4294967296 → μ2.read a = μ1.read a := fun a ha h0 => khi a h0 (by omega)
      refine ⟨rfl, rfl, rfl, (j3 1 (by decide)).trans (e1.trans (by congr 1; omega)), (j3 5 (by decide)).trans e5,
        (j3 6 (by decide)).trans e6, ⟨s', H2, fun d hd hu => ⟨kch d hd hu, fun a ha => ?_⟩⟩, ?_, ?_, kSp,
        fun a ha => roK2 a ha, fun a hg => ?_⟩
      · have hlt := heapC_data_lt H hd ha
        rw [kdat d hd hu a ha, fr1' a (by omega)]
      · have e : rdN μ2 (sp + 1496) 4 = rdN μ1 (sp + 1496) 4 := by
          unfold rdN; congr 1; exact Memory.readN_congr fun j hj => k2 _ (by omega) (by omega)
        have := sxw_mod 4 n (.inr rfl) (by simpa using hn32)
        simp only [Nat.reducePow] at this
        rw [e, r1496, this, Nat.mod_eq_of_lt hn32]
      · rw [← hmod, ← r1568]; unfold rdN; congr 1
        exact Memory.readN_congr fun j hj => k2 _ (by omega) (by omega)
      · have ha := hg; unfold Glob at ha
        rw [kgl a hg, fr1' a (by omega)]
    · exact .inl (hnull _ hn0)

end Services.Bootstrap.Acc
