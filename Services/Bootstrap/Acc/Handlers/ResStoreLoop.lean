import Services.Bootstrap.Acc.Handlers.ResultsHyp
import Services.Bootstrap.Acc.Handlers.ResStoreLoopSeg

/-!
# The results store (36170), n ≥ 1: one pass of the loop, against `ExtendH` and `OkEncH`

`LoopInv k`: at 36346 (or 36405 once k = n), the value `Vec` at S + 32 (S = sp − 96) holds
ℰ(n) ++ ℰ(rs₀) ++ … ++ ℰ(rs_{k−1}) (`encK`), ω₅ = 144·(n − k), ω₆ = rp + 144·k, the allocator's context
holds, every allocated chunk of st is kept with its data and is not the buffer's, and the callee frame
(but the vector and the staging octet at S + 56), read-only data and the globals are kept against μ₀.

`rl_item`: from `LoopInv k` with k < n, one pass reaches `LoopInv (k + 1)`, or exhausts the heap.
-/

namespace Services.Bootstrap.Acc.Handlers.ResStore

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.Spec Services.Bootstrap.Acc Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Encode.Writer Services.Bootstrap.Encode.WriterGrow
  Services.Bootstrap.Acc.Handlers.Results

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- `ExhaustsP` from a later point of a run that keeps the context and the stream. -/
theorem ExhaustsP.pre {p : ByteArray} {env : AccEnv} {pb i j : Nat} {ω ω' : Regs} {μ μ' : Memory}
    {c : AccCtx} {f : Stream} {N : Nat}
    (run : FreeStepsH p (KeepCtx (accContractS env)) i ω μ (c, f) j ω' μ' (c, f) N)
    (h : ExhaustsP p env pb j ω' μ' c f) : ExhaustsP p env pb i ω μ c f := by
  obtain ⟨ω₁, μ₁, q₁, j₁, N₁, r₁, e7, hj, rest⟩ := h
  exact ⟨ω₁, μ₁, q₁, j₁, N + N₁, run.trans r₁, e7, hj, rest⟩

theorem encode_ok (r : Ret) : Spec.Result.encode (.ok r) = 0 :: (Spec.Result.encode (.ok r)).drop 1 := by
  cases r <;> rfl

theorem encode_error (e : Err) : Spec.Result.encode (.error e) = [1, UInt8.ofNat e.tag] := rfl

theorem tag_lt (e : Err) : e.tag < 14 := by cases e <;> decide

/-- The first k results' encodings after ℰ(n). -/
def encK (n : Nat) (rs : List Spec.Result) (k : Nat) : List UInt8 :=
  Blob.encodeNat n ++ ((rs.take k).map Spec.Result.encode).flatten

theorem encK_succ (n : Nat) (rs : List Spec.Result) (k : Nat) (hk : k < rs.length) :
    encK n rs (k + 1) = encK n rs k ++ Spec.Result.encode rs[k] := by
  unfold encK
  rw [List.append_assoc, List.take_succ_eq_append_getElem hk, List.map_append, List.flatten_append]
  simp

theorem encK_len_le (n : Nat) (rs : List Spec.Result) (k : Nat) (hn : rs.length = n) :
    (encK n rs k).length ≤ (encodeResults rs).length := by
  unfold encK encodeResults vec
  have h := congrArg (fun l => (l.map Spec.Result.encode).flatten.length) (List.take_append_drop k rs)
  simp only [List.map_append, List.flatten_append, List.length_append] at h
  simp only [List.length_append, JAM.Codec.nat, hn]
  omega

/-- **The loop's invariant** after k items (see the module doc). -/
def LoopInv (code : ByteArray) (pb S0 S1 sp rp n : Nat) (rs : List Spec.Result) (st : State) (μ₀ : Memory)
    (k : Nat) (ω : Regs) (μ : Memory) (s : State) : Prop :=
  ω[1] = UInt64.ofNat (sp - 96) ∧ ω[5] = UInt64.ofNat (144 * (n - k)) ∧ ω[6] = UInt64.ofNat (rp + 144 * k) ∧
  HeapCtxC code pb S0 S1 μ s ∧
  (∃ cap ptr, WriterPre μ s (sp - 96) (sp - 96 + 32) cap ptr (encK n rs k).length S1 ∧
    μ.readN ptr (encK n rs k).length = encK n rs k ∧
    cap ≤ max (144 * n + 4) (max 8 (2 * (encK n rs k).length)) ∧
    ∀ d ∈ chunks st, d.used = true → d ∈ chunks s ∧ d.addr + 32 ≠ ptr ∧ ∀ a, InData d a → μ.read a = μ₀.read a) ∧
  (∀ a, a < 4294967296 → sp - 96 ≤ a → (a < sp - 96 + 32 ∨ sp - 96 + 57 ≤ a) → μ.read a = μ₀.read a) ∧
  (∀ a, a < 196608 → μ.read a = μ₀.read a ∧ μ.readable a = μ₀.readable a) ∧
  (∀ a, Glob a → μ.read a = μ₀.read a)

/-- The common hypotheses of the loop: the stack frame, the items' bound and the encodings' size. -/
structure LoopHyp (pb S0 S1 sp rp n : Nat) (rs : List Spec.Result) (st : State) (μ₀ : Memory) : Prop where
  hsp : S0 + 520 ≤ sp ∧ 2147484168 ≤ sp ∧ sp % 8 = 0 ∧ sp ≤ S1
  hS1 : S1 < 4294967296
  hn : rs.length = n
  hrp : 65536 ≤ rp ∧ rp + 144 * n < 2147483648
  hB : 2 * (144 * n + 4) + 4 * (encodeResults rs).length + 64 < 1073741760
  hR : ResultsAt μ₀ st rp rs

/-- One `extend` call's outcome folded into the invariant's buffer facts (used twice per item). -/
theorem writer_chain {code : ByteArray} {pb S0 S1 sp : Nat} {μ μ' : Memory} {s s' : State}
    {cap ptr len : Nat} {bs : List UInt8} {st : State} {μ₀ : Memory}
    (hpost : WriterPost code pb S0 S1 μ s (sp - 96) (sp - 96 + 32) cap ptr len bs μ' s')
    (hst : ∀ d ∈ chunks st, d.used = true → d ∈ chunks s ∧ d.addr + 32 ≠ ptr ∧ ∀ a, InData d a → μ.read a = μ₀.read a)
    (hpre : WriterPre μ s (sp - 96) (sp - 96 + 32) cap ptr len S1) (hbig : 4 * (len + bs.length) + 16 < 1073741760)
    (hbs : 0 < bs.length)
    (hcapb : 2 * cap < 1073741760) :
    ∃ cap' r, WriterPre μ' s' (sp - 96) (sp - 96 + 32) cap' r (len + bs.length) S1 ∧
      μ'.readN r (len + bs.length) = μ.readN ptr len ++ bs ∧ cap' ≤ max cap (max 8 (2 * (len + bs.length))) ∧
      HeapCtxC code pb S0 S1 μ' s' ∧
      (∀ d ∈ chunks st, d.used = true → d ∈ chunks s' ∧ d.addr + 32 ≠ r ∧ ∀ a, InData d a → μ'.read a = μ₀.read a) ∧
      (∀ a, a < 4294967296 → sp - 96 ≤ a → (a < sp - 96 + 32 ∨ sp - 96 + 56 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) := by
  obtain ⟨cap', r, m0, m8, m16, hroom, hcap', eo, en, H', ⟨d, hd, hdu, hda, hds⟩, others, hr, stk, lo, gl⟩ := hpost
  obtain ⟨hv1, hv2, -, -, -, -, -, -, -⟩ := hpre
  have hc2 : cap' ≤ cap ∨ cap' ≤ 8 ∨ cap' ≤ 2 * (len + bs.length) := by
    omega
  refine ⟨cap', r, ⟨hv1, hv2, m0, m8, m16, hroom, by omega, by omega, d, hd, hdu, hda, hds⟩, ?_, hcap', H', ?_,
    fun a h0 h1 h2 => stk a h0 h1 (by omega), lo, gl⟩
  · rw [Services.Bootstrap.Decode.VecU8.readN_split, eo, en]
  · intro e he hu
    obtain ⟨k1, k2, k3⟩ := hst e he hu
    obtain ⟨k4, k5⟩ := others e k1 hu k2
    refine ⟨k4, ?_, fun a ha => (k5 a ha).trans (k3 a ha)⟩
    rcases hr with rfl | hr
    · exact k2
    · exact hr e k1 hu

end Services.Bootstrap.Acc.Handlers.ResStore
