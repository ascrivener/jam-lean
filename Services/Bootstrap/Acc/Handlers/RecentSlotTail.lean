import Services.Bootstrap.Acc.Handlers.RecentSlotSeg
import Services.Bootstrap.Acc.Handlers.ReadExactText
import Services.Bootstrap.Acc.Handlers.HeapKeep
import Services.Bootstrap.Acc.Wrappers.GetCall
import Services.Bootstrap.Decode.DeallocCall
import Services.Bootstrap.Spec

/-!
# The ring slot's typed `get` (34377): from `get`'s `Some` to the return

`slotDec` is `addRecent`'s decoder for a ring slot (32 octets, then a 2-octet number; GP v0.8.0
Appendix C's ℰ for the SDK's `(H, u16)`), and `SlotOut` the record 34377 leaves at out: the `u16` 0
(`None`), or the `u16` 1, the 32 octets at out + 2 and the 2 at out + 34 (`Some`).

- `sg_fret`: `dealloc` of the value's buffer (40613, return address 1608), then the return;
- `sg_tailW`: from 34434 with `get`'s value w ≠ [] in a fresh chunk: the reads (`read_exact`, short
  or not), the record at out, `dealloc`, the return. Under any host relation (no host calls).
- `sg_tailE`: the same for the empty value (capacity 0, no `dealloc`).
-/

namespace Services.Bootstrap.Acc.Handlers.RecentSlot

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.Alloc Services.Bootstrap.Spec
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- `addRecent`'s decoder of a ring slot: 32 octets, then a 2-octet number. -/
def slotDec : Dec (Bytes × Nat) := do return (← Dec.take 32, ← Dec.fixedN 2)

theorem slotDec_long (w : Bytes) (h : 34 ≤ w.length) :
    decode slotDec w = some (w.take 32, Num.decodeLE ((w.drop 32).take 2)) := by
  simp [decode, slotDec, Dec.take, Dec.fixedN, StateT.run, bind, StateT.bind, pure, StateT.pure,
    Option.bind, show 32 ≤ w.length by omega, show 2 ≤ w.length - 32 by omega]

theorem slotDec_short (w : Bytes) (h : w.length < 34) : decode slotDec w = none := by
  by_cases h32 : 32 ≤ w.length
  · simp [decode, slotDec, Dec.take, Dec.fixedN, StateT.run, bind, StateT.bind, pure, StateT.pure,
      Option.bind, h32, show ¬ 2 ≤ w.length - 32 by omega]
  · simp [decode, slotDec, Dec.take, Dec.fixedN, StateT.run, bind, StateT.bind, pure, StateT.pure,
      Option.bind, h32]

/-- **The record 34377 leaves at out**: the `u16` 0 for `None`; for `Some (q, k)` the `u16` 1, q
    at out + 2 and ℰ₂(k) at out + 34. -/
def SlotOut (μ : Memory) (out : Nat) : Option (Bytes × Nat) → Prop
  | none => μ.readN out 2 = Num.encodeLE 2 0
  | some (q, k) => μ.readN out 2 = Num.encodeLE 2 1 ∧ μ.readN (out + 2) 32 = q ∧
      μ.readN (out + 34) 2 = Num.encodeLE 2 k

theorem rdN_of_readN {μ : Memory} {a n v : Nat} (h : μ.readN a n = Num.encodeLE n v) (hv : v < 2 ^ (8 * n)) :
    rdN μ a n = v := by
  show Num.decodeLE _ = _
  rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hv]

theorem readN_rdN (μ : Memory) (a n : Nat) : μ.readN a n = Num.encodeLE n (rdN μ a n) := by
  have := encodeLE_decodeLE (μ.readN a n)
  rw [Memory.length_readN] at this
  exact this.symm

open Services.Bootstrap.Decode.DeallocCall in
/-- **40613 … the return**: `dealloc` of the value's buffer (the chunk V at vptr − 32), returning
    to 34623 (1608), then ω₀, ω₅, ω₆ restored from S + 104, + 96, + 88 and the return to t. The
    context is kept for `free s vptr`; memory is kept from S on, at the globals, below 196608 and in
    every other allocated chunk's data. -/
theorem sg_fret {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P]
    (code : ByteArray) (pb S0 S1 : Nat) (x : X) (ω : Regs) (μ : Memory) (s : State) (S vptr r0 v5 v6 t : Nat)
    (V : Chunk) (H : HeapCtxC code pb S0 S1 μ s) (hV : V ∈ chunks s) (hVu : V.used = true)
    (hVa : V.addr + 32 = vptr) (h0 : ω[0] = UInt64.ofNat 1608) (h1 : ω[1] = UInt64.ofNat S)
    (h7 : ω[7] = UInt64.ofNat vptr) (hS : 2147483716 ≤ S ∧ S + 112 < 4294967296) (hSS : S0 + 40 ≤ S ∧ S + 112 ≤ S1)
    (m104 : μ.readN (S + 104) 8 = Num.encodeLE 8 r0) (m96 : μ.readN (S + 96) 8 = Num.encodeLE 8 v5)
    (m88 : μ.readN (S + 88) 8 = Num.encodeLE 8 v6)
    (hr0 : r0 < 18446744073709551616) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) :
    ∃ ω' μ', FreeStepsH p R 40613 ω μ x t ω' μ' x 254 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (S + 112) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ HeapCtxC code pb S0 S1 μ' (free s vptr) ∧
      (∀ a, a < 4294967296 → S ≤ a → μ'.read a = μ.read a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) ∧ (∀ a, a < 196608 → μ'.read a = μ.read a) ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ V → d ∈ chunks (free s vptr) ∧ ∀ a, InData d a → μ'.read a = μ.read a) := by
  have hst := H.st
  have hS1 := H.hS1
  obtain ⟨ω1, μ1, run1, H1, -, -, ro1, stk1, gl1, keep1, g0, g1, -, -⟩ :=
    dealloc_callG (R := R) (p := p) (P := P) code pb S0 S1 x ω μ s S vptr 1608 34623 V H hV hVu hVa h0 h1 h7
      ⟨by decide, by decide, by decide⟩ (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_803]) bs_34623 hS.1
      ⟨hSS.1, by omega⟩
  have kf : ∀ o, S ≤ o → o + 8 ≤ S + 112 → μ1.readN o 8 = μ.readN o 8 := fun o ho ho' =>
    Memory.readN_congr fun j hj => stk1 _ (by omega) (by omega)
  obtain ⟨ω2, run2, e0, e1, e5, e6⟩ := sg_ret (P := P) (R := R) x ω1 μ1 S r0 v5 v6 t (g1.trans h1)
    ⟨by omega, by omega⟩ (by rw [kf _ (by omega) (by omega)]; exact m104) (by rw [kf _ (by omega) (by omega)]; exact m96)
    (by rw [kf _ (by omega) (by omega)]; exact m88) hr0 hv5 hv6 hret hjt hbt
    (fun a h1 h2 => Memory.readable_of_writable (H1.st a (by omega) (by omega)))
  refine ⟨ω2, μ1, (run1.trans run2).mono (by omega), e0, e1, e5, e6, H1, fun a h0 ha => stk1 a h0 ha,
    gl1, fun a ha => ro1 a (by unfold two32; omega) (H.ro a ha), fun d hd hu hne => keep1 d hd hu hne⟩

end Services.Bootstrap.Acc.Handlers.RecentSlot
