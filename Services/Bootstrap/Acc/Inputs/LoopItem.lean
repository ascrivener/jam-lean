import Services.Bootstrap.Acc.Inputs.Loop

/-!
# One item of `Vec<AccumulateItem>::decode`, as the loop sees it

`ItemOk env cap pb N enc Rep`: the item decode (45126, returning through 2044 to 45168) turns the
reader's octets `enc` into a 184-octet stack slot whose octets satisfy `Rep`, or exhausts the
allocator. In the style of T1's `ElemOkAF` (`Decode/LoopA.lean`). Instances: a transfer (`tr_call`),
an operand with a work output or a work error (`item_op_ok`, `item_op_err`).
-/

namespace Services.Bootstrap.Acc

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- A piece of a read is a read. -/
theorem readN_drop_take (μ : Memory) (a n k m : Nat) (h : k + m ≤ n) :
    ((μ.readN a n).drop k).take m = μ.readN (a + k) m := by
  have e : μ.readN a n = μ.readN a k ++ (μ.readN (a + k) m ++ μ.readN (a + k + m) (n - k - m)) := by
    rw [← PVM.Memory.readN_split, ← PVM.Memory.readN_split]; congr 1; omega
  rw [e, List.drop_append_of_le_length (by simp), List.drop_eq_nil_of_le (by simp), List.nil_append,
    List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]

/-- **One item decodes into the loop's stack slot** (see the module doc): from 45126 with the loop's
    frame base sp (ω₁), the slot at sp + 88 (ω₇), the reader rd (ω₈) holding `enc` inside an allocated
    chunk, and return address 2044, either the run reaches 45168 with the slot's first word not −2, its
    184 octets satisfying `Rep` for every memory agreeing on the item's fresh chunks, the context for a
    new state keeping every allocated chunk and its data, and the reader past `enc`; or it exhausts the
    allocator (45975). -/
def ItemOk {X : Type} (env : HeapHost X) (cap pb : Nat) (p : ByteArray) (P : Program) (N : Nat)
    (enc : List UInt8) (Rep : List UInt8 → Memory → Prop) : Prop :=
  ∀ (x : X) (ω : Regs) (μ : Memory) (hb : Nat) (s : State) (sp rd ip rlen S0 S1 : Nat),
    HeapCtxC env.code pb S0 S1 μ s →
    ω[0] = UInt64.ofNat 2044 → ω[1] = UInt64.ofNat sp → ω[7] = UInt64.ofNat (sp + 88) → ω[8] = UInt64.ofNat rd →
    2147483960 + 424 ≤ sp → sp % 8 = 0 → S0 + 864 ≤ sp → sp + 480 ≤ rd → rd + 16 ≤ S1 →
    μ.readN rd 8 = Num.encodeLE 8 ip → μ.readN (rd + 8) 8 = Num.encodeLE 8 rlen →
    enc.length ≤ rlen → rlen < 4294967296 → μ.readN ip enc.length = enc →
    (∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ip ∧ ip + enc.length + 32 ≤ c.addr + 32 * c.size) →
    (∃ s' ω' μ', FreeStepsH p (env.rel cap) 45126 ω μ x 45168 ω' μ' x N ∧
      ω'[0] = UInt64.ofNat 2044 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      rdN μ' (sp + 88) 8 ≠ 18446744073709551614 ∧
      HeapCtxC env.code pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InDataA c a → μ'.read a = μ.read a) ∧
      (∃ cs : List Chunk, (∀ c ∈ cs, c ∈ chunks s' ∧ c.used = true ∧ ∀ d ∈ chunks s, d.used = true → d ≠ c) ∧
        ∀ μ'' : Memory, (∀ c ∈ cs, ∀ a, InDataA c a → μ''.read a = μ'.read a) →
          Rep (μ'.readN (sp + 88) 184) μ'') ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ip + enc.length) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (rlen - enc.length) ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < sp + 88 ∨ sp + 272 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
        μ'.read a = μ.read a)) ∨
    (∃ ω' μ', FreeStepsH p (env.rel cap) 45126 ω μ x 45975 ω' μ' x N)

end Services.Bootstrap.Acc
