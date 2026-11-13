import Services.Bootstrap.Acc.Inputs.LoopItem

/-!
# An operand is an `ItemOk` item

The operand's encoding (GP v0.8.0 §12 𝕌, Appendix C): the tag 0, the four hashes h (128 octets), ℰ(g),
the work result O(l) (tag 0 then ↕o, or a tag e ∈ 1 … 6) and ↕t; and its slot (`item_op_ok`,
`item_op_err`).
-/

namespace Services.Bootstrap.Acc

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- The 8-octet word at offset k of a slot's octets. -/
def wd (bs : List UInt8) (k : Nat) : Nat := Num.decodeLE ((bs.drop k).take 8)

/-- An operand with a work output: tag 0, h, ℰ(g), 0, ↕o, ↕t. -/
def encOpOk (h : List UInt8) (g : Nat) (o t : List UInt8) : List UInt8 :=
  [0] ++ (h ++ (Blob.encodeNat g ++ ([0] ++ (Blob.encodeNat o.length ++ (o ++ (Blob.encodeNat t.length ++ t))))))

/-- An operand with a work error e: tag 0, h, ℰ(g), e, ↕t. -/
def encOpErr (h : List UInt8) (g e : Nat) (t : List UInt8) : List UInt8 :=
  [0] ++ (h ++ (Blob.encodeNat g ++ ([UInt8.ofNat e] ++ (Blob.encodeNat t.length ++ t))))

/-- What both operand slots hold: the trace (capacity and length |t|, its octets at the pointer), the
    hashes at + 48 and g at + 176. -/
def RepOpBase (h : List UInt8) (g : Nat) (t : List UInt8) (bs : List UInt8) (μ : Memory) : Prop :=
  wd bs 0 = t.length ∧ wd bs 16 = t.length ∧ μ.readN (wd bs 8) t.length = t ∧
    (bs.drop 48).take 128 = h ∧ wd bs 176 = g

/-- An operand slot with a work output o (capacity and length |o| at + 24 / + 40, octets at + 32). -/
def RepOpOk (h : List UInt8) (g : Nat) (o t : List UInt8) (bs : List UInt8) (μ : Memory) : Prop :=
  RepOpBase h g t bs μ ∧ wd bs 24 = o.length ∧ wd bs 40 = o.length ∧ μ.readN (wd bs 32) o.length = o

/-- An operand slot with a work error e (−1 at + 24, e at + 32). -/
def RepOpErr (h : List UInt8) (g e : Nat) (t : List UInt8) (bs : List UInt8) (μ : Memory) : Prop :=
  RepOpBase h g t bs μ ∧ wd bs 24 = 18446744073709551615 ∧ wd bs 32 = e

end Services.Bootstrap.Acc
