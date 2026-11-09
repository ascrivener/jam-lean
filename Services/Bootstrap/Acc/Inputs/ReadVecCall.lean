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

end Services.Bootstrap.Acc
