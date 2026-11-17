import Services.Bootstrap.Acc.Handlers.ResultsDropSeg
import Services.Bootstrap.Acc.Handlers.ResultsAt
import Services.Bootstrap.Decode.DeallocCall

/-!
# The results' ownership (`ResultsOwn`) and their drop (28864)

`ResultsAt` (R4) says where the results' octets are; `ResultsOwn` (decided by the parent, option (A))
adds who owns which allocated chunk, as Rust's `Vec<Result>` does: the buffers that `drop_in_place`
frees are listed in order by `resPtrs` (per item: a `data` buffer with cap ≠ 0; a `dataVec`'s inner
buffers with cap ≠ 0, then its outer buffer if cap ≠ 0), pairwise distinct, each the data of an
allocated chunk; the items' octets lie in chunks that are not freed; a non-empty `dataVec`'s inner
array lies in its outer buffer's chunk.

`drop_results` (28864 → the return): every listed chunk is freed; every other allocated chunk is kept
with its data, and so is the stack from the caller's sp up.
-/

namespace Services.Bootstrap.Acc.Handlers.ResultsDrop

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- The inner buffers of a `dataVec` with inner array q and len inner `Vec`s (cap at q + 24·j, ptr at
    q + 24·j + 8), those with cap ≠ 0, in order. -/
def innerPtrs (μ : Memory) (q len : Nat) : List Nat :=
  (List.range len).filterMap fun j => if rdN μ (q + 24 * j) 8 = 0 then none else some (rdN μ (q + 24 * j + 8) 8)

/-- The buffers the item at a owns, in the order the drop frees them. -/
def itemPtrs (μ : Memory) (a : Nat) : List Nat :=
  if rdN μ a 1 = 5 then (if rdN μ (a + 8) 8 = 0 then [] else [rdN μ (a + 16) 8])
  else if 6 ≤ rdN μ a 1 ∧ rdN μ a 1 < 255 then
    innerPtrs μ (rdN μ (a + 16) 8) (rdN μ (a + 24) 8) ++
      (if rdN μ (a + 8) 8 = 0 then [] else [rdN μ (a + 16) 8])
  else []

/-- The buffers the first n items at rp own, in the order the drop frees them. -/
def resPtrs (μ : Memory) (rp n : Nat) : List Nat :=
  (List.range n).flatMap fun k => itemPtrs μ (rp + 144 * k)

/-- **The results' ownership** (the n items at rp, against the allocator state st): the owned buffers
    are pairwise distinct, each the data of an allocated chunk; every octet of the items lies in an
    allocated chunk that is not owned; a `dataVec` with len ≠ 0 has cap ≠ 0, and its inner array lies
    in its buffer's chunk. -/
def ResultsOwn (μ : Memory) (st : State) (rp n : Nat) : Prop :=
  (resPtrs μ rp n).Nodup ∧
  (∀ q ∈ resPtrs μ rp n, ∃ d ∈ chunks st, d.used = true ∧ d.addr + 32 = q) ∧
  (∀ k, k < 144 * n → ∃ d ∈ chunks st, d.used = true ∧ InData d (rp + k) ∧ d.addr + 32 ∉ resPtrs μ rp n) ∧
  (∀ i, i < n → 6 ≤ rdN μ (rp + 144 * i) 1 → rdN μ (rp + 144 * i) 1 < 255 →
    rdN μ (rp + 144 * i + 24) 8 ≠ 0 →
    rdN μ (rp + 144 * i + 8) 8 ≠ 0 ∧ ∃ d ∈ chunks st, d.used = true ∧ d.addr + 32 = rdN μ (rp + 144 * i + 16) 8 ∧
      rdN μ (rp + 144 * i + 16) 8 + 24 * rdN μ (rp + 144 * i + 24) 8 ≤ d.addr + 32 * d.size)

theorem innerPtrs_succ (μ : Memory) (q j : Nat) :
    innerPtrs μ q (j + 1) = innerPtrs μ q j ++
      (if rdN μ (q + 24 * j) 8 = 0 then [] else [rdN μ (q + 24 * j + 8) 8]) := by
  unfold innerPtrs
  rw [List.range_succ, List.filterMap_append]
  by_cases h : rdN μ (q + 24 * j) 8 = 0 <;> simp [h]

theorem resPtrs_succ (μ : Memory) (rp k : Nat) :
    resPtrs μ rp (k + 1) = resPtrs μ rp k ++ itemPtrs μ (rp + 144 * k) := by
  unfold resPtrs
  rw [List.range_succ, List.flatMap_append]
  simp

theorem innerPtrs_split (μ : Memory) (q j len : Nat) (h : j ≤ len) :
    ∃ R, innerPtrs μ q len = innerPtrs μ q j ++ R := by
  induction len with
  | zero => exact ⟨[], by rw [show j = 0 by omega]; simp⟩
  | succ m ih =>
    rcases Nat.lt_or_ge j (m + 1) with hj | hj
    · obtain ⟨R, hR⟩ := ih (by omega)
      exact ⟨R ++ _, by rw [innerPtrs_succ, hR, List.append_assoc]⟩
    · exact ⟨[], by rw [show j = m + 1 by omega]; simp⟩

theorem resPtrs_split (μ : Memory) (rp k n : Nat) (h : k ≤ n) :
    ∃ R, resPtrs μ rp n = resPtrs μ rp k ++ R := by
  induction n with
  | zero => exact ⟨[], by rw [show k = 0 by omega]; simp⟩
  | succ m ih =>
    rcases Nat.lt_or_ge k (m + 1) with hk | hk
    · obtain ⟨R, hR⟩ := ih (by omega)
      exact ⟨R ++ _, by rw [resPtrs_succ, hR, List.append_assoc]⟩
    · exact ⟨[], by rw [show k = m + 1 by omega]; simp⟩

/-- The next freed buffer is not among those freed before. -/
theorem nodup_next {A R : List Nat} {x : Nat} (h : (A ++ x :: R).Nodup) : x ∉ A := by
  intro hx
  rw [List.nodup_append] at h
  exact h.2.2 x hx x (List.mem_cons_self) rfl

end Services.Bootstrap.Acc.Handlers.ResultsDrop
