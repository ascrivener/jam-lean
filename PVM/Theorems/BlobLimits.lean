import PVM.Theorems.InitMem

/-!
# The v0.8.1 limits of deblob

* `Blob.parse?_limits`: every program that parses has $|\mathbf{c}| \le \mathsf{Z}_C$ and $|\mathbf{j}| \le \mathsf{Z}_J$
  (GP v0.8.1 eq. `deblob`, #559).
-/

namespace PVM.Blob

theorem slice?_length {bs : ByteArray} {pos n : Nat} {l : List UInt8} (h : slice? bs pos n = some l) :
    l.length = n := by
  unfold slice? at h
  split at h
  · cases h; rw [ByteArray.length_toList', ByteArray.size_extract]; omega
  · cases h

/-- **The v0.8.1 limits of deblob** (GP v0.8.1 eq. `deblob`, #559): every program that parses has
    $|\mathbf{c}| \le \mathsf{Z}_C$ and $|\mathbf{j}| \le \mathsf{Z}_J$. -/
theorem parse?_limits {p : ByteArray} {P : Program} (h : parse? p = some P) :
    P.code.size ≤ maxCodeSize ∧ P.jumpTable.size ≤ maxJumpTableEntries := by
  unfold parse? at h
  cases h1 : decodeNat? p 0 with
  | none => simp [h1] at h
  | some r =>
    obtain ⟨jLen, pos⟩ := r
    by_cases hj : jLen > maxJumpTableEntries
    · simp [h1, hj] at h
    cases h2 : p[pos]? with
    | none => simp [h1, hj, h2] at h
    | some zb =>
      by_cases hz : zb.toNat > 4
      · simp [h1, hj, h2, hz] at h
      cases h3 : decodeNat? p (pos + 1) with
      | none => simp [h1, hj, h2, h3] at h
      | some r' =>
        obtain ⟨cLen, pos'⟩ := r'
        by_cases hc : cLen > maxCodeSize
        · simp [h1, hj, h2, h3, hc] at h
        by_cases hsz : p.size < pos' + jLen * zb.toNat
        · simp [h1, hj, h2, hz, h3, hc, hsz] at h
        cases hs : slice? p (pos' + jLen * zb.toNat) cLen with
        | none => simp [h1, hj, h2, hz, h3, hc, hsz, hs] at h
        | some c =>
          cases hk : decodeBits? (p.extract (pos' + jLen * zb.toNat + cLen) p.size).toList cLen with
          | none => simp [h1, hj, h2, hz, h3, hc, hsz, hs, hk] at h
          | some k =>
            simp [h1, hj, h2, hz, h3, hc, hsz, hs, hk] at h
            subst h
            refine ⟨?_, ?_⟩
            · simp [ByteArray.size, slice?_length hs]; omega
            · simp; omega

end PVM.Blob
