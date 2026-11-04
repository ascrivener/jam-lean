import JAM.Refine
import PVM.Logic.ChunkBlob

/-!
# A code preimage given as a number

`splitMetadata` (the paper's ℰ(↕**m**, **c**) split of a code preimage) on the octets of a
`NatBlob`: the code is the octets after the metadata.
-/

namespace PVM.NatBlob

/-- The code after the metadata ↕**m**, whose length prefix the kernel decides on a few octets. -/
theorem splitMetadata_bytes (N o n : Nat) {mLen pos : Nat}
    (h : Blob.decodeNat? (ba N o n) 0 = some (mLen, pos)) (hle : pos + mLen ≤ n) :
    JAM.splitMetadata (bytes N o n) = some (ba N (o + pos + mLen) (n - pos - mLen)) := by
  have hb : (⟨(bytes N o n).toArray⟩ : ByteArray) = ba N o n := rfl
  simp only [JAM.splitMetadata, hb, h, Option.bind_eq_bind, Option.bind_some, size_ba]
  rw [ite_eq_right_iff.2 (fun h => absurd h (by omega)), extract_ba]
  congr 2 <;> omega

end PVM.NatBlob
