import JAM.Blake2b
import JAM.Theorems.LoopRel

/-!
# Checked indexing in Blake2b: the new definitions equal the old ones

`JAM.Blake2b` keeps its state in `Vector`s (the chaining value h of 8 words, the working vector v of
16, the message schedule σ of `Fin 16` indices) and indexes them in bounds. This file keeps the
earlier `Array` form with `a[i]!` verbatim (`JAM.Theorems.CheckedIndex.Old.Blake2b`) and proves each
function equal to its new form; `blake2b_hash_eq_old` is the digest. `JAM.Fast.Blake2b` proves its
fast forms equal to the old ones and goes through these.
-/

namespace JAM.Theorems.CheckedIndex
open JAM.Theorems JAM.Theorems.LoopRel

namespace Old.Blake2b


/-- The initialization vector (RFC 7693 §2.6). -/
def iv : Array UInt64 := #[
  0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
  0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

/-- The message schedule σ (RFC 7693 §2.7); rounds 10 and 11 reuse rows 0 and 1. -/
def sigma : Array (Array Nat) := #[
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
  #[14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
  #[11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
  #[7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
  #[9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
  #[2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
  #[12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
  #[13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
  #[6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
  #[10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]]

/-- Rotate right. -/
@[inline] def rotr (x : UInt64) (n : UInt64) : UInt64 := (x >>> n) ||| (x <<< (64 - n))

/-- The mixing function G (RFC 7693 §3.1). -/
def mix (v : Array UInt64) (a b c d : Nat) (x y : UInt64) : Array UInt64 := Id.run do
  let mut v := v
  v := v.set! a (v[a]! + v[b]! + x)
  v := v.set! d (rotr (v[d]! ^^^ v[a]!) 32)
  v := v.set! c (v[c]! + v[d]!)
  v := v.set! b (rotr (v[b]! ^^^ v[c]!) 24)
  v := v.set! a (v[a]! + v[b]! + y)
  v := v.set! d (rotr (v[d]! ^^^ v[a]!) 16)
  v := v.set! c (v[c]! + v[d]!)
  v := v.set! b (rotr (v[b]! ^^^ v[c]!) 63)
  return v

/-- A 128-octet block as sixteen little-endian 64-bit words. -/
def words (block : List UInt8) : Array UInt64 :=
  (List.range 16).toArray.map fun i =>
    (List.range 8).foldr (fun k acc => (acc <<< 8) ||| (block.getD (8 * i + k) 0).toUInt64) 0

/-- The compression function F (RFC 7693 §3.2), with byte counter `t` and final-block flag `last`. -/
def compress (h : Array UInt64) (block : List UInt8) (t : Nat) (last : Bool) : Array UInt64 := Id.run do
  let m := words block
  let mut v := h ++ iv
  v := v.set! 12 (v[12]! ^^^ UInt64.ofNat (t % 2 ^ 64))
  v := v.set! 13 (v[13]! ^^^ UInt64.ofNat (t / 2 ^ 64))
  if last then v := v.set! 14 (v[14]! ^^^ 0xFFFFFFFFFFFFFFFF)
  for r in [0:12] do
    let s := sigma[r % 10]!
    v := mix v 0 4 8 12 m[s[0]!]! m[s[1]!]!
    v := mix v 1 5 9 13 m[s[2]!]! m[s[3]!]!
    v := mix v 2 6 10 14 m[s[4]!]! m[s[5]!]!
    v := mix v 3 7 11 15 m[s[6]!]! m[s[7]!]!
    v := mix v 0 5 10 15 m[s[8]!]! m[s[9]!]!
    v := mix v 1 6 11 12 m[s[10]!]! m[s[11]!]!
    v := mix v 2 7 8 13 m[s[12]!]! m[s[13]!]!
    v := mix v 3 4 9 14 m[s[14]!]! m[s[15]!]!
  return (List.range 8).toArray.map fun i => h[i]! ^^^ v[i]! ^^^ v[i + 8]!

/-- Process the message's 128-octet blocks, the last one (possibly empty, for an empty message)
    with the final-block flag. The byte counter is the number of octets consumed so far. -/
def blocks (h : Array UInt64) (msg : ByteArray) : Array UInt64 :=
  let len := msg.size
  let nb := max 1 ((len + 127) / 128)
  let block (k : Nat) : List UInt8 := (msg.extract (128 * k) (128 * k + 128)).toList
  let h := (List.range (nb - 1)).foldl (fun h k => compress h (block k) (128 * (k + 1)) false) h
  compress h (block (nb - 1)) len true

/-- Blake2b with an `n`-octet digest (1 ≤ n ≤ 64), unkeyed (RFC 7693 §3.3). -/
def hash (n : Nat) (msg : ByteArray) : ByteArray :=
  let h := iv.set! 0 (iv[0]! ^^^ 0x01010000 ^^^ UInt64.ofNat n)
  let h := blocks h msg
  let out := (List.range n).map fun k => (h[k / 8]! >>> (8 * (k % 8)).toUInt64).toUInt8
  ⟨out.toArray⟩

end Old.Blake2b


theorem blake2b_mix_eq_old (v : Vector UInt64 16) (a b c d : Fin 16) (x y : UInt64) :
    Old.Blake2b.mix v.toArray a b c d x y = (JAM.Blake2b.mix v a b c d x y).toArray := by
  simp only [Old.Blake2b.mix, JAM.Blake2b.mix, Id.run, pure]
  simp only [getV _ _ a.isLt, getV _ _ b.isLt, getV _ _ c.isLt, getV _ _ d.isLt, setV _ _ a.isLt, setV _ _ b.isLt, setV _ _ c.isLt, setV _ _ d.isLt, Fin.getElem_fin]
  rfl

theorem blake2b_words_eq_old (block : List UInt8) : Old.Blake2b.words block = (JAM.Blake2b.words block).toArray := by
  apply Array.ext <;> simp [Old.Blake2b.words, JAM.Blake2b.words]

theorem blake2b_sigma_get (r : Nat) (i : Nat) (hr : r < 10) (hi : i < 16) :
    (Old.Blake2b.sigma[r]!)[i]! = ((JAM.Blake2b.sigma[r]'hr)[i]).val := by
  have : ∀ r (hr : r < 10) i (hi : i < 16),
      (Old.Blake2b.sigma[r]!)[i]! = ((JAM.Blake2b.sigma[r]'hr)[i]'hi).val := by decide
  exact this r hr i hi

theorem blake2b_m_get (m : Vector UInt64 16) (r : Nat) (hr : r < 10) (i : Nat) (hi : i < 16) :
    m.toArray[(Old.Blake2b.sigma[r]!)[i]!]! = m[(JAM.Blake2b.sigma[r]'hr)[i]] := by
  rw [blake2b_sigma_get r i hr hi, getV _ _ (Fin.isLt _)]; rfl

theorem blake2b_compress_eq_old (h : Vector UInt64 8) (block : List UInt8) (t : Nat) (last : Bool) :
    Old.Blake2b.compress h.toArray block t last = (JAM.Blake2b.compress h block t last).toArray := by
  unfold Old.Blake2b.compress JAM.Blake2b.compress
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  have h0 : h.toArray ++ Old.Blake2b.iv = (h ++ JAM.Blake2b.iv).toArray := by
    rw [show Old.Blake2b.iv = JAM.Blake2b.iv.toArray from rfl]; rfl
  rw [h0, blake2b_words_eq_old]
  generalize h ++ JAM.Blake2b.iv = v
  generalize JAM.Blake2b.words block = m
  have hm : ∀ r, r ∈ List.range' 0 [:12].size → ∀ (i : Nat) (hi : i < 16),
      m.toArray[(Old.Blake2b.sigma[r % 10]!)[i]!]! = m[(JAM.Blake2b.sigma[r % 10]'(Nat.mod_lt _ (by decide)))[i]] :=
    fun r _ i hi => blake2b_m_get m (r % 10) _ i hi
  have step : ∀ r, r ∈ List.range' 0 [:12].size → ∀ (a : Array UInt64) (b : Vector UInt64 16), a = b.toArray →
      LoopRel.StepRel (fun (a : Array UInt64) (b : Vector UInt64 16) => a = b.toArray)
        (pure (ForInStep.yield (Old.Blake2b.mix (Old.Blake2b.mix (Old.Blake2b.mix (Old.Blake2b.mix (Old.Blake2b.mix (Old.Blake2b.mix (Old.Blake2b.mix (Old.Blake2b.mix a
          0 4 8 12 m.toArray[(Old.Blake2b.sigma[r % 10]!)[0]!]! m.toArray[(Old.Blake2b.sigma[r % 10]!)[1]!]!)
          1 5 9 13 m.toArray[(Old.Blake2b.sigma[r % 10]!)[2]!]! m.toArray[(Old.Blake2b.sigma[r % 10]!)[3]!]!)
          2 6 10 14 m.toArray[(Old.Blake2b.sigma[r % 10]!)[4]!]! m.toArray[(Old.Blake2b.sigma[r % 10]!)[5]!]!)
          3 7 11 15 m.toArray[(Old.Blake2b.sigma[r % 10]!)[6]!]! m.toArray[(Old.Blake2b.sigma[r % 10]!)[7]!]!)
          0 5 10 15 m.toArray[(Old.Blake2b.sigma[r % 10]!)[8]!]! m.toArray[(Old.Blake2b.sigma[r % 10]!)[9]!]!)
          1 6 11 12 m.toArray[(Old.Blake2b.sigma[r % 10]!)[10]!]! m.toArray[(Old.Blake2b.sigma[r % 10]!)[11]!]!)
          2 7 8 13 m.toArray[(Old.Blake2b.sigma[r % 10]!)[12]!]! m.toArray[(Old.Blake2b.sigma[r % 10]!)[13]!]!)
          3 4 9 14 m.toArray[(Old.Blake2b.sigma[r % 10]!)[14]!]! m.toArray[(Old.Blake2b.sigma[r % 10]!)[15]!]!)) : Id _).run
        (pure (ForInStep.yield (
          let s := JAM.Blake2b.sigma[r % 10]'(Nat.mod_lt _ (by decide))
          JAM.Blake2b.mix (JAM.Blake2b.mix (JAM.Blake2b.mix (JAM.Blake2b.mix (JAM.Blake2b.mix (JAM.Blake2b.mix (JAM.Blake2b.mix (JAM.Blake2b.mix b
          0 4 8 12 m[s[0]] m[s[1]]) 1 5 9 13 m[s[2]] m[s[3]]) 2 6 10 14 m[s[4]] m[s[5]])
          3 7 11 15 m[s[6]] m[s[7]]) 0 5 10 15 m[s[8]] m[s[9]]) 1 6 11 12 m[s[10]] m[s[11]])
          2 7 8 13 m[s[12]] m[s[13]]) 3 4 9 14 m[s[14]] m[s[15]])) : Id _).run := by
    rintro r hr a b rfl
    have e := hm r hr
    simp only [LoopRel.StepRel, Id.run, pure]
    rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide), e 5 (by decide), e 6 (by decide), e 7 (by decide), e 8 (by decide), e 9 (by decide), e 10 (by decide), e 11 (by decide), e 12 (by decide), e 13 (by decide), e 14 (by decide), e 15 (by decide)]
    simp only [← blake2b_mix_eq_old]
    rfl
  have fin : ∀ (b : Vector UInt64 16), Array.map (fun i => h.toArray[i]! ^^^ b.toArray[i]! ^^^ b.toArray[i + 8]!) (List.range 8).toArray
      = (Vector.ofFn fun (i : Fin 8) => h[i] ^^^ b[i.val] ^^^ b[i.val + 8]).toArray := by
    intro b; apply Array.ext
    · simp
    · intro i h1 h2
      simp only [Array.size_map, List.size_toArray, List.length_range] at h1
      simp [h1, getV _ _ (show i < 16 by omega), getV _ _ (show i + 8 < 16 by omega), getElem!_pos]
  cases last
  · rw [getV _ _ (by decide), setV _ _ (by decide), getV _ _ (by decide), setV _ _ (by decide)]
    refine LoopRel.bind_rel (fun (a : Array UInt64) (b : Vector UInt64 16) => a = b.toArray) (fun (a : Array UInt64) (b : Vector UInt64 8) => a = b.toArray) ?_ ?_
    · refine LoopRel.forIn_forIn (fun (a : Array UInt64) (b : Vector UInt64 16) => a = b.toArray) _ _ _ _ ?_ ?_
      · rfl
      · exact step
    · rintro _ b rfl; exact fin b
  · rw [getV _ _ (by decide), setV _ _ (by decide), getV _ _ (by decide), setV _ _ (by decide)]
    simp only [ite_true]
    rw [getV _ _ (by decide), setV _ _ (by decide)]
    refine LoopRel.bind_rel (fun (a : Array UInt64) (b : Vector UInt64 16) => a = b.toArray) (fun (a : Array UInt64) (b : Vector UInt64 8) => a = b.toArray) ?_ ?_
    · refine LoopRel.forIn_forIn (fun (a : Array UInt64) (b : Vector UInt64 16) => a = b.toArray) _ _ _ _ ?_ ?_
      · rfl
      · exact step
    · rintro _ b rfl; exact fin b


theorem blake2b_blocks_eq_old (h : Vector UInt64 8) (msg : ByteArray) :
    Old.Blake2b.blocks h.toArray msg = (JAM.Blake2b.blocks h msg).toArray := by
  unfold Old.Blake2b.blocks JAM.Blake2b.blocks
  simp only
  rw [← blake2b_compress_eq_old]
  congr 1
  generalize List.range _ = l
  induction l generalizing h with
  | nil => rfl
  | cons k l ih => simp only [List.foldl_cons, blake2b_compress_eq_old, ih]

theorem blake2b_hash_eq_old (n : Nat) (msg : ByteArray) : Old.Blake2b.hash n msg = JAM.Blake2b.hash n msg := by
  unfold Old.Blake2b.hash JAM.Blake2b.hash
  have hi : Old.Blake2b.iv.set! 0 (Old.Blake2b.iv[0]! ^^^ 0x01010000 ^^^ UInt64.ofNat n)
      = (JAM.Blake2b.iv.set 0 (JAM.Blake2b.iv[0] ^^^ 0x01010000 ^^^ UInt64.ofNat n)).toArray := by
    rw [show Old.Blake2b.iv = JAM.Blake2b.iv.toArray from rfl, getV _ _ (by decide), setV _ _ (by decide)]
  simp only [hi, blake2b_blocks_eq_old]
  congr 3
  funext k
  generalize JAM.Blake2b.blocks _ msg = v
  simp [getElem!_def, Vector.getElem?_toArray]
  rfl


end JAM.Theorems.CheckedIndex
