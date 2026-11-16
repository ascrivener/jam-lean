/-!
# Blake2b (RFC 7693), as used by the Gray Paper's ℋ (GP v0.8.0 §3.8: ℋ is Blake2b-256)

Unkeyed Blake2b with a configurable digest length, in pure Lean: total, no `extern` code, so it
can be evaluated by the kernel.
-/

namespace JAM.Blake2b

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

/-! ## Fast compiled form

The definitions above read each 128-octet block as a `List UInt8` and fetch every octet with
`List.getD`, which dominates the running time. The versions below read the octets straight from the
message's `ByteArray`. They are proved equal to the definitions above and registered with
`@[csimp]`, so compiled code uses them while the kernel and every theorem see the definitions above.
-/

/-- Octet `i` of `msg`, or 0 past its end. -/
@[inline] def byteAt (msg : ByteArray) (i : Nat) : UInt8 :=
  if h : i < msg.size then msg[i] else 0

/-- The little-endian 64-bit word at octets `o … o+7` of `msg` (0 past its end), in the shape of
    `words`'s fold. -/
@[inline] def wordAt (msg : ByteArray) (o : Nat) : UInt64 :=
  ((((((((0 : UInt64) <<< 8 ||| (byteAt msg (o + 7)).toUInt64) <<< 8
    ||| (byteAt msg (o + 6)).toUInt64) <<< 8 ||| (byteAt msg (o + 5)).toUInt64) <<< 8
    ||| (byteAt msg (o + 4)).toUInt64) <<< 8 ||| (byteAt msg (o + 3)).toUInt64) <<< 8
    ||| (byteAt msg (o + 2)).toUInt64) <<< 8 ||| (byteAt msg (o + 1)).toUInt64) <<< 8
    ||| (byteAt msg o).toUInt64

/-- `words` of the block at octet `o` of `msg`. -/
def wordsAt (msg : ByteArray) (o : Nat) : Array UInt64 :=
  Array.ofFn (n := 16) fun i => wordAt msg (o + 8 * i.val)

/-- `compress` with the message words given directly. -/
def compressWords (h : Array UInt64) (m : Array UInt64) (t : Nat) (last : Bool) :
    Array UInt64 := Id.run do
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

theorem compress_eq (h : Array UInt64) (block : List UInt8) (t : Nat) (last : Bool) :
    compress h block t last = compressWords h (words block) t last := rfl

/-- `ByteArray.toList` lists the underlying array. -/
private theorem toList_eq_data (bs : ByteArray) : bs.toList = bs.data.toList := by
  suffices h : ∀ i r, ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i by
    simpa [ByteArray.toList] using h 0 []
  intro i r
  induction i, r using ByteArray.toList.loop.induct bs with
  | case1 i r h ih =>
    rw [ByteArray.toList.loop, ite_eq_left h, ih]
    have hi : i < bs.data.toList.length := by rw [Array.length_toList]; exact h
    rw [List.reverse_cons, List.append_assoc, List.drop_eq_getElem_cons hi]
    rw [List.singleton_append]
    have hb : bs.get! i = bs.data.toList[i] := by
      show bs.data[i]! = bs.data.toList[i]
      simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]
    rw [hb]
  | case2 i r h =>
    rw [ByteArray.toList.loop, ite_eq_right h]
    have : bs.data.toList.length ≤ i := by rw [Array.length_toList]; exact Nat.le_of_not_lt h
    simp [List.drop_eq_nil_of_le this]

theorem getD_extract_toList (msg : ByteArray) (o j : Nat) (hj : j < 128) :
    (msg.extract o (o + 128)).toList.getD j 0 = byteAt msg (o + j) := by
  rw [toList_eq_data, ByteArray.data_extract, List.getD_eq_getElem?_getD, Array.getElem?_toList]
  unfold byteAt
  split
  · rename_i h
    rw [Array.getElem?_extract]
    simp only [ByteArray.getElem_eq_getElem_data]
    have hd : o + j < msg.data.size := h
    rw [ite_eq_left (by omega), Array.getElem?_eq_getElem hd, Option.getD_some]
  · rename_i h
    have hd : ¬ o + j < msg.data.size := h
    rw [Array.getElem?_extract, ite_eq_right (by omega), Option.getD_none]

theorem words_extract (msg : ByteArray) (o : Nat) :
    words (msg.extract o (o + 128)).toList = wordsAt msg o := by
  apply Array.ext
  · simp [words, wordsAt]
  · intro i h1 h2
    simp only [words, Array.size_map, List.size_toArray, List.length_range] at h1
    simp only [words, wordsAt, Array.getElem_map, Array.getElem_ofFn, List.getElem_toArray,
      List.getElem_range]
    have hr : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl
    simp only [hr, List.foldr_cons, List.foldr_nil, wordAt]
    have e : ∀ k, k < 8 → (msg.extract o (o + 128)).toList.getD (8 * i + k) 0
        = byteAt msg (o + 8 * i + k) := fun k hk => by
      rw [getD_extract_toList msg o _ (by omega), Nat.add_assoc]
    simp only [e 1 (by decide), e 2 (by decide), e 3 (by decide),
      e 4 (by decide), e 5 (by decide), e 6 (by decide), e 7 (by decide), Nat.add_zero]
    have e0 := e 0 (by decide); simp only [Nat.add_zero] at e0; rw [e0]

/-- `blocks`, reading each block's words straight from the message. -/
def blocksFast (h : Array UInt64) (msg : ByteArray) : Array UInt64 :=
  let len := msg.size
  let nb := max 1 ((len + 127) / 128)
  let h := (List.range (nb - 1)).foldl
    (fun h k => compressWords h (wordsAt msg (128 * k)) (128 * (k + 1)) false) h
  compressWords h (wordsAt msg (128 * (nb - 1))) len true

@[csimp] theorem blocks_eq_blocksFast : @blocks = @blocksFast := by
  funext h msg
  simp only [blocks, blocksFast, compress_eq, words_extract]

/-- Blake2b with an `n`-octet digest (1 ≤ n ≤ 64), unkeyed (RFC 7693 §3.3). -/
def hash (n : Nat) (msg : ByteArray) : ByteArray :=
  let h := iv.set! 0 (iv[0]! ^^^ 0x01010000 ^^^ UInt64.ofNat n)
  let h := blocks h msg
  let out := (List.range n).map fun k => (h[k / 8]! >>> (8 * (k % 8)).toUInt64).toUInt8
  ⟨out.toArray⟩

/-- ℋ: Blake2b-256 (GP §3.8). -/
def hash256 (msg : ByteArray) : ByteArray := hash 32 msg

end JAM.Blake2b
