import JAM.Blake2b

/-!
# Fast compiled Blake2b, proved equal to `JAM.Blake2b`

The faster implementations of `JAM.Blake2b.blocks` and `JAM.Blake2b.hash`, moved out of the spec
file. Each equality is registered with `@[csimp]`; `hash256_eq_hash256Fast` restates ℋ so that its
compiled code uses `hashFast` too.
-/

namespace JAM.Blake2b

/-! ## Fast compiled form

The spec definitions (`JAM.Blake2b`) read each 128-octet block as a `List UInt8` and fetch every octet with
`List.getD`, which dominates the running time. The versions below read the octets straight from the
message's `ByteArray`. They are proved equal to the spec definitions and registered with
`@[csimp]`, so compiled code uses them while the kernel and every theorem see the spec definitions.
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

/-- `ByteArray.toList` lists the underlying array. -/
theorem toList_eq_data_toList (bs : ByteArray) : bs.toList = bs.data.toList := toList_eq_data bs

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

/-! ## Faster compiled form

`blocksFast` still keeps the working vector in an `Array UInt64`, whose elements are boxed, so every
step of G allocates. The versions below keep the working vector and the chaining value in structures
with unboxed `UInt64` fields (`S16`, `S8`), unroll the twelve rounds, and read the message words
straight from the `ByteArray`. `hash_eq_hashFast` proves `hash = hashFast` and registers it with
`@[csimp]`; the kernel and every theorem still see `hash`.
-/

/-- The working vector v (RFC 7693 §3.2), unboxed. -/
structure S16 where

  v0 : UInt64
  v1 : UInt64
  v2 : UInt64
  v3 : UInt64
  v4 : UInt64
  v5 : UInt64
  v6 : UInt64
  v7 : UInt64
  v8 : UInt64
  v9 : UInt64
  v10 : UInt64
  v11 : UInt64
  v12 : UInt64
  v13 : UInt64
  v14 : UInt64
  v15 : UInt64

/-- The working vector as the array `compressWords` uses. -/
def S16.toArray (s : S16) : Array UInt64 :=
  #[s.v0, s.v1, s.v2, s.v3, s.v4, s.v5, s.v6, s.v7, s.v8, s.v9, s.v10, s.v11, s.v12, s.v13, s.v14, s.v15]

/-- The chaining value h (RFC 7693 §3.2), unboxed. -/
structure S8 where

  h0 : UInt64
  h1 : UInt64
  h2 : UInt64
  h3 : UInt64
  h4 : UInt64
  h5 : UInt64
  h6 : UInt64
  h7 : UInt64

/-- The chaining value as an array. -/
def S8.toArray (h : S8) : Array UInt64 :=
  #[h.h0, h.h1, h.h2, h.h3, h.h4, h.h5, h.h6, h.h7]

/-- `mix · 0 4 8 12` on `S16`. -/
@[inline] def g0 (s : S16) (x y : UInt64) : S16 :=
  let a := s.v0 + s.v4 + x
  let d := rotr (s.v12 ^^^ a) 32
  let c := s.v8 + d
  let b := rotr (s.v4 ^^^ c) 24
  let a := a + b + y
  let d := rotr (d ^^^ a) 16
  let c := c + d
  let b := rotr (b ^^^ c) 63
  ⟨a, s.v1, s.v2, s.v3, b, s.v5, s.v6, s.v7, c, s.v9, s.v10, s.v11, d, s.v13, s.v14, s.v15⟩

theorem g0_toArray (s : S16) (x y : UInt64) :
    (g0 s x y).toArray = mix s.toArray 0 4 8 12 x y := by
  simp only [g0, mix, S16.toArray, Id.run]
  simp
  rfl

/-- `mix · 1 5 9 13` on `S16`. -/
@[inline] def g1 (s : S16) (x y : UInt64) : S16 :=
  let a := s.v1 + s.v5 + x
  let d := rotr (s.v13 ^^^ a) 32
  let c := s.v9 + d
  let b := rotr (s.v5 ^^^ c) 24
  let a := a + b + y
  let d := rotr (d ^^^ a) 16
  let c := c + d
  let b := rotr (b ^^^ c) 63
  ⟨s.v0, a, s.v2, s.v3, s.v4, b, s.v6, s.v7, s.v8, c, s.v10, s.v11, s.v12, d, s.v14, s.v15⟩

theorem g1_toArray (s : S16) (x y : UInt64) :
    (g1 s x y).toArray = mix s.toArray 1 5 9 13 x y := by
  simp only [g1, mix, S16.toArray, Id.run]
  simp
  rfl

/-- `mix · 2 6 10 14` on `S16`. -/
@[inline] def g2 (s : S16) (x y : UInt64) : S16 :=
  let a := s.v2 + s.v6 + x
  let d := rotr (s.v14 ^^^ a) 32
  let c := s.v10 + d
  let b := rotr (s.v6 ^^^ c) 24
  let a := a + b + y
  let d := rotr (d ^^^ a) 16
  let c := c + d
  let b := rotr (b ^^^ c) 63
  ⟨s.v0, s.v1, a, s.v3, s.v4, s.v5, b, s.v7, s.v8, s.v9, c, s.v11, s.v12, s.v13, d, s.v15⟩

theorem g2_toArray (s : S16) (x y : UInt64) :
    (g2 s x y).toArray = mix s.toArray 2 6 10 14 x y := by
  simp only [g2, mix, S16.toArray, Id.run]
  simp
  rfl

/-- `mix · 3 7 11 15` on `S16`. -/
@[inline] def g3 (s : S16) (x y : UInt64) : S16 :=
  let a := s.v3 + s.v7 + x
  let d := rotr (s.v15 ^^^ a) 32
  let c := s.v11 + d
  let b := rotr (s.v7 ^^^ c) 24
  let a := a + b + y
  let d := rotr (d ^^^ a) 16
  let c := c + d
  let b := rotr (b ^^^ c) 63
  ⟨s.v0, s.v1, s.v2, a, s.v4, s.v5, s.v6, b, s.v8, s.v9, s.v10, c, s.v12, s.v13, s.v14, d⟩

theorem g3_toArray (s : S16) (x y : UInt64) :
    (g3 s x y).toArray = mix s.toArray 3 7 11 15 x y := by
  simp only [g3, mix, S16.toArray, Id.run]
  simp
  rfl

/-- `mix · 0 5 10 15` on `S16`. -/
@[inline] def g4 (s : S16) (x y : UInt64) : S16 :=
  let a := s.v0 + s.v5 + x
  let d := rotr (s.v15 ^^^ a) 32
  let c := s.v10 + d
  let b := rotr (s.v5 ^^^ c) 24
  let a := a + b + y
  let d := rotr (d ^^^ a) 16
  let c := c + d
  let b := rotr (b ^^^ c) 63
  ⟨a, s.v1, s.v2, s.v3, s.v4, b, s.v6, s.v7, s.v8, s.v9, c, s.v11, s.v12, s.v13, s.v14, d⟩

theorem g4_toArray (s : S16) (x y : UInt64) :
    (g4 s x y).toArray = mix s.toArray 0 5 10 15 x y := by
  simp only [g4, mix, S16.toArray, Id.run]
  simp
  rfl

/-- `mix · 1 6 11 12` on `S16`. -/
@[inline] def g5 (s : S16) (x y : UInt64) : S16 :=
  let a := s.v1 + s.v6 + x
  let d := rotr (s.v12 ^^^ a) 32
  let c := s.v11 + d
  let b := rotr (s.v6 ^^^ c) 24
  let a := a + b + y
  let d := rotr (d ^^^ a) 16
  let c := c + d
  let b := rotr (b ^^^ c) 63
  ⟨s.v0, a, s.v2, s.v3, s.v4, s.v5, b, s.v7, s.v8, s.v9, s.v10, c, d, s.v13, s.v14, s.v15⟩

theorem g5_toArray (s : S16) (x y : UInt64) :
    (g5 s x y).toArray = mix s.toArray 1 6 11 12 x y := by
  simp only [g5, mix, S16.toArray, Id.run]
  simp
  rfl

/-- `mix · 2 7 8 13` on `S16`. -/
@[inline] def g6 (s : S16) (x y : UInt64) : S16 :=
  let a := s.v2 + s.v7 + x
  let d := rotr (s.v13 ^^^ a) 32
  let c := s.v8 + d
  let b := rotr (s.v7 ^^^ c) 24
  let a := a + b + y
  let d := rotr (d ^^^ a) 16
  let c := c + d
  let b := rotr (b ^^^ c) 63
  ⟨s.v0, s.v1, a, s.v3, s.v4, s.v5, s.v6, b, c, s.v9, s.v10, s.v11, s.v12, d, s.v14, s.v15⟩

theorem g6_toArray (s : S16) (x y : UInt64) :
    (g6 s x y).toArray = mix s.toArray 2 7 8 13 x y := by
  simp only [g6, mix, S16.toArray, Id.run]
  simp
  rfl

/-- `mix · 3 4 9 14` on `S16`. -/
@[inline] def g7 (s : S16) (x y : UInt64) : S16 :=
  let a := s.v3 + s.v4 + x
  let d := rotr (s.v14 ^^^ a) 32
  let c := s.v9 + d
  let b := rotr (s.v4 ^^^ c) 24
  let a := a + b + y
  let d := rotr (d ^^^ a) 16
  let c := c + d
  let b := rotr (b ^^^ c) 63
  ⟨s.v0, s.v1, s.v2, a, b, s.v5, s.v6, s.v7, s.v8, c, s.v10, s.v11, s.v12, s.v13, d, s.v15⟩

theorem g7_toArray (s : S16) (x y : UInt64) :
    (g7 s x y).toArray = mix s.toArray 3 4 9 14 x y := by
  simp only [g7, mix, S16.toArray, Id.run]
  simp
  rfl

/-- One round of F: the eight G calls, with the message words in the order the round uses them. -/
def roundS (s : S16) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt64) : S16 :=
  g7 (g6 (g5 (g4 (g3 (g2 (g1 (g0 s x0 x1) x2 x3) x4 x5) x6 x7) x8 x9) x10 x11) x12 x13) x14 x15

/-- One round of F on the array, as `compressWords` performs it for row `r` of σ. -/
def roundA (m : Array UInt64) (r : Nat) (v : Array UInt64) : Array UInt64 :=
  let s := sigma[r % 10]!
  let v := mix v 0 4 8 12 m[s[0]!]! m[s[1]!]!
  let v := mix v 1 5 9 13 m[s[2]!]! m[s[3]!]!
  let v := mix v 2 6 10 14 m[s[4]!]! m[s[5]!]!
  let v := mix v 3 7 11 15 m[s[6]!]! m[s[7]!]!
  let v := mix v 0 5 10 15 m[s[8]!]! m[s[9]!]!
  let v := mix v 1 6 11 12 m[s[10]!]! m[s[11]!]!
  let v := mix v 2 7 8 13 m[s[12]!]! m[s[13]!]!
  mix v 3 4 9 14 m[s[14]!]! m[s[15]!]!

theorem roundA_toArray (m : Array UInt64) (r : Nat) (s : S16) :
    roundA m r s.toArray = (roundS s m[(sigma[r % 10]!)[0]!]! m[(sigma[r % 10]!)[1]!]! m[(sigma[r % 10]!)[2]!]! m[(sigma[r % 10]!)[3]!]! m[(sigma[r % 10]!)[4]!]! m[(sigma[r % 10]!)[5]!]! m[(sigma[r % 10]!)[6]!]! m[(sigma[r % 10]!)[7]!]! m[(sigma[r % 10]!)[8]!]! m[(sigma[r % 10]!)[9]!]! m[(sigma[r % 10]!)[10]!]! m[(sigma[r % 10]!)[11]!]! m[(sigma[r % 10]!)[12]!]! m[(sigma[r % 10]!)[13]!]! m[(sigma[r % 10]!)[14]!]! m[(sigma[r % 10]!)[15]!]!).toArray := by
  simp only [roundA, roundS, g0_toArray, g1_toArray, g2_toArray, g3_toArray, g4_toArray,
    g5_toArray, g6_toArray, g7_toArray]

/-- F (RFC 7693 §3.2) on unboxed words: the chaining value `h`, the message words `m₀ … m₁₅`, the
    byte counter `t` and the final-block flag. -/
def compressS (h : S8) (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 : UInt64) (t : Nat) (last : Bool) : S8 :=
  let s : S16 := ⟨h.h0, h.h1, h.h2, h.h3, h.h4, h.h5, h.h6, h.h7,
    0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
    0x510e527fade682d1 ^^^ UInt64.ofNat (t % 2 ^ 64), 0x9b05688c2b3e6c1f ^^^ UInt64.ofNat (t / 2 ^ 64),
    if last then 0x1f83d9abfb41bd6b ^^^ 0xFFFFFFFFFFFFFFFF else 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179⟩
  let s := roundS s m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15
  let s := roundS s m14 m10 m4 m8 m9 m15 m13 m6 m1 m12 m0 m2 m11 m7 m5 m3
  let s := roundS s m11 m8 m12 m0 m5 m2 m15 m13 m10 m14 m3 m6 m7 m1 m9 m4
  let s := roundS s m7 m9 m3 m1 m13 m12 m11 m14 m2 m6 m5 m10 m4 m0 m15 m8
  let s := roundS s m9 m0 m5 m7 m2 m4 m10 m15 m14 m1 m11 m12 m6 m8 m3 m13
  let s := roundS s m2 m12 m6 m10 m0 m11 m8 m3 m4 m13 m7 m5 m15 m14 m1 m9
  let s := roundS s m12 m5 m1 m15 m14 m13 m4 m10 m0 m7 m6 m3 m9 m2 m8 m11
  let s := roundS s m13 m11 m7 m14 m12 m1 m3 m9 m5 m0 m15 m4 m8 m6 m2 m10
  let s := roundS s m6 m15 m14 m9 m11 m3 m0 m8 m12 m2 m13 m7 m1 m4 m10 m5
  let s := roundS s m10 m2 m8 m4 m7 m6 m1 m5 m15 m11 m9 m14 m3 m12 m13 m0
  let s := roundS s m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15
  let s := roundS s m14 m10 m4 m8 m9 m15 m13 m6 m1 m12 m0 m2 m11 m7 m5 m3
  ⟨h.h0 ^^^ s.v0 ^^^ s.v8, h.h1 ^^^ s.v1 ^^^ s.v9, h.h2 ^^^ s.v2 ^^^ s.v10, h.h3 ^^^ s.v3 ^^^ s.v11, h.h4 ^^^ s.v4 ^^^ s.v12, h.h5 ^^^ s.v5 ^^^ s.v13, h.h6 ^^^ s.v6 ^^^ s.v14, h.h7 ^^^ s.v7 ^^^ s.v15⟩

/-- The working vector at the start of F, before the rounds. -/
def initA (h : Array UInt64) (t : Nat) (last : Bool) : Array UInt64 := Id.run do
  let mut v := h ++ iv
  v := v.set! 12 (v[12]! ^^^ UInt64.ofNat (t % 2 ^ 64))
  v := v.set! 13 (v[13]! ^^^ UInt64.ofNat (t / 2 ^ 64))
  if last then v := v.set! 14 (v[14]! ^^^ 0xFFFFFFFFFFFFFFFF)
  return v

/-- The output of F from the chaining value and the final working vector. -/
def finalA (h v : Array UInt64) : Array UInt64 :=
  (List.range 8).toArray.map fun i => h[i]! ^^^ v[i]! ^^^ v[i + 8]!

theorem compressWords_eq_rounds (h m : Array UInt64) (t : Nat) (last : Bool) :
    compressWords h m t last = finalA h (roundA m 11 (roundA m 10 (roundA m 9 (roundA m 8
      (roundA m 7 (roundA m 6 (roundA m 5 (roundA m 4 (roundA m 3 (roundA m 2 (roundA m 1
      (roundA m 0 (initA h t last))))))))))))) := by
  cases last <;>
  simp only [compressWords, initA, finalA, roundA, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, List.range'_succ, List.range'_zero, List.forIn_cons, List.forIn_nil] <;>
  rfl

theorem finalA_toArray (h : S8) (s : S16) :
    finalA h.toArray s.toArray = (⟨h.h0 ^^^ s.v0 ^^^ s.v8, h.h1 ^^^ s.v1 ^^^ s.v9, h.h2 ^^^ s.v2 ^^^ s.v10, h.h3 ^^^ s.v3 ^^^ s.v11, h.h4 ^^^ s.v4 ^^^ s.v12, h.h5 ^^^ s.v5 ^^^ s.v13, h.h6 ^^^ s.v6 ^^^ s.v14, h.h7 ^^^ s.v7 ^^^ s.v15⟩ : S8).toArray := by
  simp [finalA, List.range_succ, S8.toArray, S16.toArray]

theorem compressWords_toArray (h : S8) (m : Array UInt64) (t : Nat) (last : Bool) :
    compressWords h.toArray m t last
      = (compressS h m[0]! m[1]! m[2]! m[3]! m[4]! m[5]! m[6]! m[7]! m[8]! m[9]! m[10]! m[11]! m[12]! m[13]! m[14]! m[15]! t last).toArray := by
  have hi : initA h.toArray t last = (⟨h.h0, h.h1, h.h2, h.h3, h.h4, h.h5, h.h6, h.h7,
      0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
      0x510e527fade682d1 ^^^ UInt64.ofNat (t % 2 ^ 64), 0x9b05688c2b3e6c1f ^^^ UInt64.ofNat (t / 2 ^ 64),
      if last then 0x1f83d9abfb41bd6b ^^^ 0xFFFFFFFFFFFFFFFF else 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179⟩ : S16).toArray := by
    cases last <;> rfl
  rw [compressWords_eq_rounds, hi]
  simp only [roundA_toArray, finalA_toArray]
  rfl


/-- F on the 128-octet block at octet `o` of `msg` (octets past its end read as 0). -/
@[inline] def compressAt (h : S8) (msg : ByteArray) (o t : Nat) (last : Bool) : S8 :=
  compressS h (wordAt msg o) (wordAt msg (o + 8)) (wordAt msg (o + 16)) (wordAt msg (o + 24))
    (wordAt msg (o + 32)) (wordAt msg (o + 40)) (wordAt msg (o + 48)) (wordAt msg (o + 56))
    (wordAt msg (o + 64)) (wordAt msg (o + 72)) (wordAt msg (o + 80)) (wordAt msg (o + 88))
    (wordAt msg (o + 96)) (wordAt msg (o + 104)) (wordAt msg (o + 112)) (wordAt msg (o + 120))
    t last

theorem compressWords_wordsAt (h : S8) (msg : ByteArray) (o t : Nat) (last : Bool) :
    compressWords h.toArray (wordsAt msg o) t last = (compressAt h msg o t last).toArray := by
  rw [compressWords_toArray]
  simp [wordsAt, compressAt]

/-- `n` non-final blocks, starting with block `k`. -/
def blocksLoop (msg : ByteArray) : Nat → Nat → S8 → S8
  | 0, _, h => h
  | n + 1, k, h => blocksLoop msg n (k + 1) (compressAt h msg (128 * k) (128 * (k + 1)) false)

theorem foldl_blocksLoop (msg : ByteArray) (n k : Nat) (h : S8) :
    (List.range' k n).foldl
        (fun h k => compressWords h (wordsAt msg (128 * k)) (128 * (k + 1)) false) h.toArray
      = (blocksLoop msg n k h).toArray := by
  induction n generalizing k h with
  | zero => rfl
  | succ n ih => simp only [List.range'_succ, List.foldl_cons, compressWords_wordsAt, ih, blocksLoop]

/-- `blocks` on unboxed words. -/
def blocksS (h : S8) (msg : ByteArray) : S8 :=
  let len := msg.size
  let nb := max 1 ((len + 127) / 128)
  compressAt (blocksLoop msg (nb - 1) 0 h) msg (128 * (nb - 1)) len true

theorem blocksFast_toArray (h : S8) (msg : ByteArray) :
    blocksFast h.toArray msg = (blocksS h msg).toArray := by
  simp only [blocksFast, blocksS, List.range_eq_range', foldl_blocksLoop, compressWords_wordsAt]

/-- Word `i` of the chaining value (0 past the eighth), as `h.toArray[i]!` reads it. -/
@[inline] def S8.get (h : S8) (i : Nat) : UInt64 :=
  match i with
  | 0 => h.h0 | 1 => h.h1 | 2 => h.h2 | 3 => h.h3
  | 4 => h.h4 | 5 => h.h5 | 6 => h.h6 | 7 => h.h7
  | _ => 0

theorem S8.get_eq (h : S8) (i : Nat) : h.toArray[i]! = h.get i := by
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => rfl
  | i + 8 =>
    simp [S8.toArray, S8.get]; rfl

/-- Append octets `k, k+1, …, k+c-1` of the digest to `b`. -/
def outLoop (h : S8) : Nat → Nat → ByteArray → ByteArray
  | 0, _, b => b
  | c + 1, k, b => outLoop h c (k + 1) (b.push (h.get (k / 8) >>> (8 * (k % 8)).toUInt64).toUInt8)

theorem outLoop_data (h : S8) (c k : Nat) (b : ByteArray) :
    (outLoop h c k b).data.toList
      = b.data.toList ++ (List.range' k c).map fun k => (h.toArray[k / 8]! >>> (8 * (k % 8)).toUInt64).toUInt8 := by
  induction c generalizing k b with
  | zero => simp [outLoop]
  | succ c ih =>
    simp [outLoop, ih, List.range'_succ, ByteArray.data_push, S8.get_eq]

/-- The first `n` octets of the chaining value, little-endian (`hash`'s output). -/
def outBytes (h : S8) (n : Nat) : ByteArray := outLoop h n 0 (ByteArray.emptyWithCapacity n)

theorem outBytes_eq (h : S8) (n : Nat) :
    outBytes h n = ⟨((List.range n).map fun k => (h.toArray[k / 8]! >>> (8 * (k % 8)).toUInt64).toUInt8).toArray⟩ := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [outBytes, outLoop_data, List.range_eq_range']
  simp [ByteArray.emptyWithCapacity]; rfl

/-- `hash` through `blocksS` and `outBytes`. -/
def hashFast (n : Nat) (msg : ByteArray) : ByteArray :=
  outBytes (blocksS ⟨0x6a09e667f3bcc908 ^^^ 0x01010000 ^^^ UInt64.ofNat n, 0xbb67ae8584caa73b,
    0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1, 0x510e527fade682d1, 0x9b05688c2b3e6c1f,
    0x1f83d9abfb41bd6b, 0x5be0cd19137e2179⟩ msg) n

@[csimp] theorem hash_eq_hashFast : @hash = @hashFast := by
  funext n msg
  have hi : iv.set! 0 (iv[0]! ^^^ 0x01010000 ^^^ UInt64.ofNat n)
      = S8.toArray ⟨0x6a09e667f3bcc908 ^^^ 0x01010000 ^^^ UInt64.ofNat n, 0xbb67ae8584caa73b,
        0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1, 0x510e527fade682d1, 0x9b05688c2b3e6c1f,
        0x1f83d9abfb41bd6b, 0x5be0cd19137e2179⟩ := rfl
  simp only [hash, hashFast, hi, blocks_eq_blocksFast, blocksFast_toArray, outBytes_eq]

/-- ℋ (`hash256`), restated so that its compiled code uses `hashFast`. -/
def hash256Fast (msg : ByteArray) : ByteArray := hash 32 msg

@[csimp] theorem hash256_eq_hash256Fast : @hash256 = @hash256Fast := rfl

end JAM.Blake2b
