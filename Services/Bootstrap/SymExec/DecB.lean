/-!
# Decimal octets of a natural

`decB n`: the UTF-8 octets of `Nat.repr n` (`repr_utf8`), by the recursion of `Nat.toDigits 10`:
the decimal of n / 10, then the digit n mod 10. Used for strings that `format!` builds from a `{}`
argument (storage keys).
-/

namespace Services.Bootstrap.SymExec

/-- The decimal octets of n: Nat.repr's UTF-8 encoding, by its recursion. -/
def decB (n : Nat) : List UInt8 :=
  if n < 10 then [UInt8.ofNat (48 + n)] else decB (n / 10) ++ [UInt8.ofNat (48 + n % 10)]
decreasing_by omega

theorem digit_utf8 (d : Nat) (hd : d < 10) : [Nat.digitChar d].utf8Encode.data.toList = [UInt8.ofNat (48 + d)] := by
  match d, hd with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => decide +kernel

theorem bsize (bs : ByteArray) : bs.size = bs.data.toList.length := by
  rw [Array.length_toList]; rfl

theorem get!_eq (bs : ByteArray) (i : Nat) (hi : i < bs.data.toList.length) : bs.get! i = bs.data.toList[i] := by
  show bs.data[i]! = _
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hi)]
  simp

theorem toList_loop (bs : ByteArray) : ∀ (k i : Nat) (r : List UInt8), bs.size - i = k →
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i
  | 0, i, r, h => by
    rw [ByteArray.toList.loop, if_neg (by omega), List.drop_eq_nil_of_le (by rw [bsize] at h; omega), List.append_nil]
  | k + 1, i, r, h => by
    rw [ByteArray.toList.loop, if_pos (by omega), toList_loop bs k (i + 1) _ (by omega)]
    have hi : i < bs.data.toList.length := by rw [bsize] at h; omega
    rw [List.reverse_cons, List.append_assoc, List.singleton_append, List.drop_eq_getElem_cons hi, get!_eq bs i hi]

theorem ByteArray.toList_eq (bs : ByteArray) : bs.toList = bs.data.toList := by
  rw [ByteArray.toList, toList_loop bs bs.size 0 [] (by omega)]; simp

theorem toDigits_utf8 (n : Nat) : (Nat.toDigits 10 n).utf8Encode.data.toList = decB n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [Nat.toDigits_eq_ite (by decide), decB]
    split
    · rename_i h; exact digit_utf8 n h
    · rename_i h
      rw [List.utf8Encode_append, ByteArray.toList_data_append, ih (n / 10) (by omega), digit_utf8 _ (Nat.mod_lt _ (by decide))]

theorem repr_utf8 (n : Nat) : (Nat.repr n).toUTF8.toList = decB n := by
  rw [ByteArray.toList_eq, String.toUTF8_eq_toByteArray, Nat.repr_eq_ofList_toDigits, String.toByteArray_ofList, toDigits_utf8]

end Services.Bootstrap.SymExec
