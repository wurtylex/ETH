/- Shared little-endian Boolean words, including words with high zero padding.
The paper-specific executable decoders remain unchanged and connect to this
Mathlib-backed arithmetic interface by equality lemmas.
-/
module
public import Mathlib.Data.Nat.Digits.Lemmas

public section
namespace EthBridge.Shared.BinaryWords

@[expose] def value (word : List Bool) : ℕ := Nat.ofDigits 2 (word.map Bool.toNat)

theorem value_eq_foldr (word : List Bool) : value word = word.foldr Nat.bit 0 := by
  induction word with
  | nil => rfl
  | cons b word ih => simp [value, Nat.ofDigits, Nat.bit_val, ← ih, Nat.add_comm]

theorem value_lt_pow_length (word : List Bool) : value word < 2 ^ word.length := by
  simpa only [value, List.length_map] using
    (Nat.ofDigits_lt_base_pow_length (b := 2) (l := word.map Bool.toNat) (by decide)
      (by simp only [List.forall_mem_map]; intro b _; cases b <;> decide))

theorem value_append (xs ys : List Bool) :
    value (xs ++ ys) = value xs + 2 ^ xs.length * value ys := by
  simp only [value, List.map_append, Nat.ofDigits_append, List.length_map]

theorem value_bits (n : ℕ) : value n.bits = n := by
  change Nat.ofDigits 2 (n.bits.map fun b => cond b 1 0) = n
  rw [← Nat.digits_two_eq_bits, Nat.ofDigits_digits]

theorem log2_value_append_true (xs : List Bool) :
    Nat.log2 (value (xs ++ [true])) = xs.length := by
  have hbound := value_lt_pow_length xs
  have hpow : 0 < 2 ^ xs.length := Nat.two_pow_pos _
  have hval : value (xs ++ [true]) = value xs + 2 ^ xs.length := by
    rw [value_append]
    simp [value, Nat.ofDigits]
  have hpos : value (xs ++ [true]) ≠ 0 := by omega
  apply Nat.le_antisymm
  · have hlt : value (xs ++ [true]) < 2 ^ (xs.length + 1) := by
      rw [pow_succ]
      omega
    have h := (Nat.log2_lt hpos).mpr hlt
    omega
  · exact (Nat.le_log2 hpos).mpr (by omega)

end EthBridge.Shared.BinaryWords
