/-
SPDX-License-Identifier: Apache-2.0
Magnitude bounds for the executable collected factors and their value program.
-/
module

public import EthBridge.Elementary.Pieces

@[expose] public section
namespace EthBridge.Elementary.PiecesBounds

open Finset Groundwork Groundwork.Grid PaddedDescent.F
open EthBridge.Elementary.Crossing EthBridge.Elementary.PieceBounds EthBridge.Elementary.Pieces

/-- The executable top factor is bounded on every name word, valid or invalid. -/
theorem sparseTop_bound (tr : Bool) (n : ℕ) (x y : Bits n) (w : List Bool) :
    |sparseTop tr (List.ofFn x) (List.ofFn y) w| ≤ 1 := by
  rw [sparseTop_eq]
  split_ifs
  · cases tr
    · exact abs_rowTop_le _ x y
    · exact abs_colTop_le _ x y
  · simp

/-- The collected executable bottom is bounded without a name-membership assumption. -/
theorem collectBot_bound (high tr : Bool) (pad : U) (n : ℕ) (x y : Bits n) (w : List Bool)
    (hp : 2 ^ n ≤ pad.length) :
    |collectBot high tr pad (List.ofFn x) (List.ofFn y) w| ≤ (2 : ℤ) ^ (2 * n) := by
  have hf (i : ℕ) :
      |(sideBit tr).Bot i ((Code.sparse (sideS0 tr) n (n/2)).dec w) x y| ≤ (2 : ℤ) ^ n := by
    cases tr
    · exact abs_rowBot_le i _ x y
    · exact abs_colBot_le i _ x y
  cases high
  · rw [collectBot_low pad tr n (n/2) x y w hp]
    exact abs_sum_le_double_bits n _ (lowIndices_card_le n) _ fun i _ => hf i
  · rw [collectBot_high pad tr n (n/2) x y w hp]
    exact abs_sum_le_double_bits n _ (highIndices_card_le n) _ fun i _ => hf i

theorem sparseBot_bound (high tr : Bool) (pad : U) (n : ℕ) (x y : Bits n) (w : List Bool)
    (hp : 2 ^ n ≤ pad.length) :
    |sparseBot high tr pad (List.ofFn x) (List.ofFn y) w| ≤ (2 : ℤ) ^ (2 * n) := by
  unfold sparseBot
  split_ifs
  · exact collectBot_bound high tr pad n x y w hp
  · simp

/-- Exact-length words round-trip through the existing finite-word reader. -/
theorem ofFn_bitsOf {n : ℕ} (w : List Bool) (hw : w.length = n) :
    List.ofFn (Grid.bitsOf n w) = w := by
  subst n
  conv_rhs => rw [← List.ofFn_get w]
  congr 1
  funext k
  simp [Grid.bitsOf]

/-- The value program is bounded on any four words of the specified length. -/
theorem value_bound (high : Bool) (pad : U) (n : ℕ) (hn : 1 ≤ n)
    (x y u v : List Bool) (hx : x.length = n) (hy : y.length = n)
    (hu : u.length = n) (hv : v.length = n) (hp : 2 ^ (2*n) ≤ pad.length) :
    |value high pad x y u v| ≤ (2 : ℤ) ^ (2*n) := by
  have he : value high pad x y u v =
      if high = true then pieceB n (Grid.bitsOf n x) (Grid.bitsOf n y) (Grid.bitsOf n u) (Grid.bitsOf n v)
      else pieceA n (Grid.bitsOf n x) (Grid.bitsOf n y) (Grid.bitsOf n u) (Grid.bitsOf n v) := by
    cases high
    · simpa only [Bool.false_eq_true, ite_false, ofFn_bitsOf x hx, ofFn_bitsOf y hy, ofFn_bitsOf u hu, ofFn_bitsOf v hv]
        using value_low pad n hn (Grid.bitsOf n x) (Grid.bitsOf n y) (Grid.bitsOf n u) (Grid.bitsOf n v) hp
    · simpa only [ite_true, ofFn_bitsOf x hx, ofFn_bitsOf y hy, ofFn_bitsOf u hu, ofFn_bitsOf v hv]
        using value_high pad n hn (Grid.bitsOf n x) (Grid.bitsOf n y) (Grid.bitsOf n u) (Grid.bitsOf n v) hp
  rw [he]
  split_ifs
  · exact abs_pieceB_le n _ _ _ _
  · exact abs_pieceA_le n _ _ _ _

/-- The full-input top factor is bounded even on invalid names. -/
theorem wideTop_bound (x y w : List Bool) : |wideTop x y w| ≤ 1 := by
  unfold wideTop
  split_ifs <;> simp

/-- The explicit length guard makes the wide bottom uniformly bounded on all names. -/
theorem wideBot_bound (high col : Bool) (pad : U) (n : ℕ) (hn : 1 ≤ n)
    (x y : Bits n) (w : List Bool) (hp : 2 ^ (2*n) ≤ pad.length) :
    |wideBot high col pad (List.ofFn x) (List.ofFn y) w| ≤ (2 : ℤ) ^ (2*n) := by
  unfold wideBot
  simp only [List.length_ofFn]
  by_cases hw : w.length = 2*n
  · rw [ite_eq_left hw]
    have ht : (w.take n).length = n := by rw [List.length_take, hw]; omega
    have hd : (w.drop n).length = n := by rw [List.length_drop, hw]; omega
    cases col
    · simp only [Bool.false_eq_true, ite_false]
      exact value_bound high pad n hn _ _ _ _ ht hd List.length_ofFn List.length_ofFn hp
    · simp only [ite_true]
      exact value_bound high pad n hn _ _ _ _ ht List.length_ofFn hd List.length_ofFn hp
  · rw [ite_eq_right hw]
    simp

/-- All factors of the actual two-piece program family meet the declared bit bound. -/
theorem family_bounds (h n : ℕ) (hn : 1 ≤ n) (pad : U) (hp : 2 ^ (2*n) ≤ pad.length)
    (i : ℕ) (_hi : i < 2) (col : Bool) (x y : Bits n) (w : List Bool) :
    |family.top ((pad, col), (h, i), (List.ofFn x, List.ofFn y, w))| ≤ (2 : ℤ) ^ (2*n) ∧
      |family.bot ((pad, col), (h, i), (List.ofFn x, List.ofFn y, w))| ≤ (2 : ℤ) ^ (2*n) := by
  have hp' : 2 ^ n ≤ pad.length :=
    (Nat.pow_le_pow_right (by decide) (by omega : n ≤ 2*n)).trans hp
  have hsTop (tr : Bool) : |sparseTop tr (List.ofFn x) (List.ofFn y) w| ≤ (2 : ℤ) ^ (2*n) :=
    (sparseTop_bound tr n x y w).trans (one_le_pow₀ (by norm_num))
  have hwTop : |wideTop (List.ofFn x) (List.ofFn y) w| ≤ (2 : ℤ) ^ (2*n) :=
    (wideTop_bound _ _ _).trans (one_le_pow₀ (by norm_num))
  by_cases hi : i = 0 <;> cases col <;>
    simp only [family, hi, Bool.false_eq_true, ite_false, ite_true]
  · exact ⟨hsTop true, sparseBot_bound false true pad n x y w hp'⟩
  · exact ⟨hwTop, wideBot_bound false true pad n hn x y w hp⟩
  · exact ⟨hwTop, wideBot_bound true false pad n hn x y w hp⟩
  · exact ⟨hsTop false, sparseBot_bound true false pad n x y w hp'⟩

end EthBridge.Elementary.PiecesBounds
