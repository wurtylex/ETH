/-
SPDX-License-Identifier: Apache-2.0
The executable two-piece family satisfies the existing generic recursion contract.
This certifies a common-width implementation variant of the collected crossing
argument; it does not identify that recursion with the manuscript's literal
unequal-width construction or its numerical recurrence.
-/
module

public import EthBridge.Elementary.Pieces
public import EthBridge.Elementary.PiecesBounds
import Mathlib.Tactic

@[expose] public section
namespace EthBridge.Elementary.PiecesSpec

open Groundwork Groundwork.Prog PaddedDescent.F Finset
open EthBridge.Elementary.Crossing EthBridge.Elementary.PieceBounds
open EthBridge.Elementary.Pieces

/-- The numbered family contains exactly the low and high collected pieces. -/
def semantic (n i : ℕ) : _root_.Pieces.Four n :=
  if i = 0 then pieceA n else pieceB n

theorem family_spec (h n : ℕ) (hn : 1 ≤ n) : family.Spec h n := by
  have hc := capW_half_le_two_mul n hn
  refine { cnt_pos := by change (1 : ℕ) ≤ 2; omega
           d_pos := by change (1 : ℕ) ≤ 1; omega
           m_pos := by decide
           cap_le := ?_
           ex := ⟨semantic n, ?_, ?_, ?_⟩ }
  · intro col i hi
    change (if i = 0 then (if col = true then 2*n else capW n (n/2))
      else (if col = true then capW n (n/2) else 2*n)) ≤ 2*1*n
    split_ifs <;> omega
  · intro x y u v
    change ∑ i ∈ range 2, semantic n i x y u v = 1 * _root_.Pieces.cross x y u v
    simpa [semantic, sum_range_succ, _root_.Pieces.cross, Groundwork.cross] using
      pieceA_add_pieceB n x y u v
  · intro i hi x y u v
    change |semantic n i x y u v| ≤ (2 : ℤ)^(2*n)
    unfold semantic
    split_ifs
    · exact abs_pieceA_le n x y u v
    · exact abs_pieceB_le n x y u v
  · intro pad hp i hi
    change 2^(2*n) ≤ pad.length at hp
    change i < 2 at hi
    have hp' : 2^n ≤ pad.length :=
      (Nat.pow_le_pow_right (by norm_num) (by omega : n ≤ 2*n)).trans hp
    refine ⟨?_, ?_, ?_⟩
    · intro x y u v
      interval_cases i
      · simpa [family, semantic, ClauseBound.Alg.bitsOf] using
          pieceA_rows_program pad n x y u v hp'
      · simpa [family, semantic, ClauseBound.Alg.bitsOf] using
          pieceB_rows_program pad n hn x y u v hp
    · intro x y u v
      interval_cases i
      · simpa [family, semantic, ClauseBound.Alg.bitsOf] using
          pieceA_cols_program pad n hn x y u v hp
      · simpa [family, semantic, ClauseBound.Alg.bitsOf] using
          pieceB_cols_program pad n x y u v hp'
    · intro col x y w
      exact EthBridge.Elementary.PiecesBounds.family_bounds h n hn pad hp i hi col x y w

/-- Concrete parameters for the old, fully implemented generic recursion. -/
theorem family_par : ClauseBound.Gen.Par family (23/24) 2 := by
  apply par_of_two_piece_data family family_spec
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; exact le_rfl
  · rfl
  · intro h n i hn hi
    change (if i = 0 then capW n (n/2) else 2*n) +
      (if i = 0 then 2*n else capW n (n/2)) ≤ capW n (n/2) + 2*n
    split_ifs <;> omega

end EthBridge.Elementary.PiecesSpec
