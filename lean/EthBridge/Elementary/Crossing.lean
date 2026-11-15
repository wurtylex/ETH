/-
SPDX-License-Identifier: Apache-2.0
The indexed crossing pieces, cuts and sparse codes reused below are from
Anthropic's Apache-2.0 development. This module assembles the two-piece split
of the user-supplied elementary ETH manuscript; it proves no ETH endpoint.
-/
module

public import Groundwork.Cross.Cuts
public import StepMachines.Math.Sparse
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
The manuscript orders the corners as x,y above u,v. Its R/C expansion is the
existing indexed expansion with arguments x,u,y,v. We collect all indices on
each side of the half threshold, retaining one common sparse label set in each
favorable cut. These identities are over integers and use no division.
-/

@[expose] public section

namespace EthBridge.Elementary.Crossing

open Finset Groundwork

/-- Indices with at most half of the C factors. -/
def lowIndices (b : ℕ) : Finset ℕ := (range (b + 1)).filter fun i => 2 * i ≤ b

/-- The complementary indices, with more than half of the C factors. -/
def highIndices (b : ℕ) : Finset ℕ := (range (b + 1)).filter fun i => ¬ 2 * i ≤ b

theorem mem_lowIndices {b i : ℕ} : i ∈ lowIndices b ↔ i ≤ b ∧ 2 * i ≤ b := by
  simp [lowIndices]

theorem mem_highIndices {b i : ℕ} : i ∈ highIndices b ↔ i ≤ b ∧ b < 2 * i := by
  simp [highIndices]

/-- The first manuscript piece, in the manuscript's port order. -/
def pieceA (b : ℕ) (x y u v : Bits b) : ℤ :=
  ∑ i ∈ lowIndices b, Groundwork.A b i x u y v

/-- The second manuscript piece, in the same port order. -/
def pieceB (b : ℕ) (x y u v : Bits b) : ℤ :=
  ∑ i ∈ highIndices b, Groundwork.A b i x u y v

/-- The split is exact, also for an empty crossing. -/
theorem pieceA_add_pieceB (b : ℕ) (x y u v : Bits b) :
    pieceA b x y u v + pieceB b x y u v = Groundwork.cross x y u v := by
  have hs : pieceA b x y u v + pieceB b x y u v =
      ∑ i ∈ range (b + 1), Groundwork.A b i x u y v := by
    unfold pieceA pieceB lowIndices highIndices
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : 2 * i ≤ b <;> simp [hi]
  rw [hs, Groundwork.sum_A]
  simp only [Groundwork.cross, eq_comm (a := u) (b := y)]

/-- Right coefficient after collecting indexed terms in the manuscript row cut. -/
def rowCoeff {b : ℕ} (S : Finset ℕ) (β : Fin b → Bell) (u v : Bits b) : ℤ :=
  ∑ i ∈ S, colBit.Bot i β u v

/-- Right coefficient after collecting indexed terms in the manuscript column cut. -/
def colCoeff {b : ℕ} (S : Finset ℕ) (β : Fin b → Bell) (y v : Bits b) : ℤ :=
  ∑ i ∈ S, rowBit.Bot i β y v

theorem indexed_rows (b i : ℕ) (x y u v : Bits b) :
    Groundwork.A b i x u y v =
      ∑ β : Fin b → Bell, colBit.Top β x y * colBit.Bot i β u v := by
  refine (Groundwork.A_cols b i x u y v).trans ?_
  refine Finset.sum_subset (Finset.subset_univ _) fun β _ hβ => ?_
  rw [Groundwork.colBot_eq_zero (by simpa [colLabels] using hβ), mul_zero]

theorem indexed_cols (b i : ℕ) (x y u v : Bits b) :
    Groundwork.A b i x u y v =
      ∑ β : Fin b → Bell, rowBit.Top β x u * rowBit.Bot i β y v := by
  refine (Groundwork.A_rows b i x u y v).trans ?_
  refine Finset.sum_subset (Finset.subset_univ _) fun β _ hβ => ?_
  rw [Groundwork.rowBot_eq_zero (by simpa [rowLabels] using hβ), mul_zero]

theorem collect_rows (b : ℕ) (S : Finset ℕ) (x y u v : Bits b) :
    (∑ i ∈ S, Groundwork.A b i x u y v) =
      ∑ β : Fin b → Bell, colBit.Top β x y * rowCoeff S β u v := by
  simp_rw [indexed_rows]
  rw [Finset.sum_comm]
  simp only [rowCoeff, Finset.mul_sum]

theorem collect_cols (b : ℕ) (S : Finset ℕ) (x y u v : Bits b) :
    (∑ i ∈ S, Groundwork.A b i x u y v) =
      ∑ β : Fin b → Bell, rowBit.Top β x u * colCoeff S β y v := by
  simp_rw [indexed_cols]
  rw [Finset.sum_comm]
  simp only [colCoeff, Finset.mul_sum]

theorem rowCoeff_low_eq_zero {b : ℕ} (β : Fin b → Bell)
    (hβ : β ∉ sparseLab (false, false) b (b / 2)) (u v : Bits b) :
    rowCoeff (lowIndices b) β u v = 0 := by
  have hb : b / 2 < others β := by simpa [sparseLab, others] using hβ
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi' := (mem_lowIndices.mp hi).2
  exact Groundwork.colBot_eq_zero (by omega) u v

theorem colCoeff_high_eq_zero {b : ℕ} (β : Fin b → Bell)
    (hβ : β ∉ sparseLab (true, true) b (b / 2)) (y v : Bits b) :
    colCoeff (highIndices b) β y v = 0 := by
  have hb : b / 2 < #{k | β k ≠ (true, true)} := by simpa [sparseLab] using hβ
  have hcard := Groundwork.card_eq_add_card_ne (true, true) β
  change singlets β + #{k | β k ≠ (true, true)} = b at hcard
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi' := (mem_highIndices.mp hi).2
  exact Groundwork.rowBot_eq_zero (by omega) y v

/-- The favorable row factorization uses one common sparse set, not separate names for i. -/
theorem pieceA_rows (b : ℕ) (x y u v : Bits b) :
    pieceA b x y u v = ∑ β ∈ sparseLab (false, false) b (b / 2),
      colBit.Top β x y * rowCoeff (lowIndices b) β u v := by
  rw [pieceA, collect_rows]
  symm
  exact Finset.sum_subset (Finset.subset_univ _) fun β _ hβ => by
    rw [rowCoeff_low_eq_zero β hβ, mul_zero]

/-- The other cut uses all 4^b Bell words. -/
theorem pieceA_cols (b : ℕ) (x y u v : Bits b) :
    pieceA b x y u v = ∑ β : Fin b → Bell,
      rowBit.Top β x u * colCoeff (lowIndices b) β y v :=
  collect_cols b (lowIndices b) x y u v

/-- The other cut uses all 4^b Bell words. -/
theorem pieceB_rows (b : ℕ) (x y u v : Bits b) :
    pieceB b x y u v = ∑ β : Fin b → Bell,
      colBit.Top β x y * rowCoeff (highIndices b) β u v :=
  collect_rows b (highIndices b) x y u v

/-- The favorable column factorization uses sparse words around the singlet. -/
theorem pieceB_cols (b : ℕ) (x y u v : Bits b) :
    pieceB b x y u v = ∑ β ∈ sparseLab (true, true) b (b / 2),
      rowBit.Top β x u * colCoeff (highIndices b) β y v := by
  rw [pieceB, collect_cols]
  symm
  exact Finset.sum_subset (Finset.subset_univ _) fun β _ hβ => by
    rw [colCoeff_high_eq_zero β hβ, mul_zero]

/-- Integer ceiling of 11b/6. -/
def nameWidth (b : ℕ) : ℕ := (11 * b + 5) / 6

theorem size_three_pow_add_three_le (c : ℕ) :
    Nat.size (3 ^ (c + 3)) ≤ Nat.size (3 ^ c) + 5 := by
  apply Nat.size_le.mpr
  rw [pow_add, pow_add]
  calc
    3 ^ c * 3 ^ 3 ≤ 3 ^ c * 2 ^ 5 := Nat.mul_le_mul_left _ (by norm_num)
    _ < 2 ^ Nat.size (3 ^ c) * 2 ^ 5 :=
      Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self _) (by norm_num)

theorem capW_half_add_six_le (b : ℕ) :
    Prog.capW (b + 6) ((b + 6) / 2) ≤ Prog.capW b (b / 2) + 11 := by
  have hd : (b + 6) / 2 = b / 2 + 3 := by omega
  have hs := size_three_pow_add_three_le (b / 2)
  simp only [Prog.capW, Prog.tb, hd]
  omega

/-- The existing constructive sparse code meets the manuscript's sharper bound. -/
theorem capW_half_le_nameWidth (b : ℕ) (hb : 1 ≤ b) :
    Prog.capW b (b / 2) ≤ nameWidth b := by
  revert hb
  induction b using Nat.strong_induction_on with
  | h b ih =>
    intro hb
    by_cases hsmall : b < 7
    · have hcases : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 := by omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · have hi := ih (b - 6) (by omega) (by omega)
      have hs := capW_half_add_six_le (b - 6)
      have he : b - 6 + 6 = b := by omega
      rw [he] at hs
      unfold nameWidth at *
      omega

theorem nameWidth_le_two_mul (b : ℕ) (hb : 1 ≤ b) : nameWidth b ≤ 2 * b := by
  unfold nameWidth
  omega

theorem capW_half_le_two_mul (b : ℕ) (hb : 1 ≤ b) : Prog.capW b (b / 2) ≤ 2 * b :=
  (capW_half_le_nameWidth b hb).trans (nameWidth_le_two_mul b hb)

theorem card_sparseLab_half_le (s₀ : Bell) (b : ℕ) (hb : 1 ≤ b) :
    (sparseLab s₀ b (b / 2)).card ≤ 2 ^ nameWidth b :=
  (Code.sparse s₀ b (b / 2)).card_le.trans
    (Nat.pow_le_pow_right (by norm_num) (capW_half_le_nameWidth b hb))

/-- The favorable row cut in the existing explicit sparse-word code; invalid names are zero. -/
theorem pieceA_rows_words (b : ℕ) (x y u v : Bits b) :
    let c := Code.sparse (false, false) b (b / 2)
    pieceA b x y u v = ∑ w ∈ words (Prog.capW b (b / 2)),
      if w ∈ c.D then colBit.Top (c.dec w) x y * rowCoeff (lowIndices b) (c.dec w) u v else 0 := by
  dsimp only
  rw [pieceA_rows]
  exact ((Code.sparse (false, false) b (b / 2)).sum_words
    (fun β => colBit.Top β x y * rowCoeff (lowIndices b) β u v)).symm

/-- The favorable column cut in the existing explicit sparse-word code. -/
theorem pieceB_cols_words (b : ℕ) (x y u v : Bits b) :
    let c := Code.sparse (true, true) b (b / 2)
    pieceB b x y u v = ∑ w ∈ words (Prog.capW b (b / 2)),
      if w ∈ c.D then rowBit.Top (c.dec w) x u * colCoeff (highIndices b) (c.dec w) y v else 0 := by
  dsimp only
  rw [pieceB_cols]
  exact ((Code.sparse (true, true) b (b / 2)).sum_words
    (fun β => rowBit.Top β x u * colCoeff (highIndices b) β y v)).symm

end EthBridge.Elementary.Crossing
