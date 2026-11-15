/-
SPDX-License-Identifier: Apache-2.0
Magnitude and capacity bounds for the collected two-piece crossing family.
The generic recursion parameter theorem is conditional on the actual piece
program specification; it does not assume an ETH conclusion.
-/
module

public import EthBridge.Elementary.Crossing
public import ClauseBound.Gen.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

@[expose] public section

namespace EthBridge.Elementary.PieceBounds

open Finset Groundwork
open EthBridge.Elementary.Crossing

/-- A small collection of b-bit coefficients fits in 2b magnitude bits, including b=0. -/
theorem abs_sum_le_double_bits {ι : Type*} (b : ℕ) (S : Finset ι) (hS : S.card ≤ b + 1)
    (f : ι → ℤ) (hf : ∀ i ∈ S, |f i| ≤ 2 ^ b) :
    |∑ i ∈ S, f i| ≤ (2 : ℤ) ^ (2 * b) := by
  have hc : (S.card : ℤ) ≤ (b + 1 : ℕ) := by exact_mod_cast hS
  have hb : (b + 1 : ℕ) ≤ 2 ^ b := by have := Nat.lt_two_pow_self (n := b); omega
  have hb' : ((b + 1 : ℕ) : ℤ) ≤ 2 ^ b := by exact_mod_cast hb
  calc
    |∑ i ∈ S, f i| ≤ ∑ i ∈ S, |f i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ S, (2 : ℤ) ^ b := sum_le_sum hf
    _ = (S.card : ℤ) * 2 ^ b := by simp
    _ ≤ 2 ^ b * 2 ^ b := mul_le_mul_of_nonneg_right (hc.trans hb') (by positivity)
    _ = 2 ^ (2 * b) := by rw [← pow_add]; congr 1; omega

theorem abs_rowCoeff_le (b : ℕ) (S : Finset ℕ) (hS : S.card ≤ b + 1)
    (β : Fin b → Bell) (u v : Bits b) : |rowCoeff S β u v| ≤ (2 : ℤ) ^ (2 * b) :=
  abs_sum_le_double_bits b S hS _ fun i _ => abs_colBot_le i β u v

theorem abs_colCoeff_le (b : ℕ) (S : Finset ℕ) (hS : S.card ≤ b + 1)
    (β : Fin b → Bell) (y v : Bits b) : |colCoeff S β y v| ≤ (2 : ℤ) ^ (2 * b) :=
  abs_sum_le_double_bits b S hS _ fun i _ => abs_rowBot_le i β y v

theorem lowIndices_card_le (b : ℕ) : (lowIndices b).card ≤ b + 1 := by
  simpa [lowIndices] using card_filter_le (range (b + 1)) (fun i => 2 * i ≤ b)

theorem highIndices_card_le (b : ℕ) : (highIndices b).card ≤ b + 1 := by
  simpa [highIndices] using card_filter_le (range (b + 1)) (fun i => ¬ 2 * i ≤ b)

theorem abs_pieceA_le (b : ℕ) (x y u v : Bits b) : |pieceA b x y u v| ≤ (2 : ℤ) ^ (2 * b) :=
  abs_sum_le_double_bits b (lowIndices b) (lowIndices_card_le b) _ fun i _ => abs_A_le b i x u y v

theorem abs_pieceB_le (b : ℕ) (x y u v : Bits b) : |pieceB b x y u v| ≤ (2 : ℤ) ^ (2 * b) :=
  abs_sum_le_double_bits b (highIndices b) (highIndices_card_le b) _ fun i _ => abs_A_le b i x u y v

/-- One favorable cut and one full-input cut have contraction parameter 23/24. -/
theorem favorable_cap_sum_le (b : ℕ) (hb : 1 ≤ b) :
    ((Prog.capW b (b / 2) + 2 * b : ℕ) : ℝ) ≤ 4 * (23 / 24 : ℝ) * b + 1 := by
  have hc := Nat.mul_le_mul_left 6 (capW_half_le_nameWidth b hb)
  have hd : 6 * nameWidth b ≤ 11 * b + 5 := by
    unfold nameWidth
    exact Nat.mul_div_le (11 * b + 5) 6
  have h : (6 : ℝ) * Prog.capW b (b / 2) ≤ 11 * b + 5 := by exact_mod_cast hc.trans hd
  push_cast
  nlinarith

theorem favorable_cap_sum_le_log (b : ℕ) (hb : 1 ≤ b) :
    ((Prog.capW b (b / 2) + 2 * b : ℕ) : ℝ) ≤
      4 * (23 / 24 : ℝ) * b + 2 * Real.logb 2 (2 * b) := by
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hlog : (1 : ℝ) ≤ Real.logb 2 (2 * b) := by
    calc
      1 = Real.logb 2 2 := (Real.logb_self_eq_one (by norm_num)).symm
      _ ≤ Real.logb 2 (2 * b) := Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by linarith)
  linarith [favorable_cap_sum_le b hb]

/-- The reusable arithmetic part of the actual two-piece program package.
The specification hypothesis includes both exact factor identities and magnitude bounds. -/
theorem par_of_two_piece_data (P : ClauseBound.Alg.PiecesF)
    (hspec : ∀ h b, 1 ≤ b → P.Spec h b)
    (hcnt : ∀ h b, P.cnt h b = 2) (hd : ∀ h b, P.d h b = 1)
    (hbits : ∀ h b, P.bits h b = 2 * b)
    (hneed : ∀ h b, P.need h b ≤ 2 * b) (hm : P.m = 1)
    (hcap : ∀ h b i, 1 ≤ b → i < P.cnt h b →
      P.cap false h b i + P.cap true h b i ≤ Prog.capW b (b / 2) + 2 * b) :
    ClauseBound.Gen.Par P (23 / 24) 2 where
  spec := hspec
  caps h b hb := by
    have hc : ClauseBound.Alg.capSum P h b ≤ Prog.capW b (b / 2) + 2 * b :=
      Finset.sup_le fun i hi => hcap h b i hb (Finset.mem_range.mp hi)
    exact (show (ClauseBound.Alg.capSum P h b : ℝ) ≤ ((Prog.capW b (b / 2) + 2 * b : ℕ) : ℝ) by
      exact_mod_cast hc).trans (favorable_cap_sum_le_log b hb)
  cnt h b hb := by rw [hcnt]; nlinarith
  bits h b hb := by rw [hbits]; nlinarith
  d h b hb := by rw [hd]; exact one_lt_pow₀ (by norm_num) (by positivity)
  need := fun h b _ => hneed h b
  m_le := by omega

end EthBridge.Elementary.PieceBounds
