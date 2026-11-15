/- Shared exponential tail bounds for finite, possibly unnormalized weights. -/
module
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic

public section
namespace EthBridge.Shared.FiniteConcentration
open Finset

variable {ι : Type*}

/-- Exponential Markov comparison; the weight sum need not be one or positive. -/
theorem sum_indicator_mul_exp_le (s : Finset ι) (w X : ι → ℝ)
    (P : ι → Prop) [DecidablePred P] (t b : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (ht : 0 ≤ t)
    (hP : ∀ i ∈ s, P i → b ≤ X i) :
    (∑ i ∈ s, if P i then w i else 0) * Real.exp (t * b) ≤
      ∑ i ∈ s, w i * Real.exp (t * X i) := by
  rw [sum_mul]
  refine sum_le_sum fun i hi => ?_
  split_ifs with hp
  · exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hP i hi hp) ht)) (hw i hi)
  · simpa using mul_nonneg (hw i hi) (Real.exp_pos (t * X i)).le

theorem sum_indicator_le_of_mgf (s : Finset ι) (w X : ι → ℝ)
    (P : ι → Prop) [DecidablePred P] (t b M : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (ht : 0 ≤ t)
    (hP : ∀ i ∈ s, P i → b ≤ X i)
    (hM : (∑ i ∈ s, w i * Real.exp (t * X i)) ≤ M) :
    (∑ i ∈ s, if P i then w i else 0) ≤ Real.exp (-t * b) * M := by
  have h := (le_div_iff₀ (Real.exp_pos (t * b))).mpr
    ((sum_indicator_mul_exp_le s w X P t b hw ht hP).trans hM)
  simpa only [div_eq_mul_inv, ← Real.exp_neg, neg_mul, mul_neg, mul_comm] using h

/-- The absolute-value exponential is bounded by the two signed exponentials. -/
theorem exp_mul_abs_le (t x : ℝ) :
    Real.exp (t * |x|) ≤ Real.exp (t * x) + Real.exp (-t * x) := by
  rcases le_total 0 x with hx | hx
  · simpa only [abs_of_nonneg hx] using
      le_add_of_nonneg_right (Real.exp_pos (-t * x)).le
  · simpa only [abs_of_nonpos hx, mul_neg, neg_mul] using
      le_add_of_nonneg_left (Real.exp_pos (t * x)).le

/-- Two-sided tails share the one-sided comparison, without normalizing weights. -/
theorem sum_indicator_le_of_abs_mgf (s : Finset ι) (w X : ι → ℝ)
    (P : ι → Prop) [DecidablePred P] (t b Mplus Mminus : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (ht : 0 ≤ t)
    (hP : ∀ i ∈ s, P i → b ≤ |X i|)
    (hplus : (∑ i ∈ s, w i * Real.exp (t * X i)) ≤ Mplus)
    (hminus : (∑ i ∈ s, w i * Real.exp ((-t) * X i)) ≤ Mminus) :
    (∑ i ∈ s, if P i then w i else 0) ≤ Real.exp (-t * b) * (Mplus + Mminus) := by
  apply sum_indicator_le_of_mgf s w (fun i => |X i|) P t b (Mplus + Mminus) hw ht hP
  calc
    (∑ i ∈ s, w i * Real.exp (t * |X i|)) ≤
        ∑ i ∈ s, (w i * Real.exp (t * X i) + w i * Real.exp (-t * X i)) := by
      refine sum_le_sum fun i hi => ?_
      simpa only [mul_add] using
        mul_le_mul_of_nonneg_left (exp_mul_abs_le t (X i)) (hw i hi)
    _ ≤ Mplus + Mminus := by
      rw [sum_add_distrib]
      exact add_le_add hplus hminus

end EthBridge.Shared.FiniteConcentration
