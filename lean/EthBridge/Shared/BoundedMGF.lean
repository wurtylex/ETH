/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Finite weighted Hoeffding bounds, generalized from the original finite PMF proofs.
-/
module
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

public section
namespace EthBridge.Shared.BoundedMGF
open scoped BigOperators
open MeasureTheory ProbabilityTheory

/-- Hoeffding's lemma for a finite probability vector, with arbitrary real parameter. -/
theorem weighted_mgf_le {ι : Type*} [Fintype ι] (w X : ι → ℝ)
    (a b t : ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hX : ∀ i, X i ∈ Set.Icc a b) :
    (∑ i, w i * Real.exp (t * (X i - ∑ j, w j * X j))) ≤
      Real.exp ((t * (b - a)) ^ 2 / 8) := by
  classical
  let : MeasurableSpace ι := ⊤
  let p := PMF.ofFintype (fun i => ENNReal.ofReal (w i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i), hsum]
    simp)
  have hint (f : ι → ℝ) : ∫ i, f i ∂p.toMeasure = ∑ i, w i * f i := by
    rw [PMF.integral_eq_sum]
    simp [p, hw]
  have h := (hasSubgaussianMGF_of_mem_Icc (μ := p.toMeasure) (X := X)
    (measurable_from_top.aemeasurable) (Filter.Eventually.of_forall hX)).mgf_le t
  rw [mgf, hint, hint] at h
  refine h.trans_eq ?_
  congr 1
  simp [div_pow, sq_abs]
  ring

/-- The uncentered form factors out the exponential of the finite mean. -/
theorem weighted_exp_le {ι : Type*} [Fintype ι] (w X : ι → ℝ)
    (a b t : ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hX : ∀ i, X i ∈ Set.Icc a b) :
    (∑ i, w i * Real.exp (t * X i)) ≤
      Real.exp (t * (∑ i, w i * X i) + (t * (b - a)) ^ 2 / 8) := by
  have h := mul_le_mul_of_nonneg_right (weighted_mgf_le w X a b t hw hsum hX)
    (Real.exp_pos (t * ∑ i, w i * X i)).le
  rw [Finset.sum_mul] at h
  simp only [mul_assoc, ← Real.exp_add] at h
  convert h using 1
  · apply Finset.sum_congr rfl
    intro i _
    congr 2
    ring
  · congr 1
    ring

end EthBridge.Shared.BoundedMGF
