/-
Released under Apache 2.0.

The finite-sum expansion below factors the algebra used independently in
Anthropic's Groundwork.Colouring.cheb_nat and OpenAI's
TypeDistribution.squared_deviation_eq_collisions.
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Ring

/-!
Shared finite second-moment algebra for the isolated refactoring variant.

Integer counts with cleared denominators and rational averages use the same
identity. No order, division, normalization, or nonempty-outcome assumption is
needed. The theorem therefore applies to empty finite types and to rings of
arbitrary characteristic, as well as the original integer and rational uses.

This module depends only on Mathlib and imports neither ETH development.
-/

namespace EthBridge.Shared.FiniteMoments

open scoped BigOperators

section Indicators

variable {I Ω R : Type*} [Fintype I] [Semiring R]

/-- Expand a weighted indicator square into ordered pairs, including empty indices. -/
public theorem square_sum_indicator (P : I → Prop) [DecidablePred P] (w : I → R) :
    (∑ i, if P i then w i else 0) ^ 2 =
      ∑ i, ∑ j, if P i ∧ P j then w i * w j else 0 := by
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases hi : P i <;> by_cases hj : P j <;> simp [hi, hj]

/-- Sum weighted squares by counting the joint events for each ordered pair. -/
public theorem sum_square_indicator [Fintype Ω]
    (P : Ω → I → Prop) [∀ ω i, Decidable (P ω i)] (w : I → R) :
    (∑ ω, (∑ i, if P ω i then w i else 0) ^ 2) =
      ∑ i, ∑ j, ∑ ω, if P ω i ∧ P ω j then w i * w j else 0 := by
  simp_rw [square_sum_indicator]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]


end Indicators

variable {Ω R : Type*} [Fintype Ω] [CommRing R]

/-- The second moment of an affine transform, with all moments left unnormalized. -/
public theorem sum_affine_square (f : Ω → R) (a b : R) :
    (∑ ω, (a * f ω - b) ^ 2) =
      (∑ ω, f ω ^ 2) * a ^ 2 - 2 * b * ((∑ ω, f ω) * a) +
        (Fintype.card Ω : R) * b ^ 2 := by
  have h : ∀ ω, (a * f ω - b) ^ 2 =
      f ω ^ 2 * a ^ 2 - 2 * b * (f ω * a) + b ^ 2 := by
    intro ω
    ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]

/-- Centered squares as raw second moment minus twice the centered first moment. -/
public theorem sum_centered_square (f : Ω → R) (b : R) :
    (∑ ω, (f ω - b) ^ 2) =
      (∑ ω, f ω ^ 2) - 2 * b * (∑ ω, f ω) +
        (Fintype.card Ω : R) * b ^ 2 := by
  simpa only [one_mul, one_pow, mul_one] using sum_affine_square f 1 b

end EthBridge.Shared.FiniteMoments
