/-
Released under Apache 2.0.

Finite weighted overlap bounds shared by the two ETH developments.
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Ring

/-!
The same matrix estimate controls collision energy with bounded dependency
sets and second moments of weighted colour-class capacities. Its pairwise
majorant is already weighted: zero-capacity entries need not satisfy an
unweighted probabilistic bound.

Only the outer weights and the error coefficient must be nonnegative.
The matrix may have negative entries (centered collisions), and neither
index type must be nonempty. There is no division or normalization, so the
natural-number counting argument loses no empty-colour or zero-weight cases.
This module imports neither ETH development.
-/

namespace EthBridge.Shared.WeightedOverlap

open scoped BigOperators

variable {I J R : Type*} [Fintype I] [Fintype J]
  [CommSemiring R] [PartialOrder R] [IsOrderedRing R]

/-- A pairwise baseline plus a weighted overlap error gives a global bound.

The rows and columns may have different finite index types and weights.
In the symmetric case the baseline is `a * (∑ i, w i) ^ 2`. Unit weights
and a zero baseline recover the bounded-dependency collision estimate. -/
public theorem sum_kernel_le_of_weighted_overlap
    (w : I → R) (v : J → R) (kernel overlap : I → J → R) (a b d : R)
    (hw : ∀ i, 0 ≤ w i) (hb : 0 ≤ b)
    (hpair : ∀ i j, kernel i j ≤ w i * (a * v j + b * (v j * overlap i j)))
    (hrow : ∀ i, ∑ j, v j * overlap i j ≤ d) :
    (∑ i, ∑ j, kernel i j) ≤
      a * (∑ i, w i) * (∑ j, v j) + b * d * (∑ i, w i) := by
  calc
    (∑ i, ∑ j, kernel i j) ≤ ∑ i, w i * (a * (∑ j, v j) + b * d) := by
      refine Finset.sum_le_sum fun i _ => ?_
      calc
        (∑ j, kernel i j) ≤ ∑ j, w i * (a * v j + b * (v j * overlap i j)) :=
          Finset.sum_le_sum fun j _ => hpair i j
        _ = w i * (a * (∑ j, v j) + b * (∑ j, v j * overlap i j)) := by
          simp only [← Finset.mul_sum, Finset.sum_add_distrib]
        _ ≤ w i * (a * (∑ j, v j) + b * d) :=
          mul_le_mul_of_nonneg_left
            (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hrow i) hb)) (hw i)
    _ = a * (∑ i, w i) * (∑ j, v j) + b * d * (∑ i, w i) := by
      rw [← Finset.sum_mul]
      ring

/-- A matrix bounded by one and vanishing outside bounded dependency sets has
total sum at most the dependency bound times its number of rows. Entries may
be negative; no symmetry or diagonal condition is needed. -/
public theorem sum_kernel_le_of_dependency_sets
    (kernel : I → I → R) (deps : I → Finset I) (d : R)
    (hbound : ∀ i j, kernel i j ≤ 1)
    (hzero : ∀ i j, j ∉ deps i → kernel i j = 0)
    (hcard : ∀ i, ((deps i).card : R) ≤ d) :
    (∑ i, ∑ j, kernel i j) ≤ d * (Fintype.card I : R) := by
  classical
  have h := sum_kernel_le_of_weighted_overlap
    (fun _ : I => (1 : R)) (fun _ : I => (1 : R)) kernel
    (fun i j => if j ∈ deps i then (1 : R) else 0) 0 1 d
    (fun _ => zero_le_one) zero_le_one
    (fun i j => by
      by_cases hj : j ∈ deps i
      · simpa [hj] using hbound i j
      · simp [hj, hzero i j hj])
    (fun i => by simpa using hcard i)
  simpa only [zero_mul, one_mul, zero_add, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one] using h

end EthBridge.Shared.WeightedOverlap
