/-
SPDX-License-Identifier: Apache-2.0
This common tensor argument generalizes the OpenAI product-kernel inverse proof.
-/
module

public import EthBridge.Shared.FiniteProduct
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
Tensor products preserve a one-sided kernel inverse. Coordinates and the two
local state spaces may be heterogeneous; the middle state spaces are finite.
The coefficient structure is a commutative semiring. No characteristic, division,
nontriviality, nonemptiness, or reverse-inverse assumption is required.
-/

namespace EthBridge.Shared.TensorContraction

open scoped BigOperators

variable {ι R : Type*} {α β : ι → Type*}
  [Fintype ι] [DecidableEq ι] [CommSemiring R]
  [∀ i, DecidableEq (α i)] [∀ i, Fintype (β i)]

/-- A local right inverse at each coordinate tensors to a right inverse on the
full assignment space. The outer state spaces need not be finite. -/
public theorem tensor_inverse
    (A : ∀ i, α i → β i → R) (B : ∀ i, β i → α i → R)
    (h : ∀ i x y, (∑ z, A i x z * B i z y) = if x = y then 1 else 0)
    (x y : ∀ i, α i) :
    (∑ z : ∀ i, β i, (∏ i, A i (x i) (z i)) * ∏ i, B i (z i) (y i)) =
      if x = y then 1 else 0 := by
  classical
  simp only [← Finset.prod_mul_distrib]
  rw [FiniteProduct.sum_prod_eq_prod_sum (fun i z => A i (x i) z * B i z (y i))]
  simp_rw [h]
  rw [Finset.prod_boole]
  simp only [Finset.mem_univ, forall_const, ← funext_iff]

end EthBridge.Shared.TensorContraction
