/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Groundwork.Net.Defs
public import EthBridge.Shared.FiniteProduct
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Set.Function

/-! The calculus of factorisations. An interaction between two nodes is «factorised» when it is
written as a sum over
labels θ of (a factor that reads one side and θ) times (a factor that reads the other side and θ);
the number of labels is
what the pair costs. Three rules: (a) a product of factorised functions is factorised over the
tuples of labels,
(b) labels may be renamed into a larger type, (c) every function factors through its second
    argument.
Also the number of pairs a < b, and the crossing X = [x=v][y=u] of Section 4 of the paper, a
function of the four
corners of a rectangle, for indices in any type α. -/

namespace Groundwork

open Finset

variable {ι X' τ A α : Type*}

/-! ### The calculus -/

/-- Membership in the set of tuples. -/
public theorem mem_tuples [Fintype ι] [DecidableEq ι] (P : ι → Prop) [DecidablePred P] (T : ι → Finset X') (d : X')
    (t : ι → X') : t ∈ tuples P T d ↔ ∀ i, (P i → t i ∈ T i) ∧ (¬P i → t i = d) := by
  unfold tuples
  rw [Fintype.mem_piFinset]
  refine forall_congr' fun i => ?_
  split_ifs with h <;> simp [h]

/-- The number of tuples. -/
public theorem card_tuples [Fintype ι] [DecidableEq ι] (P : ι → Prop) [DecidablePred P] (T : ι → Finset X') (d : X') :
    #(tuples P T d) = ∏ i with P i, #(T i) := by
  unfold tuples
  rw [Fintype.card_piFinset, Finset.prod_filter]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs <;> simp

/-- Distributivity: a sum over tuples of a product is the product of the sums. -/
public theorem sum_tuples_prod [Fintype ι] [DecidableEq ι] (P : ι → Prop) [DecidablePred P] (T : ι → Finset X') (d : X')
    (H : ι → X' → ℤ) : ∑ t ∈ tuples P T d, ∏ i with P i, H i (t i) = ∏ i with P i, ∑ x ∈ T i, H i x := by
  exact EthBridge.Shared.FiniteProduct.sum_defaultFilled_prod P T d H

/-- (a), for a family: a product of factorised functions is factorised over the tuples of labels, by
the products of the
factors. -/
public theorem prod_factorised [Fintype ι] [DecidableEq ι] (P : ι → Prop) [DecidablePred P] (T : ι → Finset X') (d : X')
    (f f' : ι → X' → ℤ) :
    ∏ i with P i, ∑ x ∈ T i, f i x * f' i x =
      ∑ t ∈ tuples P T d, (∏ i with P i, f i (t i)) * ∏ i with P i, f' i (t i) := by
  rw [← sum_tuples_prod P T d]
  simp only [Finset.prod_mul_distrib]

/-- (b): labels may be renamed into a larger type, both factors vanishing off the set D of names. -/
public theorem sum_renamed [Fintype A] [DecidableEq A] (D : Finset A) (dec : A → τ) (Θ : Finset τ)
    (h : Set.BijOn dec D Θ) (f f' : τ → ℤ) :
    ∑ x, (if x ∈ D then f (dec x) else 0) * (if x ∈ D then f' (dec x) else 0) = ∑ θ ∈ Θ, f θ * f' θ := by
  have h1 : ∀ x, (if x ∈ D then f (dec x) else 0) * (if x ∈ D then f' (dec x) else 0) =
      if x ∈ D then f (dec x) * f' (dec x) else 0 := by
    intro x; split_ifs <;> simp
  simp only [h1]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  exact Finset.sum_nbij dec (fun x hx => h.mapsTo hx) h.injOn h.surjOn (fun _ _ => rfl)

/-- (c): every function factors through its second argument. -/
public theorem sum_mul_eq [Fintype τ] [DecidableEq τ] (F : τ → ℤ) (z' : τ) :
    ∑ θ, F θ * (if z' = θ then 1 else 0) = F z' := by
  simp

/-! ### The number of pairs -/

/-- The number of pairs a < b. -/
public theorem card_pairs [Fintype α] [LinearOrder α] : #(pairs α) = (Fintype.card α).choose 2 := by
  exact Fintype.card_product_filter_lt

/-! ### The crossing -/

namespace Cross

/-- X = [x=v][y=u]: opposite corners agree (the two diagonals of a rectangle with x, y on top and u,
v below). -/
@[expose] public def X [DecidableEq α] (x y u v : α) : ℤ := if x = v ∧ y = u then 1 else 0

end Cross

end Groundwork
