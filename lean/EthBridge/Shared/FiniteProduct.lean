/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

The default-filled specialization adapts the proof of Groundwork.sum_tuples_prod.
The shared interface depends only on Mathlib, not either ETH development.
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators

/-!
Finite distributivity through one common interface. The core permits arbitrary
finite dependent label sets. Its two specializations cover the independent full
types used by OpenAI and the default-filled selected coordinates used by
Anthropic. Empty types and empty allowed-label sets need no extra assumptions.

This module is proposed only for the isolated refactoring variant. It neither
imports nor modifies the frozen standalone intertwining proofs.
-/

namespace EthBridge.Shared.FiniteProduct

open scoped BigOperators

variable {ι R : Type*} {X : ι → Type*}
  [Fintype ι] [DecidableEq ι] [CommSemiring R]

/-- Distributivity over arbitrary finite dependent sets of labels. -/
public theorem sum_piFinset_prod (T : ∀ i, Finset (X i)) (H : ∀ i, X i → R) :
    (∑ t ∈ Fintype.piFinset T, ∏ i, H i (t i)) =
      ∏ i, ∑ x ∈ T i, H i x :=
  (Finset.prod_univ_sum T H).symm

/-- The full-finite-type representation of independent coordinates. -/
public theorem sum_prod_eq_prod_sum [∀ i, Fintype (X i)] (H : ∀ i, X i → R) :
    (∑ t : ∀ i, X i, ∏ i, H i (t i)) = ∏ i, ∑ x : X i, H i x := by
  simpa only [Fintype.piFinset_univ] using
    sum_piFinset_prod (fun i => (Finset.univ : Finset (X i))) H

/-- Selected coordinates range over their label sets; other coordinates take a
fixed default and contribute the multiplicative identity. -/
public theorem sum_defaultFilled_prod {Y : Type*}
    (P : ι → Prop) [DecidablePred P] (T : ι → Finset Y) (d : Y)
    (H : ι → Y → R) :
    (∑ t ∈ Fintype.piFinset (fun i => if P i then T i else {d}),
      ∏ i with P i, H i (t i)) =
      ∏ i with P i, ∑ x ∈ T i, H i x := by
  have h := sum_piFinset_prod (fun i => if P i then T i else {d})
    (fun i x => if P i then H i x else (1 : R))
  simp only [Finset.prod_filter]
  rw [h]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : P i <;> simp [hi]

end EthBridge.Shared.FiniteProduct
