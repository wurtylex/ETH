/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Field
public import EthBridge.Shared.BernoulliMGF

/-! # Hoeffding's lemma on two points

`two_point_le`, in the namespace `ClauseBound.Rec.Tail`: p·e^{θ(1−p)} + (1−p)·e^{−θp} ≤ e^{θ²/8} for
0 ≤ p ≤ 1. This is Hoeffding's lemma for a random variable with values in {0, 1}.
It is taken from Mathlib's sub-Gaussian bound for a random variable with values in [0, 1], applied
to the measure with mass p at 1 and mass 1 − p at 0. -/

public section

open Finset

namespace ClauseBound.Rec

namespace Tail

/-- Hoeffding's lemma on two points: p·e^{θ(1−p)} + (1−p)·e^{−θp} ≤ e^{θ²/8} for 0 ≤ p ≤ 1. -/
theorem two_point_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (θ : ℝ) :
    p * Real.exp (θ * (1 - p)) + (1 - p) * Real.exp (θ * (0 - p)) ≤ Real.exp (θ ^ 2 / 8) := by
  exact EthBridge.Shared.BernoulliMGF.bernoulli_mgf_le hp0 hp1 θ

end Tail

open Tail

end ClauseBound.Rec
