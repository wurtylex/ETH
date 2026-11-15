/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Two-point specialization of the shared bounded MGF; both original bounds are retained.
-/
module
public import EthBridge.Shared.BoundedMGF

public section
namespace EthBridge.Shared.BernoulliMGF

theorem bernoulli_mgf_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (θ : ℝ) :
    p * Real.exp (θ * (1 - p)) + (1 - p) * Real.exp (θ * (0 - p)) ≤ Real.exp (θ ^ 2 / 8) := by
  have h := BoundedMGF.weighted_mgf_le
    (fun x : Bool => if x then p else 1 - p) (fun x : Bool => if x then 1 else 0)
    0 1 θ (by intro x; cases x <;> simp <;> linarith)
    (by simp [Fintype.sum_bool]) (by intro x; cases x <;> simp)
  simpa [Fintype.sum_bool, add_comm] using h

end EthBridge.Shared.BernoulliMGF
