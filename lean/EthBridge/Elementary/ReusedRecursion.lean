/-
SPDX-License-Identifier: Apache-2.0
The elementary manuscript's two collected crossing pieces, executed through
Anthropic's existing general recursion. This is an implementation variant:
it does not assert the manuscript's unequal-rectangle algorithm or its precise
rate-improvement recurrence. The old complete ETH conclusions are not premises.
-/
import EthBridge.Elementary.PiecesSpec
import EthBridge.Elementary.DecisionBridge
import EthBridge.Anthropic
import Mathlib.Tactic.NormNum

namespace EthBridge.Elementary.ReusedRecursion

/-- The new executable two-piece family supplies the actual generic counting
solver, followed by the terminal counting-to-decision conversion. -/
theorem not_eth_tm : ¬ Sat3.ETH_TM :=
  DecisionBridge.not_eth_of_pieces
    (by norm_num : (1 / 2 : ℝ) ≤ 23 / 24)
    (by norm_num : (23 / 24 : ℝ) < 1)
    PiecesSpec.family_par rfl Pieces.family_keeps

/-- The same common multitape ETH proposition used by both original graph roots.
The conditional machine-model bridge is reused; neither old ETH proof is called. -/
theorem not_eth : ¬ ComplexityAbstracts.SubexponentialSATAbstract.ETH :=
  EthBridge.Anthropic.not_eth_of_ethIsFalse not_eth_tm

end EthBridge.Elementary.ReusedRecursion
