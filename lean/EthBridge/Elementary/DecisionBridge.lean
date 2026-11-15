/-
SPDX-License-Identifier: Apache-2.0
The machine wrapper and polynomial absorption reused here are from Anthropic's
Apache-2.0 development. This module derives a decision machine from a supplied
counting machine; it does not invoke an existing unconditional ETH endpoint.
-/
module

public import FixedWidthVariableBoundStatement
public import ThreeSatRateStatement
public import GeneralPieces.ThmRunningTime
import Wrap.Main
import Wrap.Arith
import Wrap.FrontEnd
import Wrap.Sim
import VariableBound.Paper.Rename.End
import WidthThree.Rates
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

@[expose] public section

namespace EthBridge.Elementary.DecisionBridge

open Groundwork Filter Turing Finset
open scoped Topology NNReal

/-- Every positive logarithmic exponent gives a rate tending to zero. -/
theorem rate_tendsto_zero {α : ℝ} (hα : 0 < α) :
    Tendsto (SatK.rN 1 α) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 4) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    obtain ⟨N, hN⟩ := exists_nat_ge b
    refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hl : Tendsto (fun n : ℕ => Real.logb 2 ((n : ℝ) + 4)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp
      hn
  have h := ((isLittleO_log_rpow_atTop hα).tendsto_div_nhds_zero.comp hl).div_const (Real.log 2)
  convert h using 1
  · ext n
    simp only [SatK.rN, pow_one, Real.logb, Function.comp_apply]
    ring
  · simp

/-- Finite initial exceptions are absorbed into a constant, without assuming the
rate is positive or monotone. -/
theorem exponential_below {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0))
    (B : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℕ, ∀ n : ℕ, (2 : ℝ) ^ (B * n * r n) ≤ c * (2 : ℝ) ^ (ε * n) := by
  have hlim : Tendsto (fun n => B * r n) atTop (𝓝 0) := by
    simpa using hr.const_mul B
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.mp hlim).2 ε hε)
  let A : ℝ := 1 + ∑ n ∈ range N, (2 : ℝ) ^ (B * n * r n)
  have hA : 1 ≤ A := by
    have hs : 0 ≤ ∑ n ∈ range N, (2 : ℝ) ^ (B * n * r n) := by positivity
    dsimp [A]
    linarith
  obtain ⟨c, hc⟩ := exists_nat_ge A
  refine ⟨c, fun n => ?_⟩
  by_cases hn : n < N
  · have hs : (2 : ℝ) ^ (B * n * r n) ≤ A := by
      have hsum := Finset.single_le_sum (f := fun i : ℕ => (2 : ℝ) ^ (B * i * r i))
        (fun i (_ : i ∈ range N) => Real.rpow_nonneg (by norm_num) (B * i * r i))
        (mem_range.mpr hn)
      dsimp [A]
      linarith
    exact hs.trans (hc.trans (le_mul_of_one_le_right (by exact_mod_cast Nat.zero_le c)
      (Real.one_le_rpow (by norm_num) (mul_nonneg hε.le (Nat.cast_nonneg n)))))
  · have he : B * n * r n ≤ ε * n := by
      have := mul_le_mul_of_nonneg_right (hN n (by omega)).le (Nat.cast_nonneg n)
      nlinarith
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) he).trans
      (le_mul_of_one_le_left (by positivity) (hA.trans hc))

/-- The supplied counting bound is below every positive exponential rate. -/
theorem count_bound_below {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0))
    (C : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℕ, ∀ n : ℕ, (SatK.boundN r C n : ℝ) ≤ c * (2 : ℝ) ^ (ε * n) := by
  obtain ⟨c, hc⟩ := exponential_below hr (C : ℝ) hε
  refine ⟨C * c, fun n => ?_⟩
  calc (SatK.boundN r C n : ℝ) ≤ C * (2 : ℝ) ^ ((C : ℝ) * n * r n) :=
      Nat.floor_le (by positivity)
    _ ≤ C * ((c : ℝ) * (2 : ℝ) ^ (ε * n)) :=
      mul_le_mul_of_nonneg_left (hc n) (Nat.cast_nonneg C)
    _ = (C * c : ℕ) * (2 : ℝ) ^ (ε * n) := by push_cast; ring

/-- Fixed polynomial wrapper overhead preserves subexponentiality. This is used
only after obtaining the complete counting machine, not inside a rate recurrence. -/
theorem wrapped_time_below {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0))
    (q C a d : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℕ, ∀ n X : ℕ, X ≤ a * (n + 2) ^ d →
      q * (SatK.boundN r C n + X + 1) ^ q ≤ ⌊(c : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
  let ε : ℝ := δ / ((q : ℝ) + 1)
  have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have hε : 0 < ε := div_pos hδ hq1
  have hεq : ε * q ≤ δ := by
    dsimp [ε]
    rw [div_mul_eq_mul_div, div_le_iff₀ hq1]
    nlinarith
  obtain ⟨c₁, hc₁⟩ := count_bound_below hr C hε
  obtain ⟨c₂, hc₂⟩ := Wrap.Arith.poly_below d hε
  let K : ℕ := c₁ + (a + 1) * c₂
  refine ⟨q * K ^ q, fun n X hX => Nat.le_floor ?_⟩
  have hpoly : ((X + 1 : ℕ) : ℝ) ≤ (a + 1 : ℕ) * (c₂ : ℝ) * (2 : ℝ) ^ (ε * n) := by
    have hn : 1 ≤ (n + 2) ^ d := Nat.one_le_pow _ _ (by omega)
    have h : X + 1 ≤ (a + 1) * (n + 2) ^ d := by nlinarith
    calc ((X + 1 : ℕ) : ℝ) ≤ ((a + 1 : ℕ) : ℝ) * ((n : ℝ) + 2) ^ d := by exact_mod_cast h
      _ ≤ ((a + 1 : ℕ) : ℝ) * ((c₂ : ℝ) * (2 : ℝ) ^ (ε * n)) :=
        mul_le_mul_of_nonneg_left (hc₂ n) (Nat.cast_nonneg _)
      _ = _ := by ring
  have hb : ((SatK.boundN r C n + X + 1 : ℕ) : ℝ) ≤ (K : ℝ) * (2 : ℝ) ^ (ε * n) := by
    have ht := hc₁ n
    dsimp [K]
    push_cast at hpoly ⊢
    nlinarith
  have hpow : ((2 : ℝ) ^ (ε * n)) ^ q ≤ (2 : ℝ) ^ (δ * n) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_right hεq (Nat.cast_nonneg n)]
  push_cast at hb ⊢
  calc (q : ℝ) * (SatK.boundN r C n + X + 1) ^ q ≤
      (q : ℝ) * ((K : ℝ) * (2 : ℝ) ^ (ε * n)) ^ q :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb q) (Nat.cast_nonneg q)
    _ = (q : ℝ) * (K : ℝ) ^ q * ((2 : ℝ) ^ (ε * n)) ^ q := by rw [mul_pow]; ring
    _ ≤ (q : ℝ) * (K : ℝ) ^ q * (2 : ℝ) ^ (δ * n) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)

/-- A counting machine at any rate tending to zero yields one decision machine
meeting every positive exponential rate. Its actual machine is wrapped, not replaced
by a previously known SAT algorithm. -/
theorem subexp_of_count_rate {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0))
    (h : SatK.CountInRateN 3 r) : Sat3.SubexpTM := by
  classical
  obtain ⟨M, C, hfin, hM⟩ := h
  obtain ⟨N, q, hN, hwrap⟩ := Wrap.everyMachineCanBeWrapped M hfin id
    VariableBound.Rename.anyBit PolyT.id' VariableBound.Rename.anyBit_polyT
  obtain ⟨a, d, hlen⟩ := Wrap.length_encC_pad4_le
  refine ⟨N, hN, fun δ hδ => ?_⟩
  obtain ⟨c, hc⟩ := wrapped_time_below hr q C a d (show (0 : ℝ) < δ from hδ)
  refine ⟨c, fun n φ hφ => ?_⟩
  have hcount : SatK.numSat φ ≤ 2 ^ n := by
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hout := VariableBound.Rename.anyBit_binary
    (hcount.trans_lt (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self n)))
  have hrun := hwrap (Sat3.enc φ) (SatK.binary n (SatK.numSat φ)) (SatK.boundN r C n)
    (hM n φ hφ)
  rw [hout] at hrun
  refine ⟨decide (SatK.numSat φ ≠ 0), ?_, hrun.mono (hc n _ (hlen n φ hφ).2)⟩
  simp [SatK.numSat, Sat3.Satisfiable]

theorem subexp_of_countInRateN {α : ℝ} (hα : 0 < α)
    (h : SatK.CountInRateN 3 (SatK.rN 1 α)) : Sat3.SubexpTM :=
  subexp_of_count_rate (rate_tendsto_zero hα) h

/-- The final generic implication; it depends on the supplied counter. -/
theorem not_eth_of_countInRateN {α : ℝ} (hα : 0 < α)
    (h : SatK.CountInRateN 3 (SatK.rN 1 α)) : ¬ Sat3.ETH_TM :=
  WidthThree.ethFails_of_subexpTM (subexp_of_countInRateN hα h)

/-- Plug a new executable piece family into the proved generic recursion and
then into the terminal machine conversion. No unconditional ETH theorem is used. -/
theorem not_eth_of_pieces {P : ClauseBound.Alg.PiecesF} {ρ : ℝ} {c : ℕ}
    (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) (hP : ClauseBound.Gen.Par P ρ c)
    (hm : P.m = 1) (hKeeps : P.Keeps) : ¬ Sat3.ETH_TM := by
  have hpos : 0 < ρ := by linarith
  have hα : 0 < Real.logb 2 (1 / ρ) :=
    Real.logb_pos (by norm_num) ((one_lt_div hpos).mpr hρ1)
  exact not_eth_of_countInRateN hα (GeneralPieces.partC_n hρ hρ1 hP hm hKeeps
    (GeneralPieces.x₀Of_ge c) (GeneralPieces.x₀Of_pow c) 3 (by norm_num))

end EthBridge.Elementary.DecisionBridge
