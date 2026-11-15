import EthBridge.Shared.FiniteConcentration
import EthBridge.Shared.BernoulliMGF
import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSwapMultiplicity

namespace OAI.Algorithms

/-! Exponential concentration for the exact binomial swap spectrum.
All distribution parameters are explicit; no arity parameter is fixed. -/

namespace SubexponentialSAT.SqrtLog.Spectral

open scoped BigOperators

def binomialMean (θ : ℝ) (q : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ w ∈ Finset.range (q + 1),
    (q.choose w : ℝ) * (1 - θ) ^ (q - w) * θ ^ w * f w

theorem binomialMean_succ (θ : ℝ) (q : ℕ) (f : ℕ → ℝ) :
    binomialMean θ (q + 1) f =
      binomialMean θ q (fun w => (1 - θ) * f w + θ * f (w + 1)) := by
  unfold binomialMean
  simp only [mul_assoc]
  rw [Finset.sum_choose_succ_mul (fun i j => (1 - θ) ^ j * (θ ^ i * f i)) q]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  have hwle : w ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hw)
  have he : q + 1 - w = q - w + 1 := by omega
  rw [he, pow_succ, pow_succ]
  ring

theorem binomialMean_const_mul (θ c : ℝ) (q : ℕ) (f : ℕ → ℝ) :
    binomialMean θ q (fun w => c * f w) = c * binomialMean θ q f := by
  simp [binomialMean, mul_left_comm, ← Finset.mul_sum]

theorem binomialMean_add (θ : ℝ) (q : ℕ) (f g : ℕ → ℝ) :
    binomialMean θ q (fun w => f w + g w) =
      binomialMean θ q f + binomialMean θ q g := by
  simp [binomialMean, mul_add, Finset.sum_add_distrib]

theorem bernoulli_mgf_le (θ t : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 - θ) * Real.exp (-t * θ) + θ * Real.exp (t * (1 - θ)) ≤
      Real.exp (t ^ 2 / 2) := by
  have h := EthBridge.Shared.BernoulliMGF.bernoulli_mgf_le hθ0 hθ1 t
  have hle : t ^ 2 / 8 ≤ t ^ 2 / 2 := by nlinarith [sq_nonneg t]
  simpa only [zero_sub, mul_neg, neg_mul, add_comm] using
    h.trans (Real.exp_le_exp.mpr hle)

theorem binomial_mgf_le (θ t : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (q : ℕ) :
    binomialMean θ q (fun w => Real.exp (t * ((w : ℝ) - q * θ))) ≤
      Real.exp ((q : ℝ) * t ^ 2 / 2) := by
  have hθc : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
  induction q with
  | zero => simp [binomialMean]
  | succ q ih =>
    rw [binomialMean_succ]
    have hfun :
        (fun w : ℕ => (1 - θ) * Real.exp (t * ((w : ℝ) - (q + 1 : ℕ) * θ)) +
          θ * Real.exp (t * ((w + 1 : ℕ) - (q + 1 : ℕ) * θ))) =
        (fun w : ℕ => ((1 - θ) * Real.exp (-t * θ) +
          θ * Real.exp (t * (1 - θ))) * Real.exp (t * ((w : ℝ) - q * θ))) := by
      funext w
      have h0 : t * ((w : ℝ) - (q + 1 : ℕ) * θ) =
          -t * θ + t * ((w : ℝ) - q * θ) := by push_cast; ring
      have h1 : t * ((w + 1 : ℕ) - (q + 1 : ℕ) * θ) =
          t * (1 - θ) + t * ((w : ℝ) - q * θ) := by push_cast; ring
      rw [h0, h1, Real.exp_add, Real.exp_add]
      ring
    rw [hfun, binomialMean_const_mul]
    have hfac : 0 ≤ (1 - θ) * Real.exp (-t * θ) + θ * Real.exp (t * (1 - θ)) := by
      positivity
    calc
      _ ≤ ((1 - θ) * Real.exp (-t * θ) + θ * Real.exp (t * (1 - θ))) *
          Real.exp ((q : ℝ) * t ^ 2 / 2) := mul_le_mul_of_nonneg_left ih hfac
      _ ≤ Real.exp (t ^ 2 / 2) * Real.exp ((q : ℝ) * t ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right (bernoulli_mgf_le θ t hθ0 hθ1) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; push_cast; ring

theorem binomialMean_mono (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (q : ℕ) (f g : ℕ → ℝ) (hfg : ∀ w ∈ Finset.range (q + 1), f w ≤ g w) :
    binomialMean θ q f ≤ binomialMean θ q g := by
  have hθc : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
  apply Finset.sum_le_sum
  intro w hw
  exact mul_le_mul_of_nonneg_left (hfg w hw) (by positivity)

/-- Two-sided finite-binomial concentration with an absolute constant.
The event may be any finite predicate separated from the exact mean. -/
theorem binomial_tail_le (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (q : ℕ) (hq : 0 < q) (b : ℝ) (hb : 0 ≤ b)
    (bad : ℕ → Prop) [DecidablePred bad]
    (hbad : ∀ w ∈ Finset.range (q + 1), bad w → b ≤ |(w : ℝ) - q * θ|) :
    binomialMean θ q (fun w => if bad w then 1 else 0) ≤
      2 * Real.exp (-(b ^ 2) / (2 * q)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hθc : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
  let weights : ℕ → ℝ := fun w => (q.choose w : ℝ) * (1 - θ) ^ (q - w) * θ ^ w
  have hp := binomial_mgf_le θ (b / q) hθ0 hθ1 q
  have hn := binomial_mgf_le θ (-(b / q)) hθ0 hθ1 q
  have h := EthBridge.Shared.FiniteConcentration.sum_indicator_le_of_abs_mgf
    (Finset.range (q + 1)) weights (fun w => (w : ℝ) - q * θ) bad (b / q) b
    (Real.exp ((q : ℝ) * (b / q) ^ 2 / 2)) (Real.exp ((q : ℝ) * (b / q) ^ 2 / 2))
    (by intro w _; dsimp [weights]; positivity) (div_nonneg hb hqR.le) hbad
    (by simpa only [weights, binomialMean] using hp)
    (by simpa only [weights, binomialMean, neg_sq] using hn)
  simp only [binomialMean, mul_ite, mul_one, mul_zero]
  refine h.trans_eq ?_
  rw [← two_mul, mul_left_comm, ← Real.exp_add]
  congr 2
  field_simp
  ring

end SubexponentialSAT.SqrtLog.Spectral

end OAI.Algorithms
