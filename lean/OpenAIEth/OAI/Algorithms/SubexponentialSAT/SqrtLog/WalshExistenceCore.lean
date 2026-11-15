import EthBridge.Shared.BoundedMGF
import EthBridge.Shared.FiniteProduct
import EthBridge.Shared.FiniteConcentration
import OAI.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-! Fully finite exponential-moment sampling. All public averages are finite sums;
the shared moment bound internally uses Mathlib's finite probability measures. -/

namespace SubexponentialSAT.SqrtLog.WalshExistence

open scoped BigOperators

variable {X A : Type*} [Fintype X] [Fintype A]

theorem sum_exp_le (f : X → ℝ) (hf : ∀ x, |f x| ≤ 1)
    (hzero : ∑ x, f x = 0) (t : ℝ) :
    (∑ x, Real.exp (t * f x)) ≤
      (Fintype.card X : ℝ) * Real.exp (t ^ 2 / 2) := by
  classical
  cases isEmpty_or_nonempty X with
  | inl h => simp
  | inr h =>
    have hN : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
    have h := EthBridge.Shared.BoundedMGF.weighted_exp_le
      (fun _ : X => 1 / (Fintype.card X : ℝ)) f (-1) 1 t
      (by intro x; positivity) (by simp [hN.ne']) (fun x => abs_le.mp (hf x))
    simp only [← Finset.mul_sum, hzero, mul_zero, zero_add] at h
    have he : (t * (1 - (-1))) ^ 2 / 8 = t ^ 2 / 2 := by ring
    rw [he] at h
    have hdiv : (∑ x, Real.exp (t * f x)) / (Fintype.card X : ℝ) ≤ Real.exp (t ^ 2 / 2) := by
      simpa [div_eq_mul_inv, mul_comm] using h
    simpa [mul_comm] using (div_le_iff₀ hN).mp hdiv

theorem sum_exp_samples_le (f : X → ℝ) (hf : ∀ x, |f x| ≤ 1)
    (hzero : ∑ x, f x = 0) (D : ℕ) (t : ℝ) :
    (∑ s : Fin D → X, Real.exp (t * ∑ i, f (s i))) ≤
      (Fintype.card X : ℝ) ^ D * Real.exp ((D : ℝ) * t ^ 2 / 2) := by
  classical
  have heq : (∑ s : Fin D → X, Real.exp (t * ∑ i, f (s i))) =
      (∑ x, Real.exp (t * f x)) ^ D := by
    simpa [Finset.mul_sum, Real.exp_sum] using
      EthBridge.Shared.FiniteProduct.sum_prod_eq_prod_sum
        (fun (_ : Fin D) (x : X) => Real.exp (t * f x))
  rw [heq]
  calc
    (∑ x, Real.exp (t * f x)) ^ D ≤
        ((Fintype.card X : ℝ) * Real.exp (t ^ 2 / 2)) ^ D := by
      exact pow_le_pow_left₀ (by positivity) (sum_exp_le f hf hzero t) D
    _ = (Fintype.card X : ℝ) ^ D * Real.exp ((D : ℝ) * t ^ 2 / 2) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      ring

noncomputable def potential (f : A → X → ℝ) (D : ℕ) (ε : ℝ) (s : Fin D → X) : ℝ :=
  ∑ a, (Real.exp (ε * ∑ i, f a (s i)) + Real.exp (-ε * ∑ i, f a (s i)))

theorem sum_potential_le (f : A → X → ℝ) (hf : ∀ a x, |f a x| ≤ 1)
    (hzero : ∀ a, ∑ x, f a x = 0) (D : ℕ) (ε : ℝ) :
    (∑ s : Fin D → X, potential f D ε s) ≤
      (Fintype.card X : ℝ) ^ D *
        (2 * Fintype.card A * Real.exp ((D : ℝ) * ε ^ 2 / 2)) := by
  classical
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset A)) fun a _ =>
    add_le_add (sum_exp_samples_le (f a) (hf a) (hzero a) D ε)
      (sum_exp_samples_le (f a) (hf a) (hzero a) D (-ε))
  simp only [neg_sq] at h
  convert h using 1
  · simp only [potential]
    rw [Finset.sum_comm]
    simp only [Finset.sum_add_distrib]
  · simp
    ring

theorem exists_samples [Nonempty X] (f : A → X → ℝ)
    (hf : ∀ a x, |f a x| ≤ 1) (hzero : ∀ a, ∑ x, f a x = 0)
    (D : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hbudget : 2 * (Fintype.card A : ℝ) < Real.exp ((D : ℝ) * ε ^ 2 / 2)) :
    ∃ s : Fin D → X, ∀ a, |∑ i, f a (s i)| ≤ ε * D := by
  classical
  have hcard : (Fintype.card X : ℝ) ^ D > 0 :=
    pow_pos (by exact_mod_cast Fintype.card_pos) D
  have hstrict : (Fintype.card X : ℝ) ^ D *
      (2 * Fintype.card A * Real.exp ((D : ℝ) * ε ^ 2 / 2)) <
      (Fintype.card X : ℝ) ^ D * Real.exp ((D : ℝ) * ε ^ 2) := by
    apply mul_lt_mul_of_pos_left _ hcard
    have hh := mul_lt_mul_of_pos_right hbudget (Real.exp_pos ((D : ℝ) * ε ^ 2 / 2))
    rw [← Real.exp_add] at hh
    convert hh using 1; congr 1; ring
  have hsum : (∑ s : Fin D → X, potential f D ε s) <
      ∑ _s : Fin D → X, Real.exp ((D : ℝ) * ε ^ 2) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow] using
      (sum_potential_le f hf hzero D ε).trans_lt hstrict
  obtain ⟨s, _, hs⟩ := Finset.exists_lt_of_sum_lt hsum
  refine ⟨s, fun a => le_of_not_gt fun ha => ?_⟩
  have he : Real.exp ((D : ℝ) * ε ^ 2) ≤ Real.exp (ε * |∑ i, f a (s i)|) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left ha.le hε]
  have hterm := EthBridge.Shared.FiniteConcentration.exp_mul_abs_le ε (∑ i, f a (s i))
  have hsingle : Real.exp (ε * ∑ i, f a (s i)) + Real.exp (-ε * ∑ i, f a (s i)) ≤
      potential f D ε s := by
    unfold potential
    exact Finset.single_le_sum
      (f := fun b => Real.exp (ε * ∑ i, f b (s i)) + Real.exp (-ε * ∑ i, f b (s i)))
      (fun b _ => by positivity) (Finset.mem_univ a)
  exact (not_le_of_gt hs) (he.trans (hterm.trans hsingle))

end SubexponentialSAT.SqrtLog.WalshExistence

end OAI.Algorithms
