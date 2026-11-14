import TotalL1
import NoCardGrowth

/-!
# Compatibility of the accepted OpenAI Lemma 4.6 coefficient packages

This file is tested against `smwg8h0gx/m4`'s auxiliary-row total-ℓ¹ arithmetic and
`smwg8h0gx/m6`'s sharp placement interface.  It proves their two composition points:
the actual printed bound and the `hbits` exponent bound (with the deliberately unoptimized
constant 24).  It supplies no M₀ properties, no mismatch bound, no schedule, no machine
realization and no ETH conclusion.
-/

set_option maxHeartbeats 1000000

open Finset Polynomial
namespace Eth46Compatibility

/-- The exact total-l1 and printed-bound interfaces compose, including tsQ/tsNat and C-mul/scalar notation. -/
theorem total_l1_to_paperL1Bd {ι : Type} [Fintype ι] [DecidableEq ι] {Q r R : ℕ}
    (M0 : ι → ι → ℚ) (aAux dAux : ι → Fin Q → Fin r)
    (hM : Eth46.RowBd M0 ((R : ℚ) * (4 * (Q : ℚ)) ^ (R - 1))) (x : ι) :
    OpenAI4.MultiCopy.rowL1 M0 aAux dAux (OpenAI4.MultiCopy.dden R Q) x
      ≤ OpenAI4.MultiCopy.paperL1Bd R Q := by
  have hts : OpenAI4.MultiCopy.tsQ Q = OpenAI4.tsNat Q := by
    funext s
    rfl
  have h := Eth46.total_l1_row_le M0 aAux dAux hM x
  rw [← hts] at h
  simpa [OpenAI4.MultiCopy.rowL1, OpenAI4.MultiCopy.paperL1Bd,
    OpenAI4.MultiCopy.dden, Eth46.dden, Polynomial.smul_eq_C_mul,
    OpenAI4.MultiCopy.tsQ, OpenAI4.tsNat, mul_assoc] using h

/-- D2's explicit bit arithmetic supplies exactly D3's hbits with constant 24. -/
theorem paperL1Bd_bits {Q R D : ℕ} (hR : 1 ≤ R) (hRQ : R < Q) :
    ∃ cA : ℕ, OpenAI4.MultiCopy.paperL1Bd R Q ≤
      (2 : ℚ) ^ (cA * (Q * (Nat.log2 Q + 1) + Nat.log2 D + 1)) := by
  refine ⟨24, ?_⟩
  rw [show OpenAI4.MultiCopy.paperL1Bd R Q = Eth46.dden R Q *
    (1 + (1 + 2 ^ Q) * ((R : ℚ) * (4 * (Q : ℚ)) ^ (R - 1))) from by
      simp [OpenAI4.MultiCopy.paperL1Bd, OpenAI4.MultiCopy.dden, Eth46.dden, mul_assoc]]
  refine (Eth46.total_bound_pow hR hRQ).trans ?_
  have hQ1 : 1 ≤ Q := by omega
  have hne : 4 * Q ≠ 0 := by omega
  have hlt : 4 * Q < 2 ^ (Nat.log2 (4 * Q) + 1) :=
    (Nat.log2_lt hne).mp (Nat.lt_succ_self _)
  have hb : (4 * (Q : ℚ)) ≤ (2 : ℚ) ^ (Nat.log2 (4 * Q) + 1) := by
    calc (4 * (Q : ℚ)) = ((4 * Q : ℕ) : ℚ) := by push_cast; ring
      _ ≤ ((2 ^ (Nat.log2 (4 * Q) + 1) : ℕ) : ℚ) := by exact_mod_cast (le_of_lt hlt)
      _ = (2 : ℚ) ^ (Nat.log2 (4 * Q) + 1) := by push_cast; ring
  refine (pow_le_pow_left₀ (by positivity : (0 : ℚ) ≤ 4 * (Q : ℚ)) hb _).trans ?_
  rw [← pow_mul]
  exact pow_le_pow_right₀ (by norm_num) (Eth46.log2_exp_bound (D := D) hQ1)

end Eth46Compatibility
