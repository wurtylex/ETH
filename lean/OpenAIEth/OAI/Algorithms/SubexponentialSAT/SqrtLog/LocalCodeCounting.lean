import OAI.Algorithms.SubexponentialSAT.LeanCompat
import EthBridge.Shared.FiniteSampling

namespace OAI.Algorithms

/-! Finite counting lemmas for the local-code exhaustive search. -/

namespace SubexponentialSAT.SqrtLog.LocalCode

open scoped BigOperators

theorem exists_avoiding_of_budget
    {A B : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
    (s : Finset B) (bad : B → Finset A) (K : ℕ)
    (hbudget : ∀ b ∈ s, (bad b).card * K ≤ Fintype.card A)
    (hsmall : s.card < K) :
    ∃ a : A, ∀ b ∈ s, a ∉ bad b := by
  simpa using EthBridge.Shared.FiniteSampling.exists_avoiding_of_budget s bad (fun _ => 1) K
    (by simpa using hbudget) (by simpa using hsmall)

/-- Translation identifies an arbitrary fiber of a surjective homomorphism
with its zero fiber. This is the exact finite substitute for uniformity. -/
def fiberEquivZero {A B : Type*} [AddGroup A] [AddGroup B]
    (f : A →+ B) (b : B) (a : A) (ha : f a = b) :
    {x : A // f x = b} ≃ {x : A // f x = 0} where
  toFun x := ⟨x.1 - a, by rw [map_sub, x.2, ha, sub_self]⟩
  invFun x := ⟨x.1 + a, by rw [map_add, x.2, ha, zero_add]⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; simp

theorem card_zero_fiber_mul
    {A B : Type*} [AddGroup A] [AddGroup B] [Fintype A] [Fintype B] [DecidableEq B]
    (f : A →+ B) (hf : Function.Surjective f) :
    Fintype.card {x : A // f x = 0} * Fintype.card B = Fintype.card A := by
  classical
  have hsame (b : B) :
      Fintype.card {x : A // f x = b} = Fintype.card {x : A // f x = 0} := by
    obtain ⟨a, ha⟩ := hf b
    exact Fintype.card_congr (fiberEquivZero f b a ha)
  have hsum := Fintype.card_congr (Equiv.sigmaFiberEquiv f)
  simpa only [Fintype.card_sigma, hsame, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_comm] using hsum

end SubexponentialSAT.SqrtLog.LocalCode

end OAI.Algorithms
