/-
Released under Apache 2.0.

Finite sampling and avoidance shared by the two ETH developments.
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Algebra.Field.Rat

/-!
Splitting an assignment into read and unread coordinates gives one finite
sum identity. Its natural-number indicator specialization counts prescribed
colourings; its rational normalization gives uniform local reads.

The restriction-counting identities do not require an inhabited alphabet.
Nonemptiness is used for normalized averages and for choosing an outcome
outside a weighted finite budget of bad events.
This module imports neither ETH development.
-/

namespace EthBridge.Shared.FiniteSampling

open scoped BigOperators

variable {I J W R : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype W]

/-- Splitting read and unread coordinates transports finite sums. Neither
the alphabet nor either coordinate type needs to be inhabited. -/
public theorem sum_restrict [AddCommMonoid R]
    (e : J ↪ I) (F : (J → W) → R) :
    (∑ ω : I → W, F (fun j => ω (e j))) =
      Fintype.card ({i : I // i ∉ Set.range e} → W) • ∑ ξ : J → W, F ξ := by
  let split : (I → W) ≃ (J → W) × ({i : I // i ∉ Set.range e} → W) :=
    (Equiv.piEquivPiSubtypeProd (fun i => i ∈ Set.range e) (fun _ => W)).trans
      (Equiv.prodCongr
        (Equiv.arrowCongr (Equiv.ofInjective e e.injective).symm (Equiv.refl W))
        (Equiv.refl _))
  calc
    _ = ∑ p : (J → W) × ({i : I // i ∉ Set.range e} → W), F p.1 :=
      Fintype.sum_equiv split _ _ (fun _ => rfl)
    _ = _ := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp only [Finset.sum_const, Finset.card_univ]

/-- Uniform restriction with denominators cleared, valid even when the
alphabet is empty and over an arbitrary commutative semiring. -/
public theorem sum_restrict_mul_card [CommSemiring R]
    (e : J ↪ I) (F : (J → W) → R) :
    (∑ ω : I → W, F (fun j => ω (e j))) * (Fintype.card (J → W) : R) =
      (Fintype.card (I → W) : R) * ∑ ξ : J → W, F ξ := by
  have hcard : Fintype.card (I → W) =
      Fintype.card ({i : I // i ∉ Set.range e} → W) * Fintype.card (J → W) := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Nat.cast_id] using
      sum_restrict (R := ℕ) e (fun _ : J → W => 1)
  rw [sum_restrict e F, nsmul_eq_mul, hcard, Nat.cast_mul]
  ac_rfl

/-- Counting extensions of a prescribed local assignment, without division
and without a nonempty-alphabet assumption. -/
public theorem card_restrict_mul [DecidableEq W] (e : J ↪ I) (x : J → W) :
    (Finset.univ.filter (fun ω : I → W => (fun j => ω (e j)) = x)).card *
        Fintype.card (J → W) = Fintype.card (I → W) := by
  classical
  simpa using sum_restrict_mul_card (R := ℕ) e
    (fun ξ : J → W => if ξ = x then 1 else 0)

/-- Restriction along an injection preserves the uniform rational average.
Nonemptiness is needed only for this normalized form. -/
public theorem average_restrict [Nonempty W]
    (e : J ↪ I) (F : (J → W) → ℚ) :
    (∑ ω : I → W, F (fun j => ω (e j))) / (Fintype.card (I → W) : ℚ) =
      (∑ ξ : J → W, F ξ) / (Fintype.card (J → W) : ℚ) := by
  have hI : (Fintype.card (I → W) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hJ : (Fintype.card (J → W) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  apply (div_eq_div_iff hI hJ).2
  exact (sum_restrict_mul_card e F).trans (mul_comm _ _)

/-- A weighted union budget leaves an outcome outside every bad event.
The event index set may be empty and individual costs may vanish. -/
public theorem exists_avoiding_of_budget {Ω J : Type*} [Fintype Ω] [Nonempty Ω]
    (s : Finset J) (bad : J → Finset Ω) (cost : J → ℕ) (D : ℕ)
    (hbound : ∀ j ∈ s, (bad j).card * D ≤ cost j * Fintype.card Ω)
    (hbudget : (∑ j ∈ s, cost j) < D) :
    ∃ ω : Ω, ∀ j ∈ s, ω ∉ bad j := by
  classical
  have hu : (s.biUnion bad).card * D ≤ (∑ j ∈ s, cost j) * Fintype.card Ω := by
    calc
      _ ≤ (∑ j ∈ s, (bad j).card) * D := Nat.mul_le_mul_right _ Finset.card_biUnion_le
      _ = ∑ j ∈ s, (bad j).card * D := Finset.sum_mul _ _ _
      _ ≤ ∑ j ∈ s, cost j * Fintype.card Ω := Finset.sum_le_sum hbound
      _ = _ := (Finset.sum_mul _ _ _).symm
  have hlt := hu.trans_lt (Nat.mul_lt_mul_of_pos_right hbudget (Fintype.card_pos (α := Ω)))
  rw [mul_comm D] at hlt
  obtain ⟨ω, _, hω⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (t := Finset.univ) (by simpa using Nat.lt_of_mul_lt_mul_right hlt)
  exact ⟨ω, fun j hj hmem => hω (Finset.mem_biUnion.mpr ⟨j, hj, hmem⟩)⟩

end EthBridge.Shared.FiniteSampling
