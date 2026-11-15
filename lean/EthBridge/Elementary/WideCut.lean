/-
SPDX-License-Identifier: Apache-2.0
The full-input delta factorization used for the unfavorable cut of a piece.
-/
module

public import EthBridge.Elementary.PieceBounds
public import StepMachines.Math.CutWord

@[expose] public section
namespace EthBridge.Elementary.WideCut

open Finset Groundwork

/-- Any two-word function factors through the concatenated 2n input bits.
There is exactly one nonzero name; the identity includes n=0. -/
theorem full_input_identity (n : ℕ) (f : Bits n → Bits n → ℤ) (x y : Bits n) :
    f x y = ∑ w ∈ words (2 * n),
      (if List.ofFn x ++ List.ofFn y = w then (1 : ℤ) else 0) *
        f (Grid.bitsOf n (w.take n)) (Grid.bitsOf n (w.drop n)) := by
  have hx : Grid.bitsOf n (List.ofFn x) = x := by
    funext k
    simp [Grid.bitsOf, List.getD_eq_getElem]
  have hy : Grid.bitsOf n (List.ofFn y) = y := by
    funext k
    simp [Grid.bitsOf, List.getD_eq_getElem]
  have hmem : List.ofFn x ++ List.ofFn y ∈ words (2 * n) := by
    apply mem_words.mpr
    simp
    omega
  symm
  rw [Finset.sum_eq_single_of_mem (List.ofFn x ++ List.ofFn y) hmem]
  · rw [if_pos rfl, one_mul, List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn, hx, hy]
  · intro w _ hne
    rw [if_neg hne.symm, zero_mul]

end EthBridge.Elementary.WideCut
