/-
SPDX-License-Identifier: Apache-2.0
Executable collected two-piece coefficients. This is an implementation adapter
for the existing common-width recursion, not an independent ETH conclusion.
-/
module

public import EthBridge.Elementary.Crossing
public import EthBridge.Elementary.PieceBounds
public import EthBridge.Elementary.WideCut
public import ClauseBound.Alg.Data
public import PaddedDescent.F.FuelCert
import all PaddedDescent.F.CertSide
import PaddedDescent.F.Expand
import ToTuring.Poly.Cut
import Mathlib.Tactic

@[expose] public section
namespace EthBridge.Elementary.Pieces

open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
open EthBridge.Elementary.Crossing

/-- The common sparse code uses one threshold for the whole collected piece. -/
def sparseTop (tr : Bool) (x y w : List Bool) : ℤ :=
  if validW x.length (x.length / 2) w = true then
    prodL x.length (topTerm tr x y w) else 0

/-- Collect existing padded coefficient programs, without their index-dependent guards. -/
def collectBot (high tr : Bool) (pad : U) (x y w : List Bool) : ℤ :=
  ((List.range (x.length + 1)).map fun i =>
    if (if high = true then x.length < 2 * i else 2 * i ≤ x.length) then
      botF pad tr i x y w else 0).sum

def sparseBot (high tr : Bool) (pad : U) (x y w : List Bool) : ℤ :=
  if validW x.length (x.length / 2) w = true then collectBot high tr pad x y w else 0

@[fun_prop] theorem sparseTop_polyT {α : Type} [Enc α] (tr : Bool)
    {x y w : α → List Bool} (hx : PolyT x) (hy : PolyT y) (hw : PolyT w) :
    PolyT fun a => sparseTop tr (x a) (y a) (w a) := by
  unfold sparseTop
  fun_prop

@[fun_prop] theorem collectBot_polyT {α : Type} [Enc α] (high tr : Bool)
    {pad : α → U} {x y w : α → List Bool}
    (hp : PolyT pad) (hx : PolyT x) (hy : PolyT y) (hw : PolyT w) :
    PolyT fun a => collectBot high tr (pad a) (x a) (y a) (w a) := by
  unfold collectBot
  cases high <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> fun_prop

@[fun_prop] theorem sparseBot_polyT {α : Type} [Enc α] (high tr : Bool)
    {pad : α → U} {x y w : α → List Bool}
    (hp : PolyT pad) (hx : PolyT x) (hy : PolyT y) (hw : PolyT w) :
    PolyT fun a => sparseBot high tr (pad a) (x a) (y a) (w a) := by
  unfold sparseBot
  fun_prop

/-- The reused coefficient kernel has a common decoder for every index i. -/
theorem botF_common (pad : U) (tr : Bool) (i c n : ℕ) (x y w : List Bool)
    (hx : x.length = n) (hp : 2 ^ n ≤ pad.length) :
    botF pad tr i x y w = (sideBit tr).Bot i
      ((Code.sparse (sideS0 tr) n c).dec w) (Groundwork.Grid.bitsOf n x) (Groundwork.Grid.bitsOf n y) := by
  have he : botF pad tr i x y w = botW tr i x y w := by
    unfold botF botW
    rw [sumF_eq (by simpa [hx] using hp)]
    simp only [prodL_eq]
  rw [he, botW_eq tr i c w hx]

@[simp] theorem bitsOf_ofFn {n : ℕ} (x : Bits n) :
    Groundwork.Grid.bitsOf n (List.ofFn x) = x := by
  funext k
  simp [Groundwork.Grid.bitsOf]

theorem collectBot_low (pad : U) (tr : Bool) (n c : ℕ) (x y : Bits n) (w : List Bool)
    (hp : 2 ^ n ≤ pad.length) :
    collectBot false tr pad (List.ofFn x) (List.ofFn y) w =
      ∑ i ∈ lowIndices n, (sideBit tr).Bot i ((Code.sparse (sideS0 tr) n c).dec w) x y := by
  simp only [collectBot, List.length_ofFn, Bool.false_eq_true, ite_false]
  rw [PaddedDescent.F.Expand.sum_map_range]
  simp_rw [botF_common pad tr _ c n _ _ _ (List.length_ofFn) hp, bitsOf_ofFn]
  simp only [lowIndices, sum_filter]

theorem collectBot_high (pad : U) (tr : Bool) (n c : ℕ) (x y : Bits n) (w : List Bool)
    (hp : 2 ^ n ≤ pad.length) :
    collectBot true tr pad (List.ofFn x) (List.ofFn y) w =
      ∑ i ∈ highIndices n, (sideBit tr).Bot i ((Code.sparse (sideS0 tr) n c).dec w) x y := by
  simp only [collectBot, List.length_ofFn, ite_true]
  rw [PaddedDescent.F.Expand.sum_map_range]
  simp_rw [botF_common pad tr _ c n _ _ _ (List.length_ofFn) hp, bitsOf_ofFn]
  simp only [highIndices, sum_filter, Nat.not_le]

theorem sparseTop_eq (tr : Bool) (n : ℕ) (x y : Bits n) (w : List Bool) :
    sparseTop tr (List.ofFn x) (List.ofFn y) w =
      if validW n (n/2) w = true then
        (sideBit tr).Top ((Code.sparse (sideS0 tr) n (n/2)).dec w) x y else 0 := by
  unfold sparseTop
  simp only [List.length_ofFn]
  have h := topW_eq tr (n / 2) w (x := List.ofFn x) (y := List.ofFn y) List.length_ofFn
  simp only [bitsOf_ofFn, topW, List.length_ofFn] at h
  simp only [prodL_eq, h]

theorem pieceA_rows_program (pad : U) (n : ℕ) (x y u v : Bits n)
    (hp : 2 ^ n ≤ pad.length) :
    pieceA n x y u v = ∑ w ∈ words (capW n (n/2)),
      sparseTop true (List.ofFn x) (List.ofFn y) w *
        sparseBot false true pad (List.ofFn u) (List.ofFn v) w := by
  rw [pieceA_rows_words]
  apply sum_congr rfl
  intro w hw
  have ht := sparseTop_eq true n x y w
  have hb := collectBot_low pad true n (n/2) u v w hp
  simp only [sparseBot, List.length_ofFn, ht, hb, sideBit, sideS0, ite_true,
    rowCoeff, Code.sparse, mem_filter, hw, true_and]
  split_ifs <;> simp_all

theorem pieceB_cols_program (pad : U) (n : ℕ) (x y u v : Bits n)
    (hp : 2 ^ n ≤ pad.length) :
    pieceB n x y u v = ∑ w ∈ words (capW n (n/2)),
      sparseTop false (List.ofFn x) (List.ofFn u) w *
        sparseBot true false pad (List.ofFn y) (List.ofFn v) w := by
  rw [pieceB_cols_words]
  apply sum_congr rfl
  intro w hw
  have ht := sparseTop_eq false n x u w
  have hb := collectBot_high pad false n (n/2) y v w hp
  simp only [sparseBot, List.length_ofFn, ht, hb, sideBit, sideS0, Bool.false_eq_true, ite_false,
    colCoeff, Code.sparse, mem_filter, hw, true_and]
  split_ifs <;> simp_all

/-- Evaluate the row or column factorization whose sparse width is favorable.
The enumeration is bounded by the supplied pad; no binary exponential loop is uncharged. -/
def sparseValue (high tr : Bool) (pad : U) (x y u v : List Bool) : ℤ :=
  sumF (2 ^ capW x.length (x.length / 2)) pad fun t =>
    let w := toWord (capW x.length (x.length / 2)) t
    sparseTop tr x y w * sparseBot high tr pad u v w

@[fun_prop] theorem sparseValue_polyT {α : Type} [Enc α] (high tr : Bool)
    {pad : α → U} {x y u v : α → List Bool}
    (hp : PolyT pad) (hx : PolyT x) (hy : PolyT y) (hu : PolyT u) (hv : PolyT v) :
    PolyT fun a => sparseValue high tr (pad a) (x a) (y a) (u a) (v a) := by
  have hc : Unary fun a => capW (x a).length ((x a).length / 2) :=
    capW_unary (by fun_prop) (by fun_prop)
  have hw : PolyT fun p : α × ℕ => toWord (capW (x p.1).length ((x p.1).length / 2)) p.2 :=
    PolyT.toWord' (hc.comp (h := fun p : α × ℕ => p.1) (by fun_prop)) (by fun_prop)
  unfold sparseValue
  exact sumF_polyT (PolyT.pow_unary (by fun_prop) hc) hp (by dsimp; fun_prop)

theorem sparseValue_eq_sum (high tr : Bool) (pad : U) (n : ℕ) (x y u v : Bits n)
    (hp : 2 ^ capW n (n/2) ≤ pad.length) :
    sparseValue high tr pad (List.ofFn x) (List.ofFn y) (List.ofFn u) (List.ofFn v) =
      ∑ w ∈ words (capW n (n/2)), sparseTop tr (List.ofFn x) (List.ofFn y) w *
        sparseBot high tr pad (List.ofFn u) (List.ofFn v) w := by
  unfold sparseValue
  simp only [List.length_ofFn]
  rw [sumF_eq hp]
  exact sum_toWord _ (fun w => sparseTop tr (List.ofFn x) (List.ofFn y) w *
    sparseBot high tr pad (List.ofFn u) (List.ofFn v) w)

/-- Both pieces use their own favorable cut when their value is requested. -/
def value (high : Bool) (pad : U) (x y u v : List Bool) : ℤ :=
  if high = true then sparseValue true false pad x u y v
  else sparseValue false true pad x y u v

@[fun_prop] theorem value_polyT {α : Type} [Enc α] (high : Bool)
    {pad : α → U} {x y u v : α → List Bool}
    (hp : PolyT pad) (hx : PolyT x) (hy : PolyT y) (hu : PolyT u) (hv : PolyT v) :
    PolyT fun a => value high (pad a) (x a) (y a) (u a) (v a) := by
  cases high <;> simp only [value, Bool.false_eq_true, ite_false, ite_true] <;> fun_prop

theorem value_low (pad : U) (n : ℕ) (hn : 1 ≤ n) (x y u v : Bits n)
    (hp : 2 ^ (2*n) ≤ pad.length) :
    value false pad (List.ofFn x) (List.ofFn y) (List.ofFn u) (List.ofFn v) = pieceA n x y u v := by
  have h1 : 2 ^ n ≤ pad.length := (Nat.pow_le_pow_right (by norm_num) (by omega : n ≤ 2*n)).trans hp
  have h2 : 2 ^ capW n (n/2) ≤ pad.length :=
    (Nat.pow_le_pow_right (by norm_num) (capW_half_le_two_mul n hn)).trans hp
  simp only [value, Bool.false_eq_true, ite_false]
  rw [sparseValue_eq_sum false true pad n x y u v h2]
  exact (pieceA_rows_program pad n x y u v h1).symm

theorem value_high (pad : U) (n : ℕ) (hn : 1 ≤ n) (x y u v : Bits n)
    (hp : 2 ^ (2*n) ≤ pad.length) :
    value true pad (List.ofFn x) (List.ofFn y) (List.ofFn u) (List.ofFn v) = pieceB n x y u v := by
  have h1 : 2 ^ n ≤ pad.length := (Nat.pow_le_pow_right (by norm_num) (by omega : n ≤ 2*n)).trans hp
  have h2 : 2 ^ capW n (n/2) ≤ pad.length :=
    (Nat.pow_le_pow_right (by norm_num) (capW_half_le_two_mul n hn)).trans hp
  simp only [value, ite_true]
  rw [sparseValue_eq_sum true false pad n x u y v h2]
  exact (pieceB_cols_program pad n x y u v h1).symm

/-- The unfavorable cut names its entire first pair of inputs. -/
def wideTop (x y w : List Bool) : ℤ := if x ++ y = w then 1 else 0

def wideBot (high col : Bool) (pad : U) (x y w : List Bool) : ℤ :=
  if w.length = 2 * x.length then
    if col = true then value high pad (w.take x.length) x (w.drop x.length) y
    else value high pad (w.take x.length) (w.drop x.length) x y
  else 0

@[fun_prop] theorem wideTop_polyT {α : Type} [Enc α]
    {x y w : α → List Bool} (hx : PolyT x) (hy : PolyT y) (hw : PolyT w) :
    PolyT fun a => wideTop (x a) (y a) (w a) := by unfold wideTop; fun_prop

@[fun_prop] theorem wideBot_polyT {α : Type} [Enc α] (high col : Bool)
    {pad : α → U} {x y w : α → List Bool}
    (hp : PolyT pad) (hx : PolyT x) (hy : PolyT y) (hw : PolyT w) :
    PolyT fun a => wideBot high col (pad a) (x a) (y a) (w a) := by
  cases col <;> simp only [wideBot, Bool.false_eq_true, ite_false, ite_true] <;> fun_prop

theorem pieceA_cols_program (pad : U) (n : ℕ) (hn : 1 ≤ n) (x y u v : Bits n)
    (hp : 2 ^ (2*n) ≤ pad.length) :
    pieceA n x y u v = ∑ w ∈ words (2*n), wideTop (List.ofFn x) (List.ofFn u) w *
      wideBot false true pad (List.ofFn y) (List.ofFn v) w := by
  rw [WideCut.full_input_identity n (fun a b => pieceA n a y b v) x u]
  apply sum_congr rfl
  intro w hw
  by_cases he : List.ofFn x ++ List.ofFn u = w
  · subst w
    simp only [wideTop, wideBot, List.length_append, List.length_ofFn,
      show n + n = 2*n by omega, ite_true, List.take_left' List.length_ofFn,
      List.drop_left' List.length_ofFn, bitsOf_ofFn, one_mul]
    exact (value_low pad n hn x y u v hp).symm
  · simp only [wideTop, he, ite_false, zero_mul]

theorem pieceB_rows_program (pad : U) (n : ℕ) (hn : 1 ≤ n) (x y u v : Bits n)
    (hp : 2 ^ (2*n) ≤ pad.length) :
    pieceB n x y u v = ∑ w ∈ words (2*n), wideTop (List.ofFn x) (List.ofFn y) w *
      wideBot true false pad (List.ofFn u) (List.ofFn v) w := by
  rw [WideCut.full_input_identity n (fun a b => pieceB n a b u v) x y]
  apply sum_congr rfl
  intro w hw
  by_cases he : List.ofFn x ++ List.ofFn y = w
  · subst w
    simp only [wideTop, wideBot, List.length_append, List.length_ofFn,
      show n + n = 2*n by omega, ite_true, Bool.false_eq_true, ite_false,
      List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn, bitsOf_ofFn, one_mul]
    exact (value_high pad n hn x y u v hp).symm
  · simp only [wideTop, he, ite_false, zero_mul]

open ClauseBound.Alg in
/-- Constant two-piece family: A is favorable on rows, B on columns. -/
def family : PiecesF where
  cnt _ _ := 2
  d _ _ := 1
  cap col _ n i := if i = 0 then (if col = true then 2*n else capW n (n/2))
    else (if col = true then capW n (n/2) else 2*n)
  top q := if q.2.1.2 = 0 then
    (if q.1.2 = true then wideTop q.2.2.1 q.2.2.2.1 q.2.2.2.2
      else sparseTop true q.2.2.1 q.2.2.2.1 q.2.2.2.2)
    else (if q.1.2 = true then sparseTop false q.2.2.1 q.2.2.2.1 q.2.2.2.2
      else wideTop q.2.2.1 q.2.2.2.1 q.2.2.2.2)
  bot q := if q.2.1.2 = 0 then
    (if q.1.2 = true then wideBot false true q.1.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2
      else sparseBot false true q.1.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)
    else (if q.1.2 = true then sparseBot true false q.1.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2
      else wideBot true false q.1.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)
  need _ n := 2*n
  bits _ n := 2*n
  m := 1

/-- Every program is polynomial-time in its encoded arguments, including the supplied pad. -/
theorem family_keeps : family.Keeps := by
  have hc : Unary fun p : Bool × U × U × ℕ => capW p.2.2.1.length (p.2.2.1.length / 2) :=
    capW_unary (by fun_prop) (by fun_prop)
  constructor
  · change Unary fun _ : U × U => 2; fun_prop
  · change PolyT fun _ : U × U => 1; fun_prop
  · change Unary fun p : Bool × U × U × ℕ =>
      if p.2.2.2 = 0 then (if p.1 = true then 2*p.2.2.1.length else capW p.2.2.1.length (p.2.2.1.length/2))
      else (if p.1 = true then capW p.2.2.1.length (p.2.2.1.length/2) else 2*p.2.2.1.length)
    exact Unary.of_le (g := fun p => 2*p.2.2.1.length + capW p.2.2.1.length (p.2.2.1.length/2))
      (by fun_prop) (by have := hc.poly; fun_prop) (fun p => by split_ifs <;> omega)
  · change PolyT family.top
    unfold family
    fun_prop
  · change PolyT family.bot
    unfold family
    fun_prop
  · change Unary fun p : U × U => 2*p.2.length; fun_prop
  · change Unary fun p : U × U => 2*p.2.length; fun_prop

end EthBridge.Elementary.Pieces
