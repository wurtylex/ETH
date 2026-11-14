/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import RAMToTM.Transport.StepPoly
import RAMToTM.Transport.Final
import ToTuring.Lib.Unary

/-!
# Primitives for the initial state of the interpreter

**Provenance.** The proofs in this file are verbatim the first part of
`.ultramath/smwglrpay/m2/RAMToTM/Transport/InitPoly.lean` (member m2 of swarm `smwglrpay`),
sha256 3705a04385ffac74a0911b57ff263e3c91ca4a073de74007f70eb2609950b386, split off so that
`InitPoly` can start from them; only this module header is new, and the quoted file is kept whole in
`recovered/`. The last proof of the recovered file, `initTable_poly`, does not elaborate in this
build (`fun_prop` cannot discharge the `Unary` side condition of `PolyT (2 ^ ·)` when the exponent
is `Wof b x`), which is the one thing `InitPoly` replaces. Everything here is re-checked by
`verify.sh`.

The `init` of `EthWordRam.machine P b` reads the bit string `x`: the recovered variable count
`n = (x.takeWhile id).length`, the width `W = b * (log2 n + 1)`, the modulus `2^W`, the bias
`2^(W-1)` and the whole initial table, which has `tableSize P W` entries.

Two facts make this polynomial time. The width is *logarithmic* in `n ≤ |x|`, so `2^W` is a power of
`|x| + 1` (not exponential): `Unary` of `W` and `Unary` of `2^W` both follow from a polynomial bound
in `|x|`. And the table is built by a `List.range` fold, one constant-cost entry per position.
-/

namespace RAMToTM.Transport

open Groundwork Groundwork.PolyT

set_option maxHeartbeats 4000000

/-! ## The recovered variable count and the width -/

/-- The number of leading `true` bits is polynomial-time. -/
@[fun_prop] theorem nOf_poly : PolyT (fun x : List Bool => EthWordRam.nOf x) := by
  have h1 := PolyT.takeWhile (α := List Bool) (β := Bool)
    (f := fun (_ : List Bool) (b : Bool) => b) (l := fun x => x) (by fun_prop)
    (PolyT.id' (α := List Bool))
  have h2 : PolyT (fun x : List Bool => (List.takeWhile (fun b => b) x)) := h1
  exact PolyT.length h2

/-- The width `b * (log2 n + 1)` is polynomial-time. -/
@[fun_prop] theorem Wof_poly (b : ℕ) : PolyT (fun x : List Bool => EthWordRam.Wof b x) := by
  have h1 : PolyT (fun x : List Bool => EthWordRam.nOf x) := nOf_poly
  have h2 : PolyT (fun x : List Bool => (EthWordRam.nOf x).log2) := PolyT.log2' h1
  have h3 : PolyT (fun x : List Bool => b * ((EthWordRam.nOf x).log2 + 1)) := by fun_prop
  exact h3.congr fun x => rfl

/-- The width is at most `b * (|x| + 1)`. -/
theorem Wof_le_len (b : ℕ) (x : List Bool) : EthWordRam.Wof b x ≤ b * (x.length + 1) := by
  have h1 : EthWordRam.nOf x ≤ x.length :=
    List.Sublist.length_le (List.takeWhile_sublist (id : Bool → Bool) (l := x))
  have h2 : Nat.log2 (EthWordRam.nOf x) ≤ x.length := (Nat.log2_le_self _).trans h1
  simp only [EthWordRam.Wof]
  exact Nat.mul_le_mul_left b (by omega)

/-! ## `Unary` facts -/

theorem unary_len_succ : Unary (fun x : List Bool => x.length + 1) :=
  Unary.add (Unary.of_length (PolyT.id' (α := List Bool))) (Unary.const 1)

theorem unary_mul_len (b : ℕ) : Unary (fun x : List Bool => b * (x.length + 1)) :=
  Unary.mul (Unary.const b) unary_len_succ

theorem unary_pow_len : ∀ b : ℕ, Unary (fun x : List Bool => (x.length + 1) ^ b)
  | 0 => (Unary.const 1).congr fun x => by simp
  | b + 1 => by
    have ih := unary_pow_len b
    have h := Unary.mul ih unary_len_succ
    exact h.congr fun x => by simp [Nat.pow_succ]

theorem unary_Wof (b : ℕ) : Unary (fun x : List Bool => EthWordRam.Wof b x) :=
  Unary.of_le (unary_mul_len b) (Wof_poly b) (Wof_le_len b)

@[fun_prop] theorem poly_two_pow_Wof (b : ℕ) : PolyT (fun x : List Bool => 2 ^ EthWordRam.Wof b x) :=
  PolyT.two_pow (unary_Wof b)

theorem unary_two_pow_Wof (b : ℕ) : Unary (fun x : List Bool => 2 ^ EthWordRam.Wof b x) :=
  Unary.of_le (Unary.mul (Unary.const (2 ^ b)) (unary_pow_len b)) (poly_two_pow_Wof b)
    (two_pow_Wof_le b)

@[fun_prop] theorem poly_two_pow_Wof_sub_one (b : ℕ) :
    PolyT (fun x : List Bool => 2 ^ (EthWordRam.Wof b x - 1)) :=
  PolyT.two_pow (Unary.of_le (unary_mul_len b) (PolyT.sub (Wof_poly b) (PolyT.const 1))
    (fun x => by have := Wof_le_len b x; omega))

theorem unary_two_pow_Wof_sub_one (b : ℕ) :
    Unary (fun x : List Bool => 2 ^ (EthWordRam.Wof b x - 1)) :=
  Unary.of_le (unary_two_pow_Wof b) (poly_two_pow_Wof_sub_one b)
    (fun x => Nat.pow_le_pow_right (by norm_num) (by omega))

/-! ## The input words -/

/-- The initial memory words are polynomial-time in the bit string. -/
@[fun_prop] theorem wsOf_poly : PolyT (fun x : List Bool => EthWordRam.wsOf x) := by
  simp only [EthWordRam.wsOf, EthWordRam.nOf]
  have h1 : PolyT (fun x : List Bool => (List.takeWhile (fun b => b) x).length) := by
    have h := PolyT.takeWhile (α := List Bool) (β := Bool) (f := fun (_ : List Bool) (b : Bool) => b)
      (l := fun x => x) (by fun_prop) (PolyT.id' (α := List Bool))
    exact PolyT.length h
  fun_prop

/-! ## The initial table -/

/-- The unsigned word of a non-negative integer, at a modulus that is part of the data. -/
@[fun_prop] theorem toWord_poly {α : Type} [Enc α] {pw : α → ℕ} (hpw : PolyT pw) {z : α → ℤ}
    (hz : PolyT z) : PolyT (fun x => EthWordRam.toWord (pw x) (z x)) := by
  simp only [EthWordRam.toWord]
  fun_prop

/-- One entry of the initial table. -/
def initEntry (P : List EndStatement.Instr) (pw hw : ℕ) (ws : List ℤ) (i : ℕ) : ℕ :=
  if i < EthWordRam.windowSize' hw then
    (if i < hw then 0 else EthWordRam.toWord pw (ws.getD (i - hw) 0))
  else
    (if (EthWordRam.progCells P).getD (i - EthWordRam.windowSize' hw) 0 < 0 then 0
     else EthWordRam.toWord pw
       (ws.getD ((EthWordRam.progCells P).getD (i - EthWordRam.windowSize' hw) 0).toNat 0))

/-- The table as the indicator of its entries. -/
theorem initTable_eq_map (P : List EndStatement.Instr) (pw hw : ℕ) (ws : List ℤ) :
    EthWordRam.initTable P pw hw ws =
      (List.range (EthWordRam.tableSize' P hw)).map (initEntry P pw hw ws) := rfl

/-- The number of table positions is unary: it is at most a polynomial in `|x|` because the width is
logarithmic in the variable count. -/
theorem unary_tableSize' (P : List EndStatement.Instr) (b : ℕ) :
    Unary (fun x : List Bool => EthWordRam.tableSize' P (2 ^ (EthWordRam.Wof b x - 1))) := by
  have hf : PolyT (fun x : List Bool =>
      EthWordRam.tableSize' P (2 ^ (EthWordRam.Wof b x - 1))) := by
    simp only [EthWordRam.tableSize', EthWordRam.windowSize']
    fun_prop
  refine Unary.of_le (g := fun x : List Bool =>
    (2 ^ (b + 1) + 1 + (EthWordRam.progCells P).length) * (x.length + 1) ^ b) ?_ hf (fun x => ?_)
  · exact Unary.mul (Unary.const (2 ^ (b + 1) + 1 + (EthWordRam.progCells P).length))
      (unary_pow_len b)
  · have h1 : 2 ^ (EthWordRam.Wof b x - 1) ≤ 2 ^ b * (x.length + 1) ^ b :=
      le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) (two_pow_Wof_le b x)
    have h2 : 1 ≤ (x.length + 1) ^ b := Nat.one_le_pow b _ (by omega)
    have h2' : 1 + (EthWordRam.progCells P).length
        ≤ (1 + (EthWordRam.progCells P).length) * (x.length + 1) ^ b := by
      calc 1 + (EthWordRam.progCells P).length
          = (1 + (EthWordRam.progCells P).length) * 1 := by ring
        _ ≤ (1 + (EthWordRam.progCells P).length) * (x.length + 1) ^ b :=
            Nat.mul_le_mul_left _ h2
    have step1 : 2 * 2 ^ (EthWordRam.Wof b x - 1) + 1 + (EthWordRam.progCells P).length
        ≤ 2 * (2 ^ b * (x.length + 1) ^ b) + (1 + (EthWordRam.progCells P).length) * (x.length + 1) ^ b := by
      have h3 : 2 * 2 ^ (EthWordRam.Wof b x - 1) ≤ 2 * (2 ^ b * (x.length + 1) ^ b) :=
        Nat.mul_le_mul_left 2 h1
      omega
    have step2 : 2 * (2 ^ b * (x.length + 1) ^ b) + (1 + (EthWordRam.progCells P).length) * (x.length + 1) ^ b
        = (2 ^ (b + 1) + 1 + (EthWordRam.progCells P).length) * (x.length + 1) ^ b := by
      rw [Nat.pow_succ]
      ring
    simp only [EthWordRam.tableSize', EthWordRam.windowSize']
    omega

end RAMToTM.Transport
