/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import RAMToTM.Transport.InterpSize
import ToTuring.Lib.Bool
import ToTuring.Lib.Int
import ToTuring.Lib.List2
import ToTuring.Lib.List3
import ToTuring.Lib.Nat1b
import ToTuring.Lib.Nat2
import ToTuring.Lib.Table

/-!
# The step and the verdict of the interpreter are polynomial time

`EthWordRam.machine P b` is a `Groundwork.Stepped` computation, so `IsPolyT` asks for `PolyT` of its
`init`, `step` and `out`. This file does the `step` and the `out`: the table update
`List.set` at a computed position, the reading of a cell, the signed reading of a word, and the
if-chains on the opcode of the programme. The `init` (which builds the initial table) is not here.

Everything is stated for the tuple `EthWordRam.Tup` of the six components of the state; the transfer
to `EthWordRam.St` is `PolyT.of_wd`, since the encoding of a state is the encoding of its tuple.
-/

namespace RAMToTM.Transport

set_option maxHeartbeats 4000000

open Groundwork Groundwork.PolyT

/-! ## `List.set` at a computed position -/

theorem set_eq {β : Type} (l : List β) (n : ℕ) (v : β) :
    l.set n v = if n < l.length then l.take n ++ v :: l.drop (n + 1) else l := by
  by_cases h : n < l.length
  · rw [if_pos h]
    induction l generalizing n with
    | nil => exact absurd h (Nat.not_lt_zero _)
    | cons a tl ih =>
      cases n with
      | zero => rfl
      | succ n =>
        have h' : n < tl.length := by simpa using h
        simp only [List.set_cons_succ, List.take_succ_cons, List.drop_succ_cons, ih n h',
          List.cons_append]
  · rw [if_neg h, List.set_eq_of_length_le (Nat.le_of_not_lt h)]

/-- Updating the entry at a dynamic position. -/
@[fun_prop] theorem listSet_poly :
    PolyT (fun p : List ℕ × (ℕ × ℕ) => p.1.set p.2.1 p.2.2) := by
  have h : PolyT (fun p : List ℕ × (ℕ × ℕ) =>
      if p.2.1 < p.1.length then p.1.take p.2.1 ++ p.2.2 :: p.1.drop (p.2.1 + 1) else p.1) := by
    fun_prop
  exact h.congr fun p => (set_eq p.1 p.2.1 p.2.2).symm

/-! ## The pieces of the step -/

/-- The position of an address in the table. -/
theorem cellS_poly (P : List EndStatement.Instr) :
    PolyT (fun p : EthWordRam.Tup × ℤ => EthWordRam.cellS P p.1.2.2.1 p.2) := by
  simp only [EthWordRam.cellS, EthWordRam.windowSize']
  fun_prop

/-- Reading the cell of an address. -/
theorem getS_poly (P : List EndStatement.Instr) :
    PolyT (fun p : EthWordRam.Tup × ℤ => EthWordRam.getS P p.1.2.2.1 p.1.2.2.2.2.2 p.2) := by
  simp only [EthWordRam.getS, EthWordRam.cellS, EthWordRam.windowSize']
  fun_prop

/-- Writing the cell of an address. -/
theorem putS_poly (P : List EndStatement.Instr) :
    PolyT (fun p : (EthWordRam.Tup × ℤ) × ℕ =>
      EthWordRam.putS P p.1.1.2.2.1 p.1.1.2.2.2.2.2 p.1.2 p.2) := by
  simp only [EthWordRam.putS, EthWordRam.cellS, EthWordRam.windowSize']
  fun_prop

/-- The signed reading of a table entry. -/
theorem toSigned_poly :
    PolyT (fun p : (ℕ × ℕ) × ℕ => EthWordRam.toSigned p.1.1 p.1.2 p.2) := by
  simp only [EthWordRam.toSigned]
  fun_prop

/-! ## The step -/

/-- **One step of the table is polynomial time**, as a function of the tuple of the state. -/
@[fun_prop] theorem stepCore_poly (P : List EndStatement.Instr) :
    PolyT (fun s : EthWordRam.Tup => EthWordRam.stepCore P s) := by
  simp only [EthWordRam.stepCore, EthWordRam.getS, EthWordRam.putS, EthWordRam.cellS,
    EthWordRam.toSigned, EthWordRam.windowSize']
  fun_prop

/-- One step of the machine, on the tuple. -/
@[fun_prop] theorem stepT_poly (P : List EndStatement.Instr) :
    PolyT (fun s : EthWordRam.Tup => EthWordRam.stepT P s) := by
  simp only [EthWordRam.stepT]
  fun_prop

/-- The verdict of a state. -/
@[fun_prop] theorem verdictT_poly (P : List EndStatement.Instr) :
    PolyT (fun s : EthWordRam.Tup => EthWordRam.verdictT P s) := by
  simp only [EthWordRam.verdictT]
  fun_prop

/-- The one-bit output of a state. -/
theorem outT_poly (P : List EndStatement.Instr) :
    PolyT (fun s : EthWordRam.Tup => EthWordRam.outT P s) := by
  simp only [EthWordRam.outT, EthWordRam.verdictT]
  fun_prop

/-! ## Transfer to the state type of the machine

`EthWordRam.St` is encoded by the tuple of its components, so `PolyT` of a function on states
follows from `PolyT` of the same function on tuples. -/

theorem stepSt_poly (P : List EndStatement.Instr) : PolyT (EthWordRam.stepSt P) :=
  PolyT.of_wd (stepT_poly P) (φ := EthWordRam.St.toT) (fun s => rfl) (fun s => rfl)

theorem outSt_poly (P : List EndStatement.Instr) : PolyT (EthWordRam.outSt P) :=
  PolyT.of_wd (outT_poly P) (φ := EthWordRam.St.toT) (fun s => rfl) (fun s => rfl)

end RAMToTM.Transport
