/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import RAMToTM.Transport.InitPrims

/-!
# The initial state of the interpreter is polynomial time

This file finishes the `init` half of `Nonempty (IsPolyT (EthWordRam.machine P b))`, on top of the
primitives of `RAMToTM.Transport.InitPrims`. The `step` and the `out` are in
`RAMToTM.Transport.StepPoly`.

The one point that a single `fun_prop` call cannot do is the entry of the initial table at a dynamic
position: the goal there mentions `2 ^ Wof b x`, and `fun_prop` reduces `PolyT (2 ^ ·)` to `Unary` of
the exponent, a side condition it has no way to guess. The modulus and the bias are therefore read as
*data* — `initEntry` only ever uses `pw` and `hw` through `%`, `-`, `+`, `*` and comparisons — and the
composition with `pw := 2 ^ W` and `hw := 2 ^ (W - 1)` is an explicit `PolyT.comp` with an explicit
`PolyT.prodMk`, where the two powers are `PolyT.two_pow` of the `Unary` facts proved in `InitPrims`.
-/

namespace RAMToTM.Transport

open Groundwork Groundwork.PolyT

set_option maxHeartbeats 4000000

/-! ## One entry of the initial table -/

/-- **One entry, with the modulus and the bias as data.** The body is the body of `initEntry`;
nothing here computes a power, so `fun_prop` has no `Unary` side condition to discharge. -/
theorem initEntry_poly (P : List EndStatement.Instr) :
    PolyT (fun q : (ℕ × ℕ) × List ℤ × ℕ => initEntry P q.1.1 q.1.2 q.2.1 q.2.2) := by
  simp only [initEntry, EthWordRam.windowSize', EthWordRam.toWord]
  fun_prop

/-- The two powers of the width, as functions of the pair `(x, i)` of the range fold. -/
theorem poly_two_pow_Wof_fst (b : ℕ) :
    PolyT (fun p : List Bool × ℕ => 2 ^ EthWordRam.Wof b p.1) :=
  PolyT.comp (f := fun x : List Bool => 2 ^ EthWordRam.Wof b x)
    (g := fun p : List Bool × ℕ => p.1) (poly_two_pow_Wof b) PolyT.id'.fst

theorem poly_two_pow_Wof_sub_one_fst (b : ℕ) :
    PolyT (fun p : List Bool × ℕ => 2 ^ (EthWordRam.Wof b p.1 - 1)) :=
  PolyT.comp (f := fun x : List Bool => 2 ^ (EthWordRam.Wof b x - 1))
    (g := fun p : List Bool × ℕ => p.1) (poly_two_pow_Wof_sub_one b) PolyT.id'.fst

theorem wsOf_fst : PolyT (fun p : List Bool × ℕ => EthWordRam.wsOf p.1) :=
  PolyT.comp (f := EthWordRam.wsOf) (g := fun p : List Bool × ℕ => p.1)
    wsOf_poly PolyT.id'.fst

/-- **The body of the range fold**: the entry of the initial table at position `p.2` on the input
`p.1`, with the width, the modulus, the bias and the input words read off `p.1`. -/
theorem initTableBody_poly (P : List EndStatement.Instr) (b : ℕ) :
    PolyT (fun p : List Bool × ℕ =>
      initEntry P (2 ^ EthWordRam.Wof b p.1) (2 ^ (EthWordRam.Wof b p.1 - 1))
        (EthWordRam.wsOf p.1) p.2) :=
  PolyT.comp (f := fun q : (ℕ × ℕ) × List ℤ × ℕ => initEntry P q.1.1 q.1.2 q.2.1 q.2.2)
    (g := fun p : List Bool × ℕ =>
      ((2 ^ EthWordRam.Wof b p.1, 2 ^ (EthWordRam.Wof b p.1 - 1)),
        (EthWordRam.wsOf p.1, p.2)))
    (initEntry_poly P)
    (PolyT.prodMk (PolyT.prodMk (poly_two_pow_Wof_fst b) (poly_two_pow_Wof_sub_one_fst b))
      (PolyT.prodMk wsOf_fst (PolyT.id' (α := List Bool × ℕ).snd)))

/-- **The initial table is polynomial time.** This is the real `EthWordRam.initTable` at the width,
the modulus and the bias of the input, folded over its real range. -/
@[fun_prop] theorem initTable_poly (P : List EndStatement.Instr) (b : ℕ) :
    PolyT (fun x : List Bool => EthWordRam.initTable P (2 ^ EthWordRam.Wof b x)
      (2 ^ (EthWordRam.Wof b x - 1)) (EthWordRam.wsOf x)) :=
  (PolyT.map (f := fun x : List Bool => initEntry P (2 ^ EthWordRam.Wof b x)
      (2 ^ (EthWordRam.Wof b x - 1)) (EthWordRam.wsOf x))
    (l := fun x : List Bool =>
      List.range (EthWordRam.tableSize' P (2 ^ (EthWordRam.Wof b x - 1))))
    (initTableBody_poly P b) (PolyT.range (unary_tableSize' P b))).congr
    fun x => (initTable_eq_map P _ _ _).symm

/-! ## The initial state -/

@[fun_prop] theorem initT_poly (P : List EndStatement.Instr) (b : ℕ) :
    PolyT (fun x : List Bool => EthWordRam.initT P b x) := by
  simp only [EthWordRam.initT]
  fun_prop

theorem initSt_poly (P : List EndStatement.Instr) (b : ℕ) :
    PolyT (EthWordRam.initSt P b) :=
  PolyT.of_wd (initT_poly P b) (φ := fun x : List Bool => x) (fun x => rfl) (fun x => rfl)

/-! ## The instance

The three components are the existing `initSt`, `stepSt` and `outSt`: the check lemma below
elaborates `initSt_poly`, `stepSt_poly`, `outSt_poly` at the *machine's own* components, which
typechecks only because `(machine P b).init` is definitionally `initSt P b` (and likewise for the
step and the out). No new model, no new state, no cost measure is introduced here. -/

/-- **The interpreter of the RAM is polynomial time**, with the encoding and the size that the
machine's state already carries (`St.toT`, `size`, `Carried.le`).

It is declared as an `instance`, so that the `Enc`/`Carried` instances of the state *type* of the
machine are found through the class: `(machine P b).σ` is only definitionally `St`, which instance
search does not unfold on its own. -/
instance isPolyT_machine (P : List EndStatement.Instr) (b : ℕ) :
    IsPolyT (EthWordRam.machine P b) :=
  { enc := (inferInstanceAs (Enc EthWordRam.St))
    carried := (inferInstanceAs (Carried EthWordRam.St))
    init := initSt_poly P b
    step := stepSt_poly P
    out := outSt_poly P }

/-- **The hypothesis of `RAMToTM.Transport.exists_tmW_of_exec`, discharged.** -/
theorem nonempty_isPolyT_machine (P : List EndStatement.Instr) (b : ℕ) :
    Nonempty (IsPolyT (EthWordRam.machine P b)) :=
  ⟨isPolyT_machine P b⟩

/-- The three `PolyT` proofs are proofs about the machine's own components. -/
theorem machine_component_check (P : List EndStatement.Instr) (b : ℕ) :
    PolyT (EthWordRam.machine P b).init ∧ PolyT (EthWordRam.machine P b).step ∧
      PolyT (EthWordRam.machine P b).out :=
  ⟨initSt_poly P b, stepSt_poly P, outSt_poly P⟩

end RAMToTM.Transport
