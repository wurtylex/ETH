/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import RAMToTM.Transport.InitPoly
import RAMToTM.Transport.RamGlue

/-!
# The conditional endpoint, applied

`RAMToTM.Transport.exists_tmW_of_exec` (member m2 of swarm `smwglrpay`) turns a halting run of the
word RAM into one of Mathlib's multi-stack machines, *given* `Nonempty (IsPolyT (machine P b))`.
`RAMToTM.Transport.nonempty_isPolyT_machine` is that instance, constructed in `InitPoly` from the
fragment-level `PolyT` proofs of `InitPrims`, `StepPoly` and `InitPoly`.

This file applies one to the other. Nothing is assumed: the constants `N` and `q` are the ones the
host theorem `CountKSat.exists_tmW` produces, and the stack alphabets are finite.
-/

namespace RAMToTM.Transport

open Groundwork Turing

/-- **The cross-model statement, unconditional.** For every RAM programme `P` and width parameter
`b` there are one of Mathlib's multi-stack machines `N`, with finite stack alphabets, and one
constant `q`, both fixed before the input, such that whenever `P` halts on the exact input `x`
within `t` steps with verdict `v` — the initial memory being `loadWords (Wof b x) (wsOf x)`, where
`n` is the number of leading `true` bits of `x` and `Wof b x = b * (log2 n + 1)` — the machine `N`
started on the exact bit string `x` halts with the one bit `v` on its output stack within
`q * (t + |x| + 1) ^ q` steps. -/
theorem exists_tmW_of_exec_unconditional (P : List EndStatement.Instr) (b : ℕ) :
    ∃ (N : TM2ComputableAux Bool Bool) (q : ℕ), (∀ k, Finite (N.tm.Γ k)) ∧
      ∀ (x : List Bool) (t : ℕ) (v : Bool),
        (∃ m : ℤ → BitVec (EthWordRam.Wof b x),
          EndStatement.exec P t 0 (EndStatement.loadWords (EthWordRam.Wof b x)
            (EthWordRam.wsOf x)) = some (v, m)) →
        Nonempty (TM2OutputsInTime N.tm (x.map N.inputAlphabet.invFun)
          (some [N.outputAlphabet.invFun v]) (q * (t + x.length + 1) ^ q)) :=
  exists_tmW_of_exec P b (nonempty_isPolyT_machine P b)

/-- The initial memory of the RAM read off `x` is literally `ramInput x`. -/
theorem wsOf_eq_ramInput (x : List Bool) : EthWordRam.wsOf x = ramInput x := by
  simp [EthWordRam.wsOf, EthWordRam.nOf, ramInput]

/-- The same statement with the run written in the `RamHalts` form of `RamGlue`: the bit string
that `P` is started on is `ramInput x`, and the machine is started on the bits of `x`. -/
theorem exists_tmW_of_ramInput (P : List EndStatement.Instr) (b : ℕ) :
    ∃ (N : TM2ComputableAux Bool Bool) (q : ℕ), (∀ k, Finite (N.tm.Γ k)) ∧
      ∀ (x : List Bool) (t : ℕ) (v : Bool),
        (∃ m : ℤ → BitVec (EthWordRam.Wof b x),
          EndStatement.exec P t 0 (EndStatement.loadWords (EthWordRam.Wof b x)
            (ramInput x)) = some (v, m)) →
        Nonempty (TM2OutputsInTime N.tm (x.map N.inputAlphabet.invFun)
          (some [N.outputAlphabet.invFun v]) (q * (t + x.length + 1) ^ q)) := by
  obtain ⟨N, q, hfin, h⟩ := exists_tmW_of_exec_unconditional P b
  exact ⟨N, q, hfin, fun x t v hex => h x t v (by rwa [wsOf_eq_ramInput])⟩

end RAMToTM.Transport

/-! ## The fragment, exhibited

`PolyT` hides the fragment under an existential, which keeps the three proofs above cheap but also
makes it easy to *assume* the instance rather than to see it. `PolyT.elim` (in
`ToTuring/PolyT.lean`) exposes it, and the three lemmas below are that one line applied. Each says:
there is one fragment `Q` of the stack machine and one monotone polynomial bound `t` (`PB t` is
`t n ≤ c * (n + 1) ^ c` for one `c`) such that `Q`, started on the word of the input on top of an
arbitrary stack context, produces the word of the component within `t (len input)` steps, and the
word produced is itself polynomially long. That is a cost, not a decision procedure. -/

namespace RAMToTM.Transport

open Groundwork

theorem initSt_fragment (P : List EndStatement.Instr) (b : ℕ) :
    ∃ (Q : TM.Fr) (t : ℕ → ℕ), PB t ∧ Monotone t ∧
      (∀ (x : List Bool) (M A B N : List TM.Sym),
        TM.Frag.Within Q (TM.st (wd x ++ M) A B N) (t (len x))
          (TM.st (wd (EthWordRam.initSt P b x) ++ M) A B N)) ∧
      ∀ x, len (EthWordRam.initSt P b x) ≤ t (len x) :=
  PolyT.elim (initSt_poly P b)

theorem stepSt_fragment (P : List EndStatement.Instr) :
    ∃ (Q : TM.Fr) (t : ℕ → ℕ), PB t ∧ Monotone t ∧
      (∀ (s : EthWordRam.St) (M A B N : List TM.Sym),
        TM.Frag.Within Q (TM.st (wd s ++ M) A B N) (t (len s))
          (TM.st (wd (EthWordRam.stepSt P s) ++ M) A B N)) ∧
      ∀ s, len (EthWordRam.stepSt P s) ≤ t (len s) :=
  PolyT.elim (stepSt_poly P)

theorem outSt_fragment (P : List EndStatement.Instr) :
    ∃ (Q : TM.Fr) (t : ℕ → ℕ), PB t ∧ Monotone t ∧
      (∀ (s : EthWordRam.St) (M A B N : List TM.Sym),
        TM.Frag.Within Q (TM.st (wd s ++ M) A B N) (t (len s))
          (TM.st (wd (EthWordRam.outSt P s) ++ M) A B N)) ∧
      ∀ s, len (EthWordRam.outSt P s) ≤ t (len s) :=
  PolyT.elim (outSt_poly P)

end RAMToTM.Transport

/-! ## Axiom audit -/

#print axioms RAMToTM.Transport.initEntry_poly
#print axioms RAMToTM.Transport.initTableBody_poly
#print axioms RAMToTM.Transport.initTable_poly
#print axioms RAMToTM.Transport.initT_poly
#print axioms RAMToTM.Transport.initSt_poly
#print axioms RAMToTM.Transport.stepSt_poly
#print axioms RAMToTM.Transport.outSt_poly
#print axioms RAMToTM.Transport.machine_component_check
#print axioms RAMToTM.Transport.isPolyT_machine
#print axioms RAMToTM.Transport.nonempty_isPolyT_machine
#print axioms RAMToTM.Transport.exists_tmW_of_exec_unconditional
#print axioms RAMToTM.Transport.wsOf_eq_ramInput
#print axioms RAMToTM.Transport.exists_tmW_of_ramInput
#print axioms RAMToTM.Transport.initSt_fragment
#print axioms RAMToTM.Transport.stepSt_fragment
#print axioms RAMToTM.Transport.outSt_fragment
