/-
# State-size bounds for the finite-table simulation, and the polynomial-size host

This file isolates the *size* half of the Prove2Me RAM → FinTM2 transport.  It knows nothing about
the interpreter's stepping function: it works with `Groundwork.HasSize` / `Groundwork.size` (the
measure of `StepMachineStatements.lean`, the one the host `CountKSat.exists_tmW` uses) and with the
table invariants of `RAMToTM.Table`.

The things proved here:

* `size_list_nat_le`: a `List ℕ` all of whose entries are `< 2 ^ W` has
  `size ≤ (length + 1) * (W + 2)`, so the size of a table is polynomial in its length and in the
  word width and does not depend on the values beyond that.
* `initialTable_entries_lt`, `tableStep_entries_lt`: the invariant "every entry is a `W`-bit value"
  holds initially and survives the whole table iteration, so the bound above applies at every time.
* `exists_size_bound`: for a program `P`, a width `W ≤ b * (log₂ |x| + 1)`, a table of length at
  most `tableSize P W` whose entries are all `< 2 ^ W`, and `pc ≤ tableSize P W`, the state
  `(table, pc, n, verdict)` has `size ≤ c * (|x| + 1) ^ c` for a `c` depending on `P` and `b` only.
  This is the `S` that `Groundwork.Stepped.Runs` needs; it does not depend on the running time.
* `exists_tmW_run_of_polySize` and `exists_tm_run_of_polySize`: consequently the hosts
  `CountKSat.exists_tmW` and `Groundwork.exists_tm` apply *without* a size hypothesis on each run.
  A stepped machine that never leaves polynomial-size states runs in
  `q * (T + 1) * (|x| + 1) ^ q` steps, where `T` is the number of steps of the stepped computation.

What is deliberately *not* here: the stepping function itself, the recovery of `n` from the input
bits, the `PolyT` instances, and the correctness proof that the interpreter returns the RAM's
verdict.  Those belong to the interpreter direction; this file supplies only the size facts that
must be fed into `Groundwork.Stepped.Runs`.
-/

import Mathlib
import EndStatement
import RAMToTM.Table
import StepMachineStatements
import CountKSat.Host

namespace RAMToTM.SizeBounds

open Groundwork

/-! ## 1. `Groundwork.size` of a list of bounded naturals -/

theorem natSize_le_of_lt {x W : ℕ} (h : x < 2 ^ W) : Nat.size x ≤ W := Nat.size_le.mpr h

/-- `n < 2 ^ n`, so `Nat.size` never exceeds the number itself. -/
theorem lt_two_pow_self : ∀ n : ℕ, n < 2 ^ n
  | 0 => by norm_num
  | n + 1 => by
    have h : n < 2 ^ n := lt_two_pow_self n
    have h2 : 0 < 2 ^ n := Nat.pow_pos (by norm_num)
    rw [pow_succ]
    omega

theorem natSize_le_self (n : ℕ) : Nat.size n ≤ n := Nat.size_le.mpr (lt_two_pow_self n)

theorem sum_size_add_one_le (l : List ℕ) {W : ℕ} (h : ∀ x ∈ l, x < 2 ^ W) :
    (l.map (fun x => Nat.size x + 1)).sum ≤ l.length * (W + 1) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha : Nat.size a ≤ W := natSize_le_of_lt (h a List.mem_cons_self)
    have ht : (t.map (fun x => Nat.size x + 1)).sum ≤ t.length * (W + 1) :=
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hmul : (t.length + 1) * (W + 1) = t.length * (W + 1) + (W + 1) := by ring
    omega

theorem sum_map_size_eq (l : List ℕ) :
    (l.map (fun x => size x + 1)).sum = (l.map (fun x => Nat.size x + 1)).sum + l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [ih, size_nat]
    omega

/-- The size of a `List ℕ` whose entries are `< 2 ^ W`. -/
theorem size_list_nat_le (l : List ℕ) {W : ℕ} (h : ∀ x ∈ l, x < 2 ^ W) :
    size l ≤ (l.length + 1) * (W + 2) := by
  rw [size_list, sum_map_size_eq]
  have h1 := sum_size_add_one_le l h
  have h2 : l.length * (W + 1) + l.length = l.length * (W + 2) := by ring
  have h3 : l.length * (W + 2) + 1 ≤ (l.length + 1) * (W + 2) := by
    have hmul : (l.length + 1) * (W + 2) = l.length * (W + 2) + (W + 2) := by ring
    omega
  omega

/-- The same bound with the length estimated from above. -/
theorem size_list_nat_le_of_le (l : List ℕ) {W N : ℕ} (hlen : l.length ≤ N)
    (h : ∀ x ∈ l, x < 2 ^ W) : size l ≤ (N + 1) * (W + 2) := by
  have h1 := size_list_nat_le l h
  have h2 : (l.length + 1) * (W + 2) ≤ (N + 1) * (W + 2) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

theorem size_option_bool_le (v : Option Bool) : size v ≤ 2 := by
  cases v with
  | none => simp
  | some b => simp

/-! ## 2. The entry invariant of the finite table

`RAMToTM.Table` bounds the *length* of the table and the entries that `Represents` reads.  For the
size bound of the whole list we need the stronger invariant "every entry is a `W`-bit value", and
that it survives one instruction and hence the whole iteration. -/

theorem initialValue_lt (P : List EndStatement.Instr) (W : ℕ) (ws : List ℤ) (i : ℕ) :
    EthWordRam.initialValue P W ws i < 2 ^ W := by
  unfold EthWordRam.initialValue
  split <;> exact (EndStatement.loadWords W ws _).isLt

/-- Every entry of the initial table is a `W`-bit value. -/
theorem initialTable_entries_lt (P : List EndStatement.Instr) (W : ℕ) (ws : List ℤ) :
    ∀ z ∈ EthWordRam.initialTable P W ws, z < 2 ^ W := by
  intro z hz
  unfold EthWordRam.initialTable at hz
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hz
  rw [← hi]
  exact initialValue_lt P W ws i

/-- The entries `Represents` reads are `W`-bit values. -/
theorem Represents_getD_lt {P : List EndStatement.Instr} {W : ℕ} {m : ℤ → BitVec W}
    {t : EthWordRam.Table} (h : EthWordRam.Represents P W m t) {a : ℤ}
    (ha : EthWordRam.covered P W a) : t.getD (EthWordRam.cell P W a) 0 < 2 ^ W := by
  rw [h.2 a ha]
  exact (m a).isLt

theorem set_entries_lt (t : List ℕ) (i v W : ℕ) (h : ∀ z ∈ t, z < 2 ^ W) (hv : v < 2 ^ W) :
    ∀ z ∈ t.set i v, z < 2 ^ W := by
  intro z hz
  rw [List.set_eq_take_append_cons_drop] at hz
  split at hz
  · rcases List.mem_append.mp hz with h1 | h1
    · exact h z (List.mem_of_mem_take h1)
    · rcases List.mem_cons.mp h1 with rfl | h1
      · exact hv
      · exact h z (List.mem_of_mem_drop h1)
  · exact h z hz

/-- One instruction keeps every entry a `W`-bit value. -/
theorem tableInstr_entries_lt {P : List EndStatement.Instr} {W : ℕ} {t : EthWordRam.Table}
    (h : ∀ z ∈ t, z < 2 ^ W) (i : EndStatement.Instr) (pc : ℕ) (out : Option Bool) :
    ∀ z ∈ (EthWordRam.tableInstr P W i pc out t).2.2, z < 2 ^ W := by
  have hmod : ∀ v : ℕ, v % 2 ^ W < 2 ^ W := fun v => Nat.mod_lt _ (Nat.pow_pos (by norm_num))
  cases i with
  | one a => simpa only [EthWordRam.tableInstr] using set_entries_lt t _ _ _ h (hmod 1)
  | add a b c => simpa only [EthWordRam.tableInstr] using set_entries_lt t _ _ _ h (hmod _)
  | sub a b c => simpa only [EthWordRam.tableInstr] using set_entries_lt t _ _ _ h (hmod _)
  | mul a b c => simpa only [EthWordRam.tableInstr] using set_entries_lt t _ _ _ h (hmod _)
  | load a b => simpa only [EthWordRam.tableInstr] using set_entries_lt t _ _ _ h (hmod _)
  | store a b => simpa only [EthWordRam.tableInstr] using set_entries_lt t _ _ _ h (hmod _)
  | bltz a l => simpa only [EthWordRam.tableInstr] using h
  | accept => simpa only [EthWordRam.tableInstr] using h
  | reject => simpa only [EthWordRam.tableInstr] using h

/-- One step of the table iteration keeps every entry a `W`-bit value. -/
theorem tableStep_single_entries_lt {P : List EndStatement.Instr} {W : ℕ}
    {st : EthWordRam.TableState} (h : ∀ z ∈ st.2.2, z < 2 ^ W) :
    ∀ z ∈ (EthWordRam.tableStep P W st).2.2, z < 2 ^ W := by
  obtain ⟨pc, out, t⟩ := st
  cases out with
  | some b => simpa only [EthWordRam.tableStep] using h
  | none =>
    simpa only [EthWordRam.tableStep] using
      tableInstr_entries_lt (P := P) (W := W) h (P[pc]?.getD .reject) pc none

/-- Along the whole table iteration every entry stays a `W`-bit value. -/
theorem tableStep_entries_lt (P : List EndStatement.Instr) (W : ℕ) :
    ∀ (n : ℕ) (st : EthWordRam.TableState), (∀ z ∈ st.2.2, z < 2 ^ W) →
      ∀ z ∈ ((EthWordRam.tableStep P W)^[n] st).2.2, z < 2 ^ W
  | 0, st, h => h
  | n + 1, st, h => by
    rw [Function.iterate_succ_apply]
    exact tableStep_entries_lt P W n _
      (tableStep_single_entries_lt (P := P) (W := W) h)

/-! ### The program counter stays inside the program

The size bound of the whole state needs an upper bound for the program counter.  `pc ≤ P.length` is
enough, and it only needs the syntactic condition that the jump destinations of `P` are at most
`P.length` (a well-formed program of the Prove2Me compiler satisfies it by construction). -/

/-- Jump destinations named by an instruction. -/
def labels : EndStatement.Instr → List ℕ
  | .bltz _ l => [l]
  | _ => []

def progLabels (P : List EndStatement.Instr) : List ℕ := P.flatMap labels

theorem mem_progLabels_of_getD {P : List EndStatement.Instr} {pc l : ℕ}
    (h : l ∈ labels (P.getD pc .reject)) : l ∈ progLabels P := by
  by_cases hlt : pc < P.length
  · rw [List.getD_eq_getElem P .reject hlt] at h
    exact List.mem_flatMap.mpr ⟨P[pc], List.getElem_mem hlt, h⟩
  · rw [List.getD_eq_default P .reject (by omega)] at h
    simp [labels] at h

theorem eq_reject_of_getD {P : List EndStatement.Instr} {pc : ℕ} {i : EndStatement.Instr}
    (hi : P.getD pc .reject = i) (hne : i ≠ .reject) : pc < P.length := by
  by_contra hlt
  rw [List.getD_eq_default P .reject (by omega)] at hi
  exact hne hi.symm

/-- The largest jump destination of a program. -/
def maxLabel (P : List EndStatement.Instr) : ℕ := (progLabels P).foldr max 0

theorem le_foldr_max_self : ∀ (L : List ℕ) {x : ℕ}, x ∈ L → x ≤ L.foldr max 0
  | [], x, h => by simp at h
  | a :: t, x, h => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (le_foldr_max_self t h).trans (le_max_right _ _)

theorem le_maxLabel {P : List EndStatement.Instr} {l : ℕ} (h : l ∈ progLabels P) :
    l ≤ maxLabel P := le_foldr_max_self (progLabels P) h

/-- A bound that no program counter of `P` ever exceeds. -/
def pcBound (P : List EndStatement.Instr) : ℕ := max P.length (maxLabel P)

theorem le_pcBound_left (P : List EndStatement.Instr) : P.length ≤ pcBound P := le_max_left _ _

theorem le_pcBound_right (P : List EndStatement.Instr) : maxLabel P ≤ pcBound P := le_max_right _ _

theorem tableInstr_pc_le {P : List EndStatement.Instr} {W pc : ℕ} {i : EndStatement.Instr}
    (hi : P.getD pc .reject = i) (hpc : pc ≤ pcBound P) (out : Option Bool)
    (t : EthWordRam.Table) : (EthWordRam.tableInstr P W i pc out t).1 ≤ pcBound P := by
  have hpl : P.length ≤ pcBound P := le_pcBound_left P
  cases i with
  | one a =>
    have := eq_reject_of_getD hi (by simp : EndStatement.Instr.one a ≠ EndStatement.Instr.reject)
    simp only [EthWordRam.tableInstr]; omega
  | add a b c =>
    have := eq_reject_of_getD hi (by simp : EndStatement.Instr.add a b c ≠ EndStatement.Instr.reject)
    simp only [EthWordRam.tableInstr]; omega
  | sub a b c =>
    have := eq_reject_of_getD hi (by simp : EndStatement.Instr.sub a b c ≠ EndStatement.Instr.reject)
    simp only [EthWordRam.tableInstr]; omega
  | mul a b c =>
    have := eq_reject_of_getD hi (by simp : EndStatement.Instr.mul a b c ≠ EndStatement.Instr.reject)
    simp only [EthWordRam.tableInstr]; omega
  | load a b =>
    have := eq_reject_of_getD hi (by simp : EndStatement.Instr.load a b ≠ EndStatement.Instr.reject)
    simp only [EthWordRam.tableInstr]; omega
  | store a b =>
    have := eq_reject_of_getD hi (by simp : EndStatement.Instr.store a b ≠ EndStatement.Instr.reject)
    simp only [EthWordRam.tableInstr]; omega
  | bltz a l =>
    have hmem : l ∈ progLabels P :=
      mem_progLabels_of_getD (P := P) (pc := pc) (l := l) (by rw [hi]; simp [labels])
    have hl : l ≤ pcBound P := (le_maxLabel hmem).trans (le_pcBound_right P)
    have hpclt : pc < P.length :=
      eq_reject_of_getD hi (by simp : EndStatement.Instr.bltz a l ≠ EndStatement.Instr.reject)
    have hpcl : pc + 1 ≤ pcBound P := by
      have := le_pcBound_left P; omega
    simp only [EthWordRam.tableInstr]
    split <;> omega
  | accept => simpa only [EthWordRam.tableInstr] using hpc
  | reject => simpa only [EthWordRam.tableInstr] using hpc

theorem tableStep_pc_le (P : List EndStatement.Instr) (W : ℕ) :
    ∀ st : EthWordRam.TableState, st.1 ≤ pcBound P →
      (EthWordRam.tableStep P W st).1 ≤ pcBound P := by
  intro st hpc
  obtain ⟨pc, out, t⟩ := st
  cases out with
  | some b => simpa only [EthWordRam.tableStep] using hpc
  | none =>
    simpa only [EthWordRam.tableStep] using
      tableInstr_pc_le (P := P) (W := W) (pc := pc) (i := P[pc]?.getD .reject) rfl hpc none t

theorem tableStep_pc_le_along (P : List EndStatement.Instr) (W : ℕ) :
    ∀ (n : ℕ) (st : EthWordRam.TableState), st.1 ≤ pcBound P →
      ((EthWordRam.tableStep P W)^[n] st).1 ≤ pcBound P
  | 0, st, h => h
  | n + 1, st, h => by
    rw [Function.iterate_succ_apply]
    exact tableStep_pc_le_along P W n _ (tableStep_pc_le P W st h)

/-! ### The table keeps its length -/

theorem tableInstr_length {P : List EndStatement.Instr} {W : ℕ} (i : EndStatement.Instr)
    (pc : ℕ) (out : Option Bool) (t : EthWordRam.Table) :
    (EthWordRam.tableInstr P W i pc out t).2.2.length = t.length := by
  cases i <;> simp [EthWordRam.tableInstr]

theorem tableStep_length (P : List EndStatement.Instr) (W : ℕ) :
    ∀ (n : ℕ) (st : EthWordRam.TableState), ((EthWordRam.tableStep P W)^[n] st).2.2.length =
      st.2.2.length
  | 0, st => rfl
  | n + 1, st => by
    rw [Function.iterate_succ_apply, tableStep_length P W n]
    obtain ⟨pc, out, t⟩ := st
    cases out with
    | some b => rfl
    | none => simp [EthWordRam.tableStep, tableInstr_length]

/-- The size of an initial table, outright. -/
theorem size_initialTable (P : List EndStatement.Instr) (W : ℕ) (ws : List ℤ) :
    size (EthWordRam.initialTable P W ws) ≤ (EthWordRam.tableSize P W + 1) * (W + 2) := by
  have h := size_list_nat_le (l := EthWordRam.initialTable P W ws) (initialTable_entries_lt P W ws)
  simpa using h

/-- Every instruction's table keeps the length of the table, stuck, for the initial table. -/
theorem tableStep_initialTable_length (P : List EndStatement.Instr) (W : ℕ) (ws : List ℤ)
    (pc : ℕ) (out : Option Bool) (k : ℕ) :
    ((EthWordRam.tableStep P W)^[k] (pc, out, EthWordRam.initialTable P W ws)).2.2.length =
      EthWordRam.tableSize P W := by
  rw [tableStep_length P W k]
  simp

/-! ## 3. The word width and the table length, as polynomials in the input length -/

/-- The word width used by the interpreter on an input that recovers `n` variables. -/
def widthOf (b n : ℕ) : ℕ := b * (n.log2 + 1)

theorem two_pow_log2_le (n : ℕ) : 2 ^ n.log2 ≤ n + 1 := by
  have h := Nat.pow_log_le_add_one 2 n
  rwa [Nat.log2_eq_log_two]

theorem two_pow_widthOf_le (b m : ℕ) : 2 ^ widthOf b m ≤ (2 * (m + 1)) ^ b := by
  unfold widthOf
  rw [Nat.mul_comm b (m.log2 + 1), pow_mul]
  apply Nat.pow_le_pow_left
  rw [pow_succ]
  have := two_pow_log2_le m
  omega

theorem log2_mono_right {n m : ℕ} (h : n ≤ m) : n.log2 ≤ m.log2 := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  exact Nat.log_mono_right h

theorem widthOf_mono (b : ℕ) {n m : ℕ} (h : n ≤ m) : widthOf b n ≤ widthOf b m :=
  Nat.mul_le_mul_left _ (Nat.succ_le_succ (log2_mono_right h))

theorem tableSize_le (P : List EndStatement.Instr) (W : ℕ) :
    EthWordRam.tableSize P W ≤ 2 * 2 ^ W + 1 + (EthWordRam.progCells P).length := by
  have hw : 2 ^ (W - 1) ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le W 1)
  unfold EthWordRam.tableSize EthWordRam.windowSize
  omega

/-! ### Polynomial-bound (`PB`) bookkeeping -/

theorem pb_of_le {t s : ℕ → ℕ} (ht : PB t) (h : ∀ n, s n ≤ t n) : PB s := by
  obtain ⟨c, hc⟩ := ht
  exact ⟨c, fun n => (h n).trans (hc n)⟩

theorem pb_two_pow_widthOf (b : ℕ) : PB fun m => 2 ^ widthOf b m := by
  have hbase : PB fun m : ℕ => 2 * (m + 1) := (PB.const 2).mul (PB.id'.add (PB.const 1))
  exact pb_of_le (hbase.pow b) (fun m => two_pow_widthOf_le b m)

theorem pb_widthOf (b : ℕ) : PB fun m => widthOf b m := by
  have hbase : PB fun m : ℕ => b * (m + 1) := (PB.const b).mul (PB.id'.add (PB.const 1))
  refine pb_of_le hbase (fun m => ?_)
  unfold widthOf
  exact Nat.mul_le_mul_left _ (Nat.succ_le_succ (Nat.log2_le_self m))

/-- The whole size budget of a table state, as an explicit function of the input length. -/
def stateBudget (P : List EndStatement.Instr) (b m : ℕ) : ℕ :=
  (2 * 2 ^ widthOf b m + 1 + (EthWordRam.progCells P).length + 1) * (widthOf b m + 2) +
    (2 * 2 ^ widthOf b m + 1 + (EthWordRam.progCells P).length + 1 + P.length + maxLabel P) +
      (m + 1) + 2

theorem pb_stateBudget (P : List EndStatement.Instr) (b : ℕ) : PB (stateBudget P b) := by
  have h2W : PB fun m => 2 * 2 ^ widthOf b m := (PB.const 2).mul (pb_two_pow_widthOf b)
  have hT : PB fun m => 2 * 2 ^ widthOf b m + 1 + (EthWordRam.progCells P).length + 1 :=
    pb_of_le ((h2W.add (PB.const 1)).add (PB.const ((EthWordRam.progCells P).length + 1)))
      (fun m => by simp only [Nat.add_assoc]; omega)
  have hW2 : PB fun m => widthOf b m + 2 := (pb_widthOf b).add (PB.const 2)
  have h1 : PB fun m => (2 * 2 ^ widthOf b m + 1 + (EthWordRam.progCells P).length + 1) *
      (widthOf b m + 2) := hT.mul hW2
  have hT2 : PB fun m =>
      2 * 2 ^ widthOf b m + 1 + (EthWordRam.progCells P).length + 1 + P.length + maxLabel P :=
    pb_of_le (hT.add (PB.const (P.length + maxLabel P))) (fun m => by simp only [Nat.add_assoc]; omega)
  have h3 : PB fun m => m + 1 := PB.id'.add (PB.const 1)
  have h4 := ((h1.add hT2).add h3).add (PB.const 2)
  refine pb_of_le h4 (fun m => ?_)
  simp only [stateBudget, Nat.add_assoc]
  omega

/-- **The state-size bound.**  Fix a program `P` and the constant `b` of the width
`W = b * (log₂ n + 1)`.  There is a single constant `c` such that for every input bit string `x`,
every width `W ≤ b * (log₂ |x| + 1)`, and every table state whose table has length at most
`tableSize P W`, all of whose entries are `< 2 ^ W`, and whose program counter is at most
`tableSize P W`, the `Groundwork.size` of `(table, pc, n, verdict)` is at most
`c * (|x| + 1) ^ c`.

This is exactly the `S` of `Groundwork.Stepped.Runs`, and it is independent of the number of steps
the table iteration takes. -/
theorem exists_size_bound (P : List EndStatement.Instr) (b : ℕ) :
    ∃ c, ∀ (x : List Bool) (n W : ℕ) (t : List ℕ) (pc : ℕ) (v : Option Bool),
      n ≤ x.length → W ≤ widthOf b x.length →
      t.length ≤ EthWordRam.tableSize P W →
      (∀ z ∈ t, z < 2 ^ W) →
      pc ≤ pcBound P + EthWordRam.tableSize P W →
      size (t, pc, n, v) ≤ c * (x.length + 1) ^ c := by
  obtain ⟨c, hc⟩ := pb_stateBudget P b
  refine ⟨c, fun x n W t pc v _ hW ht hlt hp => ?_⟩
  set m := x.length with hm
  have h2W : 2 ^ W ≤ 2 ^ widthOf b m := Nat.pow_le_pow_right (by norm_num) hW
  have hWle : W + 2 ≤ widthOf b m + 2 := by omega
  have hTle : EthWordRam.tableSize P W + 1 ≤
      2 * 2 ^ widthOf b m + 1 + (EthWordRam.progCells P).length + 1 := by
    have := tableSize_le P W
    omega
  have ht' : ∀ z ∈ t, z < 2 ^ widthOf b m := fun z hz => (hlt z hz).trans_le h2W
  have h1 : size t ≤ (2 * 2 ^ widthOf b m + 1 + (EthWordRam.progCells P).length + 1) *
      (widthOf b m + 2) :=
    (size_list_nat_le_of_le t ht ht').trans (Nat.mul_le_mul_right _ hTle)
  have h2 : size pc ≤
      2 * 2 ^ widthOf b m + 1 + (EthWordRam.progCells P).length + 1 + P.length + maxLabel P := by
    rw [size_nat]
    have hsz := natSize_le_self pc
    have := tableSize_le P W
    have h1 := le_pcBound_left P
    have h2 := le_pcBound_right P
    have h3 : pcBound P = max P.length (maxLabel P) := rfl
    omega
  have h3 : size n ≤ m + 1 := by
    rw [size_nat]
    have := natSize_le_self n
    omega
  have h4 : size v ≤ 2 := size_option_bool_le v
  have hsum : size t + (size pc + (size n + size v)) ≤ stateBudget P b m := by
    simp only [stateBudget]
    generalize 2 * 2 ^ widthOf b m + 1 + (EthWordRam.progCells P).length + 1 = A at *
    generalize widthOf b m + 2 = B at *
    omega
  have hunfold : size (t, pc, n, v) = size t + (size pc + (size n + size v)) := rfl
  rw [hunfold]
  exact hsum.trans (hc m)

/-- The same bound for the width actually used on an input with `n` recovered variables. -/
theorem exists_size_bound_widthOf (P : List EndStatement.Instr) (b : ℕ) :
    ∃ c, ∀ (x : List Bool) (n : ℕ) (t : List ℕ) (pc : ℕ) (v : Option Bool),
      n ≤ x.length →
      t.length ≤ EthWordRam.tableSize P (widthOf b n) →
      (∀ z ∈ t, z < 2 ^ widthOf b n) →
      pc ≤ pcBound P + EthWordRam.tableSize P (widthOf b n) →
      size (t, pc, n, v) ≤ c * (x.length + 1) ^ c := by
  obtain ⟨c, hc⟩ := exists_size_bound P b
  exact ⟨c, fun x n t pc v hn => hc x n (widthOf b n) t pc v hn (widthOf_mono b hn)⟩

/-- **The size bound along the actual table iteration.**  This is the form the interpreter direction
needs for `Groundwork.Stepped.Runs`: for a program whose jump destinations stay inside `P`, start
the table iteration at the initial table of `loadWords W ws` and program counter `pc ≤ P.length`;
then at *every* time `k` the mathematical state `(table, pc, n, verdict)` has
`Groundwork.size ≤ c * (|x| + 1) ^ c`, with one `c` for the whole run.  Nothing here depends on
`k`: the bound holds for all times, halting or not. -/
theorem exists_tableStep_size_bound (P : List EndStatement.Instr) (b : ℕ) :
    ∃ c, ∀ (x : List Bool) (n W : ℕ) (ws : List ℤ) (pc : ℕ) (v : Option Bool) (k : ℕ),
      n ≤ x.length → W ≤ widthOf b x.length → pc ≤ pcBound P →
      size (((EthWordRam.tableStep P W)^[k]
            (pc, none, EthWordRam.initialTable P W ws)).2.2,
          ((EthWordRam.tableStep P W)^[k] (pc, none, EthWordRam.initialTable P W ws)).1, n, v)
          ≤ c * (x.length + 1) ^ c := by
  obtain ⟨c, hc⟩ := exists_size_bound P b
  refine ⟨c, fun x n W ws pc v k hn hW hpc => ?_⟩
  set st : EthWordRam.TableState := (pc, none, EthWordRam.initialTable P W ws) with hst
  have hlen : ((EthWordRam.tableStep P W)^[k] st).2.2.length ≤ EthWordRam.tableSize P W := by
    rw [tableStep_length P W k, hst, EthWordRam.initialTable_length]
  have hentry : ∀ z ∈ ((EthWordRam.tableStep P W)^[k] st).2.2, z < 2 ^ W :=
    tableStep_entries_lt P W k st (initialTable_entries_lt P W ws)
  have hpc' : ((EthWordRam.tableStep P W)^[k] st).1 ≤ pcBound P :=
    tableStep_pc_le_along P W k st (by rw [hst]; exact hpc)
  exact hc x n W _ _ v hn hW hlen hentry (by omega)

/-- The number of variables recovered from a raw-bit input: the leading `true` bits. -/
def recoveredVars (x : List Bool) : ℕ := (x.takeWhile id).length

theorem recoveredVars_le (x : List Bool) : recoveredVars x ≤ x.length :=
  List.Sublist.length_le (List.takeWhile_sublist _)

/-- **The turn-key form.**  `P`, `b` fixed, `n` recovered from the raw bits `x`, the width
`W = b * (log₂ n + 1)` and the table `initialTable P W ws` of the loaded words; the program counter
starts at `0`.  Then every state the table iteration visits has size at most `c * (|x| + 1) ^ c`,
with `c` depending on `P` and `b` only and no hypothesis left. -/
theorem exists_tableStep_size_bound_ram (P : List EndStatement.Instr) (b : ℕ) :
    ∃ c, ∀ (x : List Bool) (ws : List ℤ) (v : Option Bool) (k : ℕ),
      size (((EthWordRam.tableStep P (widthOf b (recoveredVars x)))^[k]
            (0, none, EthWordRam.initialTable P (widthOf b (recoveredVars x)) ws)).2.2,
          ((EthWordRam.tableStep P (widthOf b (recoveredVars x)))^[k]
            (0, none, EthWordRam.initialTable P (widthOf b (recoveredVars x)) ws)).1,
          recoveredVars x, v) ≤ c * (x.length + 1) ^ c := by
  obtain ⟨c, hc⟩ := exists_tableStep_size_bound P b
  exact ⟨c, fun x ws v k => hc x (recoveredVars x) (widthOf b (recoveredVars x)) ws 0 v k
    (recoveredVars_le x) (widthOf_mono b (recoveredVars_le x)) (Nat.zero_le _)⟩

/-! ## 4. The polynomial-size host: no size hypothesis per run -/

def evalsToInTime_mono {σ : Type} {f : σ → Option σ} {a : σ} {b : Option σ} {m m' : ℕ}
    (h : StateTransition.EvalsToInTime f a b m) (hm : m ≤ m') :
    StateTransition.EvalsToInTime f a b m' :=
  ⟨h.toEvalsTo, h.steps_le_m.trans hm⟩

def tm2OutputsInTime_mono {tm : Turing.FinTM2} {l : List (tm.Γ tm.k₀)}
    {l' : Option (List (tm.Γ tm.k₁))} {m m' : ℕ}
    (h : Turing.TM2OutputsInTime tm l l' m) (hm : m ≤ m') : Turing.TM2OutputsInTime tm l l' m' :=
  evalsToInTime_mono h hm

/-- A halted state is fixed by the iteration. -/
theorem next_iterate_of_out {α β : Type} {M : Stepped α β} {s : M.σ} {b : β}
    (h : M.out s = some b) (n : ℕ) : M.next^[n] s = s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, Stepped.next, h]

theorem run_eq_of_out {α β : Type} {M : Stepped α β} {x : α} {T n : ℕ} {w : β}
    (ho : M.out (M.run x T) = some w) (hn : T ≤ n) : M.run x n = M.run x T := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm T k, Stepped.run, Function.iterate_add_apply, Stepped.run]
  exact next_iterate_of_out ho k

/-- The bound `c * (m + 1) ^ c` can be absorbed into a single monomial `(m + 2) ^ d`. -/
theorem mul_pow_absorb {c d m : ℕ} : c * (m + 1) ^ d ≤ (m + 2) ^ (c + d) := by
  have hle : (m + 1) ^ d ≤ (m + 2) ^ d := Nat.pow_le_pow_left (by omega) d
  have hc' : c ≤ (m + 2) ^ c :=
    (Nat.le_of_lt (lt_two_pow_self c)).trans (Nat.pow_le_pow_left (by omega) c)
  calc c * (m + 1) ^ d ≤ (m + 2) ^ c * (m + 2) ^ d := Nat.mul_le_mul hc' hle
    _ = (m + 2) ^ (c + d) := by rw [← pow_add]

/-- **The host with a word as output, without a size hypothesis on the run.**  If the stepped
computation `M` has polynomial-time `init`/`step`/`out` and never leaves states of size
`c * (|x| + 1) ^ c` (for one `c` and all runs of length at most `T`), then there is a multi-stack
machine with finite alphabets that on `x` outputs the result word `w` in
`q * (T + 1) * (|x| + 1) ^ q` steps, where `T` is the number of steps of `M` on `x`. -/
theorem exists_tmW_run_of_polySize (M : Stepped (List Bool) (List Bool)) [IsPolyT M]
    (hS : ∃ c, ∀ (x : List Bool) (T : ℕ) (w : List Bool), M.out (M.run x T) = some w →
      ∀ n, n ≤ T → size (M.run x n) ≤ c * (x.length + 1) ^ c) :
    ∃ (N : Turing.TM2ComputableAux Bool Bool) (q : ℕ), (∀ k, Finite (N.tm.Γ k)) ∧
      ∀ (x : List Bool) (T : ℕ) (w : List Bool), M.out (M.run x T) = some w →
        Nonempty (Turing.TM2OutputsInTime N.tm (x.map N.inputAlphabet.invFun)
          (some (w.map N.outputAlphabet.invFun)) (q * (T + 1) * (x.length + 1) ^ q)) := by
  obtain ⟨N, q', hfin, hrun⟩ := CountKSat.exists_tmW M
  obtain ⟨c, hc⟩ := hS
  set C : ℕ := max c 1 with hC
  have hcC : c ≤ C := le_max_left c 1
  have h1C : 1 ≤ C := le_max_right c 1
  refine ⟨N, q' * (C + 1) ^ q' + C * q' + 1, hfin, fun x T w ho => ?_⟩
  have hstep : ∀ n, size (M.run x n) ≤ C * (x.length + 1) ^ C := by
    intro n
    by_cases hn : n ≤ T
    · exact (hc x T w ho n hn).trans
        (Nat.mul_le_mul hcC (Nat.pow_le_pow_right (Nat.succ_pos x.length) hcC))
    · rw [run_eq_of_out ho (by omega)]
      exact (hc x T w ho T le_rfl).trans
        (Nat.mul_le_mul hcC (Nat.pow_le_pow_right (Nat.succ_pos x.length) hcC))
  have hruns : M.Runs x T (C * (x.length + 1) ^ C) w := Stepped.runs_of_run ho hstep
  obtain ⟨hout⟩ := hrun x T _ w hruns
  refine ⟨tm2OutputsInTime_mono hout ?_⟩
  set m := x.length with hm
  have hsize : m + C * (m + 1) ^ C + 1 ≤ (C + 1) * (m + 1) ^ C := by
    have hpow : m + 1 ≤ (m + 1) ^ C := by
      have h1 : (m + 1) ^ 1 ≤ (m + 1) ^ C := Nat.pow_le_pow_right (Nat.succ_pos m) h1C
      simpa using h1
    have he : m + C * (m + 1) ^ C + 1 = (m + 1) + C * (m + 1) ^ C := by ring
    rw [he]
    calc (m + 1) + C * (m + 1) ^ C ≤ (m + 1) ^ C + C * (m + 1) ^ C :=
          Nat.add_le_add_right hpow _
      _ = (C + 1) * (m + 1) ^ C := by ring
  have hpow : (m + C * (m + 1) ^ C + 1) ^ q' ≤
      (C + 1) ^ q' * (m + 1) ^ (C * q') := by
    calc (m + C * (m + 1) ^ C + 1) ^ q' ≤ ((C + 1) * (m + 1) ^ C) ^ q' :=
          Nat.pow_le_pow_left hsize q'
      _ = (C + 1) ^ q' * (m + 1) ^ (C * q') := by
          rw [Nat.mul_pow, pow_mul]
  have hQ1 : q' * (C + 1) ^ q' ≤ q' * (C + 1) ^ q' + C * q' + 1 := by omega
  have hQ2 : C * q' ≤ q' * (C + 1) ^ q' + C * q' + 1 := by omega
  calc q' * (T + 1) * (m + C * (m + 1) ^ C + 1) ^ q'
      ≤ q' * (T + 1) * ((C + 1) ^ q' * (m + 1) ^ (C * q')) := Nat.mul_le_mul_left _ hpow
    _ = (q' * (C + 1) ^ q') * (T + 1) * (m + 1) ^ (C * q') := by ring
    _ ≤ (q' * (C + 1) ^ q' + C * q' + 1) * (T + 1) *
          (m + 1) ^ (q' * (C + 1) ^ q' + C * q' + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul hQ1 le_rfl)
          (Nat.pow_le_pow_right (Nat.succ_pos m) hQ2)

/-- **The host with a single bit as output, without a size hypothesis on the run.**  This is
`Groundwork.exists_tm` with the bound `S ≤ (|x| + 2) ^ d` discharged from a polynomial state-size
bound `c * (|x| + 1) ^ c`. -/
theorem exists_tm_run_of_polySize (M : Stepped (List Bool) Bool) [IsPolyT M]
    (hS : ∃ c, ∀ (x : List Bool) (T : ℕ) (b : Bool), M.out (M.run x T) = some b →
      ∀ n, n ≤ T → size (M.run x n) ≤ c * (x.length + 1) ^ c) :
    ∃ (N : Turing.TM2ComputableAux Bool Bool) (q : ℕ), (∀ k, Finite (N.tm.Γ k)) ∧
      ∀ (x : List Bool) (T : ℕ) (b : Bool), M.out (M.run x T) = some b →
        Nonempty (Turing.TM2OutputsInTime N.tm (x.map N.inputAlphabet.invFun)
          (some ([b].map N.outputAlphabet.invFun)) (q * (T + 1) * (x.length + 1) ^ q)) := by
  obtain ⟨c, hc⟩ := hS
  set C : ℕ := max c 1 with hC
  have hcC : c ≤ C := le_max_left c 1
  have h1C : 1 ≤ C := le_max_right c 1
  obtain ⟨N, q, hfin, hrun⟩ := Groundwork.exists_tm M (C + C)
  refine ⟨N, q, hfin, fun x T b ho => ?_⟩
  have hstep : ∀ n, size (M.run x n) ≤ C * (x.length + 1) ^ C := by
    intro n
    by_cases hn : n ≤ T
    · exact (hc x T b ho n hn).trans
        (Nat.mul_le_mul hcC (Nat.pow_le_pow_right (Nat.succ_pos x.length) hcC))
    · rw [run_eq_of_out ho (by omega)]
      exact (hc x T b ho T le_rfl).trans
        (Nat.mul_le_mul hcC (Nat.pow_le_pow_right (Nat.succ_pos x.length) hcC))
  have hsize : C * (x.length + 1) ^ C ≤ (x.length + 2) ^ (C + C) := mul_pow_absorb
  exact hrun x T _ b (Stepped.runs_of_run ho hstep) hsize

end RAMToTM.SizeBounds
