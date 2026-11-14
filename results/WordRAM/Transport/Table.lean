/-
# Exact finite-table simulation of a Prove2Me word RAM

`initialTable_represents`, `tableInstr_correct` and `exec_to_table` are the main results.
This file contains mathematical execution semantics and is not, by itself, a running-time theorem.
Its finite-address lemmas are reused through `RAMToTM.FiniteAddresses`.
-/

import Mathlib
import EndStatement
import RAMToTM.FiniteAddresses

namespace EthWordRam
open EndStatement

/-- Integer cells named by instruction arguments, excluding jump destinations. -/
def cells : Instr → List Int
  | .one i => [i]
  | .add i j k | .sub i j k | .mul i j k => [i, j, k]
  | .load i j | .store i j => [i, j]
  | .bltz i _ => [i]
  | .accept | .reject => []

def progCells (P : List Instr) : List Int := P.flatMap cells

theorem in_progCells_of_mem {P : List Instr} {i : Instr} (hi : i ∈ P)
    {a : Int} (ha : a ∈ cells i) : a ∈ progCells P :=
  List.mem_flatMap.mpr ⟨i, hi, ha⟩

theorem in_progCells_of_getD {P : List Instr} {pc : Nat} {a : Int}
    (h : a ∈ cells (P.getD pc .reject)) : a ∈ progCells P := by
  by_cases hlt : pc < P.length
  · rw [List.getD_eq_getElem P .reject hlt] at h
    exact in_progCells_of_mem (List.getElem_mem hlt) h
  · rw [List.getD_eq_default P .reject (by omega)] at h
    simp [cells] at h

/-- A slightly enlarged window; unused endpoints make the indexing uniform, including `W=0`. -/
def inWindow (W : Nat) (a : Int) : Prop := a.natAbs ≤ 2 ^ (W - 1)

def windowSize (W : Nat) : Nat := 2 * 2 ^ (W - 1) + 1

def bias (W : Nat) : Int := (2 ^ (W - 1) : Nat)

def cell (P : List Instr) (W : Nat) (a : Int) : Nat :=
  if a.natAbs ≤ 2 ^ (W - 1) then (a + bias W).toNat else windowSize W + (progCells P).idxOf a

def covered (P : List Instr) (W : Nat) (a : Int) : Prop := inWindow W a ∨ a ∈ progCells P

abbrev Table := List Nat

def tableSize (P : List Instr) (W : Nat) : Nat := windowSize W + (progCells P).length

theorem toInt_inWindow (W : Nat) (x : BitVec W) : inWindow W x.toInt := by
  have h1 : -(2 : Int) ^ (W - 1) ≤ x.toInt := BitVec.le_toInt x
  have h2 : x.toInt ≤ (2 : Int) ^ (W - 1) - 1 := BitVec.toInt_le
  have hc : (-((2 : Int) ^ (W - 1))) = -((2 ^ (W - 1) : Nat) : Int) := by push_cast; rfl
  have hc' : ((2 : Int) ^ (W - 1)) = ((2 ^ (W - 1) : Nat) : Int) := by push_cast; rfl
  rw [hc] at h1
  rw [hc'] at h2
  rcases le_total 0 x.toInt with h | h
  · rw [inWindow]
    have he : (x.toInt.natAbs : Int) = x.toInt := Int.natAbs_of_nonneg h
    omega
  · rw [inWindow]
    have he : (x.toInt.natAbs : Int) = -x.toInt := Int.ofNat_natAbs_of_nonpos h
    omega

theorem bias_eq (W : Nat) : bias W = (2 : Int) ^ (W - 1) := by
  unfold bias
  push_cast
  rfl

theorem bounds {W : Nat} {a : Int} (h : inWindow W a) :
    -(bias W) ≤ a ∧ a ≤ bias W := by
  have hw : WordRAM.inWindow W a := h
  have hb := WordRAM.inWindow_le hw
  rw [bias_eq]
  exact hb

theorem cell_inWindow {P : List Instr} {W : Nat} {a : Int} (h : inWindow W a) :
    cell P W a = (a + bias W).toNat := by
  rw [cell, if_pos (show a.natAbs ≤ 2 ^ (W - 1) from h)]

theorem cell_not_window {P : List Instr} {W : Nat} {a : Int} (h : ¬ inWindow W a) :
    cell P W a = windowSize W + (progCells P).idxOf a := by
  rw [cell, if_neg (show ¬ a.natAbs ≤ 2 ^ (W - 1) from h)]

theorem cell_window_lt {P : List Instr} {W : Nat} {a : Int} (h : inWindow W a) :
    cell P W a < windowSize W := by
  rw [cell_inWindow h]
  have _hb := bounds h
  have hnn : 0 ≤ a + bias W := by omega
  have hlt : a + bias W < 1 + 2 * bias W := by omega
  apply (Int.toNat_lt hnn).mpr
  simp only [windowSize, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat]
  simp only [bias_eq]
  have hmod : a + bias W < (1 : Int) + 2 * ((2 ^ (W - 1) : Nat) : Int) := by
    exact_mod_cast hlt
  exact_mod_cast (by omega : a + bias W < ((2 * 2 ^ (W - 1) + 1 : Nat) : Int))

theorem cell_lt {P : List Instr} {W : Nat} {a : Int} (h : covered P W a) :
    cell P W a < tableSize P W := by
  by_cases hw : inWindow W a
  · exact Nat.lt_of_lt_of_le (cell_window_lt hw) (Nat.le_add_right _ _)
  · rw [cell_not_window hw]
    have hm : a ∈ progCells P := h.resolve_left hw
    have hi : (progCells P).idxOf a < (progCells P).length :=
      List.idxOf_lt_length_iff.mpr hm
    dsimp [tableSize]
    omega

theorem cell_inj {P : List Instr} {W : Nat} {a b : Int}
    (ha : covered P W a) (hb : covered P W b) (h : cell P W a = cell P W b) : a = b := by
  by_cases hwa : inWindow W a <;> by_cases hwb : inWindow W b
  · rw [cell_inWindow hwa, cell_inWindow hwb] at h
    have hna : 0 ≤ a + bias W := by have := bounds hwa; omega
    have hnb : 0 ≤ b + bias W := by have := bounds hwb; omega
    have hc := congrArg ((↑) : Nat → Int) h
    rw [Int.toNat_of_nonneg hna, Int.toNat_of_nonneg hnb] at hc
    omega
  · have hca := cell_window_lt (P := P) hwa
    rw [cell_not_window hwb] at h
    omega
  · have hcb := cell_window_lt (P := P) hwb
    rw [cell_not_window hwa] at h
    omega
  · rw [cell_not_window hwa, cell_not_window hwb] at h
    have hi : (progCells P).idxOf a = (progCells P).idxOf b := by omega
    exact (List.idxOf_inj (ha.resolve_left hwa)).mp hi

def Represents (P : List Instr) (W : Nat) (m : Int → BitVec W) (t : Table) : Prop :=
  t.length = tableSize P W ∧ ∀ a, covered P W a → t.getD (cell P W a) 0 = (m a).toNat

theorem Represents.update {P : List Instr} {W : Nat} {m : Int → BitVec W} {t : Table}
    {a : Int} (ha : covered P W a) (h : Represents P W m t) (v : BitVec W) :
    Represents P W (fun x => if x = a then v else m x) (t.set (cell P W a) v.toNat) := by
  refine ⟨by rw [List.length_set, h.1], ?_⟩
  intro b hb
  by_cases hab : cell P W a = cell P W b
  · have he : b = a := Eq.symm (cell_inj (P := P) (a := a) (b := b) ha hb hab)
    subst b
    simp only [List.getD_eq_getElem?_getD, List.getElem?_set, if_pos]
    rw [if_pos (by show cell P W a < t.length; rw [h.1]; exact cell_lt ha)]
    simp
  · have hne : b ≠ a := fun he => hab (congrArg (cell P W) he.symm)
    simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
    rw [if_neg hab]
    simp only [hne, if_false]
    exact h.2 b hb

/-- Read a whole word, reconstructing it from its table entry. -/
theorem ofNat_get {P : List Instr} {W : Nat} {m : Int → BitVec W} {t : Table}
    (h : Represents P W m t) {a : Int} (ha : covered P W a) :
    BitVec.ofNat W (t.getD (cell P W a) 0) = m a := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_ofNat, h.2 a ha, Nat.mod_eq_of_lt (m a).isLt]

/-- One step for a fixed program, and if present an already-produced verdict. -/
def tableInstr (P : List Instr) (W : Nat) (i : Instr) (pc : Nat)
    (out : Option Bool) (t : Table) : Nat × Option Bool × Table :=
  let get (a : Int) : Nat := t.getD (cell P W a) 0
  let signed (a : Int) : Int := (BitVec.ofNat W (get a)).toInt
  let write (a : Int) (v : Nat) : Nat × Option Bool × Table :=
    (pc + 1, out, t.set (cell P W a) (v % 2 ^ W))
  match i with
  | .one a => write a 1
  | .add a b c => write a (get b + get c)
  | .sub a b c => write a (2 ^ W - get c + get b)
  | .mul a b c => write a (get b * get c)
  | .load a b => write a (get (signed b))
  | .store a b => (pc + 1, out, t.set (cell P W (signed a)) (get b % 2 ^ W))
  | .bltz a l => (if signed a < 0 then l else pc + 1, out, t)
  | .accept => (pc, some true, t)
  | .reject => (pc, some false, t)

theorem literal_one_toNat (W : Nat) : 1 % 2 ^ W = (1 : BitVec W).toNat := by
  cases W with
  | zero => simp
  | succ W =>
    have hlt : 1 < 2 ^ (W + 1) := by
      have hp : 0 < 2 ^ W := by positivity
      rw [pow_succ]
      omega
    rw [Nat.mod_eq_of_lt hlt]
    simp

/-- Every instruction preserves the exact memory representation and has the intended branch. -/
theorem tableInstr_correct {P : List Instr} {W : Nat} {m : Int → BitVec W} {t : Table}
    (h : Represents P W m t) {pc : Nat} {i : Instr} (hi : P.getD pc .reject = i) :
    let next : Int → BitVec W := match i with
      | .one a => fun x => if x = a then (1 : BitVec W) else m x
      | .add a b c => fun x => if x = a then m b + m c else m x
      | .sub a b c => fun x => if x = a then m b - m c else m x
      | .mul a b c => fun x => if x = a then m b * m c else m x
      | .load a b => fun x => if x = a then m (m b).toInt else m x
      | .store a b => fun x => if x = (m a).toInt then m b else m x
      | _ => m
    Represents P W next (tableInstr P W i pc none t).2.2 := by
  cases i with
  | one a =>
    simp only [tableInstr]
    rw [literal_one_toNat]
    exact Represents.update (Or.inr (in_progCells_of_getD (a := a) (by rw [hi]; simp [cells]))) h 1
  | add a b c =>
    simp only [tableInstr]
    have hb : covered P W b := Or.inr (in_progCells_of_getD (a := b) (by rw [hi]; simp [cells]))
    have hc : covered P W c := Or.inr (in_progCells_of_getD (a := c) (by rw [hi]; simp [cells]))
    have hv : (t.getD (cell P W b) 0 + t.getD (cell P W c) 0) % 2 ^ W = (m b + m c).toNat := by
      rw [h.2 b hb, h.2 c hc, BitVec.toNat_add]
    rw [hv]
    exact Represents.update (Or.inr (in_progCells_of_getD (a := a) (by rw [hi]; simp [cells]))) h (m b + m c)
  | sub a b c =>
    simp only [tableInstr]
    have hb : covered P W b := Or.inr (in_progCells_of_getD (a := b) (by rw [hi]; simp [cells]))
    have hc : covered P W c := Or.inr (in_progCells_of_getD (a := c) (by rw [hi]; simp [cells]))
    have hv : (2 ^ W - t.getD (cell P W c) 0 + t.getD (cell P W b) 0) % 2 ^ W =
        (m b - m c).toNat := by
      rw [h.2 b hb, h.2 c hc, BitVec.toNat_sub]
    rw [hv]
    exact Represents.update (Or.inr (in_progCells_of_getD (a := a) (by rw [hi]; simp [cells]))) h (m b - m c)
  | mul a b c =>
    simp only [tableInstr]
    have hb : covered P W b := Or.inr (in_progCells_of_getD (a := b) (by rw [hi]; simp [cells]))
    have hc : covered P W c := Or.inr (in_progCells_of_getD (a := c) (by rw [hi]; simp [cells]))
    have hv : (t.getD (cell P W b) 0 * t.getD (cell P W c) 0) % 2 ^ W = (m b * m c).toNat := by
      rw [h.2 b hb, h.2 c hc, BitVec.toNat_mul]
    rw [hv]
    exact Represents.update (Or.inr (in_progCells_of_getD (a := a) (by rw [hi]; simp [cells]))) h (m b * m c)
  | load a b =>
    simp only [tableInstr]
    have hb : covered P W b := Or.inr (in_progCells_of_getD (a := b) (by rw [hi]; simp [cells]))
    have hs := ofNat_get h hb
    have hd : (BitVec.ofNat W (t.getD (cell P W b) 0)).toInt = (m b).toInt := by rw [hs]
    have hdyn : covered P W (m b).toInt := Or.inl (toInt_inWindow W (m b))
    have hv : t.getD (cell P W (m b).toInt) 0 % 2 ^ W = (m (m b).toInt).toNat := by
      rw [h.2 _ hdyn, Nat.mod_eq_of_lt (m (m b).toInt).isLt]
    rw [hd, hv]
    exact Represents.update (Or.inr (in_progCells_of_getD (a := a) (by rw [hi]; simp [cells]))) h (m (m b).toInt)
  | store a b =>
    simp only [tableInstr]
    have ha : covered P W a := Or.inr (in_progCells_of_getD (a := a) (by rw [hi]; simp [cells]))
    have hb : covered P W b := Or.inr (in_progCells_of_getD (a := b) (by rw [hi]; simp [cells]))
    have hs := ofNat_get h ha
    have hd : (BitVec.ofNat W (t.getD (cell P W a) 0)).toInt = (m a).toInt := by rw [hs]
    have hv : t.getD (cell P W b) 0 % 2 ^ W = (m b).toNat := by
      rw [h.2 b hb, Nat.mod_eq_of_lt (m b).isLt]
    rw [hd, hv]
    exact Represents.update (Or.inl (toInt_inWindow W (m a))) h (m b)
  | bltz => exact h
  | accept => exact h
  | reject => exact h

/-- Program counter, an optional verdict and the table, without the auxiliary variable count. -/
abbrev TableState := Nat × Option Bool × Table

/-- Execute the current instruction unless a verdict is already present. -/
def tableStep (P : List Instr) (W : Nat) : TableState → TableState
  | (pc, none, t) => tableInstr P W (P[pc]?.getD .reject) pc none t
  | s => s

/-- A verdict is read either from the stored flag or from the current terminal instruction.
This matches the observation point of the RAM, before its halting instruction is charged. -/
def verdict (P : List Instr) (s : TableState) : Option Bool :=
  match s.2.1 with
  | some b => some b
  | none => match P[s.1]?.getD .reject with
    | .accept => some true
    | .reject => some false
    | _ => none



/-- The tape-side execution corresponding to a RAM run of at most `fuel` steps. -/
theorem exec_to_table {P : List Instr} {W : Nat} (m : Int → BitVec W) (t : Table)
    (hrep : Represents P W m t) (fuel pc : Nat) :
    ∀ r : Bool × (Int → BitVec W), exec P fuel pc m = some r →
      ∃ u : Nat, u < fuel ∧
        verdict P ((tableStep P W)^[u] (pc, none, t)) = some r.1 ∧
        Represents P W r.2 ((tableStep P W)^[u] (pc, none, t)).2.2 := by
  induction fuel generalizing pc m t with
  | zero => intro r h; simp [exec] at h
  | succ fuel ih =>
    intro r hex
    generalize hg : P[pc]?.getD .reject = i
    cases i with
    | one a =>
      have hg0 : P.getD pc .reject = .one a := by
        simpa only [List.getD_eq_getElem?_getD] using hg
      simp only [exec, hg0] at hex
      have hn : Represents P W (fun x => if x = a then (1 : BitVec W) else m x)
          (tableInstr P W (.one a) pc none t).2.2 := tableInstr_correct hrep hg0
      obtain ⟨u, hu, ho, hr⟩ := ih _ _ hn (pc + 1) r hex
      have hs : tableStep P W (pc, none, t) = (pc + 1, none,
          (tableInstr P W (.one a) pc none t).2.2) := by
        rw [tableStep, hg, tableInstr]
      exact ⟨u + 1, by omega,
        by simpa only [Function.iterate_succ_apply, hs] using ho,
        by simpa only [Function.iterate_succ_apply, hs] using hr⟩
    | add a b c =>
      have hg0 : P.getD pc .reject = .add a b c := by
        simpa only [List.getD_eq_getElem?_getD] using hg
      simp only [exec, hg0] at hex
      have hn : Represents P W (fun x => if x = a then m b + m c else m x)
          (tableInstr P W (.add a b c) pc none t).2.2 := tableInstr_correct hrep hg0
      obtain ⟨u, hu, ho, hr⟩ := ih _ _ hn (pc + 1) r hex
      have hs : tableStep P W (pc, none, t) = (pc + 1, none,
          (tableInstr P W (.add a b c) pc none t).2.2) := by
        rw [tableStep, hg, tableInstr]
      exact ⟨u + 1, by omega,
        by simpa only [Function.iterate_succ_apply, hs] using ho,
        by simpa only [Function.iterate_succ_apply, hs] using hr⟩
    | sub a b c =>
      have hg0 : P.getD pc .reject = .sub a b c := by
        simpa only [List.getD_eq_getElem?_getD] using hg
      simp only [exec, hg0] at hex
      have hn : Represents P W (fun x => if x = a then m b - m c else m x)
          (tableInstr P W (.sub a b c) pc none t).2.2 := tableInstr_correct hrep hg0
      obtain ⟨u, hu, ho, hr⟩ := ih _ _ hn (pc + 1) r hex
      have hs : tableStep P W (pc, none, t) = (pc + 1, none,
          (tableInstr P W (.sub a b c) pc none t).2.2) := by
        rw [tableStep, hg, tableInstr]
      exact ⟨u + 1, by omega,
        by simpa only [Function.iterate_succ_apply, hs] using ho,
        by simpa only [Function.iterate_succ_apply, hs] using hr⟩
    | mul a b c =>
      have hg0 : P.getD pc .reject = .mul a b c := by
        simpa only [List.getD_eq_getElem?_getD] using hg
      simp only [exec, hg0] at hex
      have hn : Represents P W (fun x => if x = a then m b * m c else m x)
          (tableInstr P W (.mul a b c) pc none t).2.2 := tableInstr_correct hrep hg0
      obtain ⟨u, hu, ho, hr⟩ := ih _ _ hn (pc + 1) r hex
      have hs : tableStep P W (pc, none, t) = (pc + 1, none,
          (tableInstr P W (.mul a b c) pc none t).2.2) := by
        rw [tableStep, hg, tableInstr]
      exact ⟨u + 1, by omega,
        by simpa only [Function.iterate_succ_apply, hs] using ho,
        by simpa only [Function.iterate_succ_apply, hs] using hr⟩
    | load a b =>
      have hg0 : P.getD pc .reject = .load a b := by
        simpa only [List.getD_eq_getElem?_getD] using hg
      simp only [exec, hg0] at hex
      have hn : Represents P W (fun x => if x = a then m (m b).toInt else m x)
          (tableInstr P W (.load a b) pc none t).2.2 := tableInstr_correct hrep hg0
      obtain ⟨u, hu, ho, hr⟩ := ih _ _ hn (pc + 1) r hex
      have hs : tableStep P W (pc, none, t) = (pc + 1, none,
          (tableInstr P W (.load a b) pc none t).2.2) := by
        rw [tableStep, hg, tableInstr]
      exact ⟨u + 1, by omega,
        by simpa only [Function.iterate_succ_apply, hs] using ho,
        by simpa only [Function.iterate_succ_apply, hs] using hr⟩
    | store a b =>
      have hg0 : P.getD pc .reject = .store a b := by
        simpa only [List.getD_eq_getElem?_getD] using hg
      simp only [exec, hg0] at hex
      have hn : Represents P W (fun x => if x = (m a).toInt then m b else m x)
          (tableInstr P W (.store a b) pc none t).2.2 := tableInstr_correct hrep hg0
      obtain ⟨u, hu, ho, hr⟩ := ih _ _ hn (pc + 1) r hex
      have hs : tableStep P W (pc, none, t) = (pc + 1, none,
          (tableInstr P W (.store a b) pc none t).2.2) := by
        rw [tableStep, hg, tableInstr]
      exact ⟨u + 1, by omega,
        by simpa only [Function.iterate_succ_apply, hs] using ho,
        by simpa only [Function.iterate_succ_apply, hs] using hr⟩
    | bltz a l =>
      have hg0 : P.getD pc .reject = .bltz a l := by
        simpa only [List.getD_eq_getElem?_getD] using hg
      simp only [exec, hg0] at hex
      have ha : covered P W a := Or.inr (in_progCells_of_getD (a := a) (by rw [hg0]; simp [cells]))
      have hs := ofNat_get hrep ha
      have hd : (BitVec.ofNat W (t.getD (cell P W a) 0)).toInt = (m a).toInt := by rw [hs]
      by_cases hz : (m a).toInt < 0
      · simp only [if_pos hz] at hex
        obtain ⟨u, hu, ho, hr⟩ := ih _ t hrep l r hex
        have hs : tableStep P W (pc, none, t) =
            (if (m a).toInt < 0 then l else pc + 1, none, t) := by
          rw [tableStep, hg, tableInstr]
          change (if (BitVec.ofNat W (t.getD (cell P W a) 0)).toInt < 0 then l else pc + 1, none, t) = _
          rw [hd]
        exact ⟨u + 1, by omega,
          by simpa only [Function.iterate_succ_apply, hs, if_pos hz] using ho,
          by simpa only [Function.iterate_succ_apply, hs, if_pos hz] using hr⟩
      · simp only [if_neg hz] at hex
        obtain ⟨u, hu, ho, hr⟩ := ih _ t hrep (pc + 1) r hex
        have hs : tableStep P W (pc, none, t) =
            (if (m a).toInt < 0 then l else pc + 1, none, t) := by
          rw [tableStep, hg, tableInstr]
          change (if (BitVec.ofNat W (t.getD (cell P W a) 0)).toInt < 0 then l else pc + 1, none, t) = _
          rw [hd]
        exact ⟨u + 1, by omega,
          by simpa only [Function.iterate_succ_apply, hs, if_neg hz] using ho,
          by simpa only [Function.iterate_succ_apply, hs, if_neg hz] using hr⟩
    | accept =>
      have hg0 : P.getD pc .reject = .accept := by
        change P[pc]?.getD .reject = _
        exact hg
      simp only [exec, hg0, Option.some.injEq] at hex
      obtain rfl := hex
      refine ⟨0, by omega, ?_, hrep⟩
      simp [verdict, hg]
    | reject =>
      have hg0 : P.getD pc .reject = .reject := by
        change P[pc]?.getD .reject = _
        exact hg
      simp only [exec, hg0, Option.some.injEq] at hex
      obtain rfl := hex
      refine ⟨0, by omega, ?_, hrep⟩
      simp [verdict, hg]

/-- The value at one bounded table position. -/
def initialValue (P : List Instr) (W : Nat) (ws : List Int) (i : Nat) : Nat :=
  if i < windowSize W then (loadWords W ws ((i : Int) - bias W)).toNat
  else (loadWords W ws ((progCells P).getD (i - windowSize W) 0)).toNat

/-- The complete initial table as a function on its finite index set. -/
def initialTable (P : List Instr) (W : Nat) (ws : List Int) : Table :=
  List.ofFn fun i : Fin (tableSize P W) => initialValue P W ws i.1

@[simp] theorem initialTable_length (P : List Instr) (W : Nat) (ws : List Int) :
    (initialTable P W ws).length = tableSize P W := by
  simp [initialTable]

theorem initialTable_represents (P : List Instr) (W : Nat) (ws : List Int) :
    Represents P W (loadWords W ws) (initialTable P W ws) := by
  refine ⟨initialTable_length P W ws, ?_⟩
  intro a ha
  have hi := cell_lt ha
  unfold initialTable
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp only [List.getElem_ofFn]
  by_cases hw : inWindow W a
  · have hu := cell_window_lt (P := P) hw
    rw [cell_inWindow hw] at hu ⊢
    rw [initialValue, if_pos hu]
    congr 2
    have hb := bounds hw
    have hnn : 0 ≤ a + bias W := by omega
    have he := Int.toNat_of_nonneg hnn
    omega
  · have hm : a ∈ progCells P := ha.resolve_left hw
    have hidx : (progCells P).idxOf a < (progCells P).length := List.idxOf_lt_length_iff.mpr hm
    rw [cell_not_window hw]
    rw [initialValue, if_neg (by omega)]
    congr 2
    simp only [Nat.add_sub_cancel_left]
    rw [List.getD_eq_getElem _ _ hidx, List.getElem_idxOf hidx]

end EthWordRam
