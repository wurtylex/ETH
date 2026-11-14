/-
Word-RAM / Turing-machine bridge for `EndStatement` (Prove2Me APSP/3SUM artifact,
commit e1a4e6508154ea59f030480661590a9fe3018011), Apache 2.0, © Anthropic, PBC.
This file is new work of this investigation.

# What is here

`EndStatement.exec` runs a program on a memory `Int → BitVec W`: addresses are arbitrary
integers, so at first sight the machine has unlimited zero-initialised space and no
Turing machine with a poly(n)-long tape could simulate it.  The theorems below settle
what is actually true:

* every address ever used by `load`/`store` is the signed value of a `W`-bit word, so
  its absolute value is at most `2^(W-1)` (`toInt_natAbs_le`);
* a run therefore depends only on the cells of `progCells P` (the constants named by
  the program) and on the *window* `{a : ℤ | |a| ≤ 2^(W-1)}` (`exec_ext`).  Both are
  finite, and the window is a list of `2^(W+1) + 1` addresses (`windowList`), so within a
  run the memory never escapes a finite table of at most `2^(W+1) + 1 + 3 * P.length`
  cells;
* the initial memory `loadWords W ws` cannot see words beyond the window
  (`loadWords_agree_of_prefix`): only `2^W` cells are addressable at all, so the
  zero-initialised space is finite, not unlimited.
-/
import Mathlib
import EndStatement

namespace WordRAM

open EndStatement

/-! ## Addresses and cells -/

/-- The cell constants a single instruction names. -/
def cells : Instr → List Int
  | .one i => [i]
  | .add i j k => [i, j, k]
  | .sub i j k => [i, j, k]
  | .mul i j k => [i, j, k]
  | .load i j => [i, j]
  | .store i j => [i, j]
  | .bltz i _ => [i]
  | .accept => []
  | .reject => []

/-- All cell constants of a program. -/
def progCells (P : List Instr) : List Int := P.flatMap cells

theorem cells_length_le (I : Instr) : (cells I).length ≤ 3 := by
  cases I <;> simp [cells]

theorem progCells_length_le (P : List Instr) : (progCells P).length ≤ 3 * P.length := by
  induction P with
  | nil => simp [progCells]
  | cons I P ih =>
    have h1 : (progCells (I :: P)).length ≤ (cells I).length + (progCells P).length := by
      simp only [progCells, List.flatMap_cons, List.length_append]
      omega
    have h2 := cells_length_le I
    simp only [List.length_cons]
    omega

/-- The address window: the signed values of `W`-bit words. -/
def inWindow (W : Nat) (a : Int) : Prop := a.natAbs ≤ 2 ^ (W - 1)

/-- Every address that `load`/`store` can use is the signed value of a `W`-bit word, so it
lies in the window. -/
theorem toInt_natAbs_le (W : Nat) (x : BitVec W) : (x.toInt).natAbs ≤ 2 ^ (W - 1) := by
  have h1 : -((2 : Int) ^ (W - 1)) ≤ x.toInt := BitVec.le_toInt x
  have h2 : x.toInt ≤ (2 : Int) ^ (W - 1) - 1 := BitVec.toInt_le
  have hcast : ((2 : Int) ^ (W - 1)) = ((2 ^ (W - 1) : Nat) : Int) := by push_cast; ring
  rw [hcast] at h1 h2
  rcases le_total 0 x.toInt with h | h
  · have hnn : ((x.toInt).natAbs : Int) = x.toInt := Int.natAbs_of_nonneg h
    omega
  · have hnn : ((x.toInt).natAbs : Int) = -x.toInt := Int.ofNat_natAbs_of_nonpos h
    omega

theorem inWindow_le {W : Nat} {a : Int} (h : inWindow W a) :
    -((2 ^ (W - 1) : Nat) : Int) ≤ a ∧ a ≤ ((2 ^ (W - 1) : Nat) : Int) := by
  have h' : (a.natAbs : Int) ≤ ((2 ^ (W - 1) : Nat) : Int) := by exact_mod_cast h
  constructor
  · rcases le_total 0 a with h0 | h0
    · linarith
    · have := Int.ofNat_natAbs_of_nonpos h0
      linarith
  · calc a ≤ (a.natAbs : Int) := Int.le_natAbs
      _ ≤ _ := h'

/-- Two memories agree on the cells a run can touch. -/
def Agree (W : Nat) (P : List Instr) (m m' : Int → BitVec W) : Prop :=
  ∀ a, a ∈ progCells P ∨ inWindow W a → m a = m' a

theorem agree_of_eq (W : Nat) (P : List Instr) (m : Int → BitVec W) : Agree W P m m :=
  fun _ _ => rfl

/-- Agreement survives a write to a cell the program may name or reach, when the same value is
written in both memories. -/
theorem Agree.write {W : Nat} {P : List Instr} {m m' : Int → BitVec W} (h : Agree W P m m')
    {i : Int} (hi : i ∈ progCells P ∨ inWindow W i) {v : BitVec W} :
    Agree W P (fun x => if x = i then v else m x) (fun x => if x = i then v else m' x) := by
  intro a ha
  by_cases hia : a = i
  · simp [hia]
  · simp [hia, h a ha]

theorem Agree.write_of_eq {W : Nat} {P : List Instr} {m m' : Int → BitVec W} (h : Agree W P m m')
    {i : Int} (hi : i ∈ progCells P ∨ inWindow W i) {v v' : BitVec W} (hv : v = v') :
    Agree W P (fun x => if x = i then v else m x) (fun x => if x = i then v' else m' x) := by
  subst hv
  exact h.write hi

/-! ## Programs: cell constants are cells of the program -/

theorem mem_progCells_of_getD {P : List Instr} {pc : Nat} {a : Int}
    (h : a ∈ cells (P.getD pc .reject)) : a ∈ progCells P := by
  by_cases hlt : pc < P.length
  · have hget : P.getD pc .reject = P[pc] := List.getD_eq_getElem _ _ hlt
    rw [hget] at h
    exact List.mem_flatMap.mpr ⟨P[pc], List.getElem_mem hlt, h⟩
  · have hget : P.getD pc .reject = .reject := List.getD_eq_default _ _ (by omega)
    rw [hget] at h
    simp [cells] at h

/-! ## Extensionality of runs over the finite set of touchable cells -/

/-- The results of two runs started from agreeing memories: both halt with the same verdict and
again agreeing memories, or neither halts. -/
def SameResult (W : Nat) (P : List Instr) :
    Option (Bool × (Int → BitVec W)) → Option (Bool × (Int → BitVec W)) → Prop
  | none, none => True
  | some (b, m), some (b', m') => b = b' ∧ Agree W P m m'
  | _, _ => False

/-- **A run depends only on the program's cells and on the address window.** -/
theorem exec_ext {W : Nat} (P : List Instr) (t pc : Nat) {m m' : Int → BitVec W}
    (h : Agree W P m m') : SameResult W P (exec P t pc m) (exec P t pc m') := by
  induction t generalizing pc m m' with
  | zero => exact trivial
  | succ t ih =>
    cases hP : P.getD pc .reject with
    | one i =>
      simp only [exec, hP]
      have hi : i ∈ progCells P ∨ inWindow W i :=
        Or.inl (mem_progCells_of_getD (by rw [hP]; simp [cells]))
      exact ih _ (h.write hi)
    | add i j k =>
      simp only [exec, hP]
      have hi : i ∈ progCells P ∨ inWindow W i :=
        Or.inl (mem_progCells_of_getD (by rw [hP]; simp [cells]))
      have hj : j ∈ progCells P ∨ inWindow W j :=
        Or.inl (mem_progCells_of_getD (by rw [hP]; simp [cells]))
      have hk : k ∈ progCells P ∨ inWindow W k :=
        Or.inl (mem_progCells_of_getD (by rw [hP]; simp [cells]))
      have hv : m j + m k = m' j + m' k := by rw [h j hj, h k hk]
      exact ih _ (h.write_of_eq hi hv)
    | sub i j k =>
      simp only [exec, hP]
      have hi : i ∈ progCells P ∨ inWindow W i :=
        Or.inl (mem_progCells_of_getD (by rw [hP]; simp [cells]))
      have hj : j ∈ progCells P ∨ inWindow W j :=
        Or.inl (mem_progCells_of_getD (by rw [hP]; simp [cells]))
      have hk : k ∈ progCells P ∨ inWindow W k :=
        Or.inl (mem_progCells_of_getD (by rw [hP]; simp [cells]))
      have hv : m j - m k = m' j - m' k := by rw [h j hj, h k hk]
      exact ih _ (h.write_of_eq hi hv)
    | mul i j k =>
      simp only [exec, hP]
      have hi : i ∈ progCells P ∨ inWindow W i :=
        Or.inl (mem_progCells_of_getD (by rw [hP]; simp [cells]))
      have hj : j ∈ progCells P ∨ inWindow W j :=
        Or.inl (mem_progCells_of_getD (by rw [hP]; simp [cells]))
      have hk : k ∈ progCells P ∨ inWindow W k :=
        Or.inl (mem_progCells_of_getD (by rw [hP]; simp [cells]))
      have hv : m j * m k = m' j * m' k := by rw [h j hj, h k hk]
      exact ih _ (h.write_of_eq hi hv)
    | load i j =>
      simp only [exec, hP]
      have hi : i ∈ progCells P ∨ inWindow W i :=
        Or.inl (mem_progCells_of_getD (by rw [hP]; simp [cells]))
      have hj : j ∈ progCells P ∨ inWindow W j :=
        Or.inl (mem_progCells_of_getD (by rw [hP]; simp [cells]))
      have haddr : (m j).toInt = (m' j).toInt := by rw [h j hj]
      have hwin : inWindow W (m j).toInt := toInt_natAbs_le W (m j)
      have hread : m (m j).toInt = m' (m' j).toInt := by
        rw [← haddr]
        exact h _ (Or.inr hwin)
      exact ih _ (h.write_of_eq hi hread)
    | store i j =>
      simp only [exec, hP]
      have hi : i ∈ progCells P ∨ inWindow W i :=
        Or.inl (mem_progCells_of_getD (by rw [hP]; simp [cells]))
      have hj : j ∈ progCells P ∨ inWindow W j :=
        Or.inl (mem_progCells_of_getD (by rw [hP]; simp [cells]))
      have haddr : (m i).toInt = (m' i).toInt := by rw [h i hi]
      have hval : m j = m' j := h j hj
      rw [← haddr]
      exact ih _ (h.write_of_eq (Or.inr (toInt_natAbs_le W (m i))) hval)
    | bltz i l =>
      simp only [exec, hP]
      have hi : i ∈ progCells P ∨ inWindow W i :=
        Or.inl (mem_progCells_of_getD (by rw [hP]; simp [cells]))
      have hneg : (m i).toInt < 0 ↔ (m' i).toInt < 0 := by rw [h i hi]
      by_cases hc : (m i).toInt < 0
      · rw [if_pos hc, if_pos (hneg.mp hc)]
        exact ih _ h
      · rw [if_neg hc, if_neg (fun hk => hc (hneg.mpr hk))]
        exact ih _ h
    | accept =>
      simp only [exec, hP]
      exact ⟨rfl, h⟩
    | reject =>
      simp only [exec, hP]
      exact ⟨rfl, h⟩

/-- Verdict form: two runs from agreeing memories that both halt give the same verdict. -/
theorem exec_verdict_eq {W : Nat} (P : List Instr) (t : Nat) {m m' : Int → BitVec W}
    (h : Agree W P m m') {b b' : Bool} {f f' : Int → BitVec W}
    (h1 : exec P t 0 m = some (b, f)) (h2 : exec P t 0 m' = some (b', f')) : b = b' := by
  have hres := exec_ext P t 0 h
  rw [h1, h2] at hres
  exact hres.1

/-! ## The window is an explicit finite list -/

/-- The window addresses, written out (with slack: `2^(W+1) + 1` addresses cover it). -/
def windowList (W : Nat) : List Int :=
  List.ofFn (fun k : Fin (2 ^ (W + 1) + 1) => ((k : Nat) : Int) - ((2 ^ W : Nat) : Int))

theorem length_windowList (W : Nat) : (windowList W).length = 2 ^ (W + 1) + 1 := by
  simp [windowList]

theorem two_pow_pred_le (W : Nat) : 2 ^ (W - 1) ≤ 2 ^ W :=
  Nat.pow_le_pow_right (by norm_num) (by omega)

theorem mem_windowList {W : Nat} {a : Int} (h : inWindow W a) : a ∈ windowList W := by
  obtain ⟨h1, h2⟩ := inWindow_le h
  have hmono : ((2 ^ (W - 1) : Nat) : Int) ≤ ((2 ^ W : Nat) : Int) := by
    exact_mod_cast two_pow_pred_le W
  have hk0 : (0 : Int) ≤ a + ((2 ^ W : Nat) : Int) := by omega
  have hk2 : a + ((2 ^ W : Nat) : Int) ≤ ((2 ^ (W + 1) : Nat) : Int) := by
    have hsplit : ((2 ^ (W + 1) : Nat) : Int) = ((2 ^ W : Nat) : Int) + ((2 ^ W : Nat) : Int) := by
      rw [pow_succ]; push_cast; ring
    omega
  rw [windowList, List.mem_ofFn]
  refine ⟨⟨(a + ((2 ^ W : Nat) : Int)).toNat, ?_⟩, ?_⟩
  · have h3 : (((a + ((2 ^ W : Nat) : Int)).toNat : Nat) : Int) ≤ ((2 ^ (W + 1) : Nat) : Int) := by
      rw [Int.toNat_of_nonneg hk0]; exact hk2
    have h4 : (((2 ^ (W + 1) : Nat)) : Int) + 1 = (((2 ^ (W + 1) + 1 : Nat)) : Int) := by
      push_cast; ring
    omega
  · rw [Int.toNat_of_nonneg hk0]; ring

/-- Every cell a run can touch: the window together with the program's constants. -/
def touchCells (W : Nat) (P : List Instr) : List Int := windowList W ++ progCells P

theorem length_touchCells (W : Nat) (P : List Instr) :
    (touchCells W P).length ≤ 2 ^ (W + 1) + 1 + 3 * P.length := by
  simp only [touchCells, List.length_append]
  have := progCells_length_le P
  rw [length_windowList]
  omega

theorem agree_of_eq_on_touchCells {W : Nat} {P : List Instr} {m m' : Int → BitVec W}
    (h : ∀ a ∈ touchCells W P, m a = m' a) : Agree W P m m' := by
  intro a ha
  rcases ha with hP | hW
  · exact h a (List.mem_append_right _ hP)
  · exact h a (List.mem_append_left _ (mem_windowList hW))

/-! ## The initial memory cannot see past the window -/

theorem loadWords_apply (W : Nat) (ws : List Int) (a : Int) :
    loadWords W ws a = if a < 0 then 0 else BitVec.ofInt W (ws.getD a.toNat 0) := rfl

/-- Words past the end of the list read as zero. -/
theorem loadWords_getD_zero (W : Nat) (ws : List Int) {a : Int} (h : 0 ≤ a)
    (hlen : ws.length ≤ a.toNat) : loadWords W ws a = 0 := by
  rw [loadWords_apply]
  have : ¬ a < 0 := by omega
  rw [if_neg this, List.getD_eq_default _ _ hlen]
  simp

/-- **The window truncates the input**: only the first `2^(W-1)+1` words matter. -/
theorem loadWords_agree_of_prefix {W : Nat} {ws ws' : List Int}
    (h : ∀ i : Nat, i ≤ 2 ^ (W - 1) → ws.getD i 0 = ws'.getD i 0) :
    ∀ a, inWindow W a → loadWords W ws a = loadWords W ws' a := by
  intro a ha
  rw [loadWords_apply, loadWords_apply]
  by_cases hneg : a < 0
  · rw [if_pos hneg, if_pos hneg]
  · rw [if_neg hneg, if_neg hneg, h a.toNat ?_]
    have hle : a ≤ ((2 ^ (W - 1) : Nat) : Int) := (inWindow_le ha).2
    have hcast : ((a.toNat : Nat) : Int) = a := Int.toNat_of_nonneg (by omega)
    have : ((a.toNat : Nat) : Int) ≤ ((2 ^ (W - 1) : Nat) : Int) := by rw [hcast]; exact hle
    exact_mod_cast this

/-- A longer word list whose truncation agrees is indistinguishable: words beyond the window
can never be read. -/
theorem loadWords_agree_of_take {W : Nat} (ws ws' : List Int) (m : Nat)
    (hm : 2 ^ (W - 1) + 1 ≤ m) (htake : ws.take m = ws'.take m) :
    ∀ a, inWindow W a → loadWords W ws a = loadWords W ws' a := by
  refine loadWords_agree_of_prefix (fun i hi => ?_)
  have him : i < m := by omega
  have h1 : ws.getD i 0 = (ws.take m).getD i 0 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt him]
  have h2 : ws'.getD i 0 = (ws'.take m).getD i 0 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt him]
  rw [h1, h2, htake]

/-! ## The whole state is a finite table of words -/

/-- The memory restricted to the touchable cells, as a plain list of words. -/
def tableOf (W : Nat) (P : List Instr) (m : Int → BitVec W) : List (BitVec W) :=
  (touchCells W P).map m

theorem length_tableOf (W : Nat) (P : List Instr) (m : Int → BitVec W) :
    (tableOf W P m).length ≤ 2 ^ (W + 1) + 1 + 3 * P.length := by
  rw [tableOf, List.length_map]
  exact length_touchCells W P

theorem agree_of_table_eq {W : Nat} {P : List Instr} {m m' : Int → BitVec W}
    (h : tableOf W P m = tableOf W P m') : Agree W P m m' := by
  intro a ha
  have hmem : a ∈ touchCells W P := by
    rcases ha with hP | hW
    · exact List.mem_append_right _ hP
    · exact List.mem_append_left _ (mem_windowList hW)
  obtain ⟨i, hi, hia⟩ := List.getElem_of_mem hmem
  have hlen : i < ((touchCells W P).map m).length := by rw [List.length_map]; exact hi
  have hlen' : i < ((touchCells W P).map m').length := by rw [List.length_map]; exact hi
  have h1 : ((touchCells W P).map m).getD i 0 = m a := by
    rw [List.getD_eq_getElem _ _ hlen, List.getElem_map, hia]
  have h2 : ((touchCells W P).map m').getD i 0 = m' a := by
    rw [List.getD_eq_getElem _ _ hlen', List.getElem_map, hia]
  have hcongr := congrArg (fun l : List (BitVec W) => l.getD i 0) h
  simp only [tableOf] at hcongr
  rw [h1, h2] at hcongr
  exact hcongr

/-- **A run is a function of a finite table of at most `2^(W+1) + 1 + 3|P|` words**: two memories
with the same table on the touchable cells produce the same run.  This is the precise sense in
which `EndStatement`'s "unlimited" zero-initialised memory is a finite object at word size `W`. -/
theorem exec_congr_table {W : Nat} (P : List Instr) (t pc : Nat) {m m' : Int → BitVec W}
    (h : tableOf W P m = tableOf W P m') : SameResult W P (exec P t pc m) (exec P t pc m') :=
  exec_ext P t pc (agree_of_table_eq h)

/-- Verdict form of `exec_congr_table`. -/
theorem exec_verdict_congr_table {W : Nat} (P : List Instr) (t : Nat) {m m' : Int → BitVec W}
    (h : tableOf W P m = tableOf W P m') {b b' : Bool} {f f' : Int → BitVec W}
    (h1 : exec P t 0 m = some (b, f)) (h2 : exec P t 0 m' = some (b', f')) : b = b' :=
  exec_verdict_eq P t (agree_of_table_eq h) h1 h2

/-- **The machine cannot see the tail of its input.**  If two word lists agree on all positions a
run can read (the program's cell constants and the address window), the verdict is the same. -/
theorem verdict_of_same_readable_words {W : Nat} (P : List Instr) (t : Nat) {ws ws' : List Int}
    (h : ∀ a ∈ touchCells W P, loadWords W ws a = loadWords W ws' a) {b b' : Bool}
    {f f' : Int → BitVec W}
    (h1 : exec P t 0 (loadWords W ws) = some (b, f))
    (h2 : exec P t 0 (loadWords W ws') = some (b', f')) : b = b' :=
  exec_verdict_eq P t (agree_of_eq_on_touchCells h) h1 h2

/-! ### Where the window's addresses sit -/

theorem abs_le_of_mem_windowList {W : Nat} {a : Int} (h : a ∈ windowList W) :
    -(((2 ^ W : Nat)) : Int) ≤ a ∧ a ≤ (((2 ^ W : Nat)) : Int) := by
  rw [windowList, List.mem_ofFn] at h
  obtain ⟨i, rfl⟩ := h
  have hi : (i : Nat) ≤ 2 ^ (W + 1) := by
    have := i.isLt
    omega
  have hcast : (((i : Nat)) : Int) ≤ ((2 ^ (W + 1) : Nat) : Int) := by exact_mod_cast hi
  have hsplit : ((2 ^ (W + 1) : Nat) : Int) = ((2 ^ W : Nat) : Int) + ((2 ^ W : Nat) : Int) := by
    rw [pow_succ]; push_cast; ring
  have hnn : (0 : Int) ≤ ((i : Nat) : Int) := by exact_mod_cast Nat.zero_le i
  constructor <;> omega

theorem getD_take_eq {l : List Int} {i m : Nat} (h : i < m) :
    (l.take m).getD i 0 = l.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h]

/-- Concrete form: if the program's cell constants and the window all lie below `m`, and the two
input word lists agree on their first `m` words, then the verdict is the same. -/
theorem verdict_of_same_prefix {W : Nat} (P : List Instr) (t m : Nat) {ws ws' : List Int}
    (hprog : ∀ a ∈ progCells P, (0:Int) ≤ a ∧ a.toNat < m)
    (hm : 2 ^ W + 1 ≤ m) (htake : ws.take m = ws'.take m) {b b' : Bool}
    {f f' : Int → BitVec W}
    (h1 : exec P t 0 (loadWords W ws) = some (b, f))
    (h2 : exec P t 0 (loadWords W ws') = some (b', f')) : b = b' := by
  refine verdict_of_same_readable_words P t (fun a ha => ?_) h1 h2
  rcases List.mem_append.mp ha with hwin | hprog'
  · obtain ⟨hlo, hhi⟩ := abs_le_of_mem_windowList hwin
    rw [loadWords_apply, loadWords_apply]
    by_cases hneg : a < 0
    · rw [if_pos hneg, if_pos hneg]
    · rw [if_neg hneg, if_neg hneg]
      have hat : a.toNat ≤ 2 ^ W := by
        have hcast : ((a.toNat : Nat) : Int) = a := Int.toNat_of_nonneg (by omega)
        omega
      have hlt : a.toNat < m := by omega
      rw [← getD_take_eq (l := ws) hlt, ← getD_take_eq (l := ws') hlt, htake]
  · obtain ⟨hnn, hlt⟩ := hprog a hprog'
    rw [loadWords_apply, loadWords_apply, if_neg (by omega), if_neg (by omega)]
    rw [← getD_take_eq (l := ws) hlt, ← getD_take_eq (l := ws') hlt, htake]

/-! ## At the smallest admissible word size the table is polynomial in `n` -/

theorem two_pow_log2_le (n : Nat) (hn : 1 ≤ n) : 2 ^ n.log2 ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · have hn1 : n = 1 := by omega
      subst hn1
      simp [Nat.log2_def]
    · rw [Nat.log2_def, if_pos h]
      have hhalf : 1 ≤ n / 2 := by omega
      have hlt : n / 2 < n := by omega
      have hih := ih (n / 2) hlt hhalf
      rw [Nat.pow_succ]
      have hdiv : n / 2 * 2 ≤ n := Nat.div_mul_le_self n 2
      calc 2 ^ (n / 2).log2 * 2 ≤ n / 2 * 2 := Nat.mul_le_mul_right 2 hih
        _ ≤ n := hdiv

theorem two_pow_log2_le_succ (n : Nat) : 2 ^ n.log2 ≤ n + 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp [Nat.log2_def]
  · have := two_pow_log2_le n h
    omega

/-- **At the smallest word size allowed by `SolvedInTime` the reachable table is polynomial**:
with `W ≤ b (⌊log₂ n⌋ + 1)` the window has at most `2 * 2^b * (n+1)^b` addresses, so the whole
state of the word RAM is `poly(n)` words — *independently of its running time*.  (At larger `W`
the window is only larger; `Problem.SolvedInTime` must hold for all of them, which is why a
simulation may pick the smallest.) -/
theorem two_pow_window_le {b n W : Nat} (hW : W ≤ b * (Nat.log2 n + 1)) :
    2 ^ (W + 1) ≤ 2 * 2 ^ b * (n + 1) ^ b := by
  have h1 : 2 ^ (W + 1) = 2 * 2 ^ W := by rw [pow_succ]; ring
  have h2 : 2 ^ W ≤ 2 ^ (b * (Nat.log2 n + 1)) := Nat.pow_le_pow_right (by norm_num) hW
  have h3 : 2 ^ (b * (Nat.log2 n + 1)) = 2 ^ b * (2 ^ Nat.log2 n) ^ b := by
    rw [Nat.pow_mul, ← Nat.pow_right_comm, Nat.pow_succ]
    ring
  have h4 : (2 ^ Nat.log2 n) ^ b ≤ (n + 1) ^ b :=
    Nat.pow_le_pow_left (two_pow_log2_le_succ n) b
  have := Nat.mul_le_mul_left (2 * 2 ^ b) h4
  calc 2 ^ (W + 1) = 2 * 2 ^ W := h1
    _ ≤ 2 * 2 ^ (b * (Nat.log2 n + 1)) := Nat.mul_le_mul_left 2 h2
    _ = 2 * (2 ^ b * (2 ^ Nat.log2 n) ^ b) := by rw [h3]
    _ = 2 * 2 ^ b * (2 ^ Nat.log2 n) ^ b := by ring
    _ ≤ 2 * 2 ^ b * (n + 1) ^ b := this

/-! ## What `SolvedBy` can and cannot distinguish -/

/-- **Two instances with the same readable words get the same answer.**  Since `loadWords` puts
the `i`-th input word in cell `i+1` and only cells below `2^(W-1)` are addressable, a `SolvedBy`
program for `Q` forces `Q.yes` to be constant on instances that agree on the touchable cells.
This is the model restriction that the encoding of 3-SAT has to respect: its word list must fit
in the window, i.e. `b` must exceed the logarithm of the encoding length. -/
theorem solvedBy_yes_congr {Q : EndStatement.Problem} {n : Nat} {x x' : Q.Instance n}
    {P : List Instr} {W t : Nat} (h1 : Q.SolvedBy x P W t) (h2 : Q.SolvedBy x' P W t)
    (hsame : ∀ a ∈ touchCells W P,
      loadWords W ((n : Int) :: Q.input x) a = loadWords W ((n : Int) :: Q.input x') a) :
    Q.yes x ↔ Q.yes x' := by
  obtain ⟨v, m, hex, hv⟩ := h1
  obtain ⟨v', m', hex', hv'⟩ := h2
  have hvv : v = v' := verdict_of_same_readable_words P t hsame hex hex'
  rw [← hv.1, ← hv'.1, hvv]


/-! ## More time never hurts, and word size `0` is degenerate -/

theorem exec_mono {W : Nat} (P : List Instr) :
    ∀ (t pc : Nat) {m : Int → BitVec W} {r}, exec P t pc m = some r →
      ∀ k : Nat, exec P (t + k) pc m = some r
  | 0, pc, m, r, h => by simp [exec] at h
  | t + 1, pc, m, r, h => by
    intro k
    cases hP : P.getD pc .reject with
    | one i =>
      simp only [exec, hP] at h ⊢
      rw [show t + 1 + k = t + k + 1 by ring]
      simp only [exec, hP]
      exact exec_mono P t (pc + 1) h k
    | add i j k' =>
      simp only [exec, hP] at h ⊢
      rw [show t + 1 + k = t + k + 1 by ring]
      simp only [exec, hP]
      exact exec_mono P t (pc + 1) h k
    | sub i j k' =>
      simp only [exec, hP] at h ⊢
      rw [show t + 1 + k = t + k + 1 by ring]
      simp only [exec, hP]
      exact exec_mono P t (pc + 1) h k
    | mul i j k' =>
      simp only [exec, hP] at h ⊢
      rw [show t + 1 + k = t + k + 1 by ring]
      simp only [exec, hP]
      exact exec_mono P t (pc + 1) h k
    | load i j =>
      simp only [exec, hP] at h ⊢
      rw [show t + 1 + k = t + k + 1 by ring]
      simp only [exec, hP]
      exact exec_mono P t (pc + 1) h k
    | store i j =>
      simp only [exec, hP] at h ⊢
      rw [show t + 1 + k = t + k + 1 by ring]
      simp only [exec, hP]
      exact exec_mono P t (pc + 1) h k
    | bltz i l =>
      simp only [exec, hP] at h ⊢
      rw [show t + 1 + k = t + k + 1 by ring]
      simp only [exec, hP]
      exact exec_mono P t _ h k
    | accept =>
      simp only [exec, hP] at h ⊢
      rw [show t + 1 + k = t + k + 1 by ring]
      simp only [exec, hP]
      exact h
    | reject =>
      simp only [exec, hP] at h ⊢
      rw [show t + 1 + k = t + k + 1 by ring]
      simp only [exec, hP]
      exact h

/-- A run that halts within `t` steps halts within any larger number of steps, with the same
verdict and the same memory. -/
theorem exec_mono_le {W : Nat} (P : List Instr) {t : Nat} {pc : Nat} {m : Int → BitVec W} {r}
    (h : exec P t pc m = some r) {t' : Nat} (ht : t ≤ t') : exec P t' pc m = some r := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  exact exec_mono P t pc h k

/-- `Problem.SolvedBy` only gets weaker with more time. -/
theorem solvedBy_mono {Q : EndStatement.Problem} {n : Nat} {x : Q.Instance n} {P : List Instr}
    {W t t' : Nat} (h : Q.SolvedBy x P W t) (ht : t ≤ t') : Q.SolvedBy x P W t' := by
  obtain ⟨v, m, hex, hout⟩ := h
  exact ⟨v, m, exec_mono_le P hex ht, hout⟩

/-- **Word size `0` carries only one word**, so every initial memory is the same function and the
verdict cannot depend on the instance.  Hence `Problem.SolvedInTime` needs `b ≥ 1`, and more
generally the word size has to be large enough to tell the instances apart (compare
`solvedBy_yes_congr`). -/
theorem verdict_eq_of_zero_width {Q : EndStatement.Problem} {n : Nat} {x x' : Q.Instance n}
    {P : List Instr} {t : Nat} (h1 : Q.SolvedBy x P 0 t) (h2 : Q.SolvedBy x' P 0 t) :
    Q.yes x ↔ Q.yes x' := by
  obtain ⟨v, m, hex, hv⟩ := h1
  obtain ⟨v', m', hex', hv'⟩ := h2
  have hmem : loadWords 0 ((n : Int) :: Q.input x) = loadWords 0 ((n : Int) :: Q.input x') := by
    funext a
    exact Subsingleton.elim _ _
  rw [hmem] at hex
  rw [hex] at hex'
  simp only [Option.some.injEq, Prod.mk.injEq] at hex'
  rw [← hv.1, ← hv'.1, hex'.1]

end WordRAM

#print axioms WordRAM.exec_ext
#print axioms WordRAM.exec_congr_table
#print axioms WordRAM.verdict_of_same_prefix
#print axioms WordRAM.two_pow_window_le
#print axioms WordRAM.solvedBy_yes_congr
#print axioms WordRAM.exec_mono
#print axioms WordRAM.solvedBy_mono
#print axioms WordRAM.verdict_eq_of_zero_width
