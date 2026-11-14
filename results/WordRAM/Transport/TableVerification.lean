import RAMToTM.Table

namespace EthWordRam
open EndStatement

/-- A one-step terminal run on an empty finite program, specialized to the semantic table theorem. -/
example {t : List Nat} {r : Bool × (Int → BitVec 2)}
    (hr : Represents [] 2 (loadWords 2 []) t)
    (h : exec [] 1 0 (loadWords 2 []) = some r) :
    ∃ u : Nat, u < 1 ∧ verdict [] ((tableStep [] 2)^[u] (0, none, t)) = some r.1 ∧
      Represents [] 2 r.2 ((tableStep [] 2)^[u] (0, none, t)).2.2 :=
  exec_to_table (loadWords 2 []) t hr 1 0 r h

end EthWordRam
