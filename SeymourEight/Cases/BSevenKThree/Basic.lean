import SeymourEight.CaseFramework
import SeymourEight.DegreeEight

/-!
# The `(|B|, k) = (7, 3)` case

Shared graph-level reductions for this local leaf will be developed here.
-/

namespace SeymourEight.BSevenKThree

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Members of `Q` reached from `A1 ∪ P`; its cardinality is the parameter
`y` in the computational `(7,3)` case split. -/
def reachedQ (C : G.LocalConfiguration) : Finset V :=
  C.Q ∩ G.outNeighborFinsetOf (C.A1 ∪ C.P)

/-- The number of reached vertices in `Q`. -/
def y (C : G.LocalConfiguration) : Nat :=
  (reachedQ G C).card

end SeymourEight.BSevenKThree
