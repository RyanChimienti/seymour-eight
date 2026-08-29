import SeymourEight.Cases.BSevenKOne.TightEpsilonOne.XOne

set_option linter.style.header false

/-!
# The tight epsilon-zero row `(x,z)=(1,6)`

This row shares the certificate-free `x=1` argument with the tight
epsilon-one row.  Both have six external second-neighbor targets.
-/

namespace SeymourEight.BSevenKOne.XOneAssembly

open SeymourEight.BSevenKOne SeymourEight.Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Complete tight `epsilon_s=0`, `(x,z)=(1,6)` row. -/
theorem impossible
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hEpsilon : epsilonS G C = 0)
    (hx : C.x = 1) (hz : C.z = 6) : False := by
  apply tightXOneExternalSixImpossible G hBound C hG hMin hNoSeymour
    hRootDegree hPivot hBCard hk hx
  omega

end SeymourEight.BSevenKOne.XOneAssembly
