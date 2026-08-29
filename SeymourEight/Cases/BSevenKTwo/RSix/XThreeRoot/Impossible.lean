import SeymourEight.Cases.BSevenKTwo.RSix.XThreeRoot.ReachedImpossible
import SeymourEight.Cases.BSevenKTwo.RSix.XThreeRoot.UnreachedImpossible

set_option linter.style.header false

namespace SeymourEight.BSevenKTwo.RSix.XThreeRoot

open Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The two rooted `r = 6`, `x = 3` parameter rows are impossible. -/
theorem impossible
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 2)
    (hr : C.r = 6) (hx : C.x = 3) (hRoot : epsilonS G C = 1)
    (hyz : (y G C = 0 ∧ C.z = 3) ∨ (y G C = 1 ∧ C.z = 2)) : False := by
  rcases hyz with ⟨hy, hz⟩ | ⟨hy, hz⟩
  · exact unreached_impossible G hBound C hG hMin hNoSeymour hRootDegree
      hPivot hBCard hk hr hx hRoot hy hz
  · exact reached_impossible G hBound C hG hMin hNoSeymour hRootDegree
      hPivot hBCard hk hr hx hRoot hy hz

end SeymourEight.BSevenKTwo.RSix.XThreeRoot
