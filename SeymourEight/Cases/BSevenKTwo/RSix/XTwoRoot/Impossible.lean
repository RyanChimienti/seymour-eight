import SeymourEight.Cases.BSevenKTwo.RSix.XTwoRoot.ReachedImpossible
import SeymourEight.Cases.BSevenKTwo.RSix.XTwoRoot.UnreachedImpossible

set_option linter.style.header false

namespace SeymourEight.BSevenKTwo.RSix.XTwoRoot

open Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The three rooted `r = 6`, `x = 2` parameter rows are impossible. -/
theorem impossible
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 2) (hr : C.r = 6)
    (hx : C.x = 2) (hRoot : epsilonS G C = 1)
    (hyz : (y G C = 0 ∧ C.z = 4) ∨
      (y G C = 1 ∧ (C.z = 2 ∨ C.z = 3))) : False := by
  rcases hyz with ⟨hy, hz⟩ | ⟨hy, hz | hz⟩
  · exact unreached_impossible G hBound C hG hMin hNoSeymour hRootDegree
      hPivot hBCard hk hr hx hRoot hy hz
  · exact reached_two_impossible G hBound C hG hMin hNoSeymour hRootDegree
      hPivot hBCard hk hr hx hRoot hy hz
  · exact reached_three_impossible G hBound C hG hMin hNoSeymour hRootDegree
      hPivot hBCard hk hr hx hRoot hy hz

end SeymourEight.BSevenKTwo.RSix.XTwoRoot
