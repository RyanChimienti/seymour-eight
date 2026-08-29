import SeymourEight.Cases.BSevenKOne.TightEpsilonOne.RootCoreGraphBridge
import SeymourEight.Cases.BSevenKOne.TightEpsilonOne.XOne
import SeymourEight.Cases.BSevenKOne.TightEpsilonOne.XTwoGraphBridge
import SeymourEight.Cases.BSevenKOne.TightEpsilonOne.XThreeReducedGraphBridge

/-!
# Tight `epsilon_s = 1` branch

Facade for the graph-facing development in the tight `epsilon_s = 1` family.
-/

namespace SeymourEight.BSevenKOne

open BSevenKOneCounting Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Complete tight `epsilon_s = 1`, `(x,z)=(4,2)` row. -/
theorem tightEpsilonOneXFourImpossible
    (_hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (_hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hEpsilon : epsilonS G C = 1)
    (hx : C.x = 4) (hz : C.z = 2) : False := by
  exact EpsilonOneRootCoreGraphBridge.tightEpsilonOneXFourImpossible
    G C hG hMin hNoSeymour hRootDegree hBCard hk hx hz hEpsilon

/-- Complete tight `epsilon_s = 1`, `(x,z)=(2,4)` row. -/
theorem tightEpsilonOneXTwoImpossible
    (_hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hEpsilon : epsilonS G C = 1)
    (hx : C.x = 2) (hz : C.z = 4) : False := by
  exact EpsilonOneXTwoGraphBridge.tightEpsilonOneXTwoImpossible
    G C hG hMin hNoSeymour hRootDegree hPivot hBCard hk hEpsilon hx hz

/-- Complete tight `epsilon_s = 1`, `(x,z)=(3,3)` row. -/
theorem tightEpsilonOneXThreeImpossible
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hEpsilon : epsilonS G C = 1) (hx : C.x = 3) (hz : C.z = 3) : False := by
  exact EpsilonOneXThreeReducedGraphBridge.tightEpsilonOneXThreeImpossible
    G hBound C hG hMin hNoSeymour hRootDegree hPivot hBCard hk hEpsilon hx hz

/-- All four tight `epsilon_s = 1` rows. -/
theorem tightEpsilonOneImpossible
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hEpsilon : epsilonS G C = 1)
    (hTight : C.x + C.z + epsilonS G C = 7) : False := by
  have hRows := parameterRows G C hG hMin hNoSeymour hRootDegree
    hPivot hBCard hk
  rcases hRows with h1 | h2 | h3 | h4
  · exact tightEpsilonOneXOneImpossible G hBound C hG hMin hNoSeymour
      hRootDegree hPivot hBCard hk hEpsilon h1.1 (by omega)
  · exact tightEpsilonOneXTwoImpossible G hBound C hG hMin hNoSeymour
      hRootDegree hPivot hBCard hk hEpsilon h2.1 (by omega)
  · exact tightEpsilonOneXThreeImpossible G hBound C hG hMin hNoSeymour
      hRootDegree hPivot hBCard hk hEpsilon h3.1 (by omega)
  · exact tightEpsilonOneXFourImpossible G hBound C hG hMin hNoSeymour
      hRootDegree hPivot hBCard hk hEpsilon h4.1 (by omega)

end SeymourEight.BSevenKOne
