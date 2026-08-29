import SeymourEight.Cases.BSevenKOne.TightEpsilonOne
import SeymourEight.Cases.BSevenKOne.Slack
import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XOne
import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XTwo
import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XThree
import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XFour.Assembly

set_option linter.style.header false

/-!
# The `(|B|, k) = (7, 1)` case

The six obligations are the one-unit-slack family, the tight `epsilon_s = 1`
family, and the four tight `epsilon_s = 0` rows.  The results below assemble
their proofs into the final `(7,1)` theorem.
-/

namespace SeymourEight.BSevenKOne

open BSevenKOneCounting Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- All six rows with one unit of slack in the basic
`x + z + epsilon_s ≤ 7` inequality are impossible. -/
theorem slackRowsImpossible
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hSlack : C.x + C.z + epsilonS G C = 6) : False := by
  exact BSevenKOneSlack.impossible G hBound C hG hMin hNoSeymour
    hRootDegree hPivot hBCard hk hSlack

/-- Complete tight `epsilon_s = 0`, `(x,z)=(1,6)` row. -/
theorem tightEpsilonZeroXOneImpossible
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hEpsilon : epsilonS G C = 0)
    (hx : C.x = 1) (hz : C.z = 6) : False := by
  exact XOneAssembly.impossible G hBound C hG hMin hNoSeymour
    hRootDegree hPivot hBCard hk hEpsilon hx hz

/-- The high-defect part of the tight `epsilon_s = 0`, `(x,z)=(2,5)` row,
proved by the projected high-defect certificate. -/
theorem tightEpsilonZeroXTwoHighDefectImpossible
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hEpsilon : epsilonS G C = 0)
    (hx : C.x = 2) (hz : C.z = 5)
    (hHighDefect : 4 ≤ 35 - edgeCount G C.P C.Z) : False := by
  exact FiveZHighDefectAssembly.tightEpsilonZeroXTwoHighDefectImpossible
    G hBound C hG hMin hNoSeymour hRootDegree hPivot hBCard hk
      hEpsilon hx hz hHighDefect

/-- Complete tight `epsilon_s = 0`, `(x,z)=(2,5)` row, assembling the proved
low-defect and high-defect certificates. -/
theorem tightEpsilonZeroXTwoImpossible
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hEpsilon : epsilonS G C = 0)
    (hx : C.x = 2) (hz : C.z = 5) : False := by
  by_cases hLowDefect : 35 - edgeCount G C.P C.Z ≤ 3
  · exact FiveZLowDefectAssembly.impossible_exactFiveZ_of_missing_le_three
      G C hG hPivot hMin hNoSeymour hRootDegree hBCard hk hx hz hEpsilon
      hLowDefect
  · exact tightEpsilonZeroXTwoHighDefectImpossible G hBound C hG hMin
      hNoSeymour hRootDegree hPivot hBCard hk hEpsilon hx hz (by omega)

/-- Complete tight `epsilon_s = 0`, `(x,z)=(3,4)` row, assembling the
low-defect exact/aggregate certificates and the projected high-defect
certificate. -/
theorem tightEpsilonZeroXThreeImpossible
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hEpsilon : epsilonS G C = 0)
    (hx : C.x = 3) (hz : C.z = 4) : False := by
  by_cases hLowDefect : 28 - edgeCount G C.P C.Z ≤ 1
  · exact FourZLowDefectAssembly.impossible_exactFourZ_of_missing_le_one
      G hBound C hG hPivot hMin hNoSeymour hRootDegree hBCard hk hx hz
      hEpsilon hLowDefect
  · exact FourZHighDefectAssembly.tightEpsilonZeroXThreeHighDefectImpossible
      G hBound C hG hMin hNoSeymour hRootDegree hPivot hBCard hk hEpsilon
      hx hz (by omega)

/-- Tight `epsilon_s = 0`, `(x,z)=(4,3)` case. -/
theorem tightEpsilonZeroXFourImpossible
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hEpsilon : epsilonS G C = 0)
    (hx : C.x = 4) (hz : C.z = 3) : False := by
  exact ThreeZXFourAssembly.impossible G hBound C hG hMin hNoSeymour
    hRootDegree hPivot hBCard hk hEpsilon hx hz

/-- The final `(7,1)` statement, assembled from the six explicit subcase
results above. -/
theorem bSevenKOneCase : SeymourEight.BSevenKOneCase := by
  intro V _ _ hBound G _ C hG hMin hRootDegree hPivot hBCard hk
  by_contra hNoSeymour
  have hRows := parameterRows G C hG hMin hNoSeymour hRootDegree
    hPivot hBCard hk
  have hLevel : C.x + C.z + epsilonS G C = 6 ∨
      C.x + C.z + epsilonS G C = 7 := by
    rcases hRows with h1 | h2 | h3 | h4
    · rcases h1 with ⟨hx, hw | hw⟩ <;> omega
    · rcases h2 with ⟨hx, hw | hw⟩ <;> omega
    · rcases h3 with ⟨hx, hw | hw⟩ <;> omega
    · rcases h4 with ⟨hx, hw⟩
      omega
  rcases hLevel with hSlack | hTight
  · exact slackRowsImpossible G hBound C hG hMin hNoSeymour
      hRootDegree hPivot hBCard hk hSlack
  · rcases epsilonS_eq_zero_or_one G C with hZero | hOne
    · have hxCases : C.x = 1 ∨ C.x = 2 ∨ C.x = 3 ∨ C.x = 4 := by
        rcases hRows with h1 | h2 | h3 | h4
        · exact Or.inl h1.1
        · exact Or.inr (Or.inl h2.1)
        · exact Or.inr (Or.inr (Or.inl h3.1))
        · exact Or.inr (Or.inr (Or.inr h4.1))
      rcases hxCases with hx | hx | hx | hx
      · exact tightEpsilonZeroXOneImpossible G hBound C hG hMin
          hNoSeymour hRootDegree hPivot hBCard hk hZero hx (by omega)
      · exact tightEpsilonZeroXTwoImpossible G hBound C hG hMin
          hNoSeymour hRootDegree hPivot hBCard hk hZero hx (by omega)
      · exact tightEpsilonZeroXThreeImpossible G hBound C hG hMin
          hNoSeymour hRootDegree hPivot hBCard hk hZero hx (by omega)
      · exact tightEpsilonZeroXFourImpossible G hBound C hG hMin
          hNoSeymour hRootDegree hPivot hBCard hk hZero hx (by omega)
    · exact tightEpsilonOneImpossible G hBound C hG hMin hNoSeymour
        hRootDegree hPivot hBCard hk hOne hTight

end SeymourEight.BSevenKOne
