import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XTwo.ExactUnion.FiveZExactAllOverlapAssembly
import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XTwo.UnionAtLeastEight.FiveZUnionEightBridge

set_option linter.style.header false

/-!
# Assembly of the low-defect five-`Z` branch

The capacity argument forces the external union to have at least six
vertices.  Cardinalities six and seven are handled by the exact retained-set
certificate, while cardinality at least eight is handled by the aggregate
certificate.
-/

namespace SeymourEight.FiveZLowDefectAssembly

open FiveZExactGraphBridge FiveZExactGlobalBridge FiveZExactAllOverlapAssembly
  FiveZUnionEightBridge BSevenKOneCounting Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The complete `(x,z)=(2,5)` branch with at most three missing `P → Z`
incidences. -/
theorem impossible_exactFiveZ_of_missing_le_three
    (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPivot : IsMinimalPivot G C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hBCard : C.B.card = 7)
    (hk : C.k = 1) (hx : C.x = 2) (hz : C.z = 5)
    (hEpsilon : epsilonS G C = 0)
    (hMissing : 35 - edgeCount G C.P C.Z ≤ 3) : False := by
  have hPB := SeymourEight.BSevenKOne.p_eq_B G C hG hMin hBCard hk
  have hPCard : C.P.card = 7 := by rw [hPB]; exact hBCard
  have hZCard : C.Z.card = 5 := by
    change C.Z.card = 5 at hz
    exact hz
  have hPZ := thirtyTwo_le_PZ_of_missing_le_three
    G C hPCard hZCard hMissing
  have hSix := six_le_zExternalUnion_card G C hG hMin hPCard hZCard hPZ
  by_cases hEight : 8 ≤ (zExternalUnion G C).card
  · exact impossible_exactFiveZ_unionAtLeastEight G C hG hMin hNoSeymour
      hRootDegree hBCard hk hx hz hEpsilon hPZ hEight
  · have hSixOrSeven : (zExternalUnion G C).card = 6 ∨
        (zExternalUnion G C).card = 7 := by omega
    exact impossible_exactFiveZ_unionSixOrSeven G C hG hPivot hMin
      hNoSeymour hRootDegree hBCard hk hx hz hEpsilon hPZ hSixOrSeven

end SeymourEight.FiveZLowDefectAssembly
