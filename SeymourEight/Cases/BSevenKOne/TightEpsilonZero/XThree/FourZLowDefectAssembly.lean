import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XThree.FourZCapacity
import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.BareAssembly
import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XThree.UnionAtLeastEight.Assembly

set_option linter.style.header false

/-!
# Assembly of the low-defect four-`Z` branch

The capacity argument forces the external union to have at least seven
vertices.  Exact cardinality seven is handled by the retained-set
certificate, while cardinality at least eight is handled by the aggregate
105-bit certificate.
-/

namespace SeymourEight.FourZLowDefectAssembly

open FourZCapacity FiveZExactGraphBridge FourZUnionEightAssembly Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The common capacity/cardinality split, parameterized by the exact-seven
endpoint so the capacity argument remains independent of its encoding. -/
theorem impossible_exactFourZ_of_missing_le_one_of_exactSeven
    (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hBCard : C.B.card = 7)
    (hk : C.k = 1) (hx : C.x = 3) (hz : C.z = 4)
    (hEpsilon : epsilonS G C = 0)
    (hMissing : 28 - edgeCount G C.P C.Z ≤ 1)
    (hExactSeven : (zExternalUnion G C).card = 7 → False) : False := by
  have hPB := SeymourEight.BSevenKOne.p_eq_B G C hG hMin hBCard hk
  have hPCard : C.P.card = 7 := by rw [hPB]; exact hBCard
  have hZCard : C.Z.card = 4 := by
    change C.Z.card = 4 at hz
    exact hz
  have hPZ := twentySeven_le_PZ_of_missing_le_one
    G C hPCard hZCard hMissing
  have hSeven := seven_le_zExternalUnion_card
    G C hG hMin hPCard hZCard hPZ
  by_cases hEight : 8 ≤ (zExternalUnion G C).card
  · exact impossible_exactFourZ_unionAtLeastEight G C hG hMin hNoSeymour
      hRootDegree hBCard hk hx hz hEpsilon hPZ hEight
  · exact hExactSeven (by omega)

/-- The complete `(x,z)=(3,4)` branch with at most one missing `P → Z`
incidence. -/
theorem impossible_exactFourZ_of_missing_le_one
    (_hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPivot : IsMinimalPivot G C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hBCard : C.B.card = 7)
    (hk : C.k = 1) (hx : C.x = 3) (hz : C.z = 4)
    (hEpsilon : epsilonS G C = 0)
    (hMissing : 28 - edgeCount G C.P C.Z ≤ 1) : False := by
  apply impossible_exactFourZ_of_missing_le_one_of_exactSeven G C hG hMin
    hNoSeymour hRootDegree hBCard hk hx hz hEpsilon hMissing
  intro hSeven
  have hPZ : 27 ≤ edgeCount G C.P C.Z := by omega
  exact FourZExactSevenAssembly.impossible_exactFourZ_externalUnion_eq_seven
    G C hG hPivot hMin hNoSeymour hRootDegree hBCard hk hx hz hEpsilon
    hPZ hSeven

end SeymourEight.FourZLowDefectAssembly
