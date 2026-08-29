import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XFour.HighDefect.Assembly
import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XFour.LowDefect.OneMissing

set_option linter.style.header false

/-!
# Assembly of the tight epsilon-zero, `x = 4` row

The number of missing incidences in the `7 × 3` rectangle `P × Z` is split
into zero, one, and at least two.  The first two branches use the compact
terminal cores; the last uses the projected high-defect certificates.
-/

namespace SeymourEight.ThreeZXFourAssembly

open Shared BSevenKOne BSevenKOneCounting FiveZExactGraphBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem zeroMissing_impossible
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hx : C.x = 4) (hz : C.z = 3)
    (hEpsilon : epsilonS G C = 0)
    (hPZ : edgeCount G C.P C.Z = 21) : False := by
  have hPB := p_eq_B G C hG hMin hBCard hk
  have hPCard : C.P.card = 7 := by rw [hPB]; exact hBCard
  have hZCard : C.Z.card = 3 := hz
  have hSeven := ThreeZExactSeven.seven_le_zExternalUnion_card
    G C hG hMin hPCard hZCard hPZ
  by_cases hEight : 8 ≤ (zExternalUnion G C).card
  · exact ThreeZFullUnion.impossible_of_full_union G C hG hMin hNoSeymour
      hRootDegree hBCard hk hx hz hEpsilon hPZ hEight
  · have hWCard : (zExternalUnion G C).card = 7 := by omega
    exact ThreeZExactSeven.impossible G hBound C hG hMin hNoSeymour
      hPCard hZCard hPZ hWCard

/-- Complete tight `epsilon_s = 0`, `(x,z)=(4,3)` row. -/
theorem impossible
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hEpsilon : epsilonS G C = 0)
    (hx : C.x = 4) (hz : C.z = 3) : False := by
  have hPB := p_eq_B G C hG hMin hBCard hk
  have hPCard : C.P.card = 7 := by rw [hPB]; exact hBCard
  have hZCard : C.Z.card = 3 := hz
  have hPZUpper := edgeCount_le_card_mul_card G C.P C.Z
  rw [hPCard, hZCard] at hPZUpper
  by_cases hFull : edgeCount G C.P C.Z = 21
  · exact zeroMissing_impossible G hBound C hG hMin hNoSeymour
      hRootDegree hBCard hk hx hz hEpsilon hFull
  · by_cases hOne : edgeCount G C.P C.Z = 20
    · exact ThreeZOneMissingBridge.impossible G C hG hMin hNoSeymour
        hRootDegree hBCard hk hx hz hEpsilon hOne
    · exact ThreeZHighDefectAssembly.tightEpsilonZeroXFourHighDefectImpossible
        G hBound C hG hMin hNoSeymour hRootDegree hPivot hBCard hk
        hEpsilon hx hz (by omega)

end SeymourEight.ThreeZXFourAssembly
