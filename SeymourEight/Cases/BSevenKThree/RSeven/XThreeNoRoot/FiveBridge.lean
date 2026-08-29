import SeymourEight.Cases.BSevenKThree.RSeven.XThreeNoRoot.Symmetry
import SeymourEight.Certificates.BSevenKThree.RSeven.XThree.Five

set_option linter.style.header false

/-!
# Graph bridge for the five-target no-root row
-/

namespace SeymourEight.BSevenKThree.RSeven.XThreeNoRoot.FiveBridge

open Shared Labels Encoding Core GraphFacts
open SeymourEight.BSevenKThree.RSeven.XThreeNoRoot.SymmetricCore

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem impossibleAt
    (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3)
    (hr : C.r = 7) (hx : C.x = 3)
    (hZCard : (externalTargets G C).card = 5) : False := by
  have hPCard : C.P.card = 7 := hr
  have hPB : C.P = C.B := by
    apply Finset.eq_of_subset_of_card_le
      (Digraph.LocalConfiguration.P_subset_B (G := G) C)
    omega
  have hACard : C.A.card = 8 := by
    simpa [Digraph.LocalConfiguration.A, Digraph.outdegree] using hRootDegree
  have hA1Card : C.A1.card = 3 := hk
  have hXCard : C.X.card = 3 := hx
  have hRCard : C.R.card = 1 := by
    have hR := BSixKThree.card_R_eq_four_sub_x G C hG hRootDegree hk
    omega
  have hHCard : C.H.card = 6 := by
    have hH := BSixKThree.H_card_eq_three_add_x G C hk
    omega
  let L := Labels.canonicalLabels G 5 C hPCard hACard hA1Card hXCard hRCard
    hZCard
  have hCore := Symmetry.canonical_symmetricCore_true G C hG hPB hPivot hMin hk
    hNoSeymour hRootDegree hPCard hACard hA1Card hXCard hRCard hZCard hHCard
  dsimp only at hCore
  rw [five_unsat (graphBits G L)] at hCore
  contradiction

theorem impossible
    (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3)
    (hr : C.r = 7) (hx : C.x = 3)
    (hNoRoot : epsilonS G C = 0) (hz : C.z = 5) : False := by
  apply impossibleAt G C hG hMin hNoSeymour hRootDegree hPivot hBCard hk hr hx
  rw [card_externalTargets G C, hz, hNoRoot]

theorem impossibleRoot
    (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3)
    (hr : C.r = 7) (hx : C.x = 3)
    (hRoot : epsilonS G C = 1) (hz : C.z = 4) : False := by
  apply impossibleAt G C hG hMin hNoSeymour hRootDegree hPivot hBCard hk hr hx
  rw [card_externalTargets G C, hz, hRoot]

end SeymourEight.BSevenKThree.RSeven.XThreeNoRoot.FiveBridge
