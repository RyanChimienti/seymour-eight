import SeymourEight.Cases.BSevenKThree.RSeven.XThreeNoRoot.Assembly
import SeymourEight.Cases.BSevenKThree.RSeven.XThreeNoRoot.Expansion
import SeymourEight.Certificates.BSevenKThree.RSeven.XThree.FourExpansion

set_option linter.style.header false

namespace SeymourEight.BSevenKThree.RSeven.XThreeNoRoot.FourBridge

open Shared Shared.FiniteCore Labels Encoding Core GraphFacts
open SeymourEight.BSevenKThree.RSeven.XThreeNoRoot.ExpansionCore

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem impossibleAt
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3) (hr : C.r = 7)
    (hx : C.x = 3) (hZCard : (externalTargets G C).card = 4) : False := by
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
  let L := Labels.canonicalLabels G 4 C hPCard hACard hA1Card hXCard hRCard
    hZCard
  let bits := graphBits G L
  have hOrA : orientedA bits = true := Assembly.orientedA_true G C L hG (by omega)
  have hOrP : orientedP bits = true := Assembly.orientedP_true G C L hG
  have hOrPH : orientedPH bits = true := Assembly.orientedPH_true G C L hG
  have hX : everyXReached bits = true := Assembly.everyXReached_true G C L hA1Card
  have hR : rUnreached bits = true := Assembly.rUnreached_true G C L hG
  have hZ : allZReached 4 bits = true := Assembly.allZReached_true G C L (by omega)
  have hAMin : aMinimumAndDegree bits = true :=
    Assembly.aMinimumAndDegree_true G C L hG hPB hPivot hMin hk (by omega)
  have hANon : all 8 (aNonSeymour 4 bits) = true :=
    Assembly.aNonSeymour_all_true G C L hG hPB hNoSeymour (by omega)
  have hPMin : pMinimumDegree 4 bits = true :=
    Assembly.pMinimumDegree_true G C L hG hPB hHCard hMin (by omega)
  have hStructural : structuralCore 4 bits = true := by
    simp [structuralCore, hOrA, hOrP, hOrPH, hX, hR, hZ, hAMin, hANon, hPMin]
  have hExpansion : pUnionExpansion 4 bits = true :=
    Expansion.pUnionExpansion_true G hBound C L (by omega) hG hPB hNoSeymour
  have hCore : core 4 bits = true := by
    simp [core, hStructural, hExpansion]
  rw [four_unsat bits] at hCore
  contradiction

theorem impossible
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3) (hr : C.r = 7)
    (hx : C.x = 3) (hNoRoot : epsilonS G C = 0) (hz : C.z = 4) : False := by
  apply impossibleAt G hBound C hG hMin hNoSeymour hRootDegree hPivot hBCard hk hr hx
  rw [card_externalTargets G C, hz, hNoRoot]

theorem impossibleRoot
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3) (hr : C.r = 7)
    (hx : C.x = 3) (hRoot : epsilonS G C = 1) (hz : C.z = 3) : False := by
  apply impossibleAt G hBound C hG hMin hNoSeymour hRootDegree hPivot hBCard hk hr hx
  rw [card_externalTargets G C, hz, hRoot]

end SeymourEight.BSevenKThree.RSeven.XThreeNoRoot.FourBridge
