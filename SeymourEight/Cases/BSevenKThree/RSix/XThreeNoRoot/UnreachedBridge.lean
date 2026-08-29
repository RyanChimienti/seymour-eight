import SeymourEight.Cases.BSevenKThree.RSix.XThreeNoRoot.UnreachedAssembly
import SeymourEight.Cases.BSevenKThree.RSix.XThreeNoRoot.UnreachedEffectiveBridge
import SeymourEight.Cases.BSevenKThree.RSix.XThreeNoRoot.UnreachedOrderBridge
import SeymourEight.Certificates.BSevenKThree.RSix.XThree.UnreachedDerived
import SeymourEight.Certificates.BSevenKThree.RSix.XThree.UnreachedFive

set_option linter.style.header false
set_option maxRecDepth 100000

namespace SeymourEight.BSevenKThree.RSix.XThreeNoRoot.UnreachedBridge

open Shared Shared.FiniteCore Labels Core UnreachedCore UnreachedGraphFacts
  UnreachedAssembly UnreachedEffectiveBridge UnreachedOrderBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem reducedCore_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hPivot : IsMinimalPivot G C)
    (hHCard : C.H.card = 6) (hAOneCard : C.A1.card = 3)
    (hXCard : C.X.card = 3) (hk : C.k = 3) (hr : C.r = 6)
    (hx : C.x = 3) (hy : BSevenKThree.y G C = 0)
    (hz : zCount = 4 ∨ zCount = 5)
    (hPOrder : ∀ q : Fin 5,
      XFourNoRoot.Labels.pInvariantKey G C (L.q 0).1
          (L.p ⟨q.val + 1, by omega⟩).1 ≤
        XFourNoRoot.Labels.pInvariantKey G C (L.q 0).1
          (L.p ⟨q.val, by omega⟩).1)
    (hAOrder : ∀ q : Fin 2,
      XFourNoRoot.Labels.aInvariantKey G C (L.a ⟨q.val + 2, by omega⟩).1 ≤
        XFourNoRoot.Labels.aInvariantKey G C (L.a ⟨q.val + 1, by omega⟩).1)
    (hXOrder : ∀ q : Fin 2,
      XFourNoRoot.Labels.aInvariantKey G C (L.a ⟨q.val + 5, by omega⟩).1 ≤
        XFourNoRoot.Labels.aInvariantKey G C (L.a ⟨q.val + 4, by omega⟩).1)
    (hZOrder : ∀ q : Fin (zCount - 1),
      XFourNoRoot.Labels.zInvariantKey G C (L.z ⟨q.val + 1, by omega⟩).1 ≤
        XFourNoRoot.Labels.zInvariantKey G C (L.z ⟨q.val, by omega⟩).1) :
    UnreachedCore.reducedCore zCount (UnreachedGraphFacts.graphBits G L) = true := by
  have hzLe : zCount ≤ 5 := by rcases hz with rfl | rfl <;> omega
  let arc := UnreachedCore.encodedArc (UnreachedGraphFacts.graphBits G L)
  have hOrA := orientedA_true G C L hG hzLe
  have hOrP := orientedP_true G C L hG hzLe
  have hOrAPQ := orientedAPQ_true G C L hG hzLe
  have hFixed := fixedPivot_true G C L hG hzLe
  have hEveryX := everyXReached_true G C L hG hzLe hAOneCard
  have hR := rUnreached_true G C L hG hzLe
  have hQ := qUnreached_true G C L hG hzLe hy
  have hZ := allZReached_true G C L hG hzLe
  have hAMin := aMinimumAndPivot_true G C L hG hzLe hPivot hMin hk hr
  have hANon := aNonSeymour_true G C L hG hzLe hNoSeymour
  have hPMin := pMinimum_true G C L hG hzLe hHCard hMin
  have hHall := hallCondition_true G C L hG hzLe hMin hNoSeymour
  have hMinThree : ∀ a < 8, (3 : BitVec 8).ule (aOut arc a) = true := by
    intro a ha
    rw [aMinimumAndPivot, all_eq_true_iff] at hAMin
    have hh := hAMin a ha
    simp only [Bool.and_eq_true] at hh
    exact hh.1.1
  have hDegreeThree := degreeThreeConsequences_true G C L hOrA hMinThree
  have hArithmetic := UnreachedCore.arithmetic_of_local zCount arc hOrA hOrAPQ
    hFixed hEveryX hR hQ hAMin
  have hEffective := pGenericEffective_true G C L hG hMin hNoSeymour
    hHCard hy hRootDegree hk hr hx hz
  have hSharp := sharpKing_true G C L hOrP
  have hOrder := reducedOrdered_true G C L hG hzLe hHCard hAOneCard hXCard
    hPOrder hAOrder hXOrder hZOrder
  simp only [UnreachedCore.reducedCore, UnreachedCore.reducedCoreFn,
    Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hOrA, hOrP⟩, hOrAPQ⟩, hFixed⟩,
    hEveryX⟩, hR⟩, hQ⟩, hZ⟩, hAMin⟩, hANon⟩, hPMin⟩, hHall⟩,
    hDegreeThree.1⟩, hDegreeThree.2⟩, hArithmetic⟩, hEffective⟩, hSharp⟩,
    hOrder⟩

theorem contradiction {zCount : Nat} (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hPivot : IsMinimalPivot G C)
    (hPCard : C.P.card = 6) (hACard : C.A.card = 8)
    (hQCard : C.Q.card = 1) (hZCard : (externalTargets G C).card = zCount)
    (hAOneCard : C.A1.card = 3) (hXCard : C.X.card = 3)
    (hRCard : C.R.card = 1) (hHCard : C.H.card = 6)
    (hk : C.k = 3) (hr : C.r = 6) (hx : C.x = 3)
    (hy : BSevenKThree.y G C = 0) (hz : zCount = 4 ∨ zCount = 5) : False := by
  let L := canonicalLabels G zCount C hPCard hACard hQCard hZCard
    hAOneCard hXCard hRCard
  have hCore := reducedCore_true G C L hG hMin hNoSeymour hRootDegree hPivot
    hHCard hAOneCard hXCard hk hr hx hy hz
    (canonicalLabels_p_order G zCount C hPCard hACard hQCard hZCard
      hAOneCard hXCard hRCard)
    (canonicalLabels_aOne_order G zCount C hPCard hACard hQCard hZCard
      hAOneCard hXCard hRCard)
    (canonicalLabels_x_order G zCount C hPCard hACard hQCard hZCard
      hAOneCard hXCard hRCard)
    (canonicalLabels_z_order G zCount C hPCard hACard hQCard hZCard
      hAOneCard hXCard hRCard)
  rcases hz with rfl | rfl
  · have hCert := UnreachedCore.four_unsat (UnreachedGraphFacts.graphBits G L)
    rw [hCore] at hCert
    contradiction
  · have hCert := UnreachedCore.five_unsat (UnreachedGraphFacts.graphBits G L)
    rw [hCore] at hCert
    contradiction

end SeymourEight.BSevenKThree.RSix.XThreeNoRoot.UnreachedBridge
