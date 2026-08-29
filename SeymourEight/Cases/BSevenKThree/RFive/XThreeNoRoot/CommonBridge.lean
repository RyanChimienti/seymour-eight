import SeymourEight.Cases.BSevenKThree.RFive.XThreeNoRoot.AugmentedBridge
import SeymourEight.Cases.BSevenKThree.RFive.XThreeNoRoot.InducedBridge
import SeymourEight.Cases.BSevenKThree.RFive.XThreeNoRoot.EffectiveBridge
import SeymourEight.Cases.BSevenKThree.RFive.XThreeNoRoot.OrderingBridge

set_option linter.style.header false
set_option maxRecDepth 20000

namespace SeymourEight.BSevenKThree.RFive.XThreeNoRoot.CommonBridge

open Shared Shared.FiniteCore Labels Encoding Core GraphFacts Assembly
  AugmentedBridge InducedBridge EffectiveBridge OrderingBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem core_true {zCount yValue : Nat}
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hNoSeymour : ¬G.HasSeymourVertex)
    (hPivot : IsMinimalPivot G C) (hHCard : C.H.card = 6)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 3)
    (hk : C.k = 3) (hr : C.r = 5)
    (hyValue : BSevenKThree.y G C = yValue)
    (hyz : (yValue = 1 ∧ zCount = 3) ∨
      (yValue = 2 ∧ (zCount = 1 ∨ zCount = 2)))
    (hPOrder : ∀ i : Fin 4,
      SeymourEight.BSevenKThree.RFive.XFourNoRoot.Labels.pInvariantKey G C
          (L.p ⟨i.val+1, by omega⟩).1 ≤
        SeymourEight.BSevenKThree.RFive.XFourNoRoot.Labels.pInvariantKey G C
          (L.p ⟨i.val, by omega⟩).1)
    (hAOrder : ∀ i : Fin 2,
      SeymourEight.BSevenKThree.RFive.XFourNoRoot.Labels.aInvariantKey G C
          (L.a ⟨i.val+2, by omega⟩).1 ≤
        SeymourEight.BSevenKThree.RFive.XFourNoRoot.Labels.aInvariantKey G C
          (L.a ⟨i.val+1, by omega⟩).1)
    (hXOrder : ∀ i : Fin 2,
      SeymourEight.BSevenKThree.RFive.XFourNoRoot.Labels.aInvariantKey G C
          (L.a ⟨i.val+5, by omega⟩).1 ≤
        SeymourEight.BSevenKThree.RFive.XFourNoRoot.Labels.aInvariantKey G C
          (L.a ⟨i.val+4, by omega⟩).1)
    (hQOrder :
      SeymourEight.BSevenKThree.RFive.XFourNoRoot.Labels.qInvariantKey G C
          (L.q 1).1 ≤
        SeymourEight.BSevenKThree.RFive.XFourNoRoot.Labels.qInvariantKey G C
          (L.q 0).1)
    (hZOrder : ∀ i : Fin (zCount-1),
      SeymourEight.BSevenKThree.RFive.XFourNoRoot.Labels.zInvariantKey G C
          (L.z ⟨i.val+1, by omega⟩).1 ≤
        SeymourEight.BSevenKThree.RFive.XFourNoRoot.Labels.zInvariantKey G C
          (L.z ⟨i.val, by omega⟩).1) :
    coreFn yValue zCount (encodedArc (graphBits G L)) = true := by
  have hzLe : zCount ≤ 3 := by rcases hyz with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩ <;> omega
  have hzCases : zCount = 1 ∨ zCount = 2 ∨ zCount = 3 := by
    rcases hyz with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩ <;> simp
  have hOrA := orientedA_true G C L hG hzLe
  have hOrP := orientedP_true G C L hG hzLe
  have hOrPH := orientedPH_true G C L hG hzLe
  have hFixed := fixedPivot_true G C L hG hzLe
  have hX := everyXReached_true G C L hG hzLe hA1Card
  have hR := rUnreached_true G C L hG hzLe
  have hQB := qInB_true G C L hG hzLe
  have hQR := qReachStatus_true G C L hG hzLe hA1Card yValue hyValue
  have hZ := allZReached_true G C L hG hzLe
  have hInactive := inactiveZZero_true G C L hzCases
  have hAMin := aMinimumAndPivot_true G C L hG hzLe hPivot hMin hk hr
  have hANon := aNonSeymour_true G C L hG hzLe hNoSeymour
  have hPMin := pMinimum_true G C L hG hzLe hHCard hMin
  have hAug := augmentedNonSeymour_true G C L hG hMin hNoSeymour hzLe
    hHCard hANon hyz
  have hHall := hallCondition_true G C L hG hzLe hMin hNoSeymour
  have hAOutMinimum : ∀ a < 8,
      (3 : BitVec 8).ule (aOut (encodedArc (graphBits G L)) a) = true := by
    rw [aMinimumAndPivot, all_eq_true_iff] at hAMin
    intro a ha
    have hRow := hAMin a ha
    simp only [Bool.and_eq_true] at hRow
    exact hRow.1.1
  have hDegree := degreeThreeConsequences_true G C L hOrA hAOutMinimum
  have hInduced := inducedConditions_true G hBound C L hG hzLe
  have hArithmetic := arithmetic_true G C L hOrA hOrP hOrPH hFixed hX hR
    hQB hQR hAMin hPMin hyz
  have hMissing := externalMissing_le_capacity_of_arithmetic
    (yValue := yValue) (zCount := zCount) (encodedArc (graphBits G L)) hArithmetic
  have hEffective := pEffective_true G C L hG hMin hNoSeymour hHCard hzLe
    hyValue hyz hMissing
  have hSharp := sharpKing_true G C L hOrP
  have hOrdered := ordered_true G C L hG hzLe hzCases hHCard hA1Card hXCard
    hPOrder hAOrder hXOrder hQOrder hZOrder
  simp [coreFn, hOrA, hOrP, hOrPH, hFixed, hX, hR, hQB, hQR, hZ,
    hInactive, hAMin, hANon, hPMin, hAug, hHall, hDegree.1, hDegree.2,
    hInduced, hArithmetic, hEffective, hSharp, hOrdered]

end SeymourEight.BSevenKThree.RFive.XThreeNoRoot.CommonBridge
