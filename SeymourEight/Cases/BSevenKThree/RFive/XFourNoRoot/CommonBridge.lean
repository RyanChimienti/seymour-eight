import SeymourEight.Cases.BSevenKThree.RFive.XFourNoRoot.AugmentedBridge
import SeymourEight.Cases.BSevenKThree.RFive.XFourNoRoot.InducedBridge
import SeymourEight.Cases.BSevenKThree.RFive.XFourNoRoot.EffectiveBridge
import SeymourEight.Cases.BSevenKThree.RFive.XFourNoRoot.OrderingBridge
import SeymourEight.Cases.BSevenKThree.RFive.XFourNoRoot.DeletionBridge
import SeymourEight.Certificates.BSevenKThree.RFive.XFour.Derived

set_option linter.style.header false
set_option maxRecDepth 20000

namespace SeymourEight.BSevenKThree.RFive.XFourNoRoot.CommonBridge

open Shared Shared.FiniteCore Labels Encoding Core GraphFacts Assembly
  AugmentedBridge InducedBridge EffectiveBridge OrderingBridge DeletionBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem externalMissing_le_three_graph {zCount yValue : Nat}
    (C : G.LocalConfiguration) (L : Labels G zCount C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hHCard : C.H.card = 7) (hXCard : C.X.card = 4)
    (hRCard : C.R.card = 0) (hk : C.k = 3) (hr : C.r = 5)
    (hy : yValue = 1 ∨ yValue = 2)
    (hyValue : BSevenKThree.y G C = yValue)
    (hyz : yValue + zCount = 3) :
    (externalMissing zCount (graphArc G L) (graphPToZ G L)).toNat ≤
      3 * (yValue - 1) := by
  have hx : C.x = 4 := hXCard
  have hQCard : C.Q.card = 2 := by
    simpa using (Fintype.card_congr L.q).symm
  have hZCard : (externalTargets G C).card = zCount := by
    simpa using (Fintype.card_congr L.z).symm
  have hySix : BSixKThree.y G C = yValue := hyValue
  have hHCap := BSixKThree.H_degree_capacity_general G C hG hMin hk
  have hPCap := BSixKThree.P_degree_capacity_general G C hG hMin hr
  have hAuxCap := BSixKThree.P_to_Q_external_le G C hr
  have hPQ : edgeCount G C.P C.Q =
      edgeCount G C.P (BSevenKThree.reachedQ G C) := by
    unfold edgeCount
    apply Finset.sum_congr rfl
    intro p hp
    exact directCount_Q_eq_reachedQ G C p hp
  have hAux : edgeCount G C.P C.Q +
      edgeCount G C.P (externalTargets G C) =
      edgeCount G C.P (auxiliarySet G C) := by
    rw [hPQ, auxiliarySet, edgeCount_union_of_disjoint]
    apply Finset.disjoint_of_subset_left Finset.inter_subset_left
    apply Finset.disjoint_of_subset_left
      (Digraph.LocalConfiguration.Q_subset_B (G := G) C)
    exact BSixKThree.disjoint_B_externalTargets G C
  rw [hAux] at hPCap hAuxCap
  rw [hHCard, hx, hRCard, hQCard, hySix] at hHCap
  rw [hHCard] at hPCap
  rw [hySix, ← card_externalTargets G C, hZCard] at hAuxCap
  have hExternal := externalMissing_toNat G C L hHCard (by omega)
    hyValue hyz
  rcases hy with rfl | rfl <;>
    norm_num [Nat.choose] at hHCap hPCap hAuxCap hExternal ⊢ <;>
    omega

set_option maxHeartbeats 2000000 in
theorem commonCore_true {zCount yValue : Nat}
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hNoSeymour : ¬G.HasSeymourVertex)
    (hPivot : IsMinimalPivot G C) (hHCard : C.H.card = 7)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 4)
    (hRCard : C.R.card = 0)
    (hk : C.k = 3) (hr : C.r = 5)
    (hy : yValue = 1 ∨ yValue = 2) (hyValue : BSevenKThree.y G C = yValue)
    (hyz : yValue + zCount = 3) (hzLe : zCount ≤ 2)
    (hPOrder : ∀ q : Fin 4,
      pInvariantKey G C (L.p ⟨q.val + 1, by omega⟩).1 ≤
        pInvariantKey G C (L.p ⟨q.val, by omega⟩).1)
    (hAOneOrder : ∀ q : Fin 2,
      aInvariantKey G C (L.a ⟨q.val + 2, by omega⟩).1 ≤
        aInvariantKey G C (L.a ⟨q.val + 1, by omega⟩).1)
    (hXOrder : ∀ q : Fin 3,
      aInvariantKey G C (L.a ⟨q.val + 5, by omega⟩).1 ≤
        aInvariantKey G C (L.a ⟨q.val + 4, by omega⟩).1)
    (hQOrder : qInvariantKey G C (L.q 1).1 ≤
      qInvariantKey G C (L.q 0).1)
    (hZOrder : ∀ q : Fin (zCount - 1),
      zInvariantKey G C (L.z ⟨q.val + 1, by omega⟩).1 ≤
        zInvariantKey G C (L.z ⟨q.val, by omega⟩).1) :
    commonCore yValue zCount (graphArc G L) (graphPToZ G L) = true := by
  have hOrA := orientedA_true G C L hG
  have hOrP := orientedP_true G C L hG
  have hOrPH := orientedPH_true G C L hG
  have hFixed := fixedAOne_true G C L hG
  have hNoP := noPToAOne_true G C L hG
  have hQIn := qInB_true G C L
  have hQReach := qReachStatus_true G C L hA1Card yValue hyValue
  have hXReach := everyXReached_true G C L hA1Card
  have hZReach := everyZReached_true G C L
  have hInactive := inactiveZZero_true G C L
  have hACond := aConditions_true G C L hG hPivot hMin hk hr
  have hPCond := pConditions_true G C L hG hHCard hzLe hMin
  have hANon : aNonSeymour yValue zCount (graphArc G L) (graphPToZ G L) = true := by
    rcases hy with rfl | rfl
    · have hz : zCount = 2 := by omega
      subst zCount
      exact aNonSeymour_unaugmented_true G C L hG hNoSeymour (by omega)
    · have hz : zCount = 1 := by omega
      subst zCount
      exact aNonSeymour_true G C L hG hMin hNoSeymour hHCard hFixed
  have hPNon : pNonSeymour yValue zCount (graphArc G L) (graphPToZ G L) = true := by
    rcases hy with rfl | rfl
    · have hz : zCount = 2 := by omega
      subst zCount
      exact pNonSeymour_unaugmented_true G C L hG hNoSeymour hHCard (by omega)
    · have hz : zCount = 1 := by omega
      subst zCount
      exact pNonSeymour_true G C L hG hMin hNoSeymour hHCard hFixed
  have hAOutMinimum : ∀ a < 8,
      (3 : BitVec 8).ule (aOut (graphArc G L) a) = true := by
    rw [aConditions, all_eq_true_iff] at hACond
    intro a ha
    have hRow := hACond a ha
    simp only [Bool.and_eq_true] at hRow
    exact hRow.1.1
  have hDegreeThree := degreeThreeConsequences_true G C L hOrA hAOutMinimum
  have hDual := degreeAndDual_of_local yValue (graphArc G L) hy hOrA hOrPH
    hFixed hXReach hQReach hACond
  have hDeletion := aOneDeletionConditions_true G hBound C L hG hNoSeymour
    hA1Card hk hr hzLe hFixed
  have hExternalNat :
      (externalMissing zCount (graphArc G L) (graphPToZ G L)).toNat ≤ 3 := by
    have h := externalMissing_le_three_graph G C L hG hMin hHCard
      hXCard hRCard hk hr hy hyValue hyz
    rcases hy with rfl | rfl <;> omega
  have hExternalCore :
      (externalMissing zCount (graphArc G L) (graphPToZ G L)).ule
        3#8 = true := by
    have hThree : (3#8).toNat = 3 := by decide
    simpa only [BitVec.ule_eq_decide, decide_eq_true_eq, hThree] using hExternalNat
  have hEffective := pEffectiveConditions_true G C L hG hMin hNoSeymour
    hHCard hzLe hyValue hyz hExternalNat
  have hSharp := sharpKing_of_orientedP (graphArc G L) hOrP
  have hInduced := inducedConditions_true G hBound C L hG
  have hOrderedP := orderedP_true G C L hG hHCard hA1Card hXCard hzLe hPOrder
  have hOrderedA := orderedAClasses_true G C L hAOneOrder hXOrder
  have hOrderedQ := orderedQ_true G C L hQOrder
  have hOrderedZ := orderedZ_true G C L hZOrder
  simp [commonCore, hOrA, hOrP, hOrPH, hFixed, hNoP, hQIn, hQReach,
    hXReach, hZReach, hInactive, hACond, hPCond, hANon, hPNon,
    hDegreeThree.1, hDegreeThree.2, hDual, hExternalCore, hEffective, hSharp,
    hInduced.1, hInduced.2.1, hInduced.2.2.1, hInduced.2.2.2,
    hDeletion, hOrderedP, hOrderedA, hOrderedQ, hOrderedZ]

end SeymourEight.BSevenKThree.RFive.XFourNoRoot.CommonBridge
