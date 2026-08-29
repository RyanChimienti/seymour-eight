import SeymourEight.Cases.BSevenKThree.RFive.XFourNoRoot.CommonBridge
import SeymourEight.Certificates.BSevenKThree.RFive.XFour.ProbeOne

set_option linter.style.header false
set_option maxRecDepth 20000

namespace SeymourEight.BSevenKThree.RFive.XFourNoRoot.PerfectCountsBridge

open Shared Shared.FiniteCore Labels Encoding Core GraphFacts Assembly
  AugmentedBridge EffectiveBridge CommonBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem totalPToH_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hHCard : C.H.card = 7)
    (hzSmall : zCount < 256) :
    (totalPToH (graphArc G L)).toNat = edgeCount G C.P C.H := by
  rw [totalPToH, AugmentedBridge.toNat_sumCount,
    ← Fin.sum_univ_eq_sum_range]
  have hEach : ∀ i : Fin 5,
      (pHOut (graphArc G L) i).toNat = directCount G C.H (L.p i).1 := by
    intro i
    exact (pBlockCounts G C L hHCard hzSmall i i.isLt).2.1
  rw [show (∑ i : Fin 5, (pHOut (graphArc G L) i).toNat) =
      ∑ i : Fin 5, directCount G C.H (L.p i).1 by
        apply Finset.sum_congr rfl
        intro i _
        exact hEach i,
    ← edgeCount_eq_sum_fin G C.P C.H L.p]
  have hCap := edgeCount_le_card_mul_card G C.P C.H
  have hp : C.P.card = 5 := by simpa using (Fintype.card_congr L.p).symm
  rw [hp, hHCard] at hCap
  rw [Nat.mod_eq_of_lt (by omega)]

theorem totalHToP_toNat {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hHCard : C.H.card = 7) :
    (totalHToP (graphArc G L)).toNat = edgeCount G C.H C.P := by
  rw [totalHToP, AugmentedBridge.toNat_sumCount,
    ← Fin.sum_univ_eq_sum_range]
  have hEach : ∀ i : Fin 7,
      (hPOut (graphArc G L) i).toNat =
        directCount G C.P ((hLabelEquiv G C L hHCard) i).1 := by
    intro i
    simpa [hLabelEquiv_val, Nat.add_comm] using
      hPOut_toNat G C L i i.isLt
  rw [show (∑ i : Fin 7, (hPOut (graphArc G L) i).toNat) =
      ∑ i : Fin 7, directCount G C.P ((hLabelEquiv G C L hHCard) i).1 by
        apply Finset.sum_congr rfl
        intro i _
        exact hEach i,
    ← edgeCount_eq_sum_fin G C.H C.P (hLabelEquiv G C L hHCard)]
  have hCap := edgeCount_le_card_mul_card G C.H C.P
  have hp : C.P.card = 5 := by simpa using (Fintype.card_congr L.p).symm
  rw [hp, hHCard] at hCap
  rw [Nat.mod_eq_of_lt (by omega)]

theorem perfect_counts (C : G.LocalConfiguration) (L : Labels G 2 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hHCard : C.H.card = 7) (hXCard : C.X.card = 4)
    (hRCard : C.R.card = 0) (hk : C.k = 3) (hr : C.r = 5)
    (hy : BSevenKThree.y G C = 1) :
    externalMissing 2 (graphArc G L) (graphPToZ G L) = 0 ∧
      totalPToH (graphArc G L) = 15 ∧
      totalHToP (graphArc G L) = 20 := by
  have hExtLe := externalMissing_le_three_graph G C L hG hMin hHCard
    hXCard hRCard hk hr (Or.inl rfl) hy (by omega)
  have hExtNat :
      (externalMissing 2 (graphArc G L) (graphPToZ G L)).toNat = 0 := by
    omega
  have hExt : externalMissing 2 (graphArc G L) (graphPToZ G L) = 0 := by
    apply BitVec.eq_of_toNat_eq
    simpa using hExtNat
  have hAuxNat := externalMissing_toNat G C L hHCard (by omega) hy (by omega)
  have hAuxCap := edgeCount_le_card_mul_card G C.P (auxiliarySet G C)
  have hPCard : C.P.card = 5 := hr
  have hAuxCard := auxiliarySet_card G C L hy
  rw [hPCard, hAuxCard] at hAuxCap
  have hAux : edgeCount G C.P (auxiliarySet G C) = 15 := by omega
  have hHCap := BSixKThree.H_degree_capacity_general G C hG hMin hk
  have hx : C.x = 4 := hXCard
  have hySix : BSixKThree.y G C = 1 := hy
  have hQCard : C.Q.card = 2 := by
    simpa using (Fintype.card_congr L.q).symm
  rw [hHCard, hx, hRCard, hQCard, hySix] at hHCap
  norm_num [Nat.choose] at hHCap
  have hHPLower : 20 ≤ edgeCount G C.H C.P := by omega
  have hCross := cross_edgeCount_add_reverse_le G C.P C.H hG
  rw [hPCard, hHCard] at hCross
  have hPHLower : 15 ≤ edgeCount G C.P C.H := by
    have hPLower : 40 ≤ ∑ p ∈ C.P, G.outdegree p := by
      calc
        40 = ∑ _p ∈ C.P, 8 := by simp [hPCard]
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro p hp
          exact hMin p
    have hAccounting := BSixKThree.degreeSum_P_eq_blocks G C hG
    have hInternal := internal_edgeCount_le_choose_two G C.P hG
    rw [hPCard] at hInternal
    norm_num [Nat.choose] at hInternal
    have hPQ : edgeCount G C.P C.Q =
        edgeCount G C.P (BSevenKThree.reachedQ G C) := by
      unfold edgeCount
      apply Finset.sum_congr rfl
      intro p hp
      exact directCount_Q_eq_reachedQ G C p hp
    have hAuxEq : edgeCount G C.P C.Q +
        edgeCount G C.P (externalTargets G C) =
        edgeCount G C.P (auxiliarySet G C) := by
      rw [hPQ, auxiliarySet, edgeCount_union_of_disjoint]
      apply Finset.disjoint_of_subset_left Finset.inter_subset_left
      apply Finset.disjoint_of_subset_left
        (Digraph.LocalConfiguration.Q_subset_B (G := G) C)
      exact BSixKThree.disjoint_B_externalTargets G C
    omega
  have hHP : edgeCount G C.H C.P = 20 := by omega
  have hPH : edgeCount G C.P C.H = 15 := by omega
  have hPHBV : totalPToH (graphArc G L) = 15 := by
    apply BitVec.eq_of_toNat_eq
    rw [totalPToH_toNat G C L hHCard (by omega), hPH]
    decide
  have hHPBV : totalHToP (graphArc G L) = 20 := by
    apply BitVec.eq_of_toNat_eq
    rw [totalHToP_toNat G C L hHCard, hHP]
    decide
  exact ⟨hExt, hPHBV, hHPBV⟩

end SeymourEight.BSevenKThree.RFive.XFourNoRoot.PerfectCountsBridge
