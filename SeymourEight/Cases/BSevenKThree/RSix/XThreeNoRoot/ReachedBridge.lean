import SeymourEight.Cases.BSevenKThree.RSix.XThreeNoRoot.Assembly
import SeymourEight.Cases.BSevenKThree.RSix.XThreeNoRoot.EffectiveBridge
import SeymourEight.Cases.BSevenKThree.RSix.XThreeNoRoot.OrderBridge
import SeymourEight.Cases.BSevenKThree.RSix.XThreeNoRoot.TwoEffectiveBridge
import SeymourEight.Certificates.BSevenKThree.RSix.XThree.Reduced
import SeymourEight.Certificates.BSevenKThree.RSix.XThree.ReducedFiveHasAToQ
import SeymourEight.Certificates.BSevenKThree.RSix.XThree.ReducedFiveNoAToQ

set_option linter.style.header false
set_option maxRecDepth 100000

namespace SeymourEight.BSevenKThree.RSix.XThreeNoRoot.ReachedBridge

open Shared Shared.FiniteCore Labels Encoding Core GraphFacts Assembly
  EffectiveBridge OrderBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem reducedCore_true {zCount : Nat} (C : G.LocalConfiguration)
    (L : Labels G zCount C) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hPivot : IsMinimalPivot G C)
    (hHCard : C.H.card = 6) (hAOneCard : C.A1.card = 3)
    (hXCard : C.X.card = 3) (hk : C.k = 3) (hr : C.r = 6)
    (hx : C.x = 3) (hy : BSevenKThree.y G C = 1)
    (hz : zCount = 2 ∨ zCount = 3 ∨ zCount = 4)
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
    reducedCore zCount (graphBits G L) = true := by
  have hzLe : zCount ≤ 4 := by rcases hz with rfl | rfl | rfl <;> omega
  let arc := encodedArc (graphBits G L)
  have hOrA := orientedA_true G C L hG hzLe
  have hOrP := orientedP_true G C L hG hzLe
  have hOrAPQ := orientedAPQ_true G C L hG hzLe
  have hFixed := fixedPivot_true G C L hG hzLe
  have hEveryX := everyXReached_true G C L hG hzLe hAOneCard
  have hR := rUnreached_true G C L hG hzLe
  have hQ := qReached_true G C L hG hzLe hy
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
  have hArithmetic := arithmetic_of_local zCount arc hOrA hOrAPQ hFixed
    hEveryX hR hQ hAMin
  have hEffective : pGenericEffective zCount (encodedArc (graphBits G L)) = true := by
    rcases hz with hzTwo | hzThree | hzFour
    · subst zCount
      exact TwoEffectiveBridge.pGenericEffective_true G C L hG hMin hNoSeymour
        hHCard hy hRootDegree hk hr hx
    · exact pGenericEffective_true G C L hG hMin hNoSeymour hHCard hy
        hRootDegree hk hr hx (Or.inl hzThree)
    · exact pGenericEffective_true G C L hG hMin hNoSeymour hHCard hy
        hRootDegree hk hr hx (Or.inr hzFour)
  have hSharp := sharpKing_true G C L hOrP
  have hOrder := reducedOrdered_true G C L hG hzLe hHCard hAOneCard hXCard
    hPOrder hAOrder hXOrder hZOrder
  simp only [reducedCore, reducedCoreFn, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hOrA, hOrP⟩, hOrAPQ⟩, hFixed⟩,
    hEveryX⟩, hR⟩, hQ⟩, hZ⟩, hAMin⟩, hANon⟩, hPMin⟩, hHall⟩,
    hDegreeThree.1⟩, hDegreeThree.2⟩, hArithmetic⟩, hEffective⟩, hSharp⟩,
    hOrder⟩

theorem contradictionTwo (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hPivot : IsMinimalPivot G C)
    (hPCard : C.P.card = 6) (hACard : C.A.card = 8)
    (hQCard : C.Q.card = 1) (hZCard : (externalTargets G C).card = 2)
    (hAOneCard : C.A1.card = 3) (hXCard : C.X.card = 3)
    (hRCard : C.R.card = 1) (hHCard : C.H.card = 6)
    (hk : C.k = 3) (hr : C.r = 6) (hx : C.x = 3)
    (hy : BSevenKThree.y G C = 1) : False := by
  let L := canonicalLabels G 2 C hPCard hACard hQCard hZCard
    hAOneCard hXCard hRCard
  have hCore := reducedCore_true G C L hG hMin hNoSeymour hRootDegree hPivot
    hHCard hAOneCard hXCard hk hr hx hy (Or.inl rfl)
    (canonicalLabels_p_order G 2 C hPCard hACard hQCard hZCard
      hAOneCard hXCard hRCard)
    (canonicalLabels_aOne_order G 2 C hPCard hACard hQCard hZCard
      hAOneCard hXCard hRCard)
    (canonicalLabels_x_order G 2 C hPCard hACard hQCard hZCard
      hAOneCard hXCard hRCard)
    (canonicalLabels_z_order G 2 C hPCard hACard hQCard hZCard
      hAOneCard hXCard hRCard)
  have hArithmetic : arithmetic 2 (encodedArc (graphBits G L)) = true := by
    have h := hCore
    simp only [reducedCore, reducedCoreFn, Bool.and_eq_true] at h
    exact h.1.1.1.2
  have hLower := hArithmetic
  simp only [arithmetic, Bool.and_eq_true, BitVec.ule_eq_decide,
    decide_eq_true_eq] at hLower
  have hHP := hLower.1.1.1.1.1
  have gainBounds (d : BitVec 8) :
      3 ≤ (if d.ule 1 then (3 : BitVec 8) else if d == 2 then 5
        else if d == 3 then 7 else 9).toNat ∧
      (if d.ule 1 then (3 : BitVec 8) else if d == 2 then 5
        else if d == 3 then 7 else 9).toNat ≤ 9 := by
    split
    · decide
    · split
      · decide
      · split <;> decide
  have hGainBounds := gainBounds (aMissing (encodedArc (graphBits G L)))
  have hGainLower : 3 ≤ (degreeGain (encodedArc (graphBits G L))).toNat := by
    simpa only [degreeGain] using hGainBounds.1
  have hGainUpper : (degreeGain (encodedArc (graphBits G L))).toNat ≤ 9 := by
    simpa only [degreeGain] using hGainBounds.2
  have hQUpper : (qDefect (encodedArc (graphBits G L))).toNat ≤ 6 := by
    have hCount : (count 6 fun h ↦
        encodedArc (graphBits G L) (1 + h) 14).toNat ≤ 6 := by
      rw [toNat_count_eq_fin_sum 6 _ (by omega)]
      calc
        _ ≤ ∑ _i : Fin 6, 1 := by
          apply Finset.sum_le_sum
          intro i hi
          split <;> omega
        _ = 6 := by simp
    rw [qDefect, BitVec.toNat_sub]
    have hSix : (6 : BitVec 8).toNat = 6 := by decide
    rw [hSix]
    have hRewrite : 256 - (count 6 fun h ↦
        encodedArc (graphBits G L) (1 + h) 14).toNat + 6 =
        256 + (6 - (count 6 fun h ↦
          encodedArc (graphBits G L) (1 + h) 14).toNat) := by omega
    rw [hRewrite, Nat.add_mod, Nat.mod_eq_of_lt (by omega)]
    omega
  have hFirstNat : (21 + degreeGain (encodedArc (graphBits G L)) +
      qDefect (encodedArc (graphBits G L))).toNat =
      21 + (degreeGain (encodedArc (graphBits G L))).toNat +
        (qDefect (encodedArc (graphBits G L))).toNat := by
    simp only [BitVec.toNat_add]
    have hTwentyOne : (21 : BitVec 8).toNat = 21 := by decide
    rw [hTwentyOne, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [hFirstNat, totalHToP_toNat G C L hG (by omega) hHCard] at hHP
  have hAux := TwoEffectiveBridge.auxiliary_saturated G C L hG hMin
    hRootDegree hHCard hk hr hx hy
  have hPCap := BSevenKTwo.P_degree_capacity_r_six G C hG hMin hr
  have hAuxEq : edgeCount G C.P (auxiliarySet G C) =
      edgeCount G C.P C.Q + edgeCount G C.P (externalTargets G C) := by
    rw [edgeCount_union_of_disjoint]
    apply Finset.disjoint_of_subset_left
      (Digraph.LocalConfiguration.Q_subset_B (G := G) C)
    exact BSixKThree.disjoint_B_externalTargets G C
  rw [hAuxEq] at hAux
  rw [hHCard] at hPCap
  omega

theorem contradictionThreeFour {zCount : Nat} (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hPivot : IsMinimalPivot G C)
    (hPCard : C.P.card = 6) (hACard : C.A.card = 8)
    (hQCard : C.Q.card = 1) (hZCard : (externalTargets G C).card = zCount)
    (hAOneCard : C.A1.card = 3) (hXCard : C.X.card = 3)
    (hRCard : C.R.card = 1) (hHCard : C.H.card = 6)
    (hk : C.k = 3) (hr : C.r = 6) (hx : C.x = 3)
    (hy : BSevenKThree.y G C = 1) (hz : zCount = 3 ∨ zCount = 4) : False := by
  let L := canonicalLabels G zCount C hPCard hACard hQCard hZCard
    hAOneCard hXCard hRCard
  have hCore := reducedCore_true G C L hG hMin hNoSeymour hRootDegree hPivot
    hHCard hAOneCard hXCard hk hr hx hy (Or.inr hz)
    (canonicalLabels_p_order G zCount C hPCard hACard hQCard hZCard
      hAOneCard hXCard hRCard)
    (canonicalLabels_aOne_order G zCount C hPCard hACard hQCard hZCard
      hAOneCard hXCard hRCard)
    (canonicalLabels_x_order G zCount C hPCard hACard hQCard hZCard
      hAOneCard hXCard hRCard)
    (canonicalLabels_z_order G zCount C hPCard hACard hQCard hZCard
      hAOneCard hXCard hRCard)
  rcases hz with rfl | rfl
  · have hCert := four_reduced_unsat (graphBits G L)
    rw [hCore] at hCert
    contradiction
  · by_cases hAQ : hasAToQ (encodedArc (graphBits G L))
    · have hCert := five_reduced_has_a_to_q (graphBits G L)
      simp [reducedFiveHasAToQ, hCore, hAQ] at hCert
    · have hCert := five_reduced_no_a_to_q (graphBits G L)
      simp [reducedFiveNoAToQ, hCore, hAQ] at hCert

end SeymourEight.BSevenKThree.RSix.XThreeNoRoot.ReachedBridge
