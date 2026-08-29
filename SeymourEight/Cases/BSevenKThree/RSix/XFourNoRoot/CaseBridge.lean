import SeymourEight.Cases.BSevenKThree.RSix.XFourNoRoot.StrongDualBridge
import SeymourEight.Cases.BSevenKThree.RSix.XFourNoRoot.XHDeletionBridge
import SeymourEight.Cases.BSevenKThree.RSix.XFourNoRoot.ReducedCapacityFinalBridge
import SeymourEight.Cases.BSevenKThree.RSix.XFourNoRoot.D501Bridge
import SeymourEight.Cases.BSevenKThree.RSix.XFourNoRoot.ReachedCountsBridge
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.RigidXDefs
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.BroadRigidXDefs
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.SatTailSound
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.SatCOneCuts
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.CompactActualTailSound

set_option linter.style.header false
set_option maxRecDepth 20000

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.CaseBridge

open Shared Shared.FiniteCore Labels Encoding Core GraphFacts Assembly EffectiveBridge CommonBridge
  DefectBridge AuxiliaryBridge ActualTailBridge HDeletionBridge
  RigidBridge StrongDualBridge XHDeletionBridge D501Bridge
open ActualTail SatTail HDeletion Rigid StrongDual APRigid

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

set_option maxHeartbeats 6000000 in
/-- The reduced capacity-two-through-five certificate cover is bundled so
the large case bridge carries one hypothesis rather than scanning two dozen
irrelevant universal hypotheses in every arithmetic subgoal. -/
structure ReducedCertificates where
  broadAlphaZero : ∀ raw pToZ : Nat → Nat → Bool,
    broadRigidXAlphaZeroLeaf raw pToZ = false
  positiveDelta : ∀ arc pToZ : Nat → Nat → Bool,
    reducedPositiveDeltaLeaf arc pToZ = false
  noEligibleModes : ∀ mode : BitVec 2, ∀ raw pToZ : Nat → Nat → Bool,
    noEligibleModeLeaf mode raw pToZ = false
  positiveAlphaRange : ∀ raw pToZ : Nat → Nat → Bool,
    aRigidPositiveAlphaRange raw pToZ = false

set_option maxHeartbeats 6000000 in
theorem contradiction
    (hEasy04 : ∀ arc pToZ : Nat → Nat → Bool,
      commonCore 0 4 arc pToZ = false)
    (hEasy12 : ∀ arc pToZ : Nat → Nat → Bool,
      reachedTwoDirectCore arc pToZ = false)
    (hReduced : ReducedCertificates)
    (hCOne : ∀ arc pToZ auxArc extraAuxArc : Nat → Nat → Bool,
      ∀ outsideCount : BitVec 5, ∀ outsidePrivateLoss : Nat → BitVec 5,
      ∀ pathCount : Nat → BitVec 5, ∀ namedSecondCount : BitVec 5,
      satC1Leaf arc pToZ auxArc extraAuxArc outsideCount outsidePrivateLoss
        pathCount namedSecondCount = false)
    (hCompactC6 : ∀ arc pToZ auxArc realAuxArc : Nat → Nat → Bool,
      CompactActualTail.compactCapacityRangeLeaf 6 0 4
        arc pToZ auxArc realAuxArc = false)
    (hD501Positive : ∀ raw pToZ : Nat → Nat → Bool,
      D501Positive.d501PositiveLeaf raw pToZ = false)
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3) (hr : C.r = 6)
    (hx : C.x = 4)
    (hyz : (BSevenKThree.y G C = 0 ∧
        ((externalTargets G C).card = 3 ∨ (externalTargets G C).card = 4)) ∨
      (BSevenKThree.y G C = 1 ∧
        ((externalTargets G C).card = 2 ∨ (externalTargets G C).card = 3))) : False := by
  have hPCard : C.P.card = 6 := hr
  have hACard : C.A.card = 8 := by
    simpa [Digraph.LocalConfiguration.A, Digraph.outdegree] using hRootDegree
  have hQCard : C.Q.card = 1 := by
    have h := Digraph.LocalConfiguration.card_B_eq_r_add_card_Q (G := G) C
    omega
  have hAOneCard : C.A1.card = 3 := hk
  have hXCard : C.X.card = 4 := hx
  have hRCard : C.R.card = 0 := by
    have hR := BSixKThree.card_R_eq_four_sub_x G C hG hRootDegree hk
    omega
  have hHCard : C.H.card = 7 := by
    have hH := BSixKThree.H_card_eq_three_add_x G C hk
    omega
  rcases hyz with ⟨hy, hz | hz⟩ | ⟨hy, hz | hz⟩
  · let L := canonicalLabels G 3 C hPCard hACard hQCard hz hAOneCard
      hXCard hRCard
    have hCommon := commonCore_true G C L hG hMin hNoSeymour hRootDegree
      hPivot hHCard hAOneCard hXCard hk hr hx hy (Or.inl rfl)
      (by omega) (Or.inl (by omega))
      (canonicalLabels_p_order G 3 C hPCard hACard hQCard hz hAOneCard hXCard hRCard)
      (canonicalLabels_aOne_order G 3 C hPCard hACard hQCard hz hAOneCard hXCard hRCard)
      (canonicalLabels_x_order G 3 C hPCard hACard hQCard hz hAOneCard hXCard hRCard)
      (canonicalLabels_z_order G 3 C hPCard hACard hQCard hz hAOneCard hXCard hRCard)
    have hCommonParts := hCommon
    simp only [commonCore, Bool.and_eq_true] at hCommonParts
    have hACond : aConditions (graphArc G L) = true :=
      hCommonParts.1.1.1.1.1.1.1.1.1.1.1.1.2
    have hDual : degreeAndDualConditions 0 (graphArc G L) = true :=
      hCommonParts.1.1.1.1.1.1.2
    have hQReach : qReachStatus 0 (graphArc G L) = true :=
      hCommonParts.1.1.1.1.1.1.1.1.1.1.1.1.1.2
    have hAnyA : any 3 (fun a ↦ aToQ (graphArc G L) (1 + a)) = false := by
      cases hAny : any 3 (fun a ↦ aToQ (graphArc G L) (1 + a)) with
      | false => rfl
      | true => simp [qReachStatus, hAny] at hQReach
    have hAOneQFalse (i : Nat) (hi : i < 3) :
        aToQ (graphArc G L) (1 + i) = false := by
      by_contra hTrue
      have hBit : aToQ (graphArc G L) (1 + i) = true :=
        Bool.eq_true_of_not_eq_false hTrue
      have hExists : any 3 (fun a ↦ aToQ (graphArc G L) (1 + a)) = true :=
        (any_eq_true_iff 3 _).mpr ⟨i, hi, hBit⟩
      rw [hAnyA] at hExists
      contradiction
    have hDelta := aMissing_toNat_le_four G C L hG hACond
    have hQDefect : (hQDefect 0 (graphArc G L)).toNat ≤ 4 := by
      have hCount : (totalHToQ (graphArc G L)).toNat ≤ 4 := by
        rw [totalHToQ, toNat_count_eq_fin_sum 7 _ (by omega)]
        calc
          _ ≤ ∑ i : Fin 7, if i.val < 3 then 0 else 1 := by
            apply Finset.sum_le_sum
            intro i hi
            by_cases hiThree : i.val < 3
            · simp [hiThree, hAOneQFalse i.val hiThree]
            · simp only [hiThree, ↓reduceIte]
              split <;> omega
          _ = 4 := by decide
      rw [Core.hQDefect, BitVec.toNat_sub]
      norm_num [BitVec.toNat_ofNat]
      omega
    have hLower := hDual
    simp only [degreeAndDualConditions, Bool.and_eq_true,
      BitVec.ule_eq_decide, decide_eq_true_eq] at hLower
    have hHP := hLower.1.1
    rw [totalHToP_toNat G C L hHCard] at hHP
    simp only [BitVec.toNat_add, BitVec.toNat_mul] at hHP
    norm_num [BitVec.toNat_ofNat] at hHP
    have hTwo : (2 : BitVec 8).toNat = 2 := by decide
    rw [hTwo, Nat.mod_eq_of_lt (by omega)] at hHP
    have hPCap := BSevenKTwo.P_degree_capacity_r_six G C hG hMin hr
    have hAuxCap := edgeCount_le_card_mul_card G C.P (auxiliarySet G C)
    have hAuxCard := auxiliarySet_card G C L 0 hy (Or.inl rfl)
    have hAuxEq := edgeCount_P_auxiliary_eq G C
    rw [hPCard, hAuxCard, hAuxEq] at hAuxCap
    omega
  · let L := canonicalLabels G 4 C hPCard hACard hQCard hz hAOneCard
      hXCard hRCard
    have hCommon := commonCore_true G C L hG hMin hNoSeymour hRootDegree
      hPivot hHCard hAOneCard hXCard hk hr hx hy (Or.inl rfl)
      (by omega) (Or.inr (by omega))
      (canonicalLabels_p_order G 4 C hPCard hACard hQCard hz hAOneCard hXCard hRCard)
      (canonicalLabels_aOne_order G 4 C hPCard hACard hQCard hz hAOneCard hXCard hRCard)
      (canonicalLabels_x_order G 4 C hPCard hACard hQCard hz hAOneCard hXCard hRCard)
      (canonicalLabels_z_order G 4 C hPCard hACard hQCard hz hAOneCard hXCard hRCard)
    rw [hEasy04 (graphArc G L) (graphPToZ G L)] at hCommon
    contradiction
  · let L := canonicalLabels G 2 C hPCard hACard hQCard hz hAOneCard
      hXCard hRCard
    have hCommon := commonCore_true G C L hG hMin hNoSeymour hRootDegree
      hPivot hHCard hAOneCard hXCard hk hr hx hy (Or.inr rfl)
      (by omega) (Or.inl (by omega))
      (canonicalLabels_p_order G 2 C hPCard hACard hQCard hz hAOneCard hXCard hRCard)
      (canonicalLabels_aOne_order G 2 C hPCard hACard hQCard hz hAOneCard hXCard hRCard)
      (canonicalLabels_x_order G 2 C hPCard hACard hQCard hz hAOneCard hXCard hRCard)
      (canonicalLabels_z_order G 2 C hPCard hACard hQCard hz hAOneCard hXCard hRCard)
    have hDirect := ReachedCountsBridge.reachedTwoDirectCore_true_of_common
      G C L hG hMin hHCard hy hCommon
    rw [hEasy12 (graphArc G L) (graphPToZ G L)] at hDirect
    contradiction
  · let L := canonicalLabels G 3 C hPCard hACard hQCard hz hAOneCard
      hXCard hRCard
    have hPOrder := canonicalLabels_p_order G 3 C hPCard hACard hQCard hz
      hAOneCard hXCard hRCard
    have hCommon := commonCore_true G C L hG hMin hNoSeymour hRootDegree
      hPivot hHCard hAOneCard hXCard hk hr hx hy (Or.inr rfl)
      (by omega) (Or.inr (by omega)) hPOrder
      (canonicalLabels_aOne_order G 3 C hPCard hACard hQCard hz hAOneCard hXCard hRCard)
      (canonicalLabels_x_order G 3 C hPCard hACard hQCard hz hAOneCard hXCard hRCard)
      (canonicalLabels_z_order G 3 C hPCard hACard hQCard hz hAOneCard hXCard hRCard)
    have hACond := commonCore_aConditions_true G L hCommon
    have hDual := commonCore_degreeAndDual_true G L hCommon
    have hCapLeTrue := capacityDefect_le_six_true G C L hG hMin hHCard
      hy hACond hDual
    have hCapLe : (capacityDefect (graphArc G L) (graphPToZ G L)).toNat ≤ 6 := by
      simp only [BitVec.ule_eq_decide, decide_eq_true_eq] at hCapLeTrue
      have hSix : (6 : BitVec 8).toNat = 6 := by decide
      simpa [hSix] using hCapLeTrue
    let capacity := (capacityDefect (graphArc G L) (graphPToZ G L)).toNat
    have hHDeletion := hQDeletionConditions_true G hBound C L hG hNoSeymour
    by_cases hCapacityZero : capacity = 0
    · have hComponents := capacityDefect_toNat_eq_components G C L hG hMin
        hHCard hy hACond hDual
      change capacity =
        (externalMissing 1 3 (graphArc G L) (graphPToZ G L)).toNat +
          2 * (aMissing (graphArc G L)).toNat +
          (alpha 1 (graphArc G L) +
            internalMissing (graphArc G L)).toNat at hComponents
      have hDefectAdd := internalDefect_toNat_eq_add G C L hG hHCard
        hACond hDual
      have hmNat :
          (externalMissing 1 3 (graphArc G L) (graphPToZ G L)).toNat = 0 := by
        omega
      have hDeltaNat : (aMissing (graphArc G L)).toNat = 0 := by omega
      have hDefectNat :
          (alpha 1 (graphArc G L) +
            internalMissing (graphArc G L)).toNat = 0 := by
        omega
      have hAlphaNat : (alpha 1 (graphArc G L)).toNat = 0 := by
        rw [hDefectAdd] at hDefectNat
        omega
      have hBetaNat : (internalMissing (graphArc G L)).toNat = 0 := by
        rw [hDefectAdd] at hDefectNat
        omega
      have hm : externalMissing 1 3 (graphArc G L) (graphPToZ G L) = 0 := by
        apply BitVec.eq_of_toNat_eq
        simpa using hmNat
      have hDelta : aMissing (graphArc G L) = 0 := by
        apply BitVec.eq_of_toNat_eq
        simpa using hDeltaNat
      have hAlpha : alpha 1 (graphArc G L) = 0 := by
        apply BitVec.eq_of_toNat_eq
        simpa using hAlphaNat
      have hBeta : internalMissing (graphArc G L) = 0 := by
        apply BitVec.eq_of_toNat_eq
        simpa using hBetaNat
      have hRigid := rigidArc_graph_eq G C L hG hHCard hACond hDual
        hAlpha hDelta
      have hXDelete := xQDeletionConditions_true_of_hQDeletionConditions_true
        (graphArc G L) (graphPToZ G L) hHDeletion
      have hLeaf : broadRigidXAlphaZeroLeaf (graphArc G L)
          (graphPToZ G L) = true := by
        simp [broadRigidXAlphaZeroLeaf, hRigid, hCommon, hXDelete, hDelta,
          hAlpha]
      rw [hReduced.broadAlphaZero (graphArc G L) (graphPToZ G L)] at hLeaf
      contradiction
    · have hCapacityPositive : 1 ≤ capacity := by omega
      have hCapacityLe : capacity ≤ 6 := hCapLe
      have hNotReduced : ¬(2 ≤ capacity ∧ capacity ≤ 5) := by
        intro hRange
        exact ReducedCapacityFinalBridge.contradiction G hReduced.broadAlphaZero
          hReduced.positiveDelta hReduced.noEligibleModes
          hReduced.positiveAlphaRange C L hG hMin hHCard hy
          hCommon hHDeletion hACond hDual hRange.1 hRange.2
      have hCapacityCases : capacity = 1 ∨ capacity = 6 := by omega
      let p : Fin 6 := ⟨6 - capacity, by omega⟩
      let outside := graphOutsideArc G C L (outsideSecondSet G C L p)
      have hLeaf := actualCapacityLeaf_true G hBound C L hG hMin hNoSeymour
        hHCard hy hAOneCard hXCard hPOrder hCommon capacity
        hCapacityPositive hCapacityLe rfl
      have hLeaf' : actualCapacityLeaf capacity (graphArc G L) (graphPToZ G L)
          (graphAuxArc G C L hMin) (graphRealAuxArc G C L) outside = true := by
        simpa [p, outside] using hLeaf
      have hMLe := externalMissing_le_capacityDefect G C L hG hMin hHCard
        hy hACond hDual
      change (externalMissing 1 3 (graphArc G L) (graphPToZ G L)).toNat ≤
        capacity at hMLe
      let m := (externalMissing 1 3 (graphArc G L) (graphPToZ G L)).toNat
      let delta := (aMissing (graphArc G L)).toNat
      let defect :=
        (alpha 1 (graphArc G L) + internalMissing (graphArc G L)).toNat
      let alphaValue := (alpha 1 (graphArc G L)).toNat
      let betaValue := (internalMissing (graphArc G L)).toNat
      have hComponents := capacityDefect_toNat_eq_components G C L hG hMin
        hHCard hy hACond hDual
      change capacity = m + 2 * delta + defect at hComponents
      have hDefectAdd := internalDefect_toNat_eq_add G C L hG hHCard
        hACond hDual
      change defect = alphaValue + betaValue at hDefectAdd
      have componentEqualities (mValue deltaValue alphaExact betaExact : Nat)
          (hm : m = mValue) (hDelta : delta = deltaValue)
          (hAlpha : alphaValue = alphaExact) (hBeta : betaValue = betaExact) :
          externalMissing 1 3 (graphArc G L) (graphPToZ G L) =
              BitVec.ofNat 8 mValue ∧
            aMissing (graphArc G L) = BitVec.ofNat 8 deltaValue ∧
            alpha 1 (graphArc G L) = BitVec.ofNat 8 alphaExact ∧
            internalMissing (graphArc G L) = BitVec.ofNat 8 betaExact := by
        constructor
        · apply BitVec.eq_of_toNat_eq
          rw [← hm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        constructor
        · apply BitVec.eq_of_toNat_eq
          rw [← hDelta, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        constructor
        · apply BitVec.eq_of_toNat_eq
          rw [← hAlpha, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        · apply BitVec.eq_of_toNat_eq
          rw [← hBeta, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have broadAlphaZeroContradiction
          (hDeltaZero : delta = 0) (hAlphaZero : alphaValue = 0) : False := by
        have hParts := componentEqualities m 0 0 betaValue rfl hDeltaZero
          hAlphaZero rfl
        have hRigid := rigidArc_graph_eq G C L hG hHCard hACond hDual
          hParts.2.2.1 hParts.2.1
        have hXDelete := xQDeletionConditions_true_of_hQDeletionConditions_true
          (graphArc G L) (graphPToZ G L) hHDeletion
        have hBroad : broadRigidXAlphaZeroLeaf (graphArc G L)
            (graphPToZ G L) = true := by
          simp [broadRigidXAlphaZeroLeaf, hRigid, hCommon, hXDelete,
            hParts.2.1, hParts.2.2.1]
        rw [hReduced.broadAlphaZero (graphArc G L) (graphPToZ G L)] at hBroad
        contradiction
      have hTail : actualTailCore (6 - capacity) (graphArc G L) (graphPToZ G L)
          (graphAuxArc G C L hMin) (graphRealAuxArc G C L) outside = true := by
        have hParts := hLeaf'
        simp only [actualCapacityLeaf, Bool.and_eq_true, beq_iff_eq] at hParts
        exact hParts.2
      have defectLeaf (mValue deltaValue defectValue : Nat)
          (hm : m = mValue) (hDelta : delta = deltaValue)
          (hDefect : defect = defectValue) :
          actualDefectLeaf mValue deltaValue defectValue (graphArc G L)
            (graphPToZ G L) (graphAuxArc G C L hMin) (graphRealAuxArc G C L)
            outside = true := by
        have hmBV : externalMissing 1 3 (graphArc G L) (graphPToZ G L) =
            BitVec.ofNat 8 mValue := by
          apply BitVec.eq_of_toNat_eq
          rw [← hm]
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        have hDeltaBV : aMissing (graphArc G L) = BitVec.ofNat 8 deltaValue := by
          apply BitVec.eq_of_toNat_eq
          rw [← hDelta]
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        have hDefectBV : alpha 1 (graphArc G L) + internalMissing (graphArc G L) =
            BitVec.ofNat 8 defectValue := by
          apply BitVec.eq_of_toNat_eq
          rw [← hDefect]
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        unfold actualDefectLeaf
        simp only [Bool.and_eq_true, beq_iff_eq]
        refine ⟨⟨⟨⟨hCommon, hmBV⟩, hDeltaBV⟩, hDefectBV⟩, ?_⟩
        have hSum : mValue + 2 * deltaValue + defectValue = capacity := by omega
        simpa [hSum] using hTail
      rcases hCapacityCases with hc | hc
      · have hCapacityOne :
            capacityDefect (graphArc G L) (graphPToZ G L) = 1 := by
          apply BitVec.eq_of_toNat_eq
          simpa [capacity] using hc
        have hExternalOne :
            (externalMissing 1 3 (graphArc G L) (graphPToZ G L)).ule 1 = true := by
          simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
          simpa [m, hc] using hMLe
        have hStructural := capacityOneStructuralCuts (graphArc G L)
          (graphPToZ G L) hCapacityOne hExternalOne
        simp only [Bool.and_eq_true] at hStructural
        have hPivotCut := hStructural.1
        have hDegreeCut :
            c1DegreeSumCut (graphArc G L) (graphPToZ G L) = true := by
          simpa using hStructural.2
        have hDeltaZero : delta = 0 := by omega
        have hDefectLe : defect ≤ 1 := by omega
        have hComponentSum : m + defect = 1 := by omega
        have hDeltaBV : aMissing (graphArc G L) = 0 := by
          apply BitVec.eq_of_toNat_eq
          simpa [delta] using hDeltaZero
        have hDefectBV :
            alpha 1 (graphArc G L) + internalMissing (graphArc G L) =
              BitVec.ofNat 8 defect := by
          apply BitVec.eq_of_toNat_eq
          simp [defect]
        have hmBV :
            externalMissing 1 3 (graphArc G L) (graphPToZ G L) =
              BitVec.ofNat 8 m := by
          apply BitVec.eq_of_toNat_eq
          simp [m]
        have hSumBV :
            externalMissing 1 3 (graphArc G L) (graphPToZ G L) +
                alpha 1 (graphArc G L) + internalMissing (graphArc G L) = 1 := by
          rw [show externalMissing 1 3 (graphArc G L) (graphPToZ G L) +
                alpha 1 (graphArc G L) + internalMissing (graphArc G L) =
              externalMissing 1 3 (graphArc G L) (graphPToZ G L) +
                (alpha 1 (graphArc G L) + internalMissing (graphArc G L)) by
                bv_decide]
          rw [hmBV, hDefectBV, ← BitVec.ofNat_add]
          simp [hComponentSum]
        have hTailFive : actualTailCore 5 (graphArc G L) (graphPToZ G L)
            (graphAuxArc G C L hMin) (graphRealAuxArc G C L) outside = true := by
          simpa [hc] using hTail
        have hSatTail := actualTailCore_implies_satTailCore
          (graphArc G L) (graphPToZ G L) (graphAuxArc G C L hMin)
          (graphRealAuxArc G C L) outside hCommon hTailFive
        have hDefectOne :
            (alpha 1 (graphArc G L) + internalMissing (graphArc G L)).ule 1 = true := by
          simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
          simpa [defect, BitVec.toNat_add] using hDefectLe
        have hSatLeaf : satC1Leaf (graphArc G L) (graphPToZ G L)
            (graphAuxArc G C L hMin) (graphRealAuxArc G C L)
            (actualOutsideCount5 (graphArc G L) (graphPToZ G L) outside 5)
            (actualOutsidePrivateLoss5 (graphArc G L) (graphPToZ G L) outside 5)
            (actualPathCount5 (graphArc G L) (graphPToZ G L)
              (combinedAuxArc (graphAuxArc G C L hMin) (graphRealAuxArc G C L)) 5)
            (actualNamedSecondCount5 (graphArc G L) (graphPToZ G L)
              (combinedAuxArc (graphAuxArc G C L hMin) (graphRealAuxArc G C L)) 5) =
              true := by
          simp only [satC1Leaf, satCapacityRangeLeaf, hCommon, hCapacityOne,
            BitVec.ofNat_eq_ofNat, BEq.rfl, Bool.and_self, Nat.add_one_sub_one,
            hSatTail, Bool.true_and, hDeltaBV, Bool.and_true, hSumBV,
            hPivotCut, hDegreeCut, Bool.and_eq_true]
          exact ⟨⟨by simp [BitVec.ule_eq_decide], hExternalOne⟩, hDefectOne⟩
        rw [hCOne _ _ _ _ _ _ _ _] at hSatLeaf
        contradiction
      · rw [hc] at hLeaf'
        by_cases hmFour : m ≤ 4
        · have hCompactTail := CompactActualTail.of_actualTailCore
            (6 - capacity) (graphArc G L) (graphPToZ G L)
            (graphAuxArc G C L hMin) (graphRealAuxArc G C L) outside hTail
          have hCapacitySix :
              capacityDefect (graphArc G L) (graphPToZ G L) = 6 := by
            apply BitVec.eq_of_toNat_eq
            simpa [capacity] using hc
          have hCompactLeaf : CompactActualTail.compactCapacityRangeLeaf 6 0 4
              (graphArc G L) (graphPToZ G L) (graphAuxArc G C L hMin)
              (combinedAuxArc (graphAuxArc G C L hMin)
                (graphRealAuxArc G C L)) = true := by
            have hCompactTailSix : CompactActualTail.compactActualTailCore 0
                (graphArc G L) (graphPToZ G L) (graphAuxArc G C L hMin)
                (combinedAuxArc (graphAuxArc G C L hMin)
                  (graphRealAuxArc G C L)) = true := by
              simpa [hc] using hCompactTail
            unfold CompactActualTail.compactCapacityRangeLeaf
            rw [hCommon, hCapacitySix, hCompactTailSix]
            simp only [BitVec.ofNat_eq_ofNat, BEq.rfl, Bool.true_and,
              Bool.and_eq_true, BitVec.ule_eq_decide, decide_eq_true_eq]
            constructor
            · simp
            · simpa [m] using hmFour
          rw [hCompactC6 _ _ _ _] at hCompactLeaf
          contradiction
        · have hm : 5 ≤ m := by omega
          have hDelta : delta = 0 := by omega
          have hAlphaCases : alphaValue = 0 ∨ 1 ≤ alphaValue := by omega
          rcases hAlphaCases with hAlpha | hAlpha
          · exact broadAlphaZeroContradiction hDelta hAlpha
          · have hmFive : m = 5 := by omega
            have hAlphaOne : alphaValue = 1 := by omega
            have hBetaZero : betaValue = 0 := by omega
            have hParts := componentEqualities 5 0 1 0 hmFive hDelta
              hAlphaOne hBetaZero
            exact d501Positive_contradiction G hD501Positive C L hG hHCard
              hCommon hHDeletion hACond hDual hParts.1 hParts.2.1
              hParts.2.2.1 hParts.2.2.2

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.CaseBridge
