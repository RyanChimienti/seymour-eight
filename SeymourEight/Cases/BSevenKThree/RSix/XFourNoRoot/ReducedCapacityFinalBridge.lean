import SeymourEight.Cases.BSevenKThree.RSix.XFourNoRoot.NoEligibleCapacityBridge
import SeymourEight.Cases.BSevenKThree.RSix.XFourNoRoot.DeltaZeroCapacityBridge
import SeymourEight.Cases.BSevenKThree.RSix.XFourNoRoot.XHDeletionBridge
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.BroadRigidXDefs
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.NoEligibleDefs
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.ReducedPositiveDeltaDefs

set_option linter.style.header false
set_option maxRecDepth 20000

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.ReducedCapacityFinalBridge

open Shared Labels Encoding Core GraphFacts DefectBridge ActualTailBridge
  RigidBridge XHDeletionBridge
open HDeletion Rigid StrongDual APRigid

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem contradiction
    (hBroad : ∀ raw pToZ : Nat → Nat → Bool,
      broadRigidXAlphaZeroLeaf raw pToZ = false)
    (hPositiveDelta : ∀ arc pToZ : Nat → Nat → Bool,
      reducedPositiveDeltaLeaf arc pToZ = false)
    (hNoEligibleModes : ∀ mode : BitVec 2,
      ∀ raw pToZ : Nat → Nat → Bool,
      noEligibleModeLeaf mode raw pToZ = false)
    (hPositiveAlphaRange : ∀ raw pToZ : Nat → Nat → Bool,
      aRigidPositiveAlphaRange raw pToZ = false)
    (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hHCard : C.H.card = 7)
    (hy : BSevenKThree.y G C = 1)
    (hCommon : commonCore 1 3 (graphArc G L) (graphPToZ G L) = true)
    (hDelete : hQDeletionConditions (graphArc G L) (graphPToZ G L) = true)
    (hA : aConditions (graphArc G L) = true)
    (hDual : degreeAndDualConditions 1 (graphArc G L) = true)
    (hCapacityLow : 2 ≤ (capacityDefect (graphArc G L)
      (graphPToZ G L)).toNat)
    (hCapacityHigh : (capacityDefect (graphArc G L)
      (graphPToZ G L)).toNat ≤ 5) : False := by
  let capacity := (capacityDefect (graphArc G L) (graphPToZ G L)).toNat
  let delta := (aMissing (graphArc G L)).toNat
  let alphaValue := (alpha 1 (graphArc G L)).toNat
  change 2 ≤ capacity at hCapacityLow
  change capacity ≤ 5 at hCapacityHigh
  have hComponents := capacityDefect_toNat_eq_components G C L hG hMin
    hHCard hy hA hDual
  change capacity = (externalMissing 1 3 (graphArc G L)
      (graphPToZ G L)).toNat + 2 * delta +
        (alpha 1 (graphArc G L) + internalMissing (graphArc G L)).toNat at hComponents
  have hDeltaLe : delta ≤ 2 := by omega
  by_cases hDeltaZeroNat : delta = 0
  · have hDeltaZero : aMissing (graphArc G L) = 0 := by
      apply BitVec.eq_of_toNat_eq
      simpa [hDeltaZeroNat]
    by_cases hEligibleZero : eligibleHCount (graphArc G L) = 0
    · exact NoEligibleCapacityBridge.contradiction G hNoEligibleModes C L
        hG hMin hHCard hy hCommon hA hDual hCapacityLow
        hCapacityHigh hEligibleZero hDeltaZeroNat
    · have hEligible : (1 : BitVec 8).ule
          (eligibleHCount (graphArc G L)) = true := by
        simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
        change 1 ≤ (eligibleHCount (graphArc G L)).toNat
        have hNe : (eligibleHCount (graphArc G L)).toNat ≠ 0 := by
          intro hz
          apply hEligibleZero
          apply BitVec.eq_of_toNat_eq
          simpa using hz
        omega
      by_cases hAlphaZeroNat : alphaValue = 0
      · have hAlphaZero : alpha 1 (graphArc G L) = 0 := by
          apply BitVec.eq_of_toNat_eq
          simpa [hAlphaZeroNat]
        have hRigid := rigidArc_graph_eq G C L hG hHCard hA hDual
          hAlphaZero hDeltaZero
        have hXDelete := xQDeletionConditions_true_of_hQDeletionConditions_true
          (graphArc G L) (graphPToZ G L) hDelete
        have hLeaf : broadRigidXAlphaZeroLeaf (graphArc G L)
            (graphPToZ G L) = true := by
          simp [broadRigidXAlphaZeroLeaf, hRigid, hCommon, hXDelete,
            hDeltaZero, hAlphaZero]
        rw [hBroad _ _] at hLeaf
        contradiction
      · have hAlphaPositive : (1 : BitVec 8).ule
            (alpha 1 (graphArc G L)) = true := by
          simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
          change 1 ≤ alphaValue
          omega
        exact DeltaZeroCapacityBridge.contradiction G hPositiveAlphaRange C L
          hG hMin hHCard hy hCommon hDelete hA hDual hCapacityLow
          hCapacityHigh hDeltaZero hAlphaPositive hEligible
  · have hDeltaPositive : (1 : BitVec 8).ule
        (aMissing (graphArc G L)) = true := by
      simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
      change 1 ≤ delta
      omega
    have hDeltaUpper : (aMissing (graphArc G L)).ule 2 = true := by
      simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
      change delta ≤ 2
      exact hDeltaLe
    have hCapacityBV : capacityDefect (graphArc G L) (graphPToZ G L) =
        BitVec.ofNat 8 capacity := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hCapacityRange : capacityTwoToFive (graphArc G L)
        (graphPToZ G L) = true := by
      simp only [capacityTwoToFive, Bool.and_eq_true, BitVec.ule_eq_decide,
        decide_eq_true_eq, hCapacityBV]
      norm_num [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : capacity < 256)]
      exact ⟨hCapacityLow, hCapacityHigh⟩
    have hExternalLe : (externalMissing 1 3 (graphArc G L)
        (graphPToZ G L)).ule 5 = true := by
      simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
      change (externalMissing 1 3 (graphArc G L) (graphPToZ G L)).toNat ≤ 5
      omega
    have hDefectLe : (alpha 1 (graphArc G L) +
        internalMissing (graphArc G L)).ule 3 = true := by
      simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
      change (alpha 1 (graphArc G L) +
        internalMissing (graphArc G L)).toNat ≤ 3
      omega
    have hLeaf : reducedPositiveDeltaLeaf (graphArc G L)
        (graphPToZ G L) = true := by
      simp only [reducedPositiveDeltaLeaf, hCommon, hDelete, hCapacityRange,
        Bool.true_and, Bool.and_eq_true]
      exact ⟨⟨⟨hDeltaPositive, hDeltaUpper⟩, hExternalLe⟩, hDefectLe⟩
    rw [hPositiveDelta _ _] at hLeaf
    contradiction

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.ReducedCapacityFinalBridge
