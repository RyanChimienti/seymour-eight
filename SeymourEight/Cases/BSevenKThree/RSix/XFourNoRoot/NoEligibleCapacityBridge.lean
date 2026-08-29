import SeymourEight.Cases.BSevenKThree.RSix.XFourNoRoot.LowEligibilityBridge
import SeymourEight.Cases.BSevenKThree.RSix.XFourNoRoot.StrongDualBridge
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.NoEligibleDefs

set_option linter.style.header false
set_option maxRecDepth 20000

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.NoEligibleCapacityBridge

open Shared Labels Encoding Core GraphFacts DefectBridge ActualTailBridge
  RigidBridge StrongDualBridge
open StrongDual Rigid APRigid

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

-- The exact four-way residual classification.
set_option maxHeartbeats 1000000 in
theorem contradiction
    (hModes : ∀ mode : BitVec 2, ∀ raw pToZ : Nat → Nat → Bool,
      noEligibleModeLeaf mode raw pToZ = false)
    (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hHCard : C.H.card = 7)
    (hy : BSevenKThree.y G C = 1)
    (hCommon : commonCore 1 3 (graphArc G L) (graphPToZ G L) = true)
    (hA : aConditions (graphArc G L) = true)
    (hDual : degreeAndDualConditions 1 (graphArc G L) = true)
    (hCapacityLow : 2 ≤ (capacityDefect (graphArc G L)
      (graphPToZ G L)).toNat)
    (hCapacityHigh : (capacityDefect (graphArc G L)
      (graphPToZ G L)).toNat ≤ 5)
    (hEligibleZero : eligibleHCount (graphArc G L) = 0)
    (hDeltaZero : (aMissing (graphArc G L)).toNat = 0) : False := by
  let capacity := (capacityDefect (graphArc G L) (graphPToZ G L)).toNat
  let m := (externalMissing 1 3 (graphArc G L) (graphPToZ G L)).toNat
  let delta := (aMissing (graphArc G L)).toNat
  let alphaValue := (alpha 1 (graphArc G L)).toNat
  let betaValue := (internalMissing (graphArc G L)).toNat
  change 2 ≤ capacity at hCapacityLow
  change capacity ≤ 5 at hCapacityHigh
  have hComponents := capacityDefect_toNat_eq_components G C L hG hMin
    hHCard hy hA hDual
  change capacity = m + 2 * delta +
    (alpha 1 (graphArc G L) + internalMissing (graphArc G L)).toNat at hComponents
  have hDefectAdd := internalDefect_toNat_eq_add G C L hG hHCard hA hDual
  change (alpha 1 (graphArc G L) + internalMissing (graphArc G L)).toNat =
    alphaValue + betaValue at hDefectAdd
  rw [hDefectAdd] at hComponents
  by_cases hLow : capacity ≤ 3
  · exact (LowEligibilityBridge.eligibleHCount_ne_zero_of_capacity_le_three
      G C L hG hMin hHCard hy hA hDual hLow) hEligibleZero
  · have hDeltaAlpha : 4 ≤ delta + alphaValue := by
      by_contra hNot
      have hAtMostThree : delta + alphaValue ≤ 3 := by omega
      exact (LowEligibilityBridge.eligibleHCount_ne_zero_of_delta_add_alpha_le_three
          G C L hG hHCard hA hDual hAtMostThree) hEligibleZero
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
    have hCapacityCases : capacity = 4 ∨ capacity = 5 := by omega
    rcases hCapacityCases with hc | hc
    · have hParts := componentEqualities 0 0 4 0 (by omega) (by omega)
          (by omega) (by omega)
      have hAArc := aRigidArc_graph_eq G C L hG hParts.2.1
      have hPArc := pRigidArc_graph_eq G C L hG hParts.2.2.2
      have hLeaf : noEligibleModeLeaf 0 (graphArc G L)
          (graphPToZ G L) = true := by
        simp [noEligibleModeLeaf, hPArc, hAArc, hCommon, hParts.1,
          hParts.2.1, hParts.2.2.1, hParts.2.2.2, hEligibleZero]
      rw [hModes 0 _ _] at hLeaf
      contradiction
    · have hCases :
          (m = 1 ∧ delta = 0 ∧ alphaValue = 4 ∧ betaValue = 0) ∨
          (m = 0 ∧ delta = 0 ∧ alphaValue = 4 ∧ betaValue = 1) ∨
          (m = 0 ∧ delta = 0 ∧ alphaValue = 5 ∧ betaValue = 0) := by
        change delta = 0 at hDeltaZero
        omega
      rcases hCases with hCase | hCase | hCase
      · have hParts := componentEqualities 1 0 4 0 hCase.1 hCase.2.1
            hCase.2.2.1 hCase.2.2.2
        have hAArc := aRigidArc_graph_eq G C L hG hParts.2.1
        have hPArc := pRigidArc_graph_eq G C L hG hParts.2.2.2
        have hLeaf : noEligibleModeLeaf 1 (graphArc G L)
            (graphPToZ G L) = true := by
          simp [noEligibleModeLeaf, hPArc, hAArc, hCommon, hParts.1,
            hParts.2.1, hParts.2.2.1, hParts.2.2.2, hEligibleZero]
        rw [hModes 1 _ _] at hLeaf
        contradiction
      · have hParts := componentEqualities 0 0 4 1 hCase.1 hCase.2.1
          hCase.2.2.1 hCase.2.2.2
        have hAArc := aRigidArc_graph_eq G C L hG hParts.2.1
        have hLeaf : noEligibleModeLeaf 2 (graphArc G L)
            (graphPToZ G L) = true := by
          simp [noEligibleModeLeaf, hAArc, hCommon, hParts.1,
            hParts.2.1, hParts.2.2.1,
            hParts.2.2.2, hEligibleZero]
        rw [hModes 2 _ _] at hLeaf
        contradiction
      · have hParts := componentEqualities 0 0 5 0 hCase.1 hCase.2.1
            hCase.2.2.1 hCase.2.2.2
        have hAArc := aRigidArc_graph_eq G C L hG hParts.2.1
        have hPArc := pRigidArc_graph_eq G C L hG hParts.2.2.2
        have hLeaf : noEligibleModeLeaf 3 (graphArc G L)
            (graphPToZ G L) = true := by
          simp [noEligibleModeLeaf, hPArc, hAArc, hCommon, hParts.1,
            hParts.2.1, hParts.2.2.1, hParts.2.2.2, hEligibleZero]
        rw [hModes 3 _ _] at hLeaf
        contradiction

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.NoEligibleCapacityBridge
