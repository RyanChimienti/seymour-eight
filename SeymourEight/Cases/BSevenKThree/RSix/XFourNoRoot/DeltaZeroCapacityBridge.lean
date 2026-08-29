import SeymourEight.Cases.BSevenKThree.RSix.XFourNoRoot.RigidBridge
import SeymourEight.Cases.BSevenKThree.RSix.XFourNoRoot.ReducedCapacityAssemblyBridge
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.PositiveAlphaRangeDefs

set_option linter.style.header false
set_option maxRecDepth 20000

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.DeltaZeroCapacityBridge

open Shared Labels Encoding Core GraphFacts DefectBridge RigidBridge
  ReducedCapacityAssemblyBridge ActualTailBridge Assembly
open HDeletion Rigid StrongDual

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

set_option maxHeartbeats 10000000 in
/-- The direct eligible-capacity cut makes every positive-alpha, delta-zero
capacity branch one Boolean range problem. -/
theorem contradiction
    (hRange : ∀ raw pToZ : Nat → Nat → Bool,
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
      (graphPToZ G L)).toNat ≤ 5)
    (hDelta : aMissing (graphArc G L) = 0)
    (hAlphaPositive : (1 : BitVec 8).ule (alpha 1 (graphArc G L)) = true)
    (hEligible : (1 : BitVec 8).ule
      (eligibleHCount (graphArc G L)) = true) : False := by
  let capacity := (capacityDefect (graphArc G L) (graphPToZ G L)).toNat
  let m := (externalMissing 1 3 (graphArc G L) (graphPToZ G L)).toNat
  let alphaValue := (alpha 1 (graphArc G L)).toNat
  let betaValue := (internalMissing (graphArc G L)).toNat
  change 2 ≤ capacity at hCapacityLow
  change capacity ≤ 5 at hCapacityHigh
  have hComponents := capacityDefect_toNat_eq_components G C L hG hMin
    hHCard hy hA hDual
  change capacity = m + 2 * (aMissing (graphArc G L)).toNat +
    (alpha 1 (graphArc G L) + internalMissing (graphArc G L)).toNat at hComponents
  have hDefectAdd := internalDefect_toNat_eq_add G C L hG hHCard hA hDual
  change (alpha 1 (graphArc G L) + internalMissing (graphArc G L)).toNat =
    alphaValue + betaValue at hDefectAdd
  rw [hDefectAdd] at hComponents
  have hDeltaNat : (aMissing (graphArc G L)).toNat = 0 := by simp [hDelta]
  have hCapacitySmall : capacity < 256 := by omega
  have hCapacityBV : capacityDefect (graphArc G L) (graphPToZ G L) =
      BitVec.ofNat 8 capacity := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hCapacitySmall]
  have hCapacityRange : capacityTwoToFive (graphArc G L)
      (graphPToZ G L) = true := by
    simp only [capacityTwoToFive, Bool.and_eq_true, BitVec.ule_eq_decide,
      decide_eq_true_eq, hCapacityBV]
    norm_num [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hCapacitySmall]
    exact ⟨hCapacityLow, hCapacityHigh⟩
  have hAlphaPos : 1 ≤ alphaValue := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq] at hAlphaPositive
    exact hAlphaPositive
  have hAlphaLe : alphaValue ≤ 5 := by omega
  have hBetaLe : betaValue ≤ 5 := by omega
  have hMLe : m ≤ 5 := by omega
  have hExternal : externalMissing 1 3 (graphArc G L) (graphPToZ G L) =
      BitVec.ofNat 8 m := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : m < 256)]
  have hAlpha : alpha 1 (graphArc G L) = BitVec.ofNat 8 alphaValue := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : alphaValue < 256)]
  have hBeta : internalMissing (graphArc G L) = BitVec.ofNat 8 betaValue := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : betaValue < 256)]
  have hARigid := aRigidArc_graph_eq G C L hG hDelta
  have hBase := aRigidPositiveSlice_true_of_values 1 5 0 5 0 5
    alphaValue betaValue m (graphArc G L) (graphPToZ G L) hARigid hCommon
    hDelete hCapacityRange hDelta hAlpha hBeta hExternal hAlphaPos hAlphaLe
    (by omega) hBetaLe (by omega) hMLe (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by omega) (by omega) (by omega)
    hEligible
  have hFixed := fixedAOne_true G C L hG
  have hOut : aOut (graphArc G L) 0 = 3 :=
    aOut_zero_eq_three_of_fixed hFixed
  have hCut : eligibleCapacityCut (graphArc G L) = true := by
    have hConsequence := eligibleCapacityConsequence_true (graphArc G L)
    simpa [eligibleCapacityConsequence, hOut, hA] using hConsequence
  have hRigidCut : eligibleCapacityCut (aRigidArc (graphArc G L)) = true := by
    rw [hARigid]
    exact hCut
  have hLeaf : aRigidPositiveAlphaRange (graphArc G L)
      (graphPToZ G L) = true := by
    simp [aRigidPositiveAlphaRange, hBase, hRigidCut]
  rw [hRange _ _] at hLeaf
  contradiction

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.DeltaZeroCapacityBridge
