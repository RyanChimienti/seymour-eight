import SeymourEight.Cases.BSevenKThree.RSix.XFourNoRoot.StrongDualBridge

set_option linter.style.header false
set_option maxRecDepth 20000

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.LowEligibilityBridge

open Shared Labels Encoding Core GraphFacts DefectBridge ActualTailBridge
  StrongDualBridge
open StrongDual

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- A scalar-only bit-vector consequence.  In the graph application,
`delta + alpha <= 3` follows from capacity at most three. -/
private theorem eligible_positive_of_low_capacity
    (delta alphaValue eta qDefect cross eligible : BitVec 8)
    (hDelta : delta.ule 4 = true)
    (hAlpha : alphaValue.ule 15 = true)
    (hEta : eta.ule 49 = true)
    (hQ : qDefect.ule 7 = true)
    (hCross : cross.ule 42 = true)
    (hDeltaAlpha : (delta + alphaValue).ule 3 = true)
    (hDual : alphaValue + 3 + 2 * delta =
      eta + delta + qDefect + cross)
    (hEligible : (!(eta + qDefect).ule 7 ||
      (7 - eta - qDefect).ule eligible) = true) :
    (1 : BitVec 8).ule eligible = true := by
  bv_decide

/-- The no-eligible branch forces `delta + alpha >= 4`.  This is the
scalar form used to classify the residual capacity-four and capacity-five
components. -/
theorem eligibleHCount_ne_zero_of_delta_add_alpha_le_three
    (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hHCard : C.H.card = 7)
    (hA : aConditions (graphArc G L) = true)
    (hDual : degreeAndDualConditions 1 (graphArc G L) = true)
    (hDeltaAlpha : (aMissing (graphArc G L)).toNat +
      (alpha 1 (graphArc G L)).toNat ≤ 3) :
    eligibleHCount (graphArc G L) ≠ 0 := by
  let delta := (aMissing (graphArc G L)).toNat
  let alphaValue := (alpha 1 (graphArc G L)).toNat
  have hDeltaNat := aMissing_toNat_le_four G C L hG hA
  change delta ≤ 4 at hDeltaNat
  have hAlphaFormula := alpha_toNat G C L hG hHCard hA hDual
  change alphaValue = 15 - 2 * delta - edgeCount G C.P C.H at hAlphaFormula
  have hAlphaNat : alphaValue ≤ 15 := by omega
  have hDeltaBV : (aMissing (graphArc G L)).ule 4 = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    exact hDeltaNat
  have hAlphaBV : (alpha 1 (graphArc G L)).ule 15 = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    exact hAlphaNat
  have hEtaBV := etaH_le_49_true (graphArc G L) hA
  have hQNat := hQDefect_toNat_le_seven (graphArc G L)
  have hQBV : (hQDefect 1 (graphArc G L)).ule 7 = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    exact hQNat
  have hCrossNat := crossMissing_toNat_le_42 G C L hG hHCard
  have hCrossBV : (crossMissing (graphArc G L)).ule 42 = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    exact hCrossNat
  have hDeltaAlphaBV :
      (aMissing (graphArc G L) + alpha 1 (graphArc G L)).ule 3 = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add]
    rw [Nat.mod_eq_of_lt (by omega : delta + alphaValue < 256)]
    exact hDeltaAlpha
  have hDualParts := hDual
  simp only [degreeAndDualConditions, Bool.and_eq_true] at hDualParts
  have hDualEq : alpha 1 (graphArc G L) + 3 +
      2 * aMissing (graphArc G L) = etaH (graphArc G L) +
        aMissing (graphArc G L) + hQDefect 1 (graphArc G L) +
          crossMissing (graphArc G L) := by
    simpa only [beq_iff_eq] using hDualParts.2
  have hEligibleImp := eligibleConsequence_true (graphArc G L)
  rw [eligibleConsequence, hA, Bool.not_true, Bool.false_or] at hEligibleImp
  intro hZero
  have hPositive := eligible_positive_of_low_capacity
    (aMissing (graphArc G L)) (alpha 1 (graphArc G L))
    (etaH (graphArc G L)) (hQDefect 1 (graphArc G L))
    (crossMissing (graphArc G L)) (eligibleHCount (graphArc G L))
    hDeltaBV hAlphaBV hEtaBV hQBV hCrossBV hDeltaAlphaBV hDualEq hEligibleImp
  rw [hZero] at hPositive
  exact (by decide : ¬(1 : BitVec 8).ule 0 = true) hPositive

theorem eligibleHCount_ne_zero_of_capacity_le_three
    (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hHCard : C.H.card = 7)
    (hy : BSevenKThree.y G C = 1)
    (hA : aConditions (graphArc G L) = true)
    (hDual : degreeAndDualConditions 1 (graphArc G L) = true)
    (hCapacity : (capacityDefect (graphArc G L)
      (graphPToZ G L)).toNat ≤ 3) :
    eligibleHCount (graphArc G L) ≠ 0 := by
  let capacity := (capacityDefect (graphArc G L) (graphPToZ G L)).toNat
  let m := (externalMissing 1 3 (graphArc G L) (graphPToZ G L)).toNat
  let delta := (aMissing (graphArc G L)).toNat
  let alphaValue := (alpha 1 (graphArc G L)).toNat
  let betaValue := (internalMissing (graphArc G L)).toNat
  change capacity ≤ 3 at hCapacity
  have hComponents := capacityDefect_toNat_eq_components G C L hG hMin
    hHCard hy hA hDual
  change capacity = m + 2 * delta +
    (alpha 1 (graphArc G L) + internalMissing (graphArc G L)).toNat at hComponents
  have hDefectAdd := internalDefect_toNat_eq_add G C L hG hHCard hA hDual
  change (alpha 1 (graphArc G L) + internalMissing (graphArc G L)).toNat =
    alphaValue + betaValue at hDefectAdd
  rw [hDefectAdd] at hComponents
  have hDeltaNat := aMissing_toNat_le_four G C L hG hA
  change delta ≤ 4 at hDeltaNat
  have hAlphaFormula := alpha_toNat G C L hG hHCard hA hDual
  change alphaValue = 15 - 2 * delta - edgeCount G C.P C.H at hAlphaFormula
  have hAlphaNat : alphaValue ≤ 15 := by omega
  have hDeltaAlphaNat : delta + alphaValue ≤ 3 := by omega
  have hDeltaBV : (aMissing (graphArc G L)).ule 4 = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    exact hDeltaNat
  have hAlphaBV : (alpha 1 (graphArc G L)).ule 15 = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    exact hAlphaNat
  have hEtaBV := etaH_le_49_true (graphArc G L) hA
  have hQNat := hQDefect_toNat_le_seven (graphArc G L)
  have hQBV : (hQDefect 1 (graphArc G L)).ule 7 = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    exact hQNat
  have hCrossNat := crossMissing_toNat_le_42 G C L hG hHCard
  have hCrossBV : (crossMissing (graphArc G L)).ule 42 = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    exact hCrossNat
  have hDeltaAlphaBV :
      (aMissing (graphArc G L) + alpha 1 (graphArc G L)).ule 3 = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add]
    rw [Nat.mod_eq_of_lt (by omega : delta + alphaValue < 256)]
    exact hDeltaAlphaNat
  have hDualParts := hDual
  simp only [degreeAndDualConditions, Bool.and_eq_true] at hDualParts
  have hDualEq : alpha 1 (graphArc G L) + 3 +
      2 * aMissing (graphArc G L) = etaH (graphArc G L) +
        aMissing (graphArc G L) + hQDefect 1 (graphArc G L) +
          crossMissing (graphArc G L) := by
    simpa only [beq_iff_eq] using hDualParts.2
  have hEligibleImp := eligibleConsequence_true (graphArc G L)
  rw [eligibleConsequence, hA, Bool.not_true, Bool.false_or] at hEligibleImp
  intro hZero
  have hPositive := eligible_positive_of_low_capacity
    (aMissing (graphArc G L)) (alpha 1 (graphArc G L))
    (etaH (graphArc G L)) (hQDefect 1 (graphArc G L))
    (crossMissing (graphArc G L)) (eligibleHCount (graphArc G L))
    hDeltaBV hAlphaBV hEtaBV hQBV hCrossBV hDeltaAlphaBV hDualEq hEligibleImp
  rw [hZero] at hPositive
  exact (by decide : ¬(1 : BitVec 8).ule 0 = true) hPositive

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.LowEligibilityBridge
