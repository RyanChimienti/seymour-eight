import SeymourEight.Certificates.BSevenKTwo.RSix.XFourNoRoot.LowExactDefs

namespace SeymourEight.BSevenKTwo.RSix.XFourNoRoot.MTwoCore

macro "solve_low_exact" : tactic => `(tactic|
  apply Bool.eq_false_of_not_eq_true <;>
  intro h <;>
  simp (config := { maxSteps := 1000000000 }) only
    [lowExactCore00, lowExactCore10, lowExactCore10HP, lowExactCore10HPCode,
    lowExactCore10Leaf, lowAuxPattern,
    lowExactCore10Code, lowExactCore10All, lowExactCore01All,
    lowExactCOneMOne,
    lowExactCore01, lowExactCore01Code, pECode,
    saturatedPP, saturatedPH, completePH, orderedXOnly, orderedETail,
    effectiveAuxUnionCount, badFullAuxRow, pSecondPCount,
    lowEffectivePConditions, tightHStructure, canonicalPEOneMissing,
    lowExactCore, lowTotals, lowPConditions, lowPNoDeletion,
    everyXReached, hConditions, hBOut, hInternalOut,
    rConditions, rBOut, rInternalOut,
    deletionCountESeven, retainedOutsideESeven,
    auxiliaryDeletionPConditionsSeven,
    xConditionsSeven, hOutsideSecondSeven,
    eConditionsSeven, eDegreeSeven, outsideForESeven,
    deletionLocalTarget, retainedReachesLocal,
    hLocalSecondCount, hStrictSecondLocal, hReachesLocal, rLocalArc,
    aOneLocalArc, pLocalSecondCount, pStrictSecondLocal, pReachesLocal,
    pOutsideSecondSeven, outsideAdjSeven, saturatedPairRectangles,
    orderedP, pRowKey, orderedH, hPOut,
    oriented, pEOut, pPOut, pHOut, pOut, eLocalArc, hLocalArc, pLocalArc,
    rToH, rToAOne, rToQ, rToP, eArc, eToRoot, eToR, eToAOne, eToH,
    eToP, hToQ, hToR, hToAOne, hArc, pToE, hToP, pToH, pArc,
    directedIndex, Shared.FiniteCore.count, Shared.FiniteCore.all,
    Shared.FiniteCore.any, Shared.FiniteCore.bitCount,
    Bool.and_eq_true, Bool.or_eq_true] at h <;>
  bv_decide (config := { maxSteps := 1000000000, timeout := 1200, acNf := true }))

end SeymourEight.BSevenKTwo.RSix.XFourNoRoot.MTwoCore
