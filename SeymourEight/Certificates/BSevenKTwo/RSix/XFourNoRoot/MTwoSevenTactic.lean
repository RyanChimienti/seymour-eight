import SeymourEight.Certificates.BSevenKTwo.RSix.XFourNoRoot.MTwoCoreDefs

namespace SeymourEight.BSevenKTwo.RSix.XFourNoRoot.MTwoCore

macro "solve_mtwo_leaf" : tactic => `(tactic|
  apply Bool.eq_false_of_not_eq_true <;>
  intro h <;>
  simp (config := { maxSteps := 1000000000 }) only
    [coreSevenLeaf, coreSevenPattern, coreSeven, pECode,
    eConditionsSeven, xConditionsSeven, hOutsideSecondSeven,
    auxiliaryDeletionPConditionsSeven, deletionCountESeven,
    retainedOutsideESeven, eDegreeSeven, outsideForESeven,
    orderedOutsideSeven, outsideCodeSeven, outsideAdjSeven, rConditions,
    rBOut, rInternalOut, hConditions, hBOut, hInternalOut,
    everyXReached, orderedZ, orderedH, orderedP, pRowKey,
    deletionLocalTarget, retainedReachesLocal, totals,
    saturatedPairRectangles, oriented, hLocalSecondCount,
    hStrictSecondLocal, hReachesLocal, rLocalArc, aOneLocalArc,
    pEOut, pPOut, pHOut, hPOut, pOut, eLocalArc, hLocalArc, pLocalArc,
    rToH, rToAOne, rToQ, rToP, eArc, eToRoot, eToR, eToAOne, eToH,
    eToP, hToQ, hToR, hToAOne, hArc, pToE, hToP, pToH, pArc,
    directedIndex, Shared.FiniteCore.count, Shared.FiniteCore.all,
    Shared.FiniteCore.any, Shared.FiniteCore.bitCount, Bool.and_eq_true,
    Bool.or_eq_true] at h <;>
  bv_decide (config := { maxSteps := 1000000000, timeout := 1200 }))

end SeymourEight.BSevenKTwo.RSix.XFourNoRoot.MTwoCore
