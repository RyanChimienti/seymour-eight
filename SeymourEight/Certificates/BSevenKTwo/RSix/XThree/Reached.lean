import SeymourEight.Certificates.BSevenKTwo.RSix.XThree.CoreDefs

namespace SeymourEight.BSevenKTwo.RSix.XThreeNoRoot.Core

set_option maxRecDepth 100000

set_option maxHeartbeats 512000000 in
/-- The complete finite obstruction when the unique `Q` vertex is reached. -/
theorem reachedCore_impossible (bits : Encoding) : core bits = false := by
  simp (config := { maxSteps := 1000000000 }) only [core, commonCore,
    orientedA, fixedA, aArc, pArc, pToH, hToP, pToE, rToP, aToQ,
    aToP, pToA, coreArc, directCount, aOut, aPOut, aBOut, pOut,
    pHOut, hPOut, pEOut, reachesLocal, strictSecondLocal,
    localSecondCount, aNonSeymour, pNonSeymour, orientedP, orientedPH,
    everyXReached, qReached, allZReached, aMinimumAndDegree,
    pMinimumDegree, uVertex, secondTarget, privateTarget, deletedReached,
    tightPrivate, totalPToE, totalHToP, totalPOut,
    externalMissing, internalMissing, aOneToQ,
    effectiveAtRowSize, individualEffectiveLower, pSecondPCount,
    pEffectiveCondition, reachesPH, reachCount, defectLoss, sharpKing,
    isExact, exactCount, exactInternal,
    exactOutside, exactMissing, exactClassKing, orderedP,
    orderedStructuralClasses,
    SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot.Core.aArc,
    SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot.Core.pArc,
    SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot.Core.pToH,
    SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot.Core.hToP,
    SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot.Core.pToZ,
    SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot.Core.rToP,
    SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot.Core.orientedA,
    SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot.Core.fixedA,
    SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot.Core.directedIndex,
    Shared.FiniteCore.sumCount, Shared.FiniteCore.count,
    Shared.FiniteCore.bitCount, Shared.FiniteCore.any,
    Shared.FiniteCore.all]
  bv_decide (config := { timeout := 1800, acNf := true })

end SeymourEight.BSevenKTwo.RSix.XThreeNoRoot.Core
