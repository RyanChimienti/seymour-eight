import SeymourEight.Certificates.BSevenKTwo.RSix.XThree.UnreachedCoreDefs

namespace SeymourEight.BSevenKTwo.RSix.XThreeNoRoot.UnreachedCore

set_option maxRecDepth 100000

set_option maxHeartbeats 512000000 in
/-- The complete finite obstruction when the unique `Q` vertex is unreached. -/
theorem unreachedCore_impossible (bits : Encoding) : core bits = false := by
  simp (config := { maxSteps := 1000000000 }) only [core, commonCore,
    coreArc, directCount, reachesLocal, strictSecondLocal, localSecondCount,
    aNonSeymour, pNonSeymour, allZReached, qStructure,
    Core.orientedA, Core.fixedA, Core.aArc, Core.pArc, Core.pToH,
    Core.hToP, Core.pToE, Core.rToP, Core.aToQ, Core.aToP, Core.pToA,
    Core.coreArc, Core.directCount, Core.aOut, Core.aPOut, Core.aBOut,
    Core.pOut, Core.pHOut, Core.hPOut, Core.pEOut, Core.reachesLocal,
    Core.strictSecondLocal,
    Core.orientedP, Core.orientedPH,
    Core.everyXReached, Core.aMinimumAndDegree, Core.pMinimumDegree,
    Core.uVertex, Core.secondTarget, Core.privateTarget, Core.deletedReached,
    Core.tightPrivate, Core.totalPToE, Core.totalHToP,
    Core.totalPOut, Core.externalMissing, Core.internalMissing,
    Core.effectiveAtRowSize, Core.individualEffectiveLower,
    Core.pSecondPCount, Core.pEffectiveCondition, Core.reachesPH,
    Core.reachCount, Core.defectLoss, Core.sharpKing,
    Core.isExact, Core.exactCount,
    Core.exactInternal, Core.exactOutside, Core.exactMissing,
    Core.exactClassKing, Core.orderedP, Core.orderedStructuralClasses,
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

end SeymourEight.BSevenKTwo.RSix.XThreeNoRoot.UnreachedCore
