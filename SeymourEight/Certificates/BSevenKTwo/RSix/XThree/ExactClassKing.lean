import SeymourEight.Certificates.BSevenKTwo.RSix.XThree.CoreDefs

namespace SeymourEight.BSevenKTwo.RSix.XThreeNoRoot.Core

set_option maxHeartbeats 512000000 in
set_option maxRecDepth 100000 in
theorem exactClassKing_of_effective (bits : Encoding)
    (hP : orientedP bits = true)
    (hEffective : Shared.FiniteCore.all 6 (pEffectiveCondition bits) = true)
    (hExact : Shared.FiniteCore.any 6 (isExact bits) = true) :
    exactClassKing bits = true := by
  simp (config := { maxSteps := 1000000000 }) only
    [orientedP, pEffectiveCondition, pSecondPCount, strictSecondLocal,
    reachesLocal, individualEffectiveLower, effectiveAtRowSize,
    externalMissing, totalPToE, pOut, pHOut, pEOut,
    exactClassKing, exactMissing,
    exactOutside, exactInternal, exactCount, isExact, directCount,
    defectLoss, coreArc, pToA, aToP, aToQ, pToE, rToP,
    hToP, pToH, pArc,
    SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot.Core.pToZ,
    SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot.Core.rToP,
    SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot.Core.hToP,
    SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot.Core.pToH,
    SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot.Core.pArc,
    SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot.Core.directedIndex,
    Shared.FiniteCore.sumCount, Shared.FiniteCore.count,
    Shared.FiniteCore.bitCount, Shared.FiniteCore.any,
    Shared.FiniteCore.all] at *
  bv_decide (config := { timeout := 1800, acNf := true })

end SeymourEight.BSevenKTwo.RSix.XThreeNoRoot.Core
