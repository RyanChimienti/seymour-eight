import SeymourEight.Certificates.BSevenKTwo.RSeven.XFour.ZThreeLowNoExactDefs

namespace SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeLowCore

open ZThreeCore

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 512000000 in
theorem mOneNoExact_unsat (bits : Encoding) : mOneNoExactCore bits = false := by
  simp (config := { maxSteps := 1000000000 }) only
    [mOneNoExactCore, commonCoreNoExact, mOneExternal, orderedRowsFrom,
     rowKey, orderedH, lowPConditions, lowEffectiveLower, externalMissing,
     generalSharpKing, sharpKingLower, lexGe, phColumnBit, pZPattern,
     pDegree, totalPToZ, totalHToP, totalPToH, totalPOut, allZReached,
     orientedPH, orientedP, pSecondCount, pSecond, pReached, pZOut, pHOut,
     pOut, pToZ, hToP, pToH, pArc, directedIndex, all, any, count, bitCount]
  bv_decide (config := { timeout := 1200, acNf := true })

end SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeLowCore
