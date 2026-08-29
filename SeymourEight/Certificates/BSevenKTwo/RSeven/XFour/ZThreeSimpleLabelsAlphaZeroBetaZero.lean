import SeymourEight.Certificates.BSevenKTwo.RSeven.XFour.ZThreeSimpleLabelsDefs

namespace SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeSimpleLabels

open ZThreeCore

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 512000000 in
theorem alphaZeroBetaZero_unsat (bits : Encoding) :
    (core 0 0 bits &&
      ((externalOrbit 0 bits && simpleLabels 0 bits) ||
       (externalOrbit 1 bits && simpleLabels 1 bits) ||
       (externalOrbit 2 bits && simpleLabels 2 bits))) = false := by
  simp (config := { maxSteps := 1000000000 }) only
    [simpleLabels, simpleRowsOrdered, lexGe, phColumnBit, externalOrbit,
     pZPattern, core, pConditions, exactClassKing, sharpKing,
     exactMissingPairs, exactOutsideOut, exactCount, pExact, pDegree,
     totalPToZ, totalHToP, totalPToH, totalPOut, allZReached, orientedPH,
     orientedP, effectiveLower, pSecondCount, pSecond, pReached, pZOut,
     pHOut, pOut, pToZ, hToP, pToH, pArc, directedIndex, all, any, count,
     bitCount]
  bv_decide (config := { timeout := 1200, acNf := true })

end SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeSimpleLabels
