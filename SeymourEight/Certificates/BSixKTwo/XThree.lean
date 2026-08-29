import SeymourEight.Certificates.BSixKTwo.CoreDefs

namespace SeymourEight.BSixKTwoCore

set_option maxHeartbeats 1000000 in
/-- The finite tight `x = 3` obstruction core is UNSAT. -/
theorem xThreeCore_unsat (bits : BitVec (coreWidth 3)) :
    xThreeCore bits = false := by
  simp only [xThreeCore, baseCore, representedSecondCount, secondCoreCount,
    reachedInCore, reachedT, reachedW, pDegree, hDegree, internalOut, oriented,
    totalHToP, totalPToH,
    sumCountsN, arc, xToT, pToW, coreWidth, coreSize, hSize, tSize, wSize,
    allN, anyN, sumN, bitCount]
  bv_decide (config := { timeout := 180, acNf := true })

end SeymourEight.BSixKTwoCore
