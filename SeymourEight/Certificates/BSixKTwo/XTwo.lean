import SeymourEight.Certificates.BSixKTwo.CoreDefs

namespace SeymourEight.BSixKTwoCore

set_option maxHeartbeats 1000000 in
/-- The finite `x = 2` obstruction core is UNSAT. -/
theorem xTwoCore_unsat (bits : BitVec (coreWidth 2)) :
    xTwoCore bits = false := by
  simp only [xTwoCore, baseCore, representedSecondCount, secondCoreCount,
    reachedInCore, reachedT, reachedW, pDegree, hDegree, internalOut, oriented,
    arc, xToT, pToW, coreWidth, coreSize, hSize, tSize, wSize,
    allN, anyN, sumN, bitCount]
  bv_decide (config := { timeout := 180, acNf := true })

end SeymourEight.BSixKTwoCore
