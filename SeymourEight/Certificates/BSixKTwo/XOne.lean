import SeymourEight.Certificates.BSixKTwo.CoreDefs

namespace SeymourEight.BSixKTwoCore

set_option maxHeartbeats 1000000 in
/-- The finite `x = 1` obstruction core is UNSAT. -/
theorem xOneCore_unsat (bits : BitVec (coreWidth 1)) :
    xOneCore bits = false := by
  simp only [xOneCore, baseCore, representedSecondCount, secondCoreCount,
    reachedInCore, reachedT, reachedW, pDegree, hDegree, internalOut, oriented,
    arc, xToT, pToW, coreWidth, coreSize, hSize, tSize, wSize,
    allN, anyN, sumN, bitCount]
  bv_decide (config := { timeout := 180, acNf := true })

end SeymourEight.BSixKTwoCore
