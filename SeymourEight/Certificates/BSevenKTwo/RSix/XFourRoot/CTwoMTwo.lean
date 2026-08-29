import SeymourEight.Certificates.BSevenKTwo.RSix.XFourRoot.CoreDefs

namespace SeymourEight.BSevenKTwo.RSix.XFourRoot.Core

open RSix.XFourNoRoot.Core

set_option maxHeartbeats 20000000 in
-- The rooted transport supplies the same effective-row condition at defect two.
theorem cTwo_mTwo_aZero_bZero_unsat (bits : Encoding) :
    rootCoreCase 2 2 0 0 bits = false := by
  simp only [rootCoreCase, rootCoreAt]
  unfold orientedBasic
  simp (config := { maxSteps := 1000000000 }) only
    [orderedZ, ePIn, orderedH, hPOut, orderedP, pRowKey,
    rootPConditions,
    totalPP, totalPH, totalPE, totalHP, pSecondCount, pSecond, pReached,
    pEOut, pHOut, pOut, hToP, pToH, pArc, directedIndex,
    Shared.FiniteCore.count, Shared.FiniteCore.all, Shared.FiniteCore.any,
    Shared.FiniteCore.bitCount]
  simp (config := { maxSteps := 1000000000 }) only [pToE]
  bv_decide (config := { timeout := 1200, acNf := true })

end SeymourEight.BSevenKTwo.RSix.XFourRoot.Core
