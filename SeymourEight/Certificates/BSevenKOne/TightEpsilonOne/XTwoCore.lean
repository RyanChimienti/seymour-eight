import SeymourEight.Certificates.BSevenKOne.TightEpsilonOne.XTwoCoreDefs

namespace SeymourEight.EpsilonOneXTwoCore

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem core_unsat (bits : Encoding) : core bits = false := by
  simp only [core, uNonSeymour, uSecondE, uSecondP, uSecondA,
    rootEquation, secondP, reachedP, targetCovered, predecessor, fixedHStructure, orientedPH,
    orientedOnP, hDegree, pDegree, hAOut, hPOut, pEOut, pHOut, pOut,
    hToA, pToE, hToP, pToH, pArc, all, any, sumCount, count, bitCount]
  bv_decide (config := { timeout := 1800, acNf := true })

end SeymourEight.EpsilonOneXTwoCore
