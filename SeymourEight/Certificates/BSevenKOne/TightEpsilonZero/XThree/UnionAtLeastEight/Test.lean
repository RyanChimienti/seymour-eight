import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XThree.UnionAtLeastEight.CoreDefs

namespace SeymourEight.FourZUnionEight

open FiveZExactRisk

set_option maxRecDepth 100000
set_option maxHeartbeats 64000000 in
theorem test_m0_d63 (bits : BitVec 105) : core 0 63 bits = false := by
  simp only [core, orderedP, pNonSeymour, pDegree, externalSecondLower,
    externalFirst, secondPCount, secondPViaPOrH, reachedPViaPOrH,
    totalMissingPPairs, totalHToP, totalPToH, pHOut, pOut, orientedPH,
    pArc, pToH, hToP, orientedSquare, sumCount, all, any, count, bitCount]
  bv_decide (config := { timeout := 600, acNf := true })

end SeymourEight.FourZUnionEight
