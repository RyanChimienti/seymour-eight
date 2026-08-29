import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XTwo.HighDefect.CoreDefs

namespace SeymourEight.FiveZHighDefect

open FiveZExactRisk

set_option maxRecDepth 100000
set_option maxHeartbeats 64000000 in
theorem highDefectCore_unsat (bits : BitVec 218) :
    highDefectCore bits = false := by
  simp only [highDefectCore, fixedStructure,
    aOneDeletionExpands, deletionExpansionCount, deletionReached,
    retainedAfterDelete, aOneNeighbor, aNonSeymour, aSecondCount, secondFromA,
    reachedFromA, totalMissingPZ, totalHToP, aPOut, aOut, coreOutdegree,
    coreArc, pToA, aToP, aArc, rToP, pToZ, hToP, pToH, pArc,
    orientedSquare, all, any, count, bitCount]
  bv_decide (config := { timeout := 600, acNf := true })

end SeymourEight.FiveZHighDefect
