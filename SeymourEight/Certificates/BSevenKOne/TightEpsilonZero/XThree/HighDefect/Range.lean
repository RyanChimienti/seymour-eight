import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XThree.HighDefect.RangeDefs

namespace SeymourEight.FourZHighDefect

open FiveZExactRisk

set_option maxRecDepth 100000
set_option maxHeartbeats 64000000 in
theorem highDefectRangeCore_unsat (bits : BitVec 218) :
    highDefectRangeCore bits = false := by
  simp (config := { maxSteps := 1000000 }) only [highDefectRangeCore,
    compactAOneDeletionExpands, compactDeletionExpansionCount,
    reachedFromRetainedNeighbor,
    deletionExternalTarget, pDegreeSum, pDegree, orderedZ, zCode, orderedP,
    fixedStructure, aOneNeighbor, aNonSeymour,
    aSecondCount, secondFromA, reachedFromA, totalMissingPZ, totalHToP, aPOut,
    aOut, coreOutdegree, coreArc, pToA, aToP, aArc, rToP, pToZ, hToP, pToH,
    pArc, orientedSquare, sumCount, all, any, count, count16, bitCount,
    bitCount16]
  bv_decide (config := { timeout := 1200, acNf := true })

end SeymourEight.FourZHighDefect
