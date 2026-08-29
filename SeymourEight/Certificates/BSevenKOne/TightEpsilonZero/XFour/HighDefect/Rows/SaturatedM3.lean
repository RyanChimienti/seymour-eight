import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XFour.HighDefect.CompactDeletion

namespace SeymourEight.ThreeZSaturated

open FiveZExactRisk

set_option maxRecDepth 100000
set_option maxHeartbeats 64000000 in
theorem saturatedCore_m3_unsat (bits : Encoding) :
    compactSaturatedCoreAtMissing 3 bits = false := by
  simp (config := { maxSteps := 1000000 }) only [compactSaturatedCoreAtMissing,
    compactSaturatedCoreAtMissingPToH,
    orderedZ, zCode, orderedP, pDegree, fixedStructure, compactAOneDeletionExpands,
    compactDeletionExpansionCount, reachedFromRetainedNeighbor,
    deletionExternalTarget, aOneNeighbor,
    aNonSeymour, aSecondCount, secondFromA, reachedFromA, totalMissingPZ,
    totalPToH, aPOut, aOut, coreOutdegree, coreArc, pToA, aToP, aArc, rToP,
    pToZ, hToP, pToH, pArc, upperIndex, orientedSquare, all, any, count,
    count16, bitCount, bitCount16]
  bv_decide (config := { timeout := 600, acNf := true })

end SeymourEight.ThreeZSaturated
