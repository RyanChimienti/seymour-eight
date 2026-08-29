import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XFour.HighDefect.CompactDeletion

namespace SeymourEight.ThreeZNearSaturated

open FiveZExactRisk

set_option maxRecDepth 100000
set_option maxHeartbeats 64000000 in
theorem nearSaturatedCore_a1_b0_unsat (bits : Encoding) :
    compactNearSaturatedCore true false bits = false := by
  simp (config := { maxSteps := 1000000 }) only [compactNearSaturatedCore, orderedZ,
    zCode, orderedP, pDegree, fixedStructure, compactAOneDeletionExpands,
    compactDeletionExpansionCount, reachedFromRetainedNeighbor,
    deletionExternalTarget, aOneNeighbor,
    aNonSeymour, aSecondCount, secondFromA, reachedFromA, totalMissingPZ,
    totalPOut, totalPToH, aPOut, aOut, coreOutdegree, coreArc, pToA, aToP,
    aArc, rToP, pToZ, hToP, pToH, pArc, pPairMissing, phPairMissing,
    pMissingCode, phMissingCode, upperIndex, orientedSquare, all, any, count,
    count16, bitCount, bitCount16]
  bv_decide (config := { timeout := 600, acNf := true })

end SeymourEight.ThreeZNearSaturated
