import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XFour.HighDefect.CompactDeletion

namespace SeymourEight.ThreeZSaturated

open FiveZExactRisk

set_option maxRecDepth 100000
set_option maxHeartbeats 64000000 in
/-- The `m = 2`, `alpha = 1` alternative where all `P`/`H` pairs are
oriented, so the reverse block has total nineteen rather than eighteen. -/
theorem saturatedCore_m2_ph16_unsat (bits : Encoding) :
    compactSaturatedCoreAtMissingPToH 2 16 bits = false := by
  simp (config := { maxSteps := 1000000 }) only [compactSaturatedCoreAtMissingPToH,
    orderedZ, zCode, orderedP, pDegree, fixedStructure, compactAOneDeletionExpands,
    compactDeletionExpansionCount, reachedFromRetainedNeighbor,
    deletionExternalTarget, aOneNeighbor,
    aNonSeymour, aSecondCount, secondFromA, reachedFromA, totalMissingPZ,
    totalPToH, aPOut, aOut, coreOutdegree, coreArc, pToA, aToP, aArc, rToP,
    pToZ, hToP, pToH, pArc, upperIndex, orientedSquare, all, any, count,
    count16, bitCount, bitCount16]
  bv_decide (config := { timeout := 600, acNf := true })

end SeymourEight.ThreeZSaturated
