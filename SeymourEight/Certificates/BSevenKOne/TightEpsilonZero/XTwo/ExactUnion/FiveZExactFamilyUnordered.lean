import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XTwo.ExactUnion.FiveZExactCoreDefs

namespace SeymourEight.FiveZExactRisk

set_option maxRecDepth 100000

set_option maxHeartbeats 16000000 in
/-- The union-six, `W ∩ H = {a1}` family is UNSAT without symmetry clauses. -/
theorem familyCoreUnordered_unsat (bits : BitVec 280) :
    familyCoreUnordered bits = false := by
  simp only [familyCoreUnordered, zNonSeymour, zSecondCount,
    reachesOutsideHFromZ, secondPFromZ, reachesPFromZ, secondWFromZ,
    reachesWFromZ, secondZFromZ, reachesZFromZ, zDegree, fixedAStructure,
    hNonSeymour, hSecondCount, reachesZFromH, secondPFromH, reachesPFromH,
    secondAFromH, reachesAFromH, hDegree, aOut, pNonSeymour, pDegree,
    secondMissingZCount, secondMissingZ, reachesZFromP, secondOutsideHCount,
    secondOutsideH, reachesOutsideH, secondWCount, secondW, reachesW,
    secondPCount, secondPViaPOrH, reachedPViaPOrH, totalMissingPZ,
    totalHToP, zPOut, pZOut, hPOut, pHOut, pOut, orientedPZ, orientedPH,
    orientedSquare, zToW, zArc, aArc, zToP, pToZ, hToP, pToH, pArc, all,
    any, count, bitCount]
  bv_decide (config := { timeout := 1200, acNf := true })

end SeymourEight.FiveZExactRisk
