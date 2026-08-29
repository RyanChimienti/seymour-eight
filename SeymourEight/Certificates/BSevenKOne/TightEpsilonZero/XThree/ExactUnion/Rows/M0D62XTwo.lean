import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.CoreDefs

namespace SeymourEight.FourZExactSeven

open FiveZExactRisk

set_option maxRecDepth 100000
set_option maxHeartbeats 64000000 in
theorem core_m0_d62_xTwo_unsat (bits : BitVec 214) :
    core 0 62 .xTwo bits = false := by
  simp only [core, orderedP, orderedH, hCode, zNonSeymour, zSecondCount,
    reachesOutsideHFromZ, secondPFromZ, reachesPFromZ, secondWFromZ,
    reachesWFromZ, secondZFromZ, reachesZFromZ, zDegree, exceptionalZToP,
    fixedAStructure, hNonSeymour, hSecondCount, reachesZFromH, secondPFromH,
    reachesPFromH, secondAFromH, reachesAFromH, hDegree, aOut, pNonSeymour,
    pSecondCount, pDegree, missingZSecond, secondOutsideHCount, secondOutsideH,
    reachesOutsideH, secondWCount, secondW, directWFromP, reachesW,
    secondPCount, secondPViaPOrH, reachedPViaPOrH, pToZ, totalMissingPPairs,
    totalHToP, totalPToH, hPOut, pHOut, pOut, orientedPH, z0ToP0, zToW,
    zArc, aArc, hToP, pToH, pArc, hInW, wMatchesH, orientedSquare, sumCount,
    all, any, count, count16, bitCount, bitCount16]
  bv_decide (config := { timeout := 600, acNf := true })

end SeymourEight.FourZExactSeven
