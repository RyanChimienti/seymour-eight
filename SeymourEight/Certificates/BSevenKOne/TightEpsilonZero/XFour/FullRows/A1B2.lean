import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XFour.FullCoreDefs

namespace SeymourEight.ThreeZFullCore
open TerminalCore
set_option maxRecDepth 100000
set_option maxHeartbeats 64000000 in
theorem a1_b2_unsat (bits : BitVec 119) : core bits 1 19 56 = false := by
  simp (config := { maxSteps := 1000000 }) only [core, equationAt,
    interchangeableOrdered, retainedDegree, secondPCount, reachedViaPOrH,
    totalHToP, totalPToH, pToHCount, totalPOut, pOutCount,
    orientedBetweenPAndH, orientedOnP, pArc, pToH, hToP, allFive, anyFive,
    sumFive, sumCountFive, allSeven, anySeven, sumSeven, sumCountSeven,
    bitCount]
  bv_decide (config := { timeout := 600, acNf := true })
end SeymourEight.ThreeZFullCore
