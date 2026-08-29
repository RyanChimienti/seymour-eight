import SeymourEight.Certificates.BSevenKOne.TightEpsilonOne.TerminalCoreDefs

namespace SeymourEight.TerminalCore

set_option maxHeartbeats 1000000 in
/-- The `(alpha,beta,degreeSum)=(1,1,56)` ordered terminal core is UNSAT. -/
theorem alphaOneBetaOne_unsat (bits : BitVec 119) :
    orderedOneMissingRootEdgeCore bits 1 20 56 = false := by
  simp only [orderedOneMissingRootEdgeCore, interchangeableOrdered,
    retainedDegree, equation18At, secondPCount, reachedViaPOrH, orientedOnP,
    orientedBetweenPAndH, totalPOut, totalPToH, totalHToP, pOutCount,
    pToHCount, pArc, pToH, hToP,
    allFive, anyFive, sumFive, sumCountFive, allSeven, anySeven, sumSeven,
    sumCountSeven, bitCount]
  bv_decide (config := { timeout := 180, acNf := true })

end SeymourEight.TerminalCore
