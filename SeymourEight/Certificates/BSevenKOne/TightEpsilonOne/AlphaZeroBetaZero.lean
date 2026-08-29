import SeymourEight.Certificates.BSevenKOne.TightEpsilonOne.TerminalCoreDefs

namespace SeymourEight.TerminalCore

set_option maxHeartbeats 1000000 in
/-- The degree-sum-58 `(alpha,beta)=(0,0)` ordered terminal core is UNSAT. -/
theorem alphaZeroBetaZero_unsat (bits : BitVec 119) :
    orderedOneMissingRootEdgeCore bits 0 21 58 = false := by
  simp only [orderedOneMissingRootEdgeCore, interchangeableOrdered,
    retainedDegree, equation18At, secondPCount, reachedViaPOrH, orientedOnP,
    orientedBetweenPAndH, totalPOut, totalPToH, totalHToP, pOutCount,
    pToHCount, pArc, pToH, hToP,
    allFive, anyFive, sumFive, sumCountFive, allSeven, anySeven, sumSeven,
    sumCountSeven, bitCount]
  bv_decide (config := { timeout := 180, acNf := true })

end SeymourEight.TerminalCore
