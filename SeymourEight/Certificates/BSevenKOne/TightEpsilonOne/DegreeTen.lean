import SeymourEight.Certificates.BSevenKOne.TightEpsilonOne.TerminalCoreDefs

namespace SeymourEight.TerminalCore

set_option maxHeartbeats 2000000 in
/-- The complete degree-sum-58 core, allowing degree ten, is UNSAT. -/
theorem degreeTen_unsat (bits : BitVec 119) : degreeTenCore bits = false := by
  simp only [degreeTenCore, interchangeableOrdered, retainedDegree,
    equation18At, secondPCount, reachedViaPOrH, orientedOnP,
    orientedBetweenPAndH, totalPOut, totalPToH, totalHToP, pOutCount,
    pToHCount, pArc, pToH, hToP,
    allFive, anyFive, sumFive, sumCountFive, allSeven, anySeven, sumSeven,
    sumCountSeven, bitCount]
  bv_decide (config := { timeout := 300, acNf := true })

end SeymourEight.TerminalCore
