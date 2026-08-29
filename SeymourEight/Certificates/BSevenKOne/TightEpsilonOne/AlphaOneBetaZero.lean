import SeymourEight.Certificates.BSevenKOne.TightEpsilonOne.TerminalCoreDefs

namespace SeymourEight.TerminalCore

/-- The `(alpha,beta,degreeSum)=(1,0,57)` terminal core is UNSAT. -/
theorem alphaOneBetaZero_unsat (bits : BitVec 119) :
    tournamentOneMissingRootCore bits 1 57 = false := by
  simp only [tournamentOneMissingRootCore, tournamentRetainedDegree,
    tournamentEquation18At, tournamentSecondPCount, tournamentReachedViaPOrH,
    tournamentInterchangeableOrdered, tournamentPOutCount, tournamentArc,
    orientedBetweenPAndH, totalPToH, totalHToP, pToHCount, pArc, pToH, hToP,
    allFive, anyFive, sumFive, sumCountFive, allSeven, anySeven, sumSeven,
    sumCountSeven, bitCount]
  bv_decide (config := { timeout := 180, acNf := true })

end SeymourEight.TerminalCore
