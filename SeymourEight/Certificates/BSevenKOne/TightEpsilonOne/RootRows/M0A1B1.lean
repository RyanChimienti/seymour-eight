import SeymourEight.Certificates.BSevenKOne.TightEpsilonOne.RootCoreDefs

namespace SeymourEight.EpsilonOneRootCore

open TerminalCore

theorem m0a1b1_unsat (bits : Encoding) : core 0 1 1 bits = false := by
  simp only [core, orderedP, rootEquationAt, secondPCount,
    reachedViaPOrH, totalRetainedDegree, rootReached, retainedDegree,
    totalExternal, externalCount, totalHToP, totalPToH, totalPOut, pToHCount,
    pOutCount, orientedBetweenPAndH, orientedOnP, rootArc, pToZ,
    pArc, pToH, hToP, allFive, anyFive, sumFive, sumCountFive,
    allSeven, anySeven, sumSeven, sumCountSeven, bitCount]
  bv_decide (config := { timeout := 600, acNf := true })

end SeymourEight.EpsilonOneRootCore
