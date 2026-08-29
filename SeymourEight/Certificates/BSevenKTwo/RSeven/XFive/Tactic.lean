import SeymourEight.Certificates.BSevenKTwo.RSeven.XFive.CoreDefs

namespace SeymourEight.BSevenKTwo.RSeven.XFiveNoRoot.Core

open Lean Parser Tactic

macro "solve_x_five_no_root" : tactic =>
  `(tactic|
    simp (config := { maxSteps := 1000000000 }) only
      [easyCore, hardCore, sliceCore, suffixCore, degreeEightSuffix, pExactEight,
      baseCore, orderedStructuralClasses, orderedZ,
      zColumnCode, orderedP, pRowKey, sharpKing, sharpKingLower,
      pEffectiveCondition, individualEffectiveLower, effectiveAtRowSize,
      dualTail, exactDegreeCount, xExactDegree, eligibleCount,
      xDeletionExpands, deletionCount, deletionTarget, atLeastSeven,
      retainedAfterAOneDeletion,
      xEligible, hMissing, hDefect, combinedDefect, internalMissing,
      externalMissing, totalPOut, totalHToP, totalPToH, totalPToZ,
      pMinimumDegree, aMinimumAndDegree, allZReached, everyXReached, fixedA,
      orientedPH, orientedP, orientedA, pSecondPCount, pNonSeymour,
      aNonSeymour, localSecondCount, strictSecondLocal, reachesLocal, pZOut,
      hPOut, pHOut, pOut, aPOut, aOut, directCount, coreArc, pToA, aToP,
      pToZ, hToP, pToH, pArc, directedIndex, aArc,
      Shared.FiniteCore.any, Shared.FiniteCore.all, Shared.FiniteCore.sumCount,
      Shared.FiniteCore.count, Shared.FiniteCore.bitCount] <;>
    bv_decide (config := { timeout := 1800, acNf := true }))

end SeymourEight.BSevenKTwo.RSeven.XFiveNoRoot.Core
