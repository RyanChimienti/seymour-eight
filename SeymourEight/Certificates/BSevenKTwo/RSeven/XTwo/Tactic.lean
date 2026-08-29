import SeymourEight.Certificates.BSevenKTwo.RSeven.XTwo.CoreDefs

namespace SeymourEight.BSevenKTwo.RSeven.XTwoNoRoot.Core

open Lean Parser Tactic

macro "solve_x_two_no_root" : tactic =>
  `(tactic|
    simp (config := { maxSteps := 1000000000 }) only
      [smallCore, fiveCore, commonCore, pRowKey, orderedP, orderedZ,
      zColumnCode, individualEffectiveLower, individualEffectiveLowerThree,
      individualEffectiveLowerFour, individualEffectiveLowerSix, orderedStructuralClasses, externalMissing,
      effectiveAtRowSize, individualEffectiveLowerFive,
      pEffectiveConditionFive, pEffectiveCondition, pSecondPCount,
      internalMissing, hMissing, hDefect, xTwoScalarPresolve, xEligible,
      eligibleCount, xReachedInH, xReachCount, eligibleAdmissible,
      retainedAfterAOneDeletion, xDeletionExpands, eligibleStructure,
      sharpKingLower, sharpKing, totalPToZ, totalPToH, totalHToP, totalPOut,
      pMinimumDegree, inactiveZZero, allZReached, aMinimumAndDegree,
      everyXReached, fixedA, orientedPH, orientedP, orientedA, pNonSeymour,
      aNonSeymour, localSecondCount, strictSecondLocal, reachesLocal, pZOut,
      hPOut, pHOut, pOut, aPOut, aOut, directCount, coreArc, pToA, aToP,
      rToP, pToZ, hToP, pToH, pArc, directedIndex, aArc,
      Shared.FiniteCore.any, Shared.FiniteCore.all, Shared.FiniteCore.sumCount,
      Shared.FiniteCore.count, Shared.FiniteCore.bitCount] <;>
    simp (config := { maxSteps := 1000000000 }) only
      [aOnePairDeletionExpands, Shared.FiniteCore.all] <;>
    simp (config := { maxSteps := 1000000000 }) only
      [aOnePairDeletionReached, Shared.FiniteCore.count,
      Shared.FiniteCore.bitCount] <;>
    simp (config := { maxSteps := 1000000000 }) only
      [aOneNeighbor, aOnePairLeft, aOnePairRight,
      retainedAfterAOnePairDeletion, coreArc, pToA, aToP, rToP, pToZ,
      hToP, pToH, pArc, directedIndex, aArc, Shared.FiniteCore.any,
      Shared.FiniteCore.bitCount] <;>
    bv_decide (config := { timeout := 1800, acNf := true }))

end SeymourEight.BSevenKTwo.RSeven.XTwoNoRoot.Core
