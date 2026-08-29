import SeymourEight.Certificates.BSevenKThree.RSeven.XFour.RemainingDefs

namespace SeymourEight.BSevenKThree.RSeven.XFourNoRoot.RemainingCore

open Lean Parser Tactic
open Core SymmetricCore Shared.FiniteCore

macro "solve_remaining_box" : tactic =>
  `(tactic|
    simp (config := { maxSteps := 1000000000 }) only
      [boxLeaf, symmetricCore, ordered, SymmetricCore.orderedP, pInvariantKey, pIn,
      hToPIn, SymmetricCore.orderedStructuralClasses, hInvariantKey, hIncidenceCode,
      SymmetricCore.orderedZ, zIncidenceCode,
      Core.commonCore, Core.degreeAndDualConditions,
      Core.sharpKing, Core.sharpKingLower, Core.pEffectiveCondition,
      Core.individualEffectiveLower, Core.effectiveAtRowSize,
      Core.etaH, Core.alpha, Core.crossMissing, Core.internalMissing,
      Core.externalMissing, Core.aMissing, Core.totalHOut, Core.totalPOut,
      Core.totalHToP, Core.totalPToH, Core.totalPToZ, Core.pMinimumDegree,
      Core.aMinimumAndDegree, Core.inactiveZZero, Core.allZReached,
      Core.everyXReached, Core.orientedPH, Core.orientedP, Core.orientedA,
      Core.threeInnerWitnesses, Core.degreeThreeClassification,
      Core.degreeThreeTieCondition, Core.hallCondition, Core.hallZCount,
      Core.hallZReached, Core.degreeThreeInner, Core.degreeThree,
      Core.innerSeymour, Core.innerSecondCount, Core.innerSecond,
      Core.innerReaches, Core.pSecondPCount, Core.aNonSeymour,
      Core.localSecondCount, Core.strictSecondLocal, Core.reachesLocal,
      Core.pZOut, Core.hPOut, Core.pHOut, Core.pOut, Core.aPOut, Core.aOut,
      Core.directCount, Core.coreArc, Core.pToA, Core.aToP, Core.pToZ,
      Core.hToP, Core.pToH, Core.pArc, Core.pDirectedIndex, Core.aArc,
      Core.hDirectedIndex, any, all, sumCount, count, bitCount] <;>
    bv_decide (config := { timeout := 3600, acNf := true }))

end SeymourEight.BSevenKThree.RSeven.XFourNoRoot.RemainingCore
