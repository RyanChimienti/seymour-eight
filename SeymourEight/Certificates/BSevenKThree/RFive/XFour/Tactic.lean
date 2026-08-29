import SeymourEight.Certificates.BSevenKThree.RFive.XFour.CoreDefs

namespace SeymourEight.BSevenKThree.RFive.XFourNoRoot.Core

open Lean Parser Tactic
open Shared.FiniteCore

macro "r5x4_no_root_decide" : tactic =>
  `(tactic|
    simp (config := { maxSteps := 1000000000 }) only
      [residualLeaf, commonCore, orderedZ, zIn, orderedQ, qIn,
      orderedAClasses, orderedP, pRowKey, sharpKing, sharpKingLower,
      hasAOnePInducedSeymour, aOnePSeymour,
      aOnePIndex, hasContiguousInducedSeymour, contiguousInducedSeymour,
      aOneDeletionConditions, aOneDeletionCondition, aOneDeletedReached,
      aOnePrivateTarget, aOneSecondTargetIndex,
      pEffectiveCondition, individualEffectiveLower, individualEffectiveTable,
      effectiveAtRowSize, degreeAndDualConditions, crossMissing, hQDefect,
      etaH, alpha, externalMissing, qMissing, internalMissing, aMissing,
      totalHOut, totalPToAux, totalPToQ, totalPToZ, totalHToQ, totalHToP,
      totalPToH, totalPOut, totalAOut, pNonSeymour, aNonSeymour,
      reachesBothQFromP, reachesBothQFromA, qAnonymousLower, pConditions,
      aConditions, inactiveZZero, everyZReached, everyXReached, qReachStatus,
      qReached, qInB, noPToAOne, fixedAOne, orientedPH, orientedP, orientedA,
      threeInnerWitnesses, degreeThreeClassification, degreeThreeInner,
      degreeThree, innerSeymour, innerSecondCount, innerSecond, innerReaches,
      projectedSecondCount, projectedSecond, projectedReaches, pSecondPCount,
      strictSecondLocal, reachesLocal, pDegree, aDegree, pAuxOut, pZOut,
      pQOut, hPOut, pHOut, pOut, aBOut, aQOut, aPOut, aOut, coreArc,
      pToQ, aToQ, pToA, aToP, pArc, aArc, sumCount, count, bitCount, any, all] <;>
    bv_decide (config := { timeout := 1200, acNf := true }))

end SeymourEight.BSevenKThree.RFive.XFourNoRoot.Core
