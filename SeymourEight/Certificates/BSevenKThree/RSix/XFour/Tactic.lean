import SeymourEight.Certificates.BSevenKThree.RSix.XFour.CoreDefs

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.Core

open Lean Parser Tactic
open Shared.FiniteCore

macro "r6x4_no_root_decide" : tactic =>
  `(tactic|
    simp only [hardCore, capacityDefect, exactLeaf, defectLeaf, commonCore,
      orderedZ, zIn, orderedAClasses, orderedP,
      pRowKey, sharpKing, sharpKingLower, pEffectiveCondition,
      individualEffectiveLower, individualEffectiveTable, effectiveAtRowSize,
      degreeAndDualConditions,
      crossMissing, hQDefect, etaH, alpha, externalMissing, internalMissing,
      aMissing, totalHOut, totalPToAux, totalPToQ, totalPToZ, totalHToQ,
      totalHToP, totalPToH, totalPOut, totalAOut, pNonSeymour, aNonSeymour,
      pConditions,
      aConditions, qReachStatus, inactiveZZero, everyZReached, everyXReached,
      qInB, noPToAOne, fixedAOne, orientedPH, orientedP, orientedA, threeInnerWitnesses,
      degreeThreeClassification, degreeThreeInner, degreeThree, innerSeymour,
      innerSecondCount, innerSecond, innerReaches, projectedSecondCount,
      projectedSecond, projectedReaches, pSecondPCount, strictSecondLocal,
      reachesLocal, pDegree, aDegree, pAuxOut, pZOut, hPOut, pHOut, pOut,
      aBOut, aPOut, aOut, coreArc, pToQ, aToQ, pToA, aToP, pArc, aArc,
      sumCount, count, bitCount, any, all] <;>
    bv_decide (config := { timeout := 1200, acNf := true }))

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.Core
