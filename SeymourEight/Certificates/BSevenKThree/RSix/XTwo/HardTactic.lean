import SeymourEight.Certificates.BSevenKThree.RSix.XTwo.HardDefs

namespace SeymourEight.BSevenKThree.RSix.XTwoNoRoot.HardCore

open Lean Parser Tactic Shared.FiniteCore
open SeymourEight.BSevenKThree.RSix.XFourNoRoot.Core

macro "r6x2_hard_decide" : tactic =>
  `(tactic|
    simp (config := { maxSteps := 1000000000 }) only
      [exactLeaf, commonCore, easyCore,
      SeymourEight.BSevenKThree.RSix.XTwoNoRoot.Core.core,
      SeymourEight.BSevenKThree.RSix.XTwoNoRoot.Core.pivotRow,
      SeymourEight.BSevenKThree.RSix.XTwoNoRoot.Core.representedSecondCount,
      SeymourEight.BSevenKThree.RSix.XTwoNoRoot.Core.reachedExternal,
      SeymourEight.BSevenKThree.RSix.XTwoNoRoot.Core.secondLocal,
      SeymourEight.BSevenKThree.RSix.XTwoNoRoot.Core.reachedLocal,
      SeymourEight.BSevenKThree.RSix.XTwoNoRoot.Core.outB,
      SeymourEight.BSevenKThree.RSix.XTwoNoRoot.Core.internalA,
      SeymourEight.BSevenKThree.RSix.XTwoNoRoot.Core.localOut,
      SeymourEight.BSixKThreeCore.sumN, SeymourEight.BSixKThreeCore.allN,
      SeymourEight.BSixKThreeCore.anyN, SeymourEight.BSixKThreeCore.bitCount,
      fullHallConditions, fullHallCount, aOneInner,
      fullHallZReached, fullNonSeymour, fullSecondCount, fullOutsideSecond,
      fullSecondNamed, fullReachesNamed, namedArc, namedDirect,
      auxiliaryOriented, auxiliaryExact, auxOutside, auxOutsideNeed,
      auxNamedOut, auxIncoming, hallConditions, hallCount, hallZReached,
      selectedNonSeymour, selectedSecondCount,
      extendedOutsideSecond, extendedZSecond, extendedLocalSecond, qTrimmed,
      orderedZ, orderedAClasses, orderedP, pRowKey,
      inducedConditions, inducedWitness, pEffective,
      effectiveTable, effectiveAt, degreeConditions, capacityDefect,
      externalMissing, alpha,
      hQDefect, totalHToQ, totalHToP, totalPToH, pNonSeymour, pConditions,
      everyXReached, noToR, pDegree, hPOut, pHOut,
      SeymourEight.BSevenKThree.RSix.XFourNoRoot.Core.sharpKing,
      sharpKingLower, internalMissing, totalPOut, pSecondPCount,
      degreeThreeClassification, threeInnerWitnesses, degreeThreeInner,
      degreeThree, innerSeymour, innerSecondCount, innerSecond, innerReaches,
      aNonSeymour, aConditions, qReachStatus, everyZReached, qInB,
      noPToAOne, fixedAOne, orientedPH, orientedP, orientedA,
      projectedSecondCount, projectedSecond, projectedReaches, coreArc,
      strictSecondLocal, reachesLocal, totalPToAux, totalPToQ, totalPToZ,
      pAuxOut, pZOut, pOut, aDegree, aBOut, aPOut, aOut, pToQ, aToQ,
      zIn, pToA, aToP, pArc, aArc, sumCount, count, bitCount, any, all] <;>
    bv_decide (config := { timeout := 1800, acNf := true }))

end SeymourEight.BSevenKThree.RSix.XTwoNoRoot.HardCore
