import SeymourEight.Certificates.BSevenKThree.RSix.XFour.ActualTailDefs
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.AuxiliaryTactic

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.ActualTail

open Lean Parser Tactic
open Shared.FiniteCore Core AuxiliaryCore

macro "r6x4_actual_tail_prepare" : tactic =>
  `(tactic|
    simp (config := { maxSteps := 5000000 }) only
      [encodedCapacityRangeLeaf, encodedOutsideArc, encodedExtraAuxArc,
      encodedAuxArc, encodedPToZ, encodedArc,
      actualDefectLeaf, actualCapacityRangeLeaf, actualCapacityLeaf,
      zeroCapacityLeaf, actualTailCore,
      deletionConditions, reachedSlotPrefix,
      actualAuxiliaryOriented, combinedAuxArc,
      deletionSecondCount, deletionSlotReached, deletionSecondNamed,
      deletionReachesNamed, actualSecondCount, actualSlotReached,
      actualSecondNamed, actualReachesNamed, actualNamedArc,
      canonicalAuxiliaryCore, canonicalFullNonSeymour,
      canonicalFullSecondCount, canonicalHallConditions, canonicalHallCount,
      AuxiliaryCore.canonicalOutsideNeed,
      AuxiliaryCore.auxiliaryCore,
      AuxiliaryCore.fullNonSeymour, AuxiliaryCore.fullSecondCount,
      AuxiliaryCore.fullOutsideCount, AuxiliaryCore.sourceHitsMask,
      AuxiliaryCore.fullSecondNamed, AuxiliaryCore.fullReachesNamed,
      AuxiliaryCore.namedArc, AuxiliaryCore.sourceDirect, AuxiliaryCore.pDirect,
      AuxiliaryCore.hallConditions, AuxiliaryCore.hallCount,
      AuxiliaryCore.hallZReached, AuxiliaryCore.auxiliaryOriented,
      AuxiliaryCore.incomingToAux, AuxiliaryCore.auxiliaryExact,
      AuxiliaryCore.auxOutsideOut, AuxiliaryCore.signatureValue,
      AuxiliaryCore.maskHas, AuxiliaryCore.auxNamedOut,
      Core.capacityDefect, Core.commonCore,
      Core.orderedZ, Core.zIn, Core.orderedAClasses, Core.orderedP,
      Core.pRowKey, Core.sharpKing, Core.sharpKingLower,
      Core.pEffectiveCondition, Core.individualEffectiveLower,
      Core.individualEffectiveTable, Core.effectiveAtRowSize,
      Core.degreeAndDualConditions, Core.crossMissing, Core.hQDefect,
      Core.etaH, Core.alpha, Core.externalMissing, Core.internalMissing,
      Core.aMissing, Core.totalHOut, Core.totalPToAux, Core.totalPToQ,
      Core.totalPToZ, Core.totalHToQ, Core.totalHToP, Core.totalPToH,
      Core.totalPOut, Core.totalAOut, Core.pNonSeymour, Core.aNonSeymour,
      Core.pConditions, Core.aConditions, Core.qReachStatus,
      Core.inactiveZZero, Core.everyZReached, Core.everyXReached, Core.qInB,
      Core.noPToAOne, Core.fixedAOne, Core.orientedPH, Core.orientedP,
      Core.orientedA, Core.threeInnerWitnesses,
      Core.degreeThreeClassification, Core.degreeThreeInner,
      Core.degreeThree, Core.innerSeymour, Core.innerSecondCount,
      Core.innerSecond, Core.innerReaches, Core.projectedSecondCount,
      Core.projectedSecond, Core.projectedReaches, Core.pSecondPCount,
      Core.strictSecondLocal, Core.reachesLocal, Core.pDegree, Core.aDegree,
      Core.pAuxOut, Core.pZOut, Core.hPOut, Core.pHOut, Core.pOut,
      Core.aBOut, Core.aPOut, Core.aOut, Core.coreArc, Core.pToQ,
      Core.aToQ, Core.pToA, Core.aToP, Core.pArc, Core.aArc,
      sumCount, count, bitCount, any, all])

macro "r6x4_actual_tail_decide" : tactic =>
  `(tactic| r6x4_actual_tail_prepare <;>
    bv_decide (config := { maxSteps := 1000000000, timeout := 1800 }))

macro "r6x4_actual_tail_trace" : tactic =>
  `(tactic| r6x4_actual_tail_prepare <;>
    bv_decide? (config := { maxSteps := 1000000000, timeout := 1800 }))

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.ActualTail
