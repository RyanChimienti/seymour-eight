import SeymourEight.Certificates.BSevenKThree.RSix.XFour.AuxiliaryDefs
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.Tactic

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.AuxiliaryCore

open Lean Parser Tactic
open Shared.FiniteCore
open Core

macro "r6x4_aux_decide" : tactic =>
  `(tactic|
    simp (config := { maxSteps := 5000000 }) only
      [auxiliaryAllCapacities, auxiliaryCapacityOnlyLeaf,
      auxiliaryCapacityLeaf, auxiliaryFineLeaf,
      auxiliaryDefectLeaf,
      hardAuxCore, auxiliaryCore,
      fullDeletionAt,
      externalDeletionConditions, deletionExpands, deletionRetainedCount,
      deletionRetainedOutsideCount, deletionHitsMask, deletionRetainsNamed,
      deletionReachesNamed, fullNonSeymour, fullSecondCount,
      fullOutsideCount, sourceHitsMask, fullSecondNamed, fullReachesNamed,
      namedArc, sourceDirect, pDirect,
      hallConditions, hallCount, hallZReached,
      auxiliaryOriented, incomingToAux, auxiliaryExact, auxOutsideOut,
      signatureValue, maskHas, auxNamedOut,
      Core.hardCore, Core.capacityDefect, Core.commonCore,
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
      sumCount, count, bitCount, any, all] <;>
    bv_decide (config := { maxSteps := 1000000000, timeout := 1200, acNf := true }))

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.AuxiliaryCore
