import SeymourEight.Certificates.BSevenKThree.RSix.XFour.RigidDefs
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.HDeletionTactic

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.Rigid

open Lean Parser Tactic
open Core HDeletion Shared.FiniteCore

macro "r6x4_rigid_h_deletion_decide" : tactic =>
  `(tactic|
    simp (config := { maxSteps := 1000000 }) only
      [rigidHDeletionLeaf, semiRigidHDeletionLeaf,
      aRigidDualHDeletionLeaf, rigidDualHDeletionLeaf,
      dualHDeletionLeaf, hDeletionLeaf, hQDeletionConditions,
      hDeleteQCount, hDeleteQSecond,
      hardCore, capacityDefect, exactLeaf, defectLeaf, commonCore,
      orderedZ, zIn, orderedAClasses, orderedP,
      pRowKey, sharpKing, sharpKingLower, pEffectiveCondition,
      individualEffectiveLower, individualEffectiveTable, effectiveAtRowSize,
      degreeAndDualConditions,
      crossMissing, hQDefect, etaH, alpha, externalMissing, internalMissing,
      aMissing, totalHOut, totalPToAux, totalPToQ, totalPToZ, totalHToQ,
      totalHToP, totalPToH, totalPOut, totalAOut, pNonSeymour, aNonSeymour,
      pConditions, aConditions, qReachStatus, inactiveZZero, everyZReached,
      everyXReached, qInB, noPToAOne, fixedAOne, orientedPH, orientedP,
      orientedA, threeInnerWitnesses, degreeThreeClassification,
      degreeThreeInner, degreeThree, innerSeymour, innerSecondCount,
      innerSecond, innerReaches, projectedSecondCount, projectedSecond,
      projectedReaches, pSecondPCount, strictSecondLocal, reachesLocal,
      pDegree, aDegree, pAuxOut, pZOut, hPOut, pHOut, pOut, aBOut, aPOut,
      aOut, coreArc, pToQ, aToQ, pToA, aToP, pArc, aArc,
      sumCount, count, bitCount, any, all] <;>
    simp (config := { maxSteps := 1000000 }) only
      [aRigidArc, fixedArc, rigidArc, alphaZeroArc] <;>
    bv_decide (config := { timeout := 1200, acNf := true }))

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.Rigid
