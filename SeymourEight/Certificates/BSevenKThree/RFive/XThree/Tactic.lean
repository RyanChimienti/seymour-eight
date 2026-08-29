import SeymourEight.Certificates.BSevenKThree.RFive.XThree.CoreDefs

namespace SeymourEight.BSevenKThree.RFive.XThreeNoRoot.Core

open Lean Parser Tactic

macro "r5x3_simp" : tactic => `(tactic|
  simp (config := { maxSteps := 100000000 }) only
    [dualLeafCore, qLeafCore, exactLeafCore, leafCore, defectCore, totalDefect,
    core, coreFn,
    orientedA, orientedP,
    orientedPH, fixedPivot,
    everyXReached, rUnreached, qInB, qReachStatus, qReached, allZReached,
    inactiveZZero, aMinimumAndPivot, aNonSeymour, pMinimum, hallCondition,
    hallCount, hallReached, degreeThreeClassification, threeInnerWitnesses,
    inducedConditions, inducedWitness, aOnePIndex, hPIndex,
    aOneDeletionConditions, aOneDeletionCondition, aOneDeletedReached,
    aOnePrivateTarget, aOneSecondTargetIndex, aOneNeighborIndex,
    arithmetic, pEffective, effective, effectiveFour, effectiveThree,
    effectiveAt, sharpKing, sharpKingLower, beta, alpha, etaH, tau, qDefect,
    crossMissing, aMissing, externalMissing, capacity, totalAOut, totalHToP,
    totalPToH, totalPOut, totalHToQ, totalHOut, totalPAux, totalPToQ,
    totalPDegree, qMissing, qAnonymousLower, reachesBothQ,
    augmentedNonSeymour,
    secondCount, strictSecond, reaches, innerSeymour, innerSecondCount,
    innerSecond, innerReaches, degreeThreeInner, degreeThree, pDegree,
    pAuxOut, pSecondP, pZOut, aOut, aPOut, aQOut, aBOut, pOut, pHOut,
    hPOut, hQOut, ordered, orderedZ, pKey, qIn, encodedArc, directedIndex,
    Shared.FiniteCore.sumCount, Shared.FiniteCore.count,
    Shared.FiniteCore.bitCount, Shared.FiniteCore.any, Shared.FiniteCore.all])

end SeymourEight.BSevenKThree.RFive.XThreeNoRoot.Core
