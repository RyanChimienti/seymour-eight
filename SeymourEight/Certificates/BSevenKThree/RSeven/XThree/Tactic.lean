import SeymourEight.Certificates.BSevenKThree.RSeven.XThree.SymmetryDefs

namespace SeymourEight.BSevenKThree.RSeven.XThreeNoRoot.SymmetricCore

open Lean Parser Tactic
open Core Shared.FiniteCore

macro "solve_x_three_core" : tactic =>
  `(tactic|
    simp (config := { maxSteps := 1000000000 }) only
      [symmetricCore, ordered, orderedP, pInvariantKey, pIn, hToPIn,
      orderedStructuralClasses, hInvariantKey, hIncidenceCode, orderedZ,
      zIncidenceCode, commonCore, degreeAndDualConditions, sharpKing,
      sharpKingLower, pEffectiveCondition, individualEffectiveLower,
      individualEffectiveLowerFive, individualEffectiveLowerSix,
      effectiveAtRowSize, tau, etaH, alpha, degreeGain, crossMissing,
      internalMissing, externalMissing, aMissing, totalHOut, totalPOut,
      totalHToP, totalPToH, totalPToZ, pMinimumDegree, aMinimumAndDegree,
      allZReached, rUnreached, everyXReached, orientedPH, orientedP, orientedA,
      threeInnerWitnesses, degreeThreeClassification, degreeThreeTieCondition,
      hallCondition, hallZCount, hallZReached, degreeThreeInner, degreeThree,
      innerSeymour, innerSecondCount, innerSecond, innerReaches,
      pSecondPCount, aNonSeymour, localSecondCount, strictSecondLocal,
      reachesLocal, pZOut, hPOut, pHOut, pOut, aPOut, aOut, directCount,
      coreArc, pToA, aToP, pToZ, hToP, pToH, pArc, pDirectedIndex, aArc,
      hDirectedIndex, any, all, sumCount, count, bitCount] <;>
    bv_decide (config := { timeout := 3600, acNf := true }))

end SeymourEight.BSevenKThree.RSeven.XThreeNoRoot.SymmetricCore
