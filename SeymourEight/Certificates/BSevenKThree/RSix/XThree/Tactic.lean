import SeymourEight.Certificates.BSevenKThree.RSix.XThree.CoreDefs

namespace SeymourEight.BSevenKThree.RSix.XThreeNoRoot.Core

open Lean Parser Tactic Shared.FiniteCore

macro "r6x3_no_root_decide" : tactic =>
  `(tactic|
    simp (config := { maxSteps := 1000000000 }) only
      [commonCore, commonCoreFn, encodedArc, directedIndex, arithmetic, ordered, pKey, sharpKing, sharpKingLower,
      pEffective, effective, effectiveFour, effectiveFive, effectiveAt,
      totalDefect, externalMissing, totalPAux, crossMissing, etaH, tau, beta,
      alpha, qDefect, degreeGain, aMissing, totalHOut, totalPOut, totalPToH,
      totalHToP, totalAOut, inducedConditions, inducedWitness,
      threeInnerWitnesses, degreeThreeClassification, pMinimum, aNonSeymour,
      aMinimumAndPivot, allZReached, qReached, rUnreached, everyXReached,
      fixedPivot, orientedAPQ, orientedP, orientedA, hallCondition, hallCount,
      hallReached, degreeThreeInner, degreeThree, innerSeymour,
      innerSecondCount, innerSecond, innerReaches, pSecondP, secondCount,
      strictSecond, reaches, pDegree, pZOut, pAuxOut, hPOut, pHOut, pOut,
      aBOut, aPOut, aOut, any, all, sumCount, count, bitCount] <;>
    bv_decide (config := { timeout := 3600, acNf := true }))

end SeymourEight.BSevenKThree.RSix.XThreeNoRoot.Core
