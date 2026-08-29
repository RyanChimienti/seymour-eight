import SeymourEight.Certificates.BSevenKThree.RFive.XFour.Tactic

namespace SeymourEight.BSevenKThree.RFive.XFourNoRoot.Core

open Shared.FiniteCore

def perfectDirectCore (arc pToZ : Nat → Nat → Bool) : Bool :=
  orientedA arc && orientedP arc && orientedPH arc && fixedAOne arc &&
    noPToAOne arc && qInB arc && qReachStatus 1 arc &&
    everyZReached 2 pToZ && aConditions arc && pConditions 2 arc pToZ &&
    degreeAndDualConditions 1 arc && (externalMissing 2 arc pToZ).ule 3 &&
    externalMissing 2 arc pToZ == 0 &&
    totalPToH arc == 15 && totalHToP arc == 20 && orderedQ arc &&
    aNonSeymour 1 2 arc pToZ

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
theorem perfectDirectCore_false (arc pToZ : Nat → Nat → Bool) :
    perfectDirectCore arc pToZ = false := by
  simp (config := { maxSteps := 100000000 }) only
    [perfectDirectCore, orderedQ, qIn, degreeAndDualConditions, crossMissing,
      hQDefect, etaH, alpha, externalMissing, qMissing,
      aMissing, totalHOut, totalPToAux, totalPToQ, totalPToZ, totalHToQ,
      totalHToP, totalPToH, totalAOut, aNonSeymour,
      reachesBothQFromA, qAnonymousLower, projectedSecondCount,
      projectedSecond, projectedReaches, coreArc, pConditions, aConditions,
      everyZReached, qReachStatus, qReached, qInB, noPToAOne, fixedAOne,
      orientedPH, orientedP, orientedA, pDegree, aDegree, pAuxOut, pZOut,
      pQOut, hPOut, pHOut, pOut, aBOut, aQOut, aPOut, aOut, pToQ, aToQ,
      pToA, aToP, pArc, aArc, sumCount, count, bitCount, any, all]
  bv_decide (config := { timeout := 1200, acNf := true })

end SeymourEight.BSevenKThree.RFive.XFourNoRoot.Core
