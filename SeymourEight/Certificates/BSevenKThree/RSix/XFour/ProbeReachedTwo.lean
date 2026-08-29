import SeymourEight.Certificates.BSevenKThree.RSix.XFour.Tactic

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.Core

open Shared.FiniteCore

def reachedTwoDirectCore (arc pToZ : Nat → Nat → Bool) : Bool :=
  orientedA arc && orientedP arc && orientedPH arc && fixedAOne arc &&
    noPToAOne arc && qReachStatus 1 arc && everyZReached 2 pToZ &&
    aConditions arc && pConditions 1 2 arc pToZ && orderedAClasses arc &&
    (projectedSecondCount 2 arc pToZ 7).ult (aDegree arc 7) &&
    degreeAndDualConditions 1 arc &&
    externalMissing 1 2 arc pToZ == 0 &&
    totalPToH arc == 15 && totalHToP arc == 27

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
theorem reachedTwoDirectCore_false (arc pToZ : Nat → Nat → Bool) :
    reachedTwoDirectCore arc pToZ = false := by
  simp (config := { maxSteps := 100000000 }) only
    [reachedTwoDirectCore, degreeAndDualConditions, crossMissing, hQDefect,
      etaH, alpha, externalMissing, aMissing, totalHOut,
      totalPToAux, totalPToQ, totalPToZ, totalHToQ, totalHToP, totalPToH,
      totalAOut, projectedSecondCount,
      projectedSecond, projectedReaches, coreArc, orderedAClasses,
      pConditions, aConditions,
      everyZReached, qReachStatus, noPToAOne, fixedAOne, orientedPH,
      orientedP, orientedA, pDegree, aDegree, pAuxOut, pZOut, hPOut,
      pHOut, pOut, aBOut, aPOut, aOut, pToQ, aToQ, pToA, aToP, pArc,
      aArc, sumCount, count, bitCount, any, all]
  bv_decide (config := { timeout := 1200, acNf := true })

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.Core
