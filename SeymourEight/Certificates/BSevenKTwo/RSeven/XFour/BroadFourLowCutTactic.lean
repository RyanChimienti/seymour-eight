import SeymourEight.Certificates.BSevenKTwo.RSeven.XFour.BroadFourLowCoreDefs

namespace SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.BroadFourLowCore

open BroadFourCore

macro "solve_low_cut" : tactic => `(tactic|
  (simp (config := { maxSteps := 1000000000 }) only
    [mTwoHPLowCore, mTwoPHLowCore, mOnePHLowCore, mOneHPLowCore,
    mOneHPHighCore, mZeroHPLowCore, mZeroHPHighCore,
    canonicalMOneTail, pZMissingOne, lowHPBounds,
    orderedHClasses, hRowKey, pProjectedCore,
    mTwoPHProjectedLowCore, mOnePHProjectedLowCore, broadCore, pRowKey,
    orderedP, orderedZ, zColumnCode, externalMissing, effectiveAtRowSize,
    individualEffectiveLower, pEffectiveCondition, pSecondPCount,
    internalMissing, sharpKingLower, sharpKing, totalPToZ, totalPToH,
    totalHToP, totalPOut, pMinimumDegree, allZReached, aMinimumAndDegree,
    everyXReached, fixedA, orientedPH, orientedP, orientedA, pNonSeymour,
    aNonSeymour, localSecondCount, strictSecondLocal, reachesLocal, pZOut,
    pHIn, hPOut, pHOut, pOut, aPOut, aOut, directCount, coreArc, pToA, aToP,
    rToP, pToZ, hToP, pToH, pArc, directedIndex, aArc, any, all,
    sumCount, count, bitCount]
   bv_decide (config := { timeout := 1200, acNf := true })))

end SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.BroadFourLowCore
