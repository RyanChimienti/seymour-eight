import SeymourEight.Certificates.BSevenKThree.RFive.XTwo.CoreDefs

namespace SeymourEight.BSevenKThree.RFive.XTwoNoRoot.Core

open Lean Parser Tactic SeymourEight.BSixKThreeCore

macro "r5x2_decide" : tactic =>
  `(tactic|
    simp (config := { maxSteps := 1000000000 }) only
      [core, qReached, pivotRow, representedSecondCount, reachedExternal,
      secondLocal, reachedLocal, outB, internalA, localOut, sumN, allN, anyN,
      sumCountsN, bitCount] <;>
    bv_decide (config := { timeout := 1800, acNf := true }))

macro "r5x2_hard_decide" : tactic =>
  `(tactic|
    simp (config := { maxSteps := 1000000000 }) only
      [hardCore, core, qReached, pivotRow, representedPSecondCount,
      reachedExternalStrict, representedSecondCount, reachedExternal,
      augmentedNonSeymour, hallCondition, qOut, reachesBothQ,
      qAnonymousLower, qAnonymousDefect, pToQ, hToQ,
      hallCount, hallReached, aPOut, threeInnerWitnesses,
      degreeThreeClassification, degreeThreeInner, degreeThree, innerSeymour,
      innerSecondCount, innerSecond, innerReaches,
      secondLocal, reachedLocal, outB, internalA, localOut, sumN, allN, anyN,
      sumCountsN, bitCount] <;>
    bv_decide (config := { timeout := 1800, acNf := true }))

end SeymourEight.BSevenKThree.RFive.XTwoNoRoot.Core
