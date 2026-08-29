import SeymourEight.Certificates.BSevenKThree.RSix.XTwo.CoreDefs

namespace SeymourEight.BSevenKThree.RSix.XTwoNoRoot.Core

open Lean Parser Tactic SeymourEight.BSixKThreeCore

macro "r6x2_decide" : tactic =>
  `(tactic|
    simp (config := { maxSteps := 1000000000 }) only
      [core, qReached, pivotRow, representedSecondCount, reachedExternal,
      secondLocal, reachedLocal, outB, internalA, localOut, sumN, allN, anyN,
      bitCount] <;>
    bv_decide (config := { timeout := 1800, acNf := true }))

end SeymourEight.BSevenKThree.RSix.XTwoNoRoot.Core
