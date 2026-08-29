import SeymourEight.Certificates.BSixKThree.CoreDefs

namespace SeymourEight.BSixKThreeCore

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 10000 in
/-- The strengthened `(|P|, |X|, w) = (6, 4, 4)` core is UNSAT. -/
theorem rSixXFourCore_unsat (arc externalArc : Nat → Nat → Bool) :
    xFourCore arc externalArc = false := by
  simp only [xFourCore, core, representedSecondCount, reachedExternal,
    secondLocal, reachedLocal, pivotRow, outB, internalA, localOut,
    sumCountsN, sumN, allN, anyN, bitCount]
  bv_decide (config := { timeout := 300, acNf := true })

end SeymourEight.BSixKThreeCore
