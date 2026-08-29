import SeymourEight.Certificates.BSixKThree.CoreDefs

namespace SeymourEight.BSixKThreeCore

set_option maxHeartbeats 2000000 in
/-- The maximal `(|P|, |X|, w) = (5, 2, 4)` core is UNSAT. -/
theorem rFiveXTwoCore_unsat (arc externalArc : Nat → Nat → Bool) :
    core 5 2 4 arc externalArc = false := by
  simp only [core, representedSecondCount, reachedExternal, secondLocal,
    reachedLocal, pivotRow, outB, internalA, localOut, sumN, allN, anyN,
    bitCount]
  bv_decide (config := { timeout := 180, acNf := true })

end SeymourEight.BSixKThreeCore
