import SeymourEight.Certificates.BSixKThree.CoreDefs

namespace SeymourEight.BSixKThreeCore

set_option maxHeartbeats 2000000 in
/-- The maximal `(|P|, |X|, w) = (6, 2, 6)` core is UNSAT. -/
theorem rSixXTwoCore_unsat (arc externalArc : Nat → Nat → Bool) :
    core 6 2 6 arc externalArc = false := by
  simp only [core, representedSecondCount, reachedExternal, secondLocal,
    reachedLocal, pivotRow, outB, internalA, localOut, sumN, allN, anyN,
    bitCount]
  bv_decide (config := { timeout := 180, acNf := true })

end SeymourEight.BSixKThreeCore
