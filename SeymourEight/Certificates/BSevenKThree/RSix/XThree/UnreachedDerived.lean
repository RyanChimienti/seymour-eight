import SeymourEight.Certificates.BSevenKThree.RSix.XThree.Unreached

namespace SeymourEight.BSevenKThree.RSix.XThreeNoRoot.UnreachedCore

open Shared.FiniteCore
open SeymourEight.BSevenKThree.RSix.XThreeNoRoot.Core

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- The aggregate `H` arithmetic in the unreached-`Q` branch is a finite
consequence of the local orientation, reachability, and degree conditions. -/
theorem arithmetic_of_local (zCount : Nat) (arc : Nat → Nat → Bool)
    (hA : orientedA arc = true) (hAPQ : orientedAPQ arc = true)
    (hFixed : fixedPivot arc = true) (hX : everyXReached arc = true)
    (hR : rUnreached arc = true) (hQ : qUnreached arc = true)
    (hMin : aMinimumAndPivot arc = true) :
    arithmetic zCount arc = true := by
  simp only [orientedA, orientedAPQ, fixedPivot, everyXReached, rUnreached,
    qUnreached, aMinimumAndPivot, arithmetic, degreeGain, qDefect, alpha,
    tau, etaH, crossMissing, aMissing, totalAOut, totalHToP, totalPToH,
    totalHOut, aOut, aPOut, aBOut, pHOut, hPOut,
    Shared.FiniteCore.sumCount, Shared.FiniteCore.count,
    Shared.FiniteCore.bitCount, Shared.FiniteCore.any,
    Shared.FiniteCore.all] at hA hAPQ hFixed hX hR hQ hMin ⊢
  bv_decide (config := { timeout := 600, acNf := true })

end SeymourEight.BSevenKThree.RSix.XThreeNoRoot.UnreachedCore
