import SeymourEight.Certificates.BSevenKThree.RSeven.XThree.CoreDefs

namespace SeymourEight.BSevenKThree.RSeven.XThreeNoRoot.Core

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000 in
/-- The degree-excess and dual-capacity constraints forced by the local
minimum-degree conditions and orientation across `H × P`. -/
theorem degreeAndDual_of_local (bits : Encoding)
    (hA : orientedA bits = true)
    (hPH : orientedPH bits = true)
    (hX : everyXReached bits = true)
    (hR : rUnreached bits = true)
    (hMin : aMinimumAndDegree bits = true) :
    degreeAndDualConditions bits = true := by
  simp only [orientedA, orientedPH, everyXReached, rUnreached, aMinimumAndDegree,
    degreeAndDualConditions, degreeGain, aMissing, totalHToP, totalPToH,
    totalHOut, etaH, tau, alpha, crossMissing, aOut, aPOut, hPOut, pHOut,
    aArc, aToP, hToP, pToH, hDirectedIndex, Shared.FiniteCore.sumCount,
    Shared.FiniteCore.count, Shared.FiniteCore.bitCount,
    Shared.FiniteCore.any, Shared.FiniteCore.all] at hA hPH hX hR hMin ⊢
  bv_decide (config := { timeout := 300, acNf := true })

end SeymourEight.BSevenKThree.RSeven.XThreeNoRoot.Core
