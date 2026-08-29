import SeymourEight.Certificates.BSevenKThree.RSeven.XFour.CoreDefs

namespace SeymourEight.BSevenKThree.RSeven.XFourNoRoot.Core

set_option maxRecDepth 100000

set_option maxHeartbeats 10000000 in
/-- The degree-excess/dual-capacity identities forced by the `A` minimum
degree conditions and orientation across `H × P`.  Keeping this finite
arithmetic lemma separate prevents the main UNSAT certificates from paying
for the same bookkeeping again. -/
theorem degreeAndDual_of_local (bits : Encoding)
    (hA : orientedA bits = true)
    (hPH : orientedPH bits = true)
    (hMin : aMinimumAndDegree bits = true) :
    degreeAndDualConditions bits = true := by
  simp only [orientedA, orientedPH, aMinimumAndDegree,
    degreeAndDualConditions, aMissing, totalHToP, totalPToH, totalHOut,
    etaH, alpha, crossMissing, aOut, aPOut, hPOut, pHOut, aArc, aToP,
    hToP, pToH, hDirectedIndex, Shared.FiniteCore.sumCount,
    Shared.FiniteCore.count, Shared.FiniteCore.bitCount,
    Shared.FiniteCore.all] at hA hPH hMin ⊢
  bv_decide (config := { timeout := 300, acNf := true })

end SeymourEight.BSevenKThree.RSeven.XFourNoRoot.Core
