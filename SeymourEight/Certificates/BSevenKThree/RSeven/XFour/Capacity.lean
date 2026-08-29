import SeymourEight.Certificates.BSevenKThree.RSeven.XFour.Dual

namespace SeymourEight.BSevenKThree.RSeven.XFourNoRoot.Core

set_option maxRecDepth 100000

set_option maxHeartbeats 10000000 in
/-- Summing the seven `P` minimum-degree inequalities, using the oriented
`P` bound and the dual `P → H` bound, leaves at most twelve missing
`P → Z` incidences. -/
theorem externalMissing_le_twelve (bits : Encoding)
    (hA : orientedA bits = true)
    (hP : orientedP bits = true)
    (hAMin : aMinimumAndDegree bits = true)
    (hMin : pMinimumDegree 5 bits = true)
    (hDual : degreeAndDualConditions bits = true) :
    (externalMissing 5 bits).ule 12 = true := by
  simp only [orientedA, orientedP, aMinimumAndDegree, pMinimumDegree,
    degreeAndDualConditions,
    externalMissing, totalPToZ, totalPToH, pOut, pHOut, pZOut, pArc,
    pToH, pToZ, pDirectedIndex, aMissing, etaH, alpha, crossMissing,
    totalHToP, totalHOut, aOut, hPOut, aArc, hToP, hDirectedIndex,
    Shared.FiniteCore.sumCount, Shared.FiniteCore.count,
    Shared.FiniteCore.bitCount, Shared.FiniteCore.all]
      at hA hP hAMin hMin hDual ⊢
  bv_decide (config := { timeout := 300, acNf := true })

end SeymourEight.BSevenKThree.RSeven.XFourNoRoot.Core
