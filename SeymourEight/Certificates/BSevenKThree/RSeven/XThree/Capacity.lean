import SeymourEight.Certificates.BSevenKThree.RSeven.XThree.Dual

namespace SeymourEight.BSevenKThree.RSeven.XThreeNoRoot.Core

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000 in
/-- The aggregate local degree bounds leave at most twelve missing
`P → Z` incidences in the five-column row. -/
theorem externalMissing_five_le_twelve (bits : Encoding)
    (hA : orientedA bits = true)
    (hP : orientedP bits = true)
    (hAMin : aMinimumAndDegree bits = true)
    (hMin : pMinimumDegree 5 bits = true)
    (hDual : degreeAndDualConditions bits = true) :
    (externalMissing 5 bits).ule 12 = true := by
  simp only [orientedA, orientedP, aMinimumAndDegree, pMinimumDegree,
    degreeAndDualConditions, degreeGain, externalMissing, totalPToZ,
    totalPToH, pOut, pHOut, pZOut, pArc, pToH, pToZ, pDirectedIndex,
    aMissing, etaH, tau, alpha, crossMissing, totalHToP, totalHOut, aOut,
    hPOut, aArc, hToP, hDirectedIndex, Shared.FiniteCore.sumCount,
    Shared.FiniteCore.count, Shared.FiniteCore.bitCount,
    Shared.FiniteCore.all] at hA hP hAMin hMin hDual ⊢
  bv_decide (config := { timeout := 300, acNf := true })

end SeymourEight.BSevenKThree.RSeven.XThreeNoRoot.Core
