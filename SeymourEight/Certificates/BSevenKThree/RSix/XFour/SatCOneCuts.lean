import SeymourEight.Certificates.BSevenKThree.RSix.XFour.SatTailTactic

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.SatTail

/-! Propagation-critical consequences of capacity one. -/

open Shared.FiniteCore Core AuxiliaryCore

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem capacityOneStructuralCuts (arc pToZ : Nat → Nat → Bool)
    (hCapacity : capacityDefect arc pToZ = 1)
    (hExternal : (externalMissing 1 3 arc pToZ).ule 1 = true) :
    c1PivotAuxCut arc pToZ && c1DegreeSumCut arc pToZ = true := by
  simp (config := { maxSteps := 5000000 }) only
    [c1DegreeSumCut, c1PivotAuxCut,
      capacityDefect, alpha, externalMissing, internalMissing, aMissing,
      totalPToAux, totalPToZ, totalPToQ, totalPToH, totalPOut, totalAOut,
      pDegree, pAuxOut, pZOut, pHOut, pOut, aOut,
      pDirect, coreArc, pToQ, pToA, pArc, aArc,
      sumCount, count, bitCount] at hCapacity hExternal ⊢
  bv_decide (config := { timeout := 120, acNf := true })

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.SatTail
