import SeymourEight.Certificates.BSevenKTwo.RSix.XTwo.CoreDefs

namespace SeymourEight.BSevenKTwo.RSix.XTwoNoRoot.Core

set_option maxHeartbeats 512000000 in
set_option maxRecDepth 100000 in
/-- Every oriented six-vertex `P` graph has the sharp almost-tournament
two-step king used by the projected finite core. -/
theorem sharpKing_of_orientedP (bits : Encoding)
    (h : orientedP bits = true) : sharpKing bits = true := by
  simp (config := { maxSteps := 1000000000 }) only
    [orientedP, sharpKing, internalMissing, totalPOut, pOut, reachCount,
      reachesPH, defectLoss, pToA, aToP, rToP, hToP, pToH, pArc,
      directedIndex, Shared.FiniteCore.sumCount, Shared.FiniteCore.count,
      Shared.FiniteCore.bitCount, Shared.FiniteCore.any,
      Shared.FiniteCore.all] at *
  bv_decide

end SeymourEight.BSevenKTwo.RSix.XTwoNoRoot.Core
