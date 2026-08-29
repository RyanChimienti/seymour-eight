import SeymourEight.Certificates.BSevenKTwo.RSix.XThree.CoreDefs

namespace SeymourEight.BSevenKTwo.RSix.XThreeNoRoot.Core

set_option maxHeartbeats 512000000 in
set_option maxRecDepth 100000 in
theorem sharpKing_of_orientedP (bits : Encoding)
    (h : orientedP bits = true) : sharpKing bits = true := by
  simp (config := { maxSteps := 1000000000 }) only
    [orientedP, sharpKing, internalMissing, totalPOut, pOut, reachCount,
    reachesPH, defectLoss, coreArc, pToA, aToP, aToQ, pToE, rToP,
    hToP, pToH, pArc,
    SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot.Core.pToZ,
    SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot.Core.rToP,
    SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot.Core.hToP,
    SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot.Core.pToH,
    SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot.Core.pArc,
    SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot.Core.directedIndex,
    Shared.FiniteCore.sumCount, Shared.FiniteCore.count,
    Shared.FiniteCore.bitCount, Shared.FiniteCore.any,
    Shared.FiniteCore.all] at *
  bv_decide (config := { timeout := 1800, acNf := true })

end SeymourEight.BSevenKTwo.RSix.XThreeNoRoot.Core
