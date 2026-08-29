import SeymourEight.Certificates.BSevenKTwo.RSeven.XFour.ZThreeLowCoreDefs

namespace SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeLowCore

open ZThreeCore

set_option maxRecDepth 100000

set_option maxHeartbeats 10000000 in
/-- Sharp almost-tournament king bound on the projected seven-vertex `P`. -/
theorem generalSharpKing_of_orientedP (bits : Encoding)
    (h : orientedP bits = true) : generalSharpKing bits = true := by
  simp only [generalSharpKing, sharpKingLower, orientedP, totalPOut,
    pSecondCount, pSecond, pReached, pOut, pToH, hToP, pArc,
    directedIndex, count, bitCount, any, all] at h ⊢
  bv_decide

end SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeLowCore
