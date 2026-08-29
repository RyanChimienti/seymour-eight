import SeymourEight.Certificates.BSevenKTwo.RSeven.XFour.BroadFourCoreDefs

namespace SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.BroadFourCore

set_option maxRecDepth 100000

set_option maxHeartbeats 10000000 in
/-- Finite sharp almost-tournament king bound on seven vertices. -/
theorem sharpKing_of_orientedP (bits : Encoding)
    (h : orientedP bits = true) : sharpKing bits = true := by
  simp only [orientedP, sharpKing, sharpKingLower, internalMissing,
    totalPOut, pSecondPCount, strictSecondLocal, reachesLocal, coreArc,
    pOut, pArc, directedIndex, sumCount, count, bitCount, any, all] at h ⊢
  bv_decide

end SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.BroadFourCore
