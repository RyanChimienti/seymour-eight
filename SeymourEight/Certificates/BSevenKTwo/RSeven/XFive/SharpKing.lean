import SeymourEight.Certificates.BSevenKTwo.RSeven.XFive.CoreDefs

namespace SeymourEight.BSevenKTwo.RSeven.XFiveNoRoot.Core

set_option maxRecDepth 100000

theorem sharpKing_of_orientedP (bits : Encoding) (h : orientedP bits = true) :
    sharpKing bits = true := by
  simp only [orientedP, sharpKing, sharpKingLower, internalMissing,
    totalPOut, pSecondPCount, strictSecondLocal, reachesLocal, coreArc,
    pOut, pArc, directedIndex, Shared.FiniteCore.sumCount,
    Shared.FiniteCore.count, Shared.FiniteCore.bitCount,
    Shared.FiniteCore.any, Shared.FiniteCore.all] at h ⊢
  bv_decide

end SeymourEight.BSevenKTwo.RSeven.XFiveNoRoot.Core
