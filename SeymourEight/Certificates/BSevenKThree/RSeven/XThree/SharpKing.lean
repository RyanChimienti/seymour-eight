import SeymourEight.Certificates.BSevenKThree.RSeven.XThree.CoreDefs

namespace SeymourEight.BSevenKThree.RSeven.XThreeNoRoot.Core

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000 in
/-- Finite sharp almost-tournament king bound on seven vertices. -/
theorem sharpKing_of_orientedP (zCount : Nat) (bits : Encoding)
    (h : orientedP bits = true) : sharpKing zCount bits = true := by
  simp only [orientedP, sharpKing, sharpKingLower, internalMissing,
    totalPOut, pSecondPCount, strictSecondLocal, reachesLocal, coreArc,
    pOut, pArc, pDirectedIndex, Shared.FiniteCore.sumCount,
    Shared.FiniteCore.count, Shared.FiniteCore.bitCount,
    Shared.FiniteCore.any, Shared.FiniteCore.all] at h ⊢
  bv_decide

end SeymourEight.BSevenKThree.RSeven.XThreeNoRoot.Core
