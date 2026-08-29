import SeymourEight.Certificates.BSevenKTwo.RSeven.XTwo.CoreDefs

namespace SeymourEight.BSevenKTwo.RSeven.XTwoNoRoot.Core

set_option maxRecDepth 100000

/-- Finite sharp almost-tournament king bound on seven vertices. -/
theorem sharpKing_of_orientedP (zCount : Nat) (bits : Encoding)
    (h : orientedP bits = true) : sharpKing zCount bits = true := by
  simp only [orientedP, sharpKing, sharpKingLower, internalMissing,
    totalPOut, pSecondPCount, strictSecondLocal, reachesLocal, coreArc,
    pOut, pArc, directedIndex, Shared.FiniteCore.sumCount,
    Shared.FiniteCore.count, Shared.FiniteCore.bitCount,
    Shared.FiniteCore.any, Shared.FiniteCore.all] at h ⊢
  bv_decide

end SeymourEight.BSevenKTwo.RSeven.XTwoNoRoot.Core
