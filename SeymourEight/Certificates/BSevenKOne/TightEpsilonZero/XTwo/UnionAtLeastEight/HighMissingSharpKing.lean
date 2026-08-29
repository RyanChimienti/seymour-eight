import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XTwo.UnionAtLeastEight.HighMissingCompressedDefs

namespace SeymourEight.FiveZExactRisk.HighMissingCompressed

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000 in
/-- Finite sharp almost-tournament king bound on the compressed `P` square. -/
theorem sharpKing_of_orientedP (raw : Nat → Nat → Bool)
    (h : orientedSquare 7 (pArc raw) = true) : sharpKing raw = true := by
  simp only [orientedSquare, sharpKing, sharpKingLower, internalMissing,
    totalPOut, pOut, secondPCount, secondPViaPOrH, reachedPViaPOrH,
    pArc, pToH, hToP, sumCount, count, bitCount, any, all] at h ⊢
  bv_decide

end SeymourEight.FiveZExactRisk.HighMissingCompressed
