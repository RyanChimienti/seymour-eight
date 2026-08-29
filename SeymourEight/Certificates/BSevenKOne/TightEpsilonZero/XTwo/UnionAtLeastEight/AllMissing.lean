import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XTwo.UnionAtLeastEight.HighMissingCompressedDefs

namespace SeymourEight.FiveZExactRisk.HighMissingCompressed

set_option maxRecDepth 100000
set_option maxHeartbeats 64000000 in
/-- The row-count quotient covers every possible total `P → Z` defect. -/
theorem allMissingCore_unsat (raw : Nat → Nat → Bool)
    (missing : Nat → BitVec 2) : allMissingCore raw missing = false := by
  simp only [allMissingCore, core, pNonSeymourUnionEight,
    fiveZExternalLower, pDegree, secondPCount, secondPViaPOrH,
    reachedPViaPOrH, totalMissingPZ, totalPToH, totalHToP, pZOut, rowMissing,
    sharpKing, sharpKingLower, internalMissing, totalPOut, orderedP, pRowKey,
    pHOut, pOut, pArc, pToH, hToP, orientedSquare, all, any,
    sumCount, count, bitCount]
  bv_decide (config := { timeout := 1800, acNf := true })

end SeymourEight.FiveZExactRisk.HighMissingCompressed
