import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XTwo.UnionAtLeastEight.HighMissingSharpKing

namespace SeymourEight.FiveZExactRisk.HighMissingCompressed

open SeymourEight.FiveZExactRisk

theorem pHOut_projectRaw (bits : BitVec 280) (i : Nat) (hi : i < 7) :
    pHOut (projectRaw bits) i = FiveZExactRisk.pHOut bits i := by
  simp [pHOut, pToH, projectRaw, FiveZExactRisk.pHOut,
    FiveZExactRisk.pToH, count, hi]

theorem pOut_projectRaw (bits : BitVec 280) (i : Nat) (hi : i < 7) :
    pOut (projectRaw bits) i = FiveZExactRisk.pOut bits i := by
  simp [pOut, pArc, projectRaw, FiveZExactRisk.pOut,
    FiveZExactRisk.pArc, count, hi]

theorem totalPToH_projectRaw (bits : BitVec 280) :
    totalPToH (projectRaw bits) = sumCount 7 (FiveZExactRisk.pHOut bits) := by
  simp only [totalPToH, pToH, projectRaw, FiveZExactRisk.pHOut,
    FiveZExactRisk.pToH, sumCount, count]
  bv_decide

theorem totalHToP_projectRaw (bits : BitVec 280) :
    totalHToP (projectRaw bits) = FiveZExactRisk.totalHToP bits := by
  simp [totalHToP, hToP, projectRaw, FiveZExactRisk.totalHToP,
    FiveZExactRisk.hToP, count]

theorem totalPOut_projectRaw (bits : BitVec 280) :
    totalPOut (projectRaw bits) = sumCount 7 (FiveZExactRisk.pOut bits) := by
  simp only [totalPOut, pOut, pArc, projectRaw, FiveZExactRisk.pOut,
    FiveZExactRisk.pArc, sumCount, count]
  bv_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem totalMissingPZ_eq_of_rows (bits : BitVec 280)
    (missing : Nat → BitVec 2)
    (hRows : all 7 (fun i =>
      rowMissing missing i == (5 - FiveZExactRisk.pZOut bits i)) = true) :
    totalMissingPZ missing = FiveZExactRisk.totalMissingPZ bits := by
  simp only [totalMissingPZ, rowMissing, FiveZExactRisk.totalMissingPZ,
    FiveZExactRisk.pZOut, FiveZExactRisk.pToZ, all, sumCount, count,
    bitCount] at hRows ⊢
  bv_decide

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000 in
/-- Project the aggregate 280-bit core to row-defect counts.  The two scalar
cuts are redundant consequences exposed here to improve the final SAT proof. -/
theorem allMissingCore_of_projection (bits : BitVec 280)
    (missing : Nat → BitVec 2)
    (hCore : familyCoreUnionEight bits = true)
    (hRows : all 7 (fun i =>
      rowMissing missing i == (5 - FiveZExactRisk.pZOut bits i)) = true)
    (hMissingLe : (totalMissingPZ missing).ule 3 = true)
    (hOrdered : orderedP (projectRaw bits) missing = true)
    (hPHCapacity : (totalHToP (projectRaw bits) +
      totalPToH (projectRaw bits)).ule 21 = true)
    (hDegreeCut : (21 + totalMissingPZ missing).ule
      (totalPOut (projectRaw bits) + totalPToH (projectRaw bits)) = true)
    (hPHLower : (4 : BitVec 8).ule (totalPToH (projectRaw bits)) = true) :
    allMissingCore (projectRaw bits) missing = true := by
  have hSharp : sharpKing (projectRaw bits) = true := by
    apply sharpKing_of_orientedP
    have hExpanded := hCore
    simp only [familyCoreUnionEight, Bool.and_eq_true] at hExpanded
    have hOr := hExpanded.1.1.1.1.1
    simp only [orientedSquare, pArc, projectRaw, all] at hOr ⊢
    bv_decide
  simp only [familyCoreUnionEight, allMissingCore, core,
    pNonSeymourUnionEight, fiveZExternalLower, pDegree, secondPCount,
    secondPViaPOrH, reachedPViaPOrH, totalMissingPZ, totalPToH,
    totalHToP, pZOut, rowMissing, totalPOut,
    orderedP, pRowKey, pHOut, pOut, pArc, pToH, hToP, projectRaw,
    FiveZExactRisk.pNonSeymourUnionEight,
    FiveZExactRisk.fiveZExternalLower, FiveZExactRisk.pDegree,
    FiveZExactRisk.secondPCount, FiveZExactRisk.secondPViaPOrH,
    FiveZExactRisk.reachedPViaPOrH, FiveZExactRisk.totalMissingPZ,
    FiveZExactRisk.totalHToP, FiveZExactRisk.pZOut,
    FiveZExactRisk.pHOut, FiveZExactRisk.pOut, FiveZExactRisk.orientedPH,
    FiveZExactRisk.pToZ, FiveZExactRisk.hToP, FiveZExactRisk.pToH,
    FiveZExactRisk.pArc, orientedSquare, all, any, sumCount, count,
    bitCount] at hCore hRows hMissingLe hOrdered hPHCapacity hDegreeCut hPHLower hSharp ⊢
  bv_decide (config := { timeout := 300, acNf := true })

end SeymourEight.FiveZExactRisk.HighMissingCompressed
