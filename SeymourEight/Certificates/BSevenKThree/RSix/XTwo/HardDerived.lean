import SeymourEight.Certificates.BSevenKThree.RSix.XTwo.HardTactic

namespace SeymourEight.BSevenKThree.RSix.XTwoNoRoot.HardCore

open Shared.FiniteCore
open SeymourEight.BSevenKThree.RSix.XFourNoRoot.Core

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem arithmetic_consequences (arc pToZ : Nat → Nat → Bool)
    (hCore : easyCore 5 true arc pToZ = true) :
    aOneInner arc = true ∧ degreeConditions arc = true ∧
      (capacityDefect arc pToZ).ule 11 = true ∧
      sharpKing arc = true ∧ (externalMissing arc pToZ).ule 11 = true := by
  simp (config := { maxSteps := 100000000 }) only
      [easyCore,
      SeymourEight.BSevenKThree.RSix.XTwoNoRoot.Core.core,
      SeymourEight.BSevenKThree.RSix.XTwoNoRoot.Core.pivotRow,
      SeymourEight.BSevenKThree.RSix.XTwoNoRoot.Core.representedSecondCount,
      SeymourEight.BSevenKThree.RSix.XTwoNoRoot.Core.reachedExternal,
      SeymourEight.BSevenKThree.RSix.XTwoNoRoot.Core.secondLocal,
      SeymourEight.BSevenKThree.RSix.XTwoNoRoot.Core.reachedLocal,
      SeymourEight.BSevenKThree.RSix.XTwoNoRoot.Core.outB,
      SeymourEight.BSevenKThree.RSix.XTwoNoRoot.Core.internalA,
      SeymourEight.BSevenKThree.RSix.XTwoNoRoot.Core.localOut,
      SeymourEight.BSixKThreeCore.sumN, SeymourEight.BSixKThreeCore.allN,
      SeymourEight.BSixKThreeCore.anyN, SeymourEight.BSixKThreeCore.bitCount,
      aOneInner, degreeThreeInner, degreeThree, innerSeymour,
      innerSecondCount, innerSecond, innerReaches,
      degreeConditions, capacityDefect, externalMissing, alpha, hQDefect,
      totalHToQ, totalHToP, totalPToH, hPOut, pHOut,
      sharpKing, sharpKingLower, internalMissing, totalPOut, pSecondPCount,
      strictSecondLocal, reachesLocal, totalPToAux, totalPToQ, totalPToZ,
      pZOut, pOut, aOut,
      pToQ, aToQ, pToA, aToP, pArc, aArc,
      sumCount, count, bitCount, any, all]
      at hCore ⊢
  bv_decide

end SeymourEight.BSevenKThree.RSix.XTwoNoRoot.HardCore
