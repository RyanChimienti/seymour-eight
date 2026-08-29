import SeymourEight.Certificates.BSevenKTwo.RSix.XFourNoRoot.MTwoSevenTactic

namespace SeymourEight.BSevenKTwo.RSix.XFourNoRoot.MTwoCore

open Shared.FiniteCore

def projectedMinimalCore (bits : Encoding) : Bool :=
  oriented bits && hToQ bits 0 && hToQ bits 1 &&
    everyXReached bits && hConditions bits &&
    rConditions bits && totals bits &&
    saturatedPairRectangles bits &&
    auxiliaryDeletionPConditionsSeven bits && xConditionsSeven bits &&
    eConditionsSeven bits

def projectedMinimalCoreLeaf (lastE code4 code5 : Nat) (bits : Encoding) : Bool :=
  projectedMinimalCore bits && pEOut bits 5 == lastE &&
    (all 4 fun p => pECode bits p == 7) && pECode bits 4 == code4 &&
    pECode bits 5 == code5

set_option maxRecDepth 100000

set_option maxHeartbeats 30000000 in
theorem projectedMinimalCore_unsat (bits : Encoding) :
    projectedMinimalCore bits = false := by
  apply Bool.eq_false_of_not_eq_true
  intro h
  simp (config := { maxSteps := 1000000000 }) only
    [projectedMinimalCore,
    outsideAdjSeven,
    everyXReached, hConditions, hBOut, hInternalOut,
    rConditions, rBOut, rInternalOut,
    auxiliaryDeletionPConditionsSeven, deletionCountESeven,
    retainedOutsideESeven, xConditionsSeven, hOutsideSecondSeven,
    eConditionsSeven, eDegreeSeven, outsideForESeven,
    deletionLocalTarget, retainedReachesLocal, totals,
    hLocalSecondCount, hStrictSecondLocal, hReachesLocal, rLocalArc,
    aOneLocalArc,
    saturatedPairRectangles, oriented,
    pOut, eLocalArc, hLocalArc, pLocalArc,
    rToH, rToAOne, rToQ, rToP, eArc, eToRoot, eToR, eToAOne, eToH,
    eToP, hToQ, hToR, hToAOne, hArc, pToE, hToP, pToH, pArc,
    directedIndex, Shared.FiniteCore.count, Shared.FiniteCore.all,
    Shared.FiniteCore.any, Shared.FiniteCore.bitCount, Bool.and_eq_true,
    Bool.or_eq_true] at h
  bv_decide (config := { maxSteps := 1000000000, timeout := 1200 })

end SeymourEight.BSevenKTwo.RSix.XFourNoRoot.MTwoCore
