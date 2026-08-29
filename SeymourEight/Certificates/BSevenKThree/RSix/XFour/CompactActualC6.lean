import SeymourEight.Certificates.BSevenKThree.RSix.XFour.CompactActualTailDefs
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.ActualTailTactic

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.CompactActualTail

open Shared.FiniteCore Core AuxiliaryCore ActualTail

set_option compiler.extract_closed false in
set_option compiler.reuse false in
set_option compiler.small 0 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 512000000 in
theorem compactActualC6_false
    (arc pToZ auxArc realAuxArc : Nat → Nat → Bool) :
    compactCapacityRangeLeaf 6 0 4 arc pToZ auxArc realAuxArc = false := by
  simp only [compactCapacityRangeLeaf, compactActualTailCore,
    namedDeletionConditions, namedSecondCount, auxArcSubReal]
  r6x4_actual_tail_prepare
  bv_decide (config := { maxSteps := 1000000000, timeout := 1800 })

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.CompactActualTail
