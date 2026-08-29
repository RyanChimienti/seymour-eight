import SeymourEight.Certificates.BSevenKThree.RSix.XFour.CompactActualTailDefs

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.CompactActualTail

open Shared.FiniteCore Core AuxiliaryCore ActualTail

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
/-- Forget the identities of anonymous outside second neighbours.  Removing a
direct arc can only decrease their contribution, so the old exact deletion
inequality forces the named contribution after deletion to be at least its
original value. -/
theorem of_actualTailCore (p : Nat)
    (arc pToZ auxArc extraAuxArc outsideArc : Nat → Nat → Bool)
    (hTail : actualTailCore p arc pToZ auxArc extraAuxArc outsideArc = true) :
    compactActualTailCore p arc pToZ auxArc
      (combinedAuxArc auxArc extraAuxArc) = true := by
  simp only [actualTailCore, compactActualTailCore, auxArcSubReal,
    namedSecondCount, namedDeletionConditions, deletionConditions,
    actualSecondCount, deletionSecondCount, deletionSlotReached,
    actualSlotReached, combinedAuxArc, Bool.or_eq_true,
    all, any, count, bitCount] at hTail ⊢
  bv_decide (config := { timeout := 300, acNf := true })

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.CompactActualTail
