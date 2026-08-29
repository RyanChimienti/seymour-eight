import SeymourEight.Certificates.BSevenKThree.RSix.XFour.SatTailTactic

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.SatTail

set_option compiler.extract_closed false in
set_option compiler.reuse false in
set_option compiler.small 0 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 512000000 in
theorem satCOne_false
    (arc pToZ auxArc extraAuxArc : Nat → Nat → Bool)
    (outsideCount : BitVec 5) (outsidePrivateLoss : Nat → BitVec 5)
    (pathCount : Nat → BitVec 5) (namedSecondCount : BitVec 5) :
    satC1Leaf arc pToZ auxArc extraAuxArc outsideCount outsidePrivateLoss
      pathCount namedSecondCount = false := by
  r6x4_sat_tail_decide

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.SatTail
