import SeymourEight.Certificates.BSevenKThree.RSix.XFour.HDeletionTactic
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.ReducedPositiveDeltaDefs

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.StrongDual

open Core HDeletion

set_option compiler.extract_closed false in
set_option compiler.reuse false in
set_option compiler.small 0 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 512000000 in
theorem reducedPositiveDelta_false (arc pToZ : Nat → Nat → Bool) :
    reducedPositiveDeltaLeaf arc pToZ = false := by
  simp only [reducedPositiveDeltaLeaf, capacityTwoToFive]
  r6x4_h_deletion_decide

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.StrongDual
