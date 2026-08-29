import SeymourEight.Certificates.BSevenKThree.RSix.XFour.D501PositiveTactic

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.D501Positive

set_option compiler.extract_closed false in
set_option compiler.reuse false in
set_option compiler.small 0 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 512000000 in
theorem d501Positive_false (raw pToZ : Nat → Nat → Bool) :
    d501PositiveLeaf raw pToZ = false := by
  r6x4_d501_positive_decide

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.D501Positive
