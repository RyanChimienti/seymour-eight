import SeymourEight.Certificates.BSevenKThree.RFive.XTwo.Tactic

namespace SeymourEight.BSevenKThree.RFive.XTwoNoRoot.Core

set_option maxHeartbeats 100000000 in
set_option compiler.extract_closed false in
set_option compiler.reuse false in
set_option compiler.small 0 in
set_option maxRecDepth 100000 in
theorem five_zero_unsat (arc externalArc : Nat → Nat → Bool) :
    core 5 0 arc externalArc = false := by
  r5x2_decide

end SeymourEight.BSevenKThree.RFive.XTwoNoRoot.Core
