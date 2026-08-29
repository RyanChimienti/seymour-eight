import SeymourEight.Certificates.BSevenKThree.RSix.XTwo.Tactic

namespace SeymourEight.BSevenKThree.RSix.XTwoNoRoot.Core

set_option maxHeartbeats 100000000 in
set_option compiler.extract_closed false in
set_option compiler.reuse false in
set_option compiler.small 0 in
set_option maxRecDepth 100000 in
theorem six_unsat (arc externalArc : Nat → Nat → Bool) :
    core 6 false arc externalArc = false := by
  r6x2_decide

end SeymourEight.BSevenKThree.RSix.XTwoNoRoot.Core
