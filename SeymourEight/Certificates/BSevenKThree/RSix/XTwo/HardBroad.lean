import SeymourEight.Certificates.BSevenKThree.RSix.XTwo.HardTactic

namespace SeymourEight.BSevenKThree.RSix.XTwoNoRoot.HardCore

set_option compiler.extract_closed false in
set_option compiler.reuse false in
set_option compiler.small 0 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 512000000 in
theorem hard_broad_false (arc pToZ auxArc : Nat → Nat → Bool) :
    commonCore arc pToZ auxArc = false := by
  r6x2_hard_decide

end SeymourEight.BSevenKThree.RSix.XTwoNoRoot.HardCore
